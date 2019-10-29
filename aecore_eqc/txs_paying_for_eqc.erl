%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Hans Svensson
%%% @doc Paying for
%%%

-module(txs_paying_for_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-import(txs_eqc, [gen_tx/1]).

-include("txs_eqc.hrl").

%% -- State and state functions ----------------------------------------------
initial_state(S) -> S.

%% --- Operation: paying_for ---
-define(PAYING(A, S), (S)#{ paying_for => A }).
-define(NO_PAYING(S), maps:remove(paying_for, S)).

paying_for_pre(S) ->
  maps:size(maps:get(accounts, S)) > 1.

paying_for_args(S) ->
  ?LET(Paying, gen_account(1, 49, S),
  ?LET(TxArgs = [_M, _Tx, _TxData], gen_tx(?PAYING(Paying, txs_ga_eqc:not_wga(S))),
  ?LET({Nonce, Fee}, {gen_nonce(), gen_fee_above(S, 5500)},
    [Paying, #{ nonce => Nonce, fee => Fee }, TxArgs]
  ))).

paying_for_pre(S, [_P, _, TxArgs]) ->
  maps:get(protocol, S) >= ?IRIS_PROTOCOL_VSN  %% TODO: Properly model valid_at_protocol
  andalso txs_eqc:tx_pre(S, TxArgs).

paying_for_valid(S = #{protocol := P}, [Paying, PTx, [M, Tx, TxData] = TxArgs]) ->
  P >= ?IRIS_PROTOCOL_VSN
  andalso is_account(S, Paying)
  andalso check_balance(S, Paying, maps:get(fee, PTx) + deep_fee(TxData))
  andalso Paying /= signer(S, TxArgs)
  andalso maps:get(fee, PTx) >= 5500 * minimum_gas_price(P)
  andalso maps:get(nonce, PTx) == good
  andalso apply(M, ?valid(Tx), [?PAYING(Paying, S), TxData]).

paying_for_tx(S, [Paying, PTx, [M, Tx, TxData] = TxArgs]) ->
  {ok, InnerTx} = apply(M, ?tx(Tx), [S, TxData]),
  STx           = sign(S, signer(S, TxArgs), Tx, InnerTx),

  PayingId      = aeser_id:create(account, get_account_key(S, Paying)),
  PTx1          = update_nonce(S, Paying, PTx#{payer_id => PayingId, tx => STx}),
  aec_paying_for_tx:new(PTx1).

paying_for_next(S, Value, Args = [Paying, MTx, [M, Tx, TxData]]) ->
  case paying_for_valid(S, Args) of
    true ->
      #{ fee := Fee } = MTx,
      S1 = apply(M, ?next(Tx), [?PAYING(Paying, S), Value, TxData]),
      reserve_fee(Fee, bump_and_charge(Paying, Fee, ?NO_PAYING(S1)));
    _ -> S
  end.

paying_for_post(S, Args, Res) ->
  common_postcond(paying_for_valid(S, Args), Res).

paying_for_features(S, Args = [_, _, [_, Tx, _]], Res) ->
  Correct = paying_for_valid(S, Args),
  [{correct, if Correct -> paying_for; true -> false end}] ++
  [{paying_for, Res}] ++
  [{paying_for_inner, Tx} ].

weight(S, paying_for) ->
  case good_accounts(S) of
    []  -> 0;
    _   -> case maps:size(maps:get(accounts, S, #{})) < 3 of
              true  -> 0;
              false -> 10 end
  end;
weight(_S, _) -> 0.

%% -- Local helpers ---------------------------------------------------------
sign(_S, _Signer, ga_meta, Tx) ->
  aetx_sign:new(Tx, []);
sign(S, Signer, _, Tx) ->
  case get_account(S, Signer) of
    #account{ key = Key } ->
      #key{ private = PrivKey } = maps:get(Key, maps:get(keys, S)),

      case maps:get(protocol, S) < ?LIMA_PROTOCOL_VSN of
        true  -> aec_test_utils:sign_tx(Tx, PrivKey, false);
        false -> aec_test_utils:sign_tx(Tx, PrivKey, true)
      end;
    _ ->
      aetx_sign:new(Tx, [])
  end.

signer(S, Id) -> txs_ga_eqc:ga_signer(S, Id).

deep_fee(Args) when is_list(Args) -> lists:sum([deep_fee(A) || A <- Args ]);
deep_fee(Arg) when is_map(Arg)    -> tx_fee(Arg);
deep_fee(_)                       -> 0.

tx_fee(#{ fee := Fee, gas := Gas, gas_price := GasPrice }) -> Fee + Gas * GasPrice;
tx_fee(#{ fee := Fee }) -> Fee.
