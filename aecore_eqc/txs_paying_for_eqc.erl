%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Hans Svensson
%%% @doc Paying for
%%%

-module(txs_paying_for_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-import(txs_eqc, [gen_tx/1]).
-import(txs_ga_eqc, [not_wga/1]).

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
  ?LET(TxArgs = [_M, _Tx, _TxData], gen_tx(?PAYING(Paying, not_wga(S))),
  ?LET({Nonce, Fee}, {gen_nonce(), gen_fee_above(S, 7000)},
    [Paying, #{ nonce => Nonce, fee => Fee }, TxArgs]
  ))).

paying_for_pre(S, [_P, _, TxArgs]) ->
  maps:get(protocol, S) >= ?IRIS_PROTOCOL_VSN  %% TODO: Properly model valid_at_protocol
  andalso txs_eqc:tx_pre(S, TxArgs).

paying_for_valid(S = #{protocol := P}, [Paying, PTx, [M, Tx, TxData]]) ->
  P >= ?IRIS_PROTOCOL_VSN
  andalso is_account(S, Paying)
  andalso check_balance(S, Paying, maps:get(fee, PTx) + deep_fee(TxData))
  andalso maps:get(fee, PTx) >= 7000 * minimum_gas_price(P)
  andalso maps:get(nonce, PTx) == good
  andalso apply(M, ?valid(Tx), [?PAYING(Paying, not_wga(S)), TxData]).

paying_for_tx(S, [Paying, PTx, [M, Tx, TxData] = TxArgs]) ->
  {ok, InnerTx} = apply(M, ?tx(Tx), [try_bump_nonce(Paying, not_wga(S)), TxData]),

  STx           = sign(S, basic_signers(S, TxArgs), Tx, InnerTx),

  PayingId      = aeser_id:create(account, get_account_key(S, Paying)),
  PTx1          = update_nonce(S, Paying, PTx#{payer_id => PayingId, tx => STx}),
  aec_paying_for_tx:new(PTx1).

paying_for_next(S, Value, Args = [Paying, MTx, [M, Tx, TxData]]) ->
  case paying_for_valid(S, Args) of
    true ->
      #{ fee := Fee } = MTx,
      S1 = bump_nonce(Paying, S),
      S2 = apply(M, ?next(Tx), [?PAYING(Paying, S1), Value, TxData]),
      reserve_fee(Fee, charge(Paying, Fee, ?NO_PAYING(S2)));
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

sign(_, _, ga_meta, GAMeta) -> aetx_sign:new(GAMeta, []);
sign(S, Signers, _, Tx) -> sign_(S, Signers, Tx, []).

sign_(_S, [], Tx, Sigs) -> aetx_sign:new(Tx, Sigs);
sign_(S, [Signer | Signers], Tx, Sigs) ->
  case get_account(S, Signer) of
    #account{ key = Key } ->
      #key{ private = PrivKey } = maps:get(Key, maps:get(keys, S)),

      STx = case maps:get(protocol, S) < ?LIMA_PROTOCOL_VSN of
              true  -> aec_test_utils:sign_tx(Tx, PrivKey, false);
              false -> aec_test_utils:sign_tx(Tx, PrivKey, true)
            end,
      sign_(S, Signers, Tx, Sigs ++ aetx_sign:signatures(STx));
    _ ->
      sign_(S, Signers, Tx, Sigs)
  end.

basic_signers(_S, [_, ga_meta, _]) -> [];
basic_signers(S, TxArgs) -> txs_ga_eqc:signers(S, TxArgs).

deep_fee(Args) when is_list(Args) -> lists:sum([deep_fee(A) || A <- Args ]);
deep_fee(Arg) when is_map(Arg)    -> tx_fee(Arg);
deep_fee(_)                       -> 0.

tx_fee(#{ fee := Fee, gas := Gas, gas_price := GasPrice }) -> Fee + Gas * GasPrice;
tx_fee(#{ fee := Fee }) -> Fee.

try_bump_nonce(Id, S) ->
  try bump_nonce(Id, S)
  catch _:_ -> S end.
