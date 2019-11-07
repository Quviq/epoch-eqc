%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Hans Svensson
%%% @doc Generalized accounts

-module(txs_ga_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-import(txs_eqc, [gen_tx/1]).

-import(txs_contracts_eqc, [gen_contract_opts/1, contract_tx_fee/4, contract_gas/4]).

-import(txs_channels_eqc, [is_channel_party/3]).

-include("txs_eqc.hrl").

%% -- State and state functions ----------------------------------------------
initial_state(S) -> S#{ contracts => #{} }.

%% --- Operation: ga_attach ---
ga_attach_pre(S) ->
  length(non_ga_accounts(S)) > 0.

ga_attach_args(#{protocol := P} = S) ->
  ?LET(Account, gen_account(1, 49, S),
  ?LET(Name, gen_auth_contract(),
  ?LET({Compiler, VM, ABI}, gen_contract_opts(P),
  begin
    TxFee   = contract_tx_fee(S, create, Name, ABI) + 32 * 20,
    GasUsed = contract_gas(Name, init, ABI, P),
    SymName = next_id(contract),
    [Account, Name, SymName, Compiler,
     #{vm_version  => VM,
       abi_version => ABI,
       fee         => gen_fee_above(S, TxFee),
       gas_price   => gen_gas_price(P),
       gas         => gen_gas(GasUsed),
       nonce       => gen_nonce(),
       amount      => 0, %% Necessary to be able to use contracts functions
       deposit     => 0,
       auth_fun    => gen_auth_fun(Name, ABI)}]
  end))).

ga_attach_valid(S = #{protocol := P}, Args = [Account, Name, _, _, Tx]) ->
  P >= ?FORTUNA_PROTOCOL_VSN
  andalso not is_ga_account(S, Account)
  andalso not lists:member(maps:get(vm_version, Tx), [aevm_sophia_1, aevm_sophia_2])
  andalso check_auth_fun(Name, maps:get(auth_fun, Tx), maps:get(abi_version, Tx))
  andalso txs_contracts_eqc:contract_create_valid(S, Args).

check_auth_fun(authorize_nonce, FunHash, abi_aevm_1) ->
  FunHash == <<175,167,108,196,77,122,134,90,197,152,206,179,38,153,232,187,88,41,45,167,79,246,181,13,185,101,189,45,109,228,184,223>>;
check_auth_fun(authorize_nonce, FunHash, abi_fate_1) ->
  FunHash == <<(aeb_fate_code:symbol_identifier(<<"nonce_correct">>))/binary, 0:28/unit:8>>;
check_auth_fun(_, _, _) ->
  false.

ga_attach_tx(S, Args) ->
  NTx = txs_contracts_eqc:contract_create_tx_(S, Args),
  aega_attach_tx:new(NTx).

ga_attach_next(S, Value, [AccId, _, SymName, _, Tx] = Args) ->
  case ga_attach_valid(S, Args) of
    false -> S;
    true ->
      S1 = txs_contracts_eqc:contract_create_next(S, Value, Args),
      case maps:is_key(SymName, maps:get(contracts, S1)) of
        false -> S1;
        true  ->
          A  = get_account(S1, AccId),
          GA = #ga{ contract = SymName, auth_fun = maps:get(auth_fun, Tx) },
          update_account(S1, AccId, A#account{ ga = GA, nonce = 1 })
      end
  end.

ga_attach_post(S, Args, Res) ->
  common_postcond(ga_attach_valid(S, Args), Res).

ga_attach_features(S, Args, Res) ->
  Correct = ga_attach_valid(S, Args),
  [{ga_attach, Res}] ++
  [{correct, ga_attach} || Correct] ++
  [{correct, false} || not Correct].

%% --- Operation: ga_meta ---
-define(WGA(S),     S#{ ga => true }).
-define(WGA(GA, S), wga(GA, S)).
-define(NO_WGA(S),  not_wga(S)).

ga_meta_pre(S) ->
  length(ga_accounts(S)) > 0.

ga_meta_args(S) ->
  ?LET(TxArgs = [_M, _Tx, _TxData], gen_tx(?WGA(S)),
  case ga_signer(S, TxArgs) of
    [GAAccount] ->
      ga_meta_args_(S, GAAccount, TxArgs);
    [GAAccount1, GAAccount2] ->
      ?LET(GAArgs1, ga_meta_args_(S, GAAccount1, TxArgs),
            ga_meta_args_(S, GAAccount2, [?MODULE, ga_meta, GAArgs1]))
  end).

ga_meta_args_(S, GAAccount, TxArgs = [_M, Tx, _TxData]) ->
  ?LET({ABI, Fee, Gas, GasPrice}, gen_meta_params(S, GAAccount, Tx),
       [GAAccount, #{ abi_version => txs_contracts_eqc:abi_to_int(ABI), gas => Gas, fee => Fee,
                      gas_price => GasPrice, auth_data => gen_nonce() }, TxArgs]).

ga_meta_pre(S, [GA, _, TxArgs = [_, Tx, [X | _]]]) ->
  %% maps:get(protocol, S) >= ?LIMA_PROTOCOL_VSN andalso %% Skip fortuna - it doesn't catch crashes
  %% (Tx /= ga_meta orelse GA /= X) andalso
  txs_eqc:tx_pre(S, TxArgs).

ga_meta_valid(S = #{protocol := P}, [GAAccount, MTx, TxArgs = [_, Tx, _]]) ->
  P >= ?FORTUNA_PROTOCOL_VSN
  andalso is_ga_account(S, GAAccount)
  andalso maps:get(auth_data, MTx) == good
  andalso check_balance(S, GAAccount, maps:get(fee, MTx) + maps:get(gas, MTx) * maps:get(gas_price, MTx))
  andalso is_valid_auth_gas(S, GAAccount, maps:get(abi_version, MTx), P, maps:get(gas, MTx))
  andalso check_abi(S, GAAccount, maps:get(abi_version, MTx))
  andalso check_relevant_signer(S, GAAccount, TxArgs)
  andalso txs_contracts_eqc:valid_contract_fee(S, ga_meta_tx_fee(Tx), MTx).

ga_meta_tx(S, [GAAccount, MTx, [M, Tx, TxData]]) ->
  {ok, InnerTx} = apply(M, ?tx(Tx), [?WGA(GAAccount, ga_bump_nonce(GAAccount, S)), TxData]),
  WGA = maps:is_key(ga, S),
  STx =
    case aetx:signers(InnerTx, get(trees)) of
      {ok, [X, Y]} when not WGA -> %% Two signers, and only one GA "signature"
        sign(S, X, Y, GAAccount, InnerTx);
      _ ->
        aetx_sign:new(InnerTx, [])
    end,

  {ok, AuthData} = make_auth_data(S, GAAccount, maps:get(abi_version, MTx), maps:get(auth_data, MTx)),
  GAId = aeser_id:create(account, get_account_key(S, GAAccount)),
  MTx1 = MTx#{ ga_id => GAId, auth_data => AuthData, tx => STx },
  aega_meta_tx:new(MTx1).

ga_meta_next(S, Value, Args = [GA, MTx, [M, Tx, TxData]]) ->
  case ga_meta_valid(S, Args) of
    false -> S;
    true  ->
      A = #account{ nonce = N, ga = #ga{ contract = CId } } = get_account(S, GA),
      #contract{ abi = ABI } = txs_contracts_eqc:get_contract(S, CId),
      UseGas = auth_gas(txs_contracts_eqc:abi_to_int(ABI), N + 1, maps:get(protocol, S)),
      #{ fee := Fee, gas_price := GasPrice } = MTx,
      S1 = update_account(S, GA, A#account{ nonce = N + 1 }),
      S2 = apply(M, ?next(Tx), [?WGA(GA, S1), Value, TxData]),
      %% A  = get_account(S1, GA),
      %% Re-set the nonce and remove the GA tag from state.
      %% S2 = update_account(?NO_WGA(S1), GA, A#account{ nonce = N }),
      reserve_fee(Fee + UseGas * GasPrice,
        charge(GA, Fee + UseGas * GasPrice, ?NO_WGA(S2)))
  end.

ga_meta_post(S, Args, Res) ->
  common_postcond(ga_meta_valid(S, Args), Res).

ga_meta_features(S, Args = [_GA, _, [_, Tx, _]], Res) ->
  Correct = ga_meta_valid(S, Args),
  [{correct, if Correct -> ga_meta; true -> false end}] ++
    [{ga_meta, Res}] ++
    [{ga_meta_inner, Tx} || Correct ].

weight(#{ protocol := P }, ga_attach) when P < ?FORTUNA_PROTOCOL_VSN -> 1;
weight(S, ga_attach)  ->
  case length(non_ga_accounts(S)) of
    N when N < 2 -> 1;
    N            -> 4 * N
  end;
weight(S, ga_meta) ->
  case ga_accounts(S) of
    [] -> 0;
    _  -> 15 end;
weight(_S, _)         -> 0.

%% -- Generators -------------------------------------------------------------
gen_auth_contract() ->
  weighted_default({99, authorize_nonce}, {1, identity}).

gen_auth_fun(identity, _) ->
  noshrink(binary(32));
gen_auth_fun(authorize_nonce, abi_aevm_1) ->
  weighted_default({99, <<175,167,108,196,77,122,134,90,197,152,206,179,38,153,232,187,88,41,45,167,79,246,181,13,185,101,189,45,109,228,184,223>>},
                   {1,  binary(32)});
gen_auth_fun(authorize_nonce, abi_fate_1) ->
  weighted_default({99, <<(aeb_fate_code:symbol_identifier(<<"nonce_correct">>))/binary, 0:28/unit:8>>},
                   {1,  binary(32)});
gen_auth_fun(authorize_nonce, _) ->
  noshrink(binary(32)).

gen_auth_gas(GasUsed) ->
  frequency([{40, GasUsed}, {9, GasUsed + 30000}, {1, ?LET(Delta, choose(1, 250), max(1, GasUsed - Delta))}]).

gen_meta_params(S = #{ protocol := P }, GA, Tx) ->
  case get_account_contract(S, GA) of
    #contract{ abi = SymABI } ->
      %% {txs_contracts_eqc:gen_abi(ABI), ga_meta_tx_fee() * 1000000, gen_gas(500), gen_gas_price(P)};
      ABI = txs_contracts_eqc:abi_to_int(SymABI),
      #account{ nonce = N } = get_account(S, GA),
      {txs_contracts_eqc:gen_abi(SymABI), ga_meta_tx_fee(Tx) * 1000000, gen_auth_gas(auth_gas(ABI, N + 1, P)), gen_gas_price(P)};
    _ ->
      {elements([abi_fate_1, abi_aevm_1]), ga_meta_tx_fee(Tx) * 1000000, 500, 1000000}
  end.

ga_meta_tx_fee(contract_create) ->
  125000;
ga_meta_tx_fee(_) ->
  99999.

%% -- Local helpers ---------------------------------------------------------
is_valid_auth_gas(S, GA, ABI, P, Gas) ->
  #account{ nonce = N } = get_account(S, GA),
  Gas >= auth_gas(ABI, N + 1, P).

auth_gas(?ABI_AEVM_1, _, P) when P < ?LIMA_PROTOCOL_VSN -> 402;
auth_gas(?ABI_AEVM_1, _, _)                             -> 722;
auth_gas(?ABI_FATE_1, N, _) when N < 64                 -> 167;
auth_gas(?ABI_FATE_1, _, _)                             -> 172;
auth_gas(_, _, _)                                       -> 1.

check_abi(S, GA, ABI) ->
  case get_account_contract(S, GA) of
    #contract{ abi = SymABI } -> txs_contracts_eqc:abi_to_int(SymABI) == ABI;
    _ -> false
  end.

check_relevant_signer(S, GA, TxArgs) ->
  lists:member(GA, signers(S, TxArgs)).

get_account_contract(S, GA) ->
  case get_account(S, GA) of
    #account{ ga = #ga{ contract = CId } } ->
      txs_contracts_eqc:get_contract(S, CId);
    _ -> false
  end.

non_ga_accounts(#{ accounts := As }) ->
  [A || {A, #account{ ga = false }} <- maps:to_list(As) ].

ga_accounts(#{ accounts := As }) ->
  [A || {A, #account{ ga = GA }} <- maps:to_list(As), GA /= false ].

-define(IS_SC_DOUBLE_SIGNED(Tx), (Tx == sc_create orelse Tx == sc_deposit
                                  orelse Tx == sc_withdraw orelse Tx == sc_close_mutual)).

signers(S, [_, ga_meta, [_, _, TxArgs]]) -> signers(S, TxArgs);
signers(S, [_, sc_create, [I, R, _, _]]) ->
  [signer(S, I), signer(S, R)];
signers(S, [_, Tx, [S1, S2, ChId, _]]) when ?IS_SC_DOUBLE_SIGNED(Tx) ->
  [S1 || is_channel_party(S, S1, ChId)] ++ [S2 || is_channel_party(S, S2, ChId)];
signers(S, [_, response_oracle, [QId, _]]) ->
  [signer(S, QId)];
signers(S, A = [_, _, [Signer | _]]) ->
  [signer(S, Signer)].

%% ga_signer(S, [_, ga_meta, [_, _, TxArgs]])       -> ga_signer(S, TxArgs);
ga_signer(S, [_, response_oracle, [QId, _]])     -> [signer(S, QId)];
ga_signer(S, [_, Tx, [Actor, NotActor, _, _]]) when ?IS_SC_DOUBLE_SIGNED(Tx) ->
  case [signer(S, X) || X <- [Actor, NotActor], is_ga_account(S, X)] of
    [] -> [signer(S, Actor)];
    Xs -> Xs end;
ga_signer(S, [_, _, [Signer | _]])               -> [signer(S, Signer)].

signer(S, ?QUERY(_) = QId) ->
  Q = txs_oracles_eqc:get_query(S, QId),
  txs_oracles_eqc:get_oracle_account(S, Q#query.oracle);
signer(_S, #query{ oracle = RawKey }) ->
  RawKey;
signer(S, ?ORACLE(_) = OId) ->
  txs_oracles_eqc:get_oracle_account(S, OId);
signer(_S, ?ACCOUNT(_) = AccId) ->
  AccId;
signer(_S, {_, ?KEY(_)} = NewAcc) ->
  NewAcc;
signer(_S, Key = <<_:32/unit:8>>) ->
  Key;
signer(_S, {neither, Key = <<_:32/unit:8>>}) ->
  Key;
signer(_S, Id) -> error({todo, Id}).

make_auth_data(S, GAAcc, ABI, NonceGood) ->
  case get_account(S, GAAcc) of
    #account{ ga = #ga{}, nonce = Nonce0 } ->
      Nonce = calc_nonce(Nonce0, NonceGood),
      encode_calldata(ABI, Nonce);
    _ ->
      {ok, <<123456789:256>>}
  end.

-define(STUB, "contract X =\n  entrypoint nonce_correct : (int) => bool\n").

encode_calldata(ABI, Nonce) ->
  txs_contracts_eqc:encode_calldata(ABI, ?STUB, "nonce_correct", [Nonce]).

calc_nonce(N, good)         -> N;
calc_nonce(N, {bad, Delta}) -> max(0, N + Delta).

wga(GA, S = #{ ga := GAs  }) when is_list(GAs) -> S#{ ga => [GA | GAs] };
wga(GA, S)                                     -> S#{ ga => [GA] }.

not_wga(S = #{ ga := [_ | [_ | _] = GAs] }) -> S#{ ga => GAs };
not_wga(S)                                  -> maps:remove(ga, S).

sign(S, X, Y, GAAccount, Tx) ->
  case get_account_key(S, GAAccount) of
    X -> sign(S, Y, Tx);
    Y -> sign(S, X, Tx);
    _Neither -> aetx_sign:new(Tx, [])
  end.

sign(S, PubKey, Tx) ->
  case lists:keyfind(PubKey, #key.public, maps:values(maps:get(keys, S))) of
    false -> error;
    #key{ private = PrivKey } -> aec_test_utils:sign_tx(Tx, PrivKey, false)
  end.

ga_bump_nonce(GAAccount, S) ->
  case get_account(S, GAAccount) of
    A = #account{ nonce = N } -> update_account(S, GAAccount, A#account{ nonce = N + 1 });
    _ -> S
  end.
