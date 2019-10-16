%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Hans Svensson
%%% @doc Generalized accounts

-module(txs_ga_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-import(txs_eqc, [gen_tx/1]).

-import(txs_contracts_eqc, [gen_contract_opts/1, contract_tx_fee/3, contract_gas/4]).

-include("txs_eqc.hrl").

-record(ga, {key, amount, contract, auth_fun}).

%% -- State and state functions ----------------------------------------------
initial_state(S) -> S#{ ga => [], contracts => [] }.

%% --- Operation: ga_attach ---
ga_attach_pre(S) ->
  length(maps:get(accounts, S, [])) > 1.

ga_attach_args(#{protocol := P} = S) ->
  ?LET(Account, gen_account(1, 49, S),
  ?LET(Name, gen_auth_contract(),
  ?LET({Compiler, VM, ABI}, gen_contract_opts(P),
  begin
    TxFee   = contract_tx_fee(create, Name, ABI) + 32 * 20,
    GasUsed = contract_gas(Name, init, ABI, P),
    SymName = list_to_atom(lists:concat(["contract_", length(maps:get(contracts, S, []))])),
    [Account, Name, SymName, Compiler,
     #{owner_id    => aeser_id:create(account, Account),
       vm_version  => VM,
       abi_version => ABI,
       fee         => gen_fee_above(S, TxFee),
       gas_price   => gen_gas_price(P),
       gas         => gen_gas(GasUsed),
       nonce       => gen_nonce(),
       amount      => 0, %% Necessary to be able to use contracts functions
       deposit     => 0,
       auth_fun    => gen_auth_fun(Name, ABI)}]
  end))).

ga_attach_valid(S = #{protocol := P}, Args = [_, Name, _, _, Tx]) ->
  P >= ?FORTUNA_PROTOCOL_VSN
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

ga_attach_next(S, Value, [Key, _, SymName, _, Tx] = Args) ->
  case ga_attach_valid(S, Args) of
    false -> S;
    true ->
      S1 = txs_contracts_eqc:contract_create_next(S, Value, Args),
      A  = txs_spend_eqc:account(S1, Key),
      GA = #ga{ key = Key, amount = A#account.amount,
                contract = SymName, auth_fun = maps:get(auth_fun, Tx) },
      S1#{ accounts := maps:get(accounts, S1) -- [A],
           ga := maps:get(ga, S1) ++ [GA] }
  end.

ga_attach_post(S, Args, Res) ->
  common_postcond(ga_attach_valid(S, Args), Res).

ga_attach_features(S, Args, _Res) ->
  Correct = ga_attach_valid(S, Args),
  [{correct, contract_create} || Correct] ++
  [{correct, false} || not Correct].

weight(_S, ga_attach) -> 5;
weight(_S, _) -> 0.

%% -- Generators -------------------------------------------------------------
gen_auth_contract() ->
  weighted_default({49, authorize_nonce}, {1, identity}).

gen_auth_fun(identity, _) ->
  noshrink(binary(32));
gen_auth_fun(authorize_nonce, abi_aevm_1) ->
  weighted_default({49, <<175,167,108,196,77,122,134,90,197,152,206,179,38,153,232,187,88,41,45,167,79,246,181,13,185,101,189,45,109,228,184,223>>},
                   {1,  binary(32)});
gen_auth_fun(authorize_nonce, abi_fate_1) ->
  weighted_default({49, <<(aeb_fate_code:symbol_identifier(<<"nonce_correct">>))/binary, 0:28/unit:8>>},
                   {1,  binary(32)});
gen_auth_fun(authorize_nonce, _) ->
  noshrink(binary(32)).
