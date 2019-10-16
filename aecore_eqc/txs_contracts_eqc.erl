%%% @author Thomas Arts
%%% @doc
%%%
%%% @end
%%% Created : 11 October 2019 by Thomas Arts (copied from Hans Svensson's Lima updated model)

-module(txs_contracts_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).
-import(txs_spend_eqc, [is_account/2, reserve_fee/2, bump_and_charge/3, check_balance/3, credit/3]).

-include("txs_eqc.hrl").


-record(contract, {name, id, pubkey, amount, deposit, vm, abi,
                   compiler_version, protocol, src, functions}).

%% -- State and state functions ----------------------------------------------
initial_state(S) ->
    S#{contracts => []}.

%% -- Operations -------------------------------------------------------------

is_payable_contract(S, C) ->
    case [ Cx#contract.vm || Cx <- maps:get(contracts, S),
                             Cx#contract.id == C orelse Cx#contract.pubkey == C ] of
        [VM] when VM == fate_sophia_1; VM == aevm_sophia_4 -> false;
        _ -> true
    end.

%% --- Operation: create_contract ---
contract_create_pre(S) ->
    maps:is_key(accounts, S) andalso maps:get(height, S) > 0.

contract_create_args(#{protocol := Protocol} = S) ->
    ?LET(Sender, gen_account(1, 100, S),
    ?LET(Name, gen_contract(),
    ?LET({Compiler, VM, ABI}, gen_contract_opts(Protocol),
        begin
            Fixed   = contract_tx_fee(create, Name, ABI),
            GasUsed = contract_gas(Name, init, ABI, Protocol),
            SymName = list_to_atom(lists:concat(["contract_", length(maps:get(contracts, S, []))])),
            [Sender, Name, SymName, Compiler,
             #{owner_id => aeser_id:create(account, Sender),
               vm_version  => VM,
               abi_version => ABI,
               fee => gen_fee_above(S, Fixed),
               gas_price => gen_gas_price(Protocol),
               gas => gen_gas(GasUsed),
               nonce => gen_nonce(),
               deposit => gen_deposit(),
               amount => txs_spend_eqc:gen_spend_amount(S, Sender)
              }]
        end))).

contract_create_valid(S, [Sender, Name, _SymName, CompilerVersion, Tx]) ->
    ABI      = maps:get(abi_version, Tx),
    Fixed    = contract_tx_fee(create, Name, ABI),
    Protocol = maps:get(protocol, S),
    Gas      = maps:get(gas, Tx),
    is_account(S, Sender)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Sender, maps:get(fee, Tx) + Gas * maps:get(gas_price, Tx) +
                                     maps:get(amount, Tx) + maps:get(deposit, Tx))
    andalso valid_contract_fee(S, Fixed, Tx)
    andalso check_contract_opts(Protocol, CompilerVersion, maps:get(vm_version, Tx), ABI).

check_contract_opts(?ROMA_PROTOCOL_VSN,    ?SOPHIA_ROMA,      aevm_sophia_1, abi_aevm_1) -> true;
check_contract_opts(?MINERVA_PROTOCOL_VSN, ?SOPHIA_ROMA,      aevm_sophia_2, abi_aevm_1) -> true;
check_contract_opts(?MINERVA_PROTOCOL_VSN, ?SOPHIA_MINERVA,   aevm_sophia_2, abi_aevm_1) -> true;
check_contract_opts(?MINERVA_PROTOCOL_VSN, ?SOPHIA_FORTUNA,   aevm_sophia_2, abi_aevm_1) -> true;
check_contract_opts(?FORTUNA_PROTOCOL_VSN, ?SOPHIA_ROMA,      aevm_sophia_2, abi_aevm_1) -> true;
check_contract_opts(?FORTUNA_PROTOCOL_VSN, ?SOPHIA_ROMA,      aevm_sophia_3, abi_aevm_1) -> true;
check_contract_opts(?FORTUNA_PROTOCOL_VSN, ?SOPHIA_MINERVA,   aevm_sophia_2, abi_aevm_1) -> true;
check_contract_opts(?FORTUNA_PROTOCOL_VSN, ?SOPHIA_MINERVA,   aevm_sophia_3, abi_aevm_1) -> true;
check_contract_opts(?FORTUNA_PROTOCOL_VSN, ?SOPHIA_FORTUNA,   aevm_sophia_2, abi_aevm_1) -> true;
check_contract_opts(?FORTUNA_PROTOCOL_VSN, ?SOPHIA_FORTUNA,   aevm_sophia_3, abi_aevm_1) -> true;
check_contract_opts(?LIMA_PROTOCOL_VSN,    ?SOPHIA_LIMA_AEVM, aevm_sophia_4, abi_aevm_1) -> true;
check_contract_opts(?LIMA_PROTOCOL_VSN,    ?SOPHIA_LIMA_FATE, fate_sophia_1, abi_fate_1) -> true;
check_contract_opts(_, _, _, _) -> false.

contract_create_tx(S, Args) ->
    NTx = contract_create_tx_(S, Args),
    aect_create_tx:new(NTx).

contract_create_tx_(S, [Sender, Name, _SymName, CompilerVersion, Tx]) ->
    NTx = update_nonce(S, Sender, Tx),
    #{src := Contract, args := Args} = CompiledContract = contract(Name),
    %% This is cheating a bit, but ABI hasn't moved... So use the latest version
    EncVersion = case maps:get(abi_version, NTx) of abi_aevm_1 -> ?SOPHIA_LIMA_AEVM; _ -> ?SOPHIA_LIMA_FATE end,
    {ok, CallData} = aect_test_utils:encode_call_data(EncVersion, Contract, "init", Args),
    Code = maps:get({code, CompilerVersion}, CompiledContract),
    NTx1 = maps:update_with(vm_version, fun vm_to_int/1, NTx),
    NTx2 = maps:update_with(abi_version, fun abi_to_int/1, NTx1),
    NTx2#{code => Code, call_data => CallData}.

%% Since the nonce is part of the contract ID, shrinking a contract create could possibly work, but then it will
%% no longer be called by a contract call, since the create ID has changed!
contract_create_next(S, _Value, [Sender, Name, ContractId,
                                 CompilerVersion, Tx] = Args) ->
    case contract_create_valid(S, Args) of
        false -> S;
        true  ->
            #{src := Source, functions := Funs} = contract(Name),
            #{fee := Fee, gas_price := GasPrice, amount := Amount,
              deposit := Deposit, gas := Gas, vm_version := Vm, abi_version := Abi} = Tx,
            GasUsed = contract_gas(Name, init, Abi, maps:get(protocol, S)),
            case Gas >= GasUsed of
                true ->
                    %% Account must exist
                    Nonce = txs_spend_eqc:account_nonce(txs_spend_eqc:account(S, Sender)),
                    ContractPK = aect_contracts:compute_contract_pubkey(Sender, Nonce),
                    reserve_fee(Fee + GasUsed * GasPrice,
                                bump_and_charge(Sender,
                                                Fee + GasUsed * GasPrice + Amount + Deposit,
                                                add(contracts,
                                                    #contract{name = Name,
                                                              id = ContractId,
                                                              pubkey = ContractPK,
                                                              amount = Amount,
                                                              deposit = Deposit,
                                                              vm = Vm,
                                                              abi = Abi,
                                                              compiler_version = CompilerVersion,
                                                              src = Source,
                                                              functions = Funs,
                                                              protocol = maps:get(protocol, S)}, S)));
                false ->
                    %% out of gas
                    reserve_fee(Fee + Gas * GasPrice, bump_and_charge(Sender, Fee + Gas * GasPrice, S))
            end
    end.

contract_create_post(S, Args, Res) ->
  common_postcond(contract_create_valid(S, Args), Res).


contract_create_features(S, [_Sender, Name, _SymName, CompilerVersion, Tx] = Args, Res) ->
    Correct = contract_create_valid(S, Args)
                andalso maps:get(gas, Tx) >= contract_gas(Name, init, maps:get(abi_version, Tx), maps:get(protocol, S)),
    [{correct, if Correct -> contract_create; true -> false end},
     {contract_create, Res},
     {contract_compiler, CompilerVersion},
     {contract_vm, maps:get(vm_version, Tx)},
     {contract_context, {maps:get(protocol, S), CompilerVersion, maps:get(vm_version, Tx)}}].

%% --- Operation: call_contract ---
contract_call_pre(S) ->
    maps:is_key(accounts, S) andalso maps:get(contracts, S) /= [].

%% Given https://github.com/aeternity/protocol/blame/44b459970144fb030df55e32b166a9d62a79b523/contracts/contract_vms.md#L23
%% I would expect vm_version to be present either in ct_version form or as separate key
%% But not so in aect_call_tx
%% Most likely determined by the contract's VM version!
contract_call_args(#{protocol := Protocol, contracts := Contracts} = S) ->
    ?LET([Sender, {ContractTag, Contract}],
         [gen_account(1, 100, S), gen_contract_id(1, 100, Contracts)],
         ?LET(ABI, gen_abi(Contract#contract.abi),
         ?LET({Func, As, _},
              case ContractTag of
                  invalid -> {<<"main">>, [], <<>>};
                  _ -> oneof(Contract#contract.functions)
              end,
              begin
              UseGas = contract_gas(Contract#contract.name, Func, ABI, maps:get(protocol, S)),
              [Sender, {ContractTag, Contract#contract.id, Contract#contract.name, Contract#contract.vm},
               #{caller_id   => aeser_id:create(account, Sender),
                 abi_version => abi_to_int(ABI),
                 fee         => gen_fee_above(S, contract_tx_fee(call, Contract#contract.name, ABI)),
                 gas_price   => gen_gas_price(Protocol),
                 gas         => gen_gas(UseGas),
                 nonce       => gen_nonce(),
                 amount      => nat(),
                 call_data   => {Func, As, UseGas, contract_payable_fun(Contract#contract.name, Func, Contract#contract.vm)}
                }]
               end ))).

contract_call_pre(S, [_Sender, {CTag, CId, CName, CVM}, Tx]) ->
    %% #{abi_version := ABI, call_data := {F, _, UseGas0, _}} = Tx,
    C0 = lists:keyfind(CId, #contract.id, maps:get(contracts, S)),
    (CTag == invalid orelse ((C0 /= false andalso C0#contract.name == CName andalso C0#contract.vm == CVM))).
                                %% andalso UseGas0 == contract_gas(C#contract.name, F, ABI, maps:get(protocol, S)))).

contract_call_valid(S, [Sender, {ContractTag, CId, CName, CVM}, Tx]) ->
    Contract = lists:keyfind(CId, #contract.id, maps:get(contracts, S)),
    #{abi_version := ABI, call_data := {F, _, _, _}} = Tx,
    is_account(S, Sender)
    andalso ContractTag == valid
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Sender, maps:get(fee, Tx) + maps:get(gas, Tx) * maps:get(gas_price, Tx))
    andalso valid_contract_fee(S, contract_tx_fee(call, Contract#contract.name, ABI), Tx)
    andalso is_valid_gas(CName, F, ABI, CVM, maps:get(protocol, S), maps:get(gas, Tx))
    andalso ABI == abi_to_int(Contract#contract.abi).

contract_call_tx(S, [Sender, {invalid, _CId, _CName, _CVM}, Tx]) ->
    ContractId = aeser_id:create(contract, <<0:256>>),
    contract_call_with_data(S, Sender, Tx#{call_data => <<"Blubber">>, contract_id => ContractId});
contract_call_tx(S, [Sender, {valid, CId, _CName, _CVM}, #{call_data := {Func, As, _, _}} = Tx]) ->
    C = lists:keyfind(CId, #contract.id, maps:get(contracts, S)),
    ContractId = aeser_id:create(contract, C#contract.pubkey),
    BinaryAs = [ to_binary(A) || A <- As],
    EncVersion = case maps:get(abi_version, Tx) of 1 -> ?SOPHIA_LIMA_AEVM; _ -> ?SOPHIA_LIMA_FATE end,
    {ok, CallData} = aect_test_utils:encode_call_data(EncVersion, C#contract.src, Func, BinaryAs),
    contract_call_with_data(S, Sender, Tx#{call_data => CallData, contract_id => ContractId}).

contract_call_with_data(S, Sender, Tx) ->
    NTx = update_nonce(S, Sender, Tx),
    aect_call_tx:new(NTx).

to_binary(B) when is_binary(B) ->
    B;
to_binary(I) when is_integer(I) ->
    integer_to_binary(I);
to_binary(Other) ->
    error({cannot_convert, Other}).


contract_call_next(S, _Value, [Sender, _C, Tx] = Args) ->
    case contract_call_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, gas_price := GasPrice, amount := Amount,
               gas := Gas, call_data := {_Func, _As, UseGas, Payable}} = Tx,
            case Gas >= UseGas andalso (Payable orelse Amount == 0) of
                true ->
                    %% ContractId = compute_contract_pubkey(Sender, maps:get(nonce, untag_nonce(Tx))),
                    reserve_fee(Fee + UseGas * GasPrice,
                                bump_and_charge(Sender,
                                                Fee + UseGas * GasPrice + Amount,
                                                S));
                false ->
                    %% out of gas
                    reserve_fee(Fee + Gas * GasPrice,
                                bump_and_charge(Sender,
                                                Fee + Gas * GasPrice,
                                                S))
            end
    end.

contract_call_post(S, Args, Res) ->
  common_postcond(contract_call_valid(S, Args), Res).


contract_call_features(S, [_Sender, {_, _, CName, _}, Tx] = Args, Res) ->
    Correct = contract_call_valid(S, Args),
    #{gas := Gas, call_data := {Func, _As, UseGas, _}} = Tx,
    [{correct, if Correct -> contract_call; true -> false end}] ++
     [{contract_call_fun, CName} || Correct andalso Gas >= UseGas ] ++
     [{contract_call, Res}].


%% -- Property ---------------------------------------------------------------

weight(S, contract_create) ->
    case maps:get(contracts, S, []) of
      [] -> 10;
      _  -> 2 end;
weight(S, contract_call) ->
    case maps:get(contracts, S, []) of
        [] -> 0;
        _  -> 10 end;
weight(_S, _) -> 0.

compile_contracts() ->
    %% read and compile contracts once (and use them in parallel
    catch ets:delete(contracts),
    ets:new(contracts, [{read_concurrency, true}, named_table]),
    [ ets:insert(contracts, {maps:get(name, C), C}) || C <- contracts() ].


%% -- State update and query functions ---------------------------------------

add(Tag, X, S) ->
    S#{ Tag => maps:get(Tag, S, []) ++ [X] }.

update_contract_id(OldId, NewId, S) ->
    Fun = fun(C) -> C#contract{id = NewId} end,
    on_contract(OldId, Fun, S).

credit_amount(Id, Credit, S) ->
    Fun = fun(C) -> C#contract{amount = C#contract.amount + Credit} end,
    on_contract(Id, Fun, S).

on_contract(Id, Fun, S = #{contracts := Contracts}) ->
    Upd = fun(C = #contract{ id = I }) when I == Id -> Fun(C);
             (C) -> C end,
    S#{ contracts => lists:map(Upd, Contracts) }.

remove(Tag, X, I, S) ->
    S#{ Tag := lists:keydelete(X, I, maps:get(Tag, S)) }.

get(S, Tag, Key, I) ->
    lists:keyfind(Key, I, maps:get(Tag, S)).


%% --- local helpers ------


valid_account(S, Tag, Key) -> valid_account(S, {Tag, Key}).
valid_account(_S, {name, _}) -> true;
valid_account(S, {Tag, Key}) ->
    IsA = is_account(S, Key),
    (IsA andalso Tag == existing) orelse (not IsA andalso Tag == new).

valid_contract_fee(S, Fixed, #{ fee := Fee, gas_price := GasPrice }) ->
    GasPrice >= minimum_gas_price(maps:get(protocol, S))
        andalso Fee >= Fixed * minimum_gas_price(maps:get(protocol, S)).

is_valid_gas(Name, Fun, ABI, VM, P, Gas) ->
    GasUse = contract_gas(Name, Fun, ABI, P),
    %% io:format("XXX: ~p ~p ~p ~p\n", [Fun, VM, GasUse, Gas - GasUse]),
    case {lists:member(VM, [aevm_sophia_1, aevm_sophia_2]), Gas - GasUse} of
      {true, N} when N < 0, N > -3, P < ?LIMA_PROTOCOL_VSN -> Fun /= <<"nonce_correct">>;
      {true, N} when N < 0, N > -163, P >= ?LIMA_PROTOCOL_VSN -> Fun /= <<"nonce_correct">>;
      _ -> true
    end.


abi_to_int(abi_raw)    -> 0;
abi_to_int(abi_aevm_1) -> 1;
abi_to_int(abi_fate_1) -> 3.

vm_to_int(aevm_sophia_1) -> 1;
vm_to_int(vm_solidity)   -> 2;
vm_to_int(aevm_sophia_2) -> 3;
vm_to_int(aevm_sophia_3) -> 4;
vm_to_int(fate_sophia_1) -> 5;
vm_to_int(aevm_sophia_4) -> 6;
vm_to_int(N)             -> N.


%% -- Generators -------------------------------------------------------------

unique_name(List) ->
    ?LET([W],
         noshrink(?SUCHTHAT([Word],
                            eqc_erlang_program:words(1), not lists:member(Word, List))),
         W).

gen_ttl() ->
    choose(5, 50).

%% Generate a contract
gen_abi(Good) ->
    weighted_default({49, Good}, {1, elements([abi_raw, abi_aevm_1, abi_fate_1] -- [Good])}).

gen_contract_opts(?ROMA_PROTOCOL_VSN) ->
    ?LET(Compiler, frequency([{99, ?SOPHIA_ROMA}, {1, ?SOPHIA_MINERVA}]),
    ?LET(VM, frequency([{99, aevm_sophia_1}, {1, elements([22, vm_solidity, aevm_sophia_2])}]),
    ?LET(ABI, frequency([{99, abi_aevm_1}, {1, elements([abi_fate_1, abi_raw])}]),
         {Compiler, VM, ABI})));
gen_contract_opts(?MINERVA_PROTOCOL_VSN) ->
    ?LET(Compiler, frequency([{99, ?SOPHIA_MINERVA}, {1, elements([?SOPHIA_ROMA, ?SOPHIA_FORTUNA])}]),
    ?LET(VM, frequency([{99, aevm_sophia_2}, {1, elements([22, vm_solidity, aevm_sophia_1, aevm_sophia_3])}]),
    ?LET(ABI, frequency([{99, abi_aevm_1}, {1, elements([abi_fate_1, abi_raw])}]),
         {Compiler, VM, ABI})));
gen_contract_opts(?FORTUNA_PROTOCOL_VSN) ->
    ?LET(Compiler, frequency([{99, ?SOPHIA_FORTUNA}, {1, elements([?SOPHIA_ROMA, ?SOPHIA_LIMA_AEVM])}]),
    ?LET(VM, frequency([{60, aevm_sophia_3}, {39, aevm_sophia_2}, {1, elements([22, vm_solidity, aevm_sophia_1, aevm_sophia_4])}]),
    ?LET(ABI, frequency([{99, abi_aevm_1}, {1, elements([abi_fate_1, abi_raw])}]),
         {Compiler, VM, ABI})));
gen_contract_opts(?LIMA_PROTOCOL_VSN) ->
    ?LET(Kind, elements([fate, aevm]),
         gen_contract_opts(?LIMA_PROTOCOL_VSN, Kind)).

gen_contract_opts(?LIMA_PROTOCOL_VSN, aevm) ->
    ?LET(Compiler, frequency([{99, ?SOPHIA_LIMA_AEVM}, {1, elements([?SOPHIA_FORTUNA, ?SOPHIA_LIMA_FATE])}]),
    ?LET(VM, frequency([{99, aevm_sophia_4}, {1, elements([22, vm_solidity, aevm_sophia_3, fate_sophia_1])}]),
    ?LET(ABI, frequency([{99, abi_aevm_1}, {1, elements([abi_fate_1, abi_raw])}]),
         {Compiler, VM, ABI})));
gen_contract_opts(?LIMA_PROTOCOL_VSN, fate) ->
    ?LET(Compiler, frequency([{99, ?SOPHIA_LIMA_FATE}, {1, elements([?SOPHIA_FORTUNA, ?SOPHIA_LIMA_AEVM])}]),
    ?LET(VM, frequency([{99, fate_sophia_1}, {1, elements([22, vm_solidity, aevm_sophia_3, aevm_sophia_4])}]),
    ?LET(ABI, frequency([{99, abi_fate_1}, {1, elements([abi_aevm_1, abi_raw])}]),
         {Compiler, VM, ABI}))).

gen_contract() ->
    elements([identity, authorize_nonce]).

contract(Name) ->
    [{_, Map}] = ets:lookup(contracts, Name),
    Map.

%% Add srcs dynamically for the compilers available
contracts() ->
    Static =
        [#{name => identity,
           args => [],
           functions => [{<<"main">>, [nat()], <<>>}]
          },
         #{name => authorize_nonce,
           args => [],
           auth_fun => <<"nonce_correct">>,
           functions => [{<<"nonce_correct">>, [nat()], <<175,167,108,196,77,122,134,90,197,152,206,179,38,153,232,187,88,41,45,167,79,246,181,13,185,101,189,45,109,228,184,223>> }]
          }
        ],
    [ begin
          File = maps:get(name, C),
          {ok, ContractSrc} = aect_test_utils:read_contract(File),
          CompiledCode =
              [ begin
                    {ok, Code} = aect_test_utils:compile_contract(CompilerVersion, File),
                    {{code, CompilerVersion}, Code}
                end || CompilerVersion <- [1, 2, 3, 4, 5] ],
          maps:merge(C#{src => ContractSrc}, maps:from_list(CompiledCode))
      end || C <- Static ].

contract_gas(Contract, Fun, ABI, P) when is_atom(ABI) -> contract_gas(Contract, Fun, abi_to_int(ABI), P);
contract_gas(identity, init, ?ABI_AEVM_1, _) -> 193;
contract_gas(identity, init, ?ABI_FATE_1, _) -> 56;
contract_gas(identity, <<"main">>, ?ABI_AEVM_1, P) when P < ?LIMA_PROTOCOL_VSN -> 192;
contract_gas(identity, <<"main">>, ?ABI_AEVM_1, _) -> 192;
contract_gas(identity, <<"main">>, ?ABI_FATE_1, _) -> 11;
contract_gas(authorize_nonce, init, ?ABI_AEVM_1, _) -> 275;
contract_gas(authorize_nonce, init, ?ABI_FATE_1, _) -> 86;
contract_gas(authorize_nonce, <<"nonce_correct">>, ?ABI_AEVM_1, P) when P < ?LIMA_PROTOCOL_VSN -> 314;
contract_gas(authorize_nonce, <<"nonce_correct">>, ?ABI_AEVM_1, _) -> 474;
contract_gas(authorize_nonce, <<"nonce_correct">>, ?ABI_FATE_1, _) -> 108;
contract_gas(_, _, _, _) -> 1000.

contract_tx_fee(Type, Name, ABI) when is_atom(ABI) -> contract_tx_fee(Type, Name, abi_to_int(ABI));
contract_tx_fee(create, identity, ?ABI_AEVM_1)        -> 75000 + 20 * 1200;
contract_tx_fee(create, identity, ?ABI_FATE_1)        -> 75000 + 20 * 200;
contract_tx_fee(create, authorize_nonce, ?ABI_AEVM_1) -> 75000 + 20 * 1400;
contract_tx_fee(create, authorize_nonce, ?ABI_FATE_1) -> 75000 + 20 * 230;
contract_tx_fee(call, identity, ?ABI_AEVM_1)          -> 450000 + 20 * 230;
contract_tx_fee(call, identity, ?ABI_FATE_1)          -> 180000 + 20 * 100;
contract_tx_fee(call, authorize_nonce, ?ABI_AEVM_1)   -> 450000 + 20 * 230;
contract_tx_fee(call, authorize_nonce, ?ABI_FATE_1)   -> 180000 + 20 * 100;
contract_tx_fee(_, _, _)                              -> 450000 + 20 * 1000.

contract_payable_fun(authorize_nonce, <<"nonce_correct">>, VM) ->
    VM /= aevm_sophia_4 andalso VM /= fate_sophia_1;
contract_payable_fun(_, _, _) -> true.

gen_contract_id(_, _, []) ->
    {invalid, fake_contract_id()};
gen_contract_id(Invalid, Valid, Contracts) ->
    weighted_default({Valid,
                      ?LET(Contract, elements(Contracts),
                           {valid, Contract})
                     },
                     {Invalid, {invalid, fake_contract_id()}}).

gen_map_key(Map) ->
    elements(maps:keys(Map)).

fake_contract_id() ->
    ?LET(Pubkey, noshrink(binary(32)),
         #contract{id = aect_contracts:compute_contract_pubkey(Pubkey, 12),
                   abi = abi_raw,
                   vm = aevm_sophia_1
                  }).

propsetup(HardForks, Prop) ->
    ?SETUP(
    fun() ->
            _ = application:load(aecore),
            compile_contracts(),
            HardForksTeardown = setup_hard_forks(HardForks),
            DataDirTeardown = setup_data_dir(),
            fun() ->
                    DataDirTeardown(),
                    HardForksTeardown()
            end
    end, Prop).

setup_data_dir() ->
    %% make sure we can run in eqc/aecore_eqc
    {ok, Dir} = file:get_cwd(),
    %% Not asserting that configuration parameter is undefined so to ease experimenting in Erlang shell.
    case lists:reverse(filename:split(Dir)) of
        [_, "eqc" | _] ->
            application:set_env(setup, data_dir, "../../data");
        _ ->
            application:set_env(setup, data_dir, "data")
    end,
    fun() ->
            ok = application:unset_env(setup, data_dir)
    end.

setup_hard_forks(HF) ->
    HF1 = maps:from_list([{integer_to_binary(P), H} || {P, H} <- maps:to_list(HF)]),
    %% Not asserting that configuration parameter is undefined so to ease experimenting in Erlang shell.
    ok = application:set_env(aecore, hard_forks, HF1),
    fun() ->
            ok = application:unset_env(aecore, hard_forks)
    end.
