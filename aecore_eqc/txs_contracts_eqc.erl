%%% @author Thomas Arts
%%% @doc
%%%
%%% @end
%%% Created : 11 October 2019 by Thomas Arts (copied from Hans Svensson's Lima updated model)

-module(txs_contracts_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-include("txs_eqc.hrl").

%% -- State and state functions ----------------------------------------------
initial_state(S) ->
    S#{contracts => #{}}.

%% -- Operations -------------------------------------------------------------

%% --- Operation: create_contract ---
contract_create_pre(S) ->
    maps:is_key(accounts, S) andalso maps:get(height, S) > 0.

contract_create_args(#{protocol := Protocol} = S) ->
    ?LET(Creator, gen_account(1, 100, S),
    ?LET(Name, noshrink(gen_contract()),
    ?LET({Compiler, VM, ABI}, gen_contract_opts(Protocol),
        begin
            Fixed   = contract_tx_fee(S, create, Name, ABI),
            GasUsed = contract_gas(Name, init, ABI, Protocol),
            SymName = next_id(contract),
            [Creator, Name, SymName, Compiler,
             #{vm_version  => VM,
               abi_version => ABI,
               fee         => gen_fee_above(S, Fixed),
               gas_price   => gen_gas_price(Protocol),
               gas         => gen_gas(GasUsed),
               nonce       => gen_nonce(),
               deposit     => gen_deposit(),
               amount      => txs_spend_eqc:gen_spend_amount(S, Creator)
              }]
        end))).

contract_create_valid(S, [Creator, Name, _SymName, CompilerVersion, Tx]) ->
    ABI      = maps:get(abi_version, Tx),
    Fixed    = contract_tx_fee(S, create, Name, ABI),
    Protocol = maps:get(protocol, S),
    Gas      = maps:get(gas, Tx),
    is_account(S, Creator)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Creator, maps:get(fee, Tx) + Gas * maps:get(gas_price, Tx) +
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

contract_create_tx_(S, [Creator, Name, _SymName, CompilerVersion, Tx]) ->
    NTx = update_nonce(S, Creator, Tx),
    CreatorId = aeser_id:create(account, get_account_key(S, Creator)),
    #{src := Contract, init_args := Args} = CompiledContract = contract(Name),
    {ok, CallData} = encode_calldata(maps:get(abi_version, NTx), Contract, "init", Args),
    Code = maps:get({code, CompilerVersion}, CompiledContract),
    NTx1 = maps:update_with(vm_version, fun vm_to_int/1, NTx),
    NTx2 = maps:update_with(abi_version, fun abi_to_int/1, NTx1),
    NTx2#{owner_id => CreatorId, code => Code, call_data => CallData}.

%% Since the nonce is part of the contract ID, shrinking a contract create could possibly work, but then it will
%% no longer be called by a contract call, since the create ID has changed!
contract_create_next(S, _Value, [Creator, Name, ContractId, CompilerVsn, Tx] = Args) ->
    case contract_create_valid(S, Args) of
        false -> S;
        true  ->
            #{functions := Funs} = contract(Name),
            #{fee := Fee, gas_price := GasPrice, amount := Amount,
              deposit := Deposit, gas := Gas, vm_version := Vm, abi_version := Abi} = Tx,
            GasUsed = contract_gas(Name, init, Abi, maps:get(protocol, S)),
            case Gas >= GasUsed of
                true ->
                    %% Account must exist
                    ContractPK = calc_contract_pubkey(S, Creator),
                    reserve_fee(Fee + GasUsed * GasPrice,
                      bump_and_charge(Creator, Fee + GasUsed * GasPrice + Amount + Deposit,
                        update_contract(ContractId, #contract{name = Name,
                                                              pubkey = ContractPK,
                                                              amount = Amount,
                                                              deposit = Deposit,
                                                              vm = Vm,
                                                              abi = Abi,
                                                              compiler_version = CompilerVsn,
                                                              functions = Funs,
                                                              protocol = maps:get(protocol, S)}, S)));
                false ->
                    %% out of gas
                    reserve_fee(Fee + Gas * GasPrice, bump_and_charge(Creator, Fee + Gas * GasPrice, S))
            end
    end.

calc_contract_pubkey(S, Creator) ->
    case get_account(S, Creator) of
        #account{ ga = #ga{ contract = CId }, key = Key } ->
            #contract{ abi = ABI } = txs_contracts_eqc:get_contract(S, CId),
            GAPK                   = get_pubkey(S, Key),
            {ok, AuthData}         = txs_ga_eqc:make_auth_data(S, Creator, ABI, good),
            GANonce                = aega_meta_tx:auth_id(GAPK, AuthData),
            aect_contracts:compute_contract_pubkey(GAPK, GANonce);
        #account{ nonce = Nonce, key = Key } ->
            aect_contracts:compute_contract_pubkey(get_pubkey(S, Key), Nonce)
    end.

contract_create_post(S, Args, Res) ->
    common_postcond(contract_create_valid(S, Args), Res).

contract_create_features(S, [_Creator, Name, _SymName, CompilerVersion, Tx] = Args, Res) ->
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

contract_call_args(#{protocol := Protocol} = S) ->
    ?LET([Caller, ContractId], [gen_account(1, 100, S), gen_contract_id(1, 100, S)],
    begin
        Contract = #contract{ name = Name } = get_contract(S, ContractId),
        ?LET(ABI, gen_abi(Contract#contract.abi),
        ?LET({Fun, As}, oneof(Contract#contract.functions),
         begin
             UseGas = contract_gas(Name, Fun, ABI, Protocol),
             [Caller, ContractId,
              #{abi_version => abi_to_int(ABI),
                fee         => gen_fee_above(S, contract_tx_fee(S, call, Name, ABI)),
                gas_price   => gen_gas_price(Protocol),
                gas         => gen_gas(UseGas),
                nonce       => gen_nonce(),
                amount      => gen_deposit(),
                call_data   => {Fun, As}
               }]
         end ))
    end).

contract_call_pre(S, [_Caller, CId = ?CONTRACT(_), #{ call_data := {F, _} }]) ->
    case get_contract(S, CId) of
      #contract{ functions = Fs } -> lists:keymember(F, 1, Fs);
      _                           -> false
    end;
contract_call_pre(_, _) ->
    true.

contract_call_valid(S, [Caller, CId = ?CONTRACT(_), Tx]) ->
    #contract{ name = Name, vm = VM, abi = CABI } = get_contract(S, CId),
    #{abi_version := ABI, call_data := {F, _}} = Tx,

    is_account(S, Caller)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Caller, maps:get(fee, Tx) + maps:get(gas, Tx) * maps:get(gas_price, Tx))
    andalso valid_contract_fee(S, contract_tx_fee(S, call, Name, ABI), Tx)
    andalso is_valid_gas(Name, F, ABI, VM, maps:get(protocol, S), maps:get(gas, Tx))
    andalso ABI == abi_to_int(CABI);
contract_call_valid(_, _) ->
    false.

contract_call_tx(S, [Caller, CId = ?CONTRACT(_), #{call_data := {Func, As}} = Tx]) ->
    C              = get_contract(S, CId),
    ContractId     = aeser_id:create(contract, C#contract.pubkey),
    #{src := Src}  = contract(C#contract.name),
    {ok, CallData} = encode_calldata(maps:get(abi_version, Tx), Src, Func, As),
    contract_call_with_data(S, Caller, Tx#{call_data => CallData, contract_id => ContractId});
contract_call_tx(S, [Caller, fake_contract_id, Tx]) ->
    ContractId = aeser_id:create(contract, (fake_contract_id())#contract.pubkey),
    contract_call_with_data(S, Caller, Tx#{call_data => <<"Blubber">>, contract_id => ContractId}).

contract_call_with_data(S, Caller, Tx) ->
    NTx      = update_nonce(S, Caller, Tx),
    CallerId = aeser_id:create(account, get_account_key(S, Caller)),
    aect_call_tx:new(NTx#{caller_id => CallerId}).

contract_call_next(S, _Value, [Caller, CId, Tx] = Args) ->
    case contract_call_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, gas_price := GasPrice, amount := Amount,
               gas := Gas, call_data := {Func, _As}} = Tx,
            #contract{ name = Name, vm = VM, abi = ABI } = get_contract(S, CId),
            UseGas  = contract_gas(Name, Func, ABI, maps:get(protocol, S)),
            Payable = contract_payable_fun(Name, Func, VM),
            case Gas >= UseGas andalso (Payable orelse Amount == 0) of
                true ->
                    reserve_fee(Fee + UseGas * GasPrice,
                      bump_and_charge(Caller, Fee + UseGas * GasPrice + Amount, S));
                false -> %% out of gas
                    reserve_fee(Fee + Gas * GasPrice,
                      bump_and_charge(Caller, Fee + Gas * GasPrice, S))
            end
    end.

contract_call_post(S, Args, Res) ->
  common_postcond(contract_call_valid(S, Args), Res).


contract_call_features(S, [_Caller, _, _Tx] = Args, Res) ->
    Correct = contract_call_valid(S, Args),
    %% #{gas := Gas, call_data := {_Func, _As}} = Tx,
    [{correct, if Correct -> contract_call; true -> false end}] ++
     %% [{contract_call_fun, CName} || Correct andalso Gas >= UseGas ] ++
     [{contract_call, Res}].


%% -- Property ---------------------------------------------------------------

weight(S, contract_create) ->
    case maps:get(contracts, S, []) of
      [] -> 10;
      _  -> 2 end;
weight(S, contract_call) ->
    case maps:get(contracts, S, []) of
        [] -> 0;
        _  -> 7 end;
weight(_S, _) -> 0.

compile_contracts() ->
    %% read and compile contracts once (and use them in parallel
    catch ets:delete(contracts),
    ets:new(contracts, [{read_concurrency, true}, named_table]),
    [ ets:insert(contracts, {maps:get(name, C), C}) || C <- contracts() ].


%% -- State update and query functions ---------------------------------------

get_contract(_S, fake_contract_id) ->
  fake_contract_id();
get_contract(S, ?CONTRACT(C)) ->
  get_contract(S, C);
get_contract(S, C) ->
  maps:get(C, maps:get(contracts, S), false).

get_contract_key(_S, #contract{ pubkey = PK }) ->
  PK;
get_contract_key(S, C) ->
  #contract{ pubkey = PK } = get_contract(S, C),
  PK.

update_contract(?CONTRACT(CId), C, S) -> update_contract(CId, C, S);
update_contract(CId, C, S = #{ contracts := Cs }) ->
  S#{ contracts := Cs#{ CId => C } }.

%% --- local helpers ------
is_payable_contract(S, C) ->
    case get_contract(S, C) of
        false -> true;
        #contract{ vm = VM } ->
          not lists:member(VM, [fate_sophia_1, aevm_sophia_4])
    end.

valid_contract_fee(S, Fixed, #{ fee := Fee, gas_price := GasPrice }) ->
    GasPrice >= minimum_gas_price(maps:get(protocol, S))
        andalso Fee >= Fixed * minimum_gas_price(maps:get(protocol, S)).

is_valid_gas(Name, Fun, ABI, VM, P, Gas) ->
    GasUse = contract_gas(Name, Fun, ABI, P),
    %% io:format("XXX: ~p ~p ~p ~p\n", [Fun, VM, Gas, GasUse]),
    case {lists:member(VM, [aevm_sophia_1, aevm_sophia_2]), Gas - GasUse} of
      {true, N} when N < 0, N > -4, P < ?LIMA_PROTOCOL_VSN -> Fun /= "check_nonce" andalso Fun /= "n_checks";
      {true, N} when N < 0, N > -323, P >= ?LIMA_PROTOCOL_VSN -> Fun /= "check_nonce" andalso Fun /= "n_checks";
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

%% This is cheating a bit, but ABI hasn't moved... So use the latest version
encode_calldata(ABI, Src, Fun, As) when ABI == abi_aevm_1; ABI == ?ABI_AEVM_1 ->
    aect_test_utils:encode_call_data(?SOPHIA_LIMA_AEVM, Src, Fun, [to_binary(A) || A <- As]);
encode_calldata(_ABI, Src, Fun, As) ->
    aect_test_utils:encode_call_data(?SOPHIA_LIMA_FATE, Src, Fun, [to_binary(A) || A <- As]).

to_binary(B) when is_binary(B) ->
    B;
to_binary(I) when is_integer(I) ->
    integer_to_binary(I);
to_binary(Other) ->
    error({cannot_convert, Other}).

%% -- Generators -------------------------------------------------------------

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

gen_contract_id(Invalid, Valid, S) ->
  gen_contract_id_(Invalid, Valid, maps:keys(maps:get(contracts, S))).

gen_contract_id_(_, _, []) ->
    fake_contract_id;
gen_contract_id_(Invalid, Valid, Cs) ->
    weighted_default({Valid,   ?LET(C, elements(Cs), ?CONTRACT(C))},
                     {Invalid, fake_contract_id}).

fake_contract_id() ->
  #contract{ pubkey    = <<12345:256>>,
             abi       = abi_raw,
             vm        = aevm_sophia_1,
             functions = [{"foo", []}] }.

%% Add srcs dynamically for the compilers available
contracts() ->
    Static =
        [#{name => identity,
           init_args => [],
           functions => [{"main", [choose(-100, 1000)]}]
          },
         #{name => authorize_nonce,
           init_args => [],
           functions => [{"check_nonce", [nat()]}, {"n_checks", []}]
          }
        ],
    [ begin
          File = maps:get(name, C),
          {ok, ContractSrc} = aect_test_utils:read_contract(?SOPHIA_LIMA_AEVM, File),
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
contract_gas(identity, "main", ?ABI_AEVM_1, _) -> 192;
contract_gas(identity, "main", ?ABI_FATE_1, _) -> 11;

contract_gas(authorize_nonce, init, ?ABI_AEVM_1, _) -> 417;
contract_gas(authorize_nonce, init, ?ABI_FATE_1, _) -> 103;
contract_gas(authorize_nonce, "check_nonce", ?ABI_AEVM_1, P) when P < ?LIMA_PROTOCOL_VSN -> 422;
contract_gas(authorize_nonce, "check_nonce", ?ABI_AEVM_1, _) -> 742;
contract_gas(authorize_nonce, "check_nonce", ?ABI_FATE_1, _) -> 135;
contract_gas(authorize_nonce, "n_checks", ?ABI_AEVM_1, P) when P < ?LIMA_PROTOCOL_VSN -> 357;
contract_gas(authorize_nonce, "n_checks", ?ABI_AEVM_1, _) -> 677;
contract_gas(authorize_nonce, "n_checks", ?ABI_FATE_1, _) -> 21;
contract_gas(_, _, _, _) -> 1000.

contract_tx_fee(S, Type, Name, ABI) when is_atom(ABI) ->
  contract_tx_fee(S, Type, Name, abi_to_int(ABI));
contract_tx_fee(#{with_ga := true}, Type, _Name, ABI) ->
  base_gas(Type, ABI);
contract_tx_fee(_S, Type, Name, ABI) ->
  base_gas(Type, ABI) + 20 * size_gas(Type, Name, ABI).

base_gas(create, _)         -> 75000;
base_gas(call, ?ABI_AEVM_1) -> 450000;
base_gas(call, ?ABI_FATE_1) -> 180000;
base_gas(_, _)              -> 450000.

size_gas(create, identity, ?ABI_AEVM_1)        -> 1200;
size_gas(create, identity, ?ABI_FATE_1)        -> 200;
size_gas(create, authorize_nonce, ?ABI_AEVM_1) -> 2300;
size_gas(create, authorize_nonce, ?ABI_FATE_1) -> 350;
size_gas(call, _, ?ABI_AEVM_1)                 -> 230;
size_gas(call, _, ?ABI_FATE_1)                 -> 110;
size_gas(_, _, _)                              -> 1000.

contract_payable_fun(authorize_nonce, "n_checks", VM) ->
    VM /= aevm_sophia_4 andalso VM /= fate_sophia_1;
contract_payable_fun(authorize_nonce, "check_nonce", VM) ->
    VM /= aevm_sophia_4 andalso VM /= fate_sophia_1;
contract_payable_fun(_, _, _) -> true.

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
