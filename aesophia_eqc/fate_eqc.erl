%%% File        : fate_eqc.erl
%%% Author      : Ulf Norell
%%% Description : Properties for the FATE VM.
%%% Created     : 8 Oct 2019 by Ulf Norell
-module(fate_eqc).

-compile([export_all, nowarn_export_all]).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-define(TODO(Fmt, Args), io:format("TODO: " Fmt "\n", Args)).
-define(TODO(Fmt), ?TODO(Fmt, [])).

%% -- Instruction specs ------------------------------------------------------

-type type()     :: term(). %% TODO
-type arg_mode() :: immediate | any.
-type arg_spec() :: {in | out, arg_mode(), type()}.

-type mnemonic() :: atom().

%% Simple instruction (no jumping or stack expectations).
-record(instr,  {op     :: mnemonic(),
                 args   :: [arg_spec()]}).
-type instr_spec() :: #instr{}.

-spec simple_instructions() -> [instr_spec()].
simple_instructions() ->
    I = fun(Op, Ins, Out) ->
            fix_bad_types(
            #instr{ op   = Op,
                    args = [{out, any, Out} | [{in, any, In} || In <- Ins]] })
        end,
    [ I(Op, tuple_to_list(ArgTypes), ResType)
     || #{ arg_types := ArgTypes,
           res_type  := ResType,
           format    := Format,
           end_bb    := false,
           opname    := Op
         } <- aeb_fate_generate_ops:get_ops(),
        [a] == lists:usort(Format),
        length(Format) == tuple_size(ArgTypes) + 1,
        not black_listed(Op) ].

spec_overrides() ->
    #{ 'MAKE_VARIANT' => [{out, any, variant},
                          {in, any, {list, integer}},
                          {in, any, integer},
                          {in, any, integer}] }.

fix_bad_types(#instr{ op = Op } = I) ->
    case maps:get(Op, spec_overrides(), none) of
        none -> I;
        Args -> #instr{op = Op, args = Args}
    end.

black_listed(Op) ->
    lists:member(Op, ['MICROBLOCK']).

other_instructions() ->
    Simple = maps:from_list([{Op, true} || #instr{ op = Op } <- simple_instructions() ]),
    [ Op || #{ opname := Op } <- aeb_fate_generate_ops:get_ops(),
            not maps:is_key(Op, Simple) ].

-define(InstrSpecCache, '$ispec_cache').
-spec instruction_spec() -> #{ mnemonic() => instr_spec() }.
instruction_spec() ->
    case get(?InstrSpecCache) of
        undefined ->
            Spec = maps:from_list([ {I#instr.op, I} || I <- simple_instructions() ]),
            put(?InstrSpecCache, Spec),
            Spec;
        Spec -> Spec
    end.

%% -- VM state model ---------------------------------------------------------

-type fun_name() :: <<_:32>>.
-type fun_spec() :: {fun_name(), [type()], type()}.

-record(state, { stack        :: [type()],
                 vars         :: #{ integer() => type() },
                 args         :: #{ integer() => type() },
                 funs         :: [fun_spec()] }).

-type state() :: #state{}.

-type arg()   :: aeb_fate_ops:fate_arg().
-type instr() :: {mnemonic(), [arg()]}.

-type value() :: aeb_fate_data:fate_type().

-spec initial_state([type()], [fun_spec()]) -> state().
initial_state(Args, Funs) ->
    #state{ args         = maps:from_list(indexed(0, Args)),
            vars         = #{},
            stack        = [],
            funs         = Funs }.

-spec get_instr(mnemonic()) -> instr_spec() | undefined.
get_instr(Op) ->
    maps:get(Op, instruction_spec(), undefined).

-spec get_type(state(), arg()) -> type() | void.
get_type(_, {immediate, V}) -> infer_type(V);
get_type(S, {arg, N})       -> maps:get(N, S#state.args, void);
get_type(S, {var, N})       -> maps:get(N, S#state.vars, void);
get_type(S, {stack, 0})     -> hd(S#state.stack ++ [void]).

-spec pop(non_neg_integer(), state()) -> state().
pop(N, S) ->
    S#state{ stack = drop(N, S#state.stack) }.

-spec write_arg(arg(), type(), state()) -> state().
write_arg({stack, 0}, Type, S) -> S#state{ stack = [Type | S#state.stack] };
write_arg({var, N},   Type, S) -> S#state{ vars  = (S#state.vars)#{ N => Type } };
write_arg({arg, N},   Type, S) -> S#state{ args  = (S#state.args)#{ N => Type } }.

-spec matching_regs(state(), type()) -> [arg()].
matching_regs(#state{ vars = VarMap, args = ArgMap }, Type) ->
    Vars = [ {{var, I}, T} || {I, T} <- maps:to_list(VarMap) ],
    Args = [ {{arg, I}, T} || {I, T} <- maps:to_list(ArgMap) ],
    [ A || {A, T} <- Vars ++ Args, match_type(Type, T) ].

-spec infer_type(value()) -> type().
infer_type(_) -> any.

%% Check that an instruction can be executed in the given state.
-spec check_instr(state(), instr()) -> boolean().
check_instr(S, {Op, Args}) ->
    case get_instr(Op) of
        undefined ->
            ?TODO("non-simple instruction ~s", [Op]),
            false;
        #instr{ args = ArgsSpec } ->
            check_arguments(S, ArgsSpec, Args);
        _ -> false
    end.

-spec check_arguments(state(), [instr_spec()], [instr()]) -> boolean().
check_arguments(_S, [], []) -> true;
check_arguments(S, [{out, Mode, _} | ArgSpec], [Arg | Args]) ->
    check_mode(out, Mode, Arg) andalso
    check_arguments(S, ArgSpec, Args);
check_arguments(S, [{in, Mode, Type} | ArgSpec], [Arg | Args]) ->
    S1 = case Arg of
             {stack, 0} -> pop(1, S);
             _          -> S
         end,
    check_mode(in, Mode, Arg) andalso
    match_type(Type, get_type(S, Arg)) andalso
    check_arguments(S1, ArgSpec, Args);
check_arguments(_, _, _) -> false.

-spec check_mode(in | out, arg_mode(), arg()) -> boolean().
check_mode(out, _, {immediate, _})        -> false;
check_mode(out, any, _)                   -> true;
check_mode(in, any, _)                    -> true;
check_mode(in, immediate, {immediate, _}) -> true;
check_mode(in, immediate, _)              -> false.

-spec match_type(Need :: type(), Have :: type()) -> boolean().
match_type(T, T)                             -> true;
match_type(_, void)                          -> false;
match_type(_, any)                           -> false;
match_type(any, _)                           -> true;
match_type(S, T) when is_atom(S), is_atom(T) -> false;
match_type({list, S}, {list, T})             -> match_type(S, T);
match_type({list, any}, list)                -> true;
match_type({list, _}, _)                     -> false;
match_type(S, T)                             ->
    ?TODO("match_type(~p, ~p)", [S, T]),
    false.

-spec step_instr(state(), instr()) -> state().
step_instr(S, {Op, Args}) ->
    #instr{ args = ArgsSpec } = get_instr(Op),
    Args1 = lists:zip(ArgsSpec, Args),
    S1  = pop(length([ 1 || {{in, _, _}, {stack, _}} <- Args1 ]), S),
    Out = [ {Arg, Type} || {{out, _, Type}, Arg} <- Args1 ],
    lists:foldl(fun({Arg, Type}, St) -> write_arg(Arg, Type, St) end,
                S1, Out).

%% -- Generators -------------------------------------------------------------

out_arg_g() ->
    oneof([{stack, 0},
           {var, nat()},
           {var, ?LET(N, nat(), -N - 1)},
           {arg, nat()}]).

args_g(_, []) -> [];
args_g(S, [{out, _, _} | ArgsSpec]) ->
    [out_arg_g() | args_g(S, ArgsSpec)];
args_g(S, [{in, immediate, Type} | ArgsSpec]) ->
    [{immediate, value_g(Type)} | args_g(S, ArgsSpec)];
args_g(S, [{in, any, Type} | ArgsSpec]) ->
    ?LET(Arg, arg_g(S, Type),
    case Arg of
        {stack, 0} -> [Arg | args_g(pop(1, S), ArgsSpec)];
        _          -> [Arg | args_g(S, ArgsSpec)]
    end).

arg_g(S, Type) ->
    Regs = matching_regs(S, Type),
    frequency(
      [{1, {immediate, value_g(Type)}}] ++
      [{5, elements(Regs)} || Regs /= []]).

pubkey_g() -> binary(32).

value_g(integer)      -> int();
value_g(boolean)      -> bool();
value_g(address)      -> {address, pubkey_g()};
value_g(bits)         -> {bits, int()};
value_g(bytes)        -> {bytes, binary()};
value_g({bytes, N})   -> {bytes, binary(N)};
value_g(contract)     -> {contract, pubkey_g()};
value_g(hash)         -> value_g({bytes, 32});
value_g(signature)    -> value_g({bytes, 64});
value_g(oracle)       -> {oracle, pubkey_g()};
value_g(oracle_query) -> {oracle_query, pubkey_g()};
value_g(string)       -> eqc_gen:fmap(fun list_to_binary/1, list(choose($!, $~)));
value_g({list, T})    -> list(value_g(T));
value_g({tuple, Ts})  -> {tuple, eqc_gen:fmap(fun list_to_tuple/1, [value_g(T) || T <- Ts])};
value_g(map)          -> {todo, map};
value_g(list)         -> {todo, list};
value_g(typerep)      -> {todo, typerep};
value_g(tuple)        -> {todo, tuple};
value_g(variant)      -> {todo, variant};
value_g(any)          -> {todo, any}.

no_todo(todo)               -> false;
no_todo([H | T])            -> no_todo(H) andalso no_todo(T);
no_todo(T) when is_tuple(T) -> no_todo(tuple_to_list(T));
no_todo(M) when is_map(M)   -> no_todo(maps:to_list(M));
no_todo(_)                  -> true.

timestamp_g() -> choose(1550000000000, 1900000000000).

%% -- State machine ----------------------------------------------------------

simple_instr_args(S) ->
    ?LET(#instr{ op = Op, args = ArgsSpec }, elements(maps:values(instruction_spec())),
         [{Op, args_g(S, ArgsSpec)}]).

simple_instr_pre(S, [I]) ->
    no_todo(I) andalso
    check_instr(S, I).

simple_instr_next(S, _, [I]) ->
    %% io:format("S = ~p\nI = ~p\n", [S, I]),
    step_instr(S, I).

%% -- Running the code -------------------------------------------------------

-define(TestFun, <<"test">>).
-define(TestContract, <<"test_contract___________________">>).
-define(CallGas, 6000000).
-define(Caller, <<117733:256>>).
-define(Origin, <<228844:256>>).

build_code(Instrs) ->
    BB = build_bb(Instrs),
    FCode = aeb_fate_code:new(),
    aeb_fate_code:insert_fun(?TestFun, [], {[], integer}, #{0 => BB}, FCode).

build_bb(Instr) ->
    ToInstr = fun({set, _, {call, ?MODULE, Fun, Args}}) ->
                    case {Fun, Args} of
                        {simple_instr, [{Op, As}]} -> [list_to_tuple([Op | As])]
                    end;
                 (_) -> []
              end,
    lists:flatmap(ToInstr, Instr) ++ [{'RETURNR', {immediate, 0}}].

make_store(undefined) -> aefa_stores:initial_contract_store();
make_store(Store)     -> Store.

make_trees(Caller, Cache) ->
    %% All contracts and the caller must have accounts
    Trees = aec_trees:new_without_backend(),
    Pubkeys = [Caller| [X || X <- maps:keys(Cache)]],
    ATrees = lists:foldl(fun(Pubkey, Acc) ->
                                 Account = aec_accounts:new(Pubkey, 10000),
                                 aec_accounts_trees:enter(Account, Acc)
                         end, aec_trees:accounts(Trees), Pubkeys),
    CTrees = lists:foldl(fun(Pubkey, Acc) ->
                                 Contract0 = aect_contracts:new(Pubkey, 1, #{vm => 5, abi => 3}, <<>>, 0),
                                 Contract  = aect_contracts:set_pubkey(Pubkey, Contract0),
                                 aect_state_tree:enter_contract(Contract, Acc)
                         end, aec_trees:contracts(Trees), Pubkeys),
    aec_trees:set_contracts(aec_trees:set_accounts(Trees, ATrees), CTrees).

call_spec(Store) ->
    Fun = aeb_fate_code:symbol_identifier(?TestFun),
    #{ contract => ?TestContract,
       gas      => ?CallGas,
       value    => 0,
       call     => aeb_fate_encoding:serialize({tuple, {Fun, {tuple, {}}}}),
       store    => make_store(Store) }.

call_env(#{ timestamp := Time, height := Height }, Cache) ->
    TimeFieldIx = 13,   %% tx_env is opaque and no setter for timestamp
    TxEnv       = setelement(TimeFieldIx, aetx_env:tx_env(Height), Time),
    #{ trees     => make_trees(?Caller, Cache),
       caller    => ?Caller,
       origin    => ?Origin,
       gas_price => 1,
       tx_env    => TxEnv }.

gas_used(ES) ->
    ?CallGas - aefa_engine_state:gas(ES).

gas_per_us(Time, ES) ->
    gas_used(ES) / Time.

stats(Time, ES) ->
    #{ gas_per_us => gas_per_us(Time, ES),
       gas_used   => gas_used(ES),
       time       => Time }.

run(Env0, FCode, Store) ->
    Spec  = call_spec(Store),
    Cache = #{ ?TestContract => FCode },
    Env   = call_env(Env0, Cache),
    erlang:garbage_collect(),
    timer:sleep(50),
    case timer:tc(fun() -> aefa_fate:run_with_cache(Spec, Env, Cache) end) of
        {Time, {ok, ES}} ->
            Res = aefa_engine_state:accumulator(ES),
            {Res, stats(Time, ES)};
        {Time, {error, Err, ES}} ->
            {{error, binary_to_list(Err)}, stats(Time, ES)}
    end.

%% -- Property ---------------------------------------------------------------

prop_instr() ->
    ?FORALL(Timestamp, timestamp_g(),
    ?FORALL(Instrs, commands(?MODULE, initial_state([], [])),
    begin
        FCode = build_code(Instrs),
        Store = undefined,
        Env   = #{ timestamp => Timestamp, height => 1 },
        ?WHENFAIL(io:format("~s", [aeb_fate_asm:pp(FCode)]),
        aggregate([ element(1, I) || I <- build_bb(Instrs) ],
        try
            {Res, Stats} = run(Env, FCode, Store),
            measure(block_time, 6 / maps:get(gas_per_us, Stats),
            collect(with_title(gas_used),   maps:get(gas_used, Stats) div 100 * 100,
            collect(classify(Res),
            conjunction([ {result, check_result(Res)},
                          {gas_cost, check_gas_cost(Stats)} ]))))
        catch _:Err ->
            equals(ok, {'EXIT', Err, erlang:get_stacktrace()})
        end))
    end)).

check_result(0)          -> true;
check_result({error, _}) -> true;
check_result(Res)        -> equals(0, Res).

check_gas_cost(#{ gas_used := Gas }) when Gas < 1000 -> true;
check_gas_cost(#{ gas_used := GasUsed, time := Time, gas_per_us := GasRate }) ->
    BlockTime = 6 / GasRate,
    ?WHENFAIL(io:format("Gas used: ~p\nTime: ~.2fms\nBlockTime: ~.3fs\n", [GasUsed, Time / 1000, BlockTime]),
              BlockTime < 300.0).

classify(0) -> ok;
classify({error, Str}) ->
    {error, hd(string:split(Str, ":"))};
classify(Other) ->
    Other.

%% -- Utility functions ------------------------------------------------------

drop(N, Xs) -> lists:sublist(Xs, N + 1, 1 bsl 64).

indexed(Xs) -> indexed(1, Xs).

indexed(I, Xs) ->
    lists:zip(lists:seq(I, length(Xs) - 1 + I), Xs).
