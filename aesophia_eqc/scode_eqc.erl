%%% File        : scode_eqc.erl
%%% Author      : Ulf Norell
%%% Description : Tests for the FATE compiler backend
%%% Created     : 5 Nov 2019 by Ulf Norell
-module(scode_eqc).

-compile([export_all, nowarn_export_all]).
-include_lib("eqc/include/eqc.hrl").

-type mode() :: in | out.

-record(instr, {op :: atom(), args :: list(mode())}).
-type instr() :: #instr{}.

-spec instructions() -> [instr()].
instructions() ->
    Args = fun(Types, Format) ->
                In = lists:duplicate(tuple_size(Types), in),
                case tuple_size(Types) == length(Format) of
                    true -> In;
                    false -> [out | In]
                end end,
    [ #instr{ op = Op, args = Args(ArgTypes, Format) }
      || #{ arg_types := ArgTypes,
            format    := Format,
            opname    := Op } <- aeb_fate_generate_ops:get_ops(),
         is_scode_instr(Op) ].

is_scode_instr(Op) ->
    Control        = ['RETURN', 'RETURNR', 'JUMP', 'JUMPIF', 'SWITCH_V2', 'SWITCH_V3', 'SWITCH_VN'],
    Unused         = ['DUP', 'DUPA', 'NOP', 'BITS_ALLA', 'BITS_NONEA'],
    NotImplemented = ['AENS_UPDATE', 'DEACTIVATE'],
    NotScode = Control ++ Unused ++ NotImplemented,
    not lists:member(Op, NotScode).

desugared_instrs() ->
    ['POP', 'PUSH', 'INC', 'INCA', 'DEC', 'DECA'].

side_effect_instrs() ->
    ['SPEND', 'LOG0', 'LOG1', 'LOG2', 'LOG3', 'LOG4',
     'ORACLE_RESPOND', 'ORACLE_EXTEND',
     'AENS_CLAIM', 'AENS_PRECLAIM', 'AENS_REVOKE', 'AENS_TRANSFER',
     'ABORT'].

is_side_effect(Op) ->
    lists:member(Op, side_effect_instrs()).

-define(InstrSpecCache, {?MODULE, '$ispec_cache'}).
-spec instruction_map() -> #{ atom() => list(mode()) }.
instruction_map() ->
    case get(?InstrSpecCache) of
        undefined ->
            Spec = maps:from_list([ {I#instr.op, I#instr.args} || I <- instructions() ]),
            put(?InstrSpecCache, Spec),
            Spec;
        Spec -> Spec
    end.

instruction(Op) ->
    maps:get(Op, instruction_map()).

%% -- Generators -------------------------------------------------------------

string_g() ->
    ?LET([W], eqc_erlang_program:words(1), return(W)).

immediate_g() ->
    {immediate, fate_eqc:value_g()}.

immediate_g(Type) ->
    {immediate, fate_eqc:value_g(Type)}.

out_arg_g() ->
    oneof([{stack, 0},
           {arg,   choose(0, 2)},
           {var,   choose(0, 2)},
           {store, choose(1, 3)}]).

arg_g() ->
    weighted_default({1,  immediate_g()},
                     {19, out_arg_g()}).

arg_g(Type) ->
    weighted_default({1, immediate_g(Type)},
                     {19, out_arg_g()}).

args_g('CALL_R') ->
    ?LET({Fun, [R | Args]}, {string_g(), vector(4, arg_g())},
         [R, {immediate, list_to_binary(Fun)} | Args]);
args_g('CALL_GR') ->
    ?LET({Fun, [R | Args]}, {string_g(), vector(5, arg_g())},
         [R, {immediate, list_to_binary(Fun)} | Args]);
args_g('TUPLE') ->
    ?LET({Dst, N}, {out_arg_g(), choose(0, 4)},
         [Dst, {immediate, N}]);
args_g(Op) ->
    Args = instruction(Op),
    G    = fun(in) -> arg_g(); (out) -> out_arg_g() end,
    lists:map(G, Args).

simple_instr_g() ->
    ?LET(Op, elements(maps:keys(instruction_map()) -- desugared_instrs()),
         eqc_gen:fmap(fun list_to_tuple/1, [Op | args_g(Op)])).

-define(SwitchDepth, 2).
switch_g() ->
    switch_g(?SwitchDepth).

switch_type_g() ->
    oneof([boolean, tuple,
           {variant, eqc_gen:fmap(fun(N) -> lists:duplicate(N, tuple) end, choose(1, 3))}]).

switch_alt_g(D) ->
    weighted_default(
      {1, missing},
      {3, frequency([{3, [switch_g(D - 1)]} || D > 0] ++
                    [{1, [switch_body | smaller(3, program_g())]}])}).

switch_alts_g(T, D) ->
    N = case T of boolean      -> 2;
                  tuple        -> 1;
                  {variant, A} -> length(A)
        end,
    vector(N, smaller(N + 1, switch_alt_g(D))).

switch_g(D) ->
    ?LAZY(
    ?LET(Type, switch_type_g(),
    ?LET(Alts, switch_alts_g(Type, D - 1),
    ?LET(Def,  smaller(2, switch_alt_g(D - 1)),
        {switch, arg_g(Type), Type, Alts, Def})))).

smaller(K, G) -> ?SIZED(N, resize(N div K, G)).
longer_list(K, G) -> ?SIZED(N, resize(N * K, list(resize(N, G)))).

instr_g() ->
    frequency([{9, simple_instr_g()},
               {1, switch_g()}]).

code_g() -> longer_list(5, instr_g()).
coda_g() -> weighted_default({4, []}, {1, [loop]}).

-define(MaxBranches, 2000).

max_branches(0) -> 1000;
max_branches(1) -> 30;
max_branches(2) -> 10;
max_branches(_) -> 6.

count_branches([I | Is]) ->
    count_branches(I) * count_branches(Is);
count_branches(S = {switch, _, _, _, _}) ->
    Bs = try prune_branches(init_state(), branches(init_state(), S)) catch throw:type_error -> [] end,
    max(1, lists:sum([ count_branches(Code) || {_, Code} <- Bs ]));
count_branches(_) -> 1.

cap_branches(_, []) -> [];
cap_branches(Cap, [I | Is]) ->
    B = count_branches(I),
    case B > Cap of
        true  -> cap_branches(Cap, Is);
        false ->
            Cap1 = if B =< 1 -> Cap;
                      true   -> Cap div B end,
            [I | cap_branches(Cap1, Is)]
    end.


program_g(MaxBranches) ->
    ?LET(P, program_g(),
         cap_branches(MaxBranches, P)).

program_g() ->
    ?LET({Code, Coda}, {code_g(), coda_g()},
         return(Code ++ Coda)).

%% -- Symbolic evaluation ----------------------------------------------------

init_state() ->
    #{ stack => {underflow, 0},
       args  => #{},
       vars  => #{},
       store => #{},
       effects => [] }.

op_view(switch_body) ->
    {switch_body, none, []};
op_view(I) when element(1, I) == 'PUSH';
                element(1, I) == 'CALL';
                element(1, I) == 'CALL_R';
                element(1, I) == 'CALL_GR' ->
    [Op | Args] = tuple_to_list(I),
    {Op, {stack, 0}, Args};
op_view('INCA')       -> {'INC', {stack, 0}, [{stack, 0}]};
op_view('DECA')       -> {'INC', {stack, 0}, [{stack, 0}]};
op_view('BITS_NONEA') -> {'BITS_NONE', {stack, 0}, []};
op_view('BITS_ALLA')  -> {'BITS_ALL', {stack, 0}, []};
op_view({'POP', R}) ->
    {'POP', R, [{stack, 0}]};
op_view(I) ->
    [Op | Args] = tuple_to_list(I),
    case {instruction(Op), Args} of
        {[out | _], [Dst | In]} -> {Op, Dst, In};
        _                       -> {Op, none, Args}
    end.

is_value(N) when is_integer(N) -> true;
is_value(S) when is_binary(S)  -> true;
is_value(false)                -> true;
is_value(true)                 -> true;
is_value({bits, _})            -> true;
is_value({bytes, _})           -> true;
is_value({address, _})         -> true;
is_value({contract, _})        -> true;
is_value({oracle, _})          -> true;
is_value({oracle_query, _})    -> true;
is_value({tuple, _})           -> true;
is_value({variant, _, _, _})   -> true;
is_value(L) when is_list(L)    -> true;
is_value(M) when is_map(M)     -> true;
is_value({typerep, _})         -> true;
is_value(_)                    -> false.

read_arg(#{ stack := Stack } = S, {stack, 0}) ->
    case Stack of
        {underflow, N} -> {{stack, N}, S#{ stack := {underflow, N + 1} }};
        [V | Stack1]   -> {V, S#{ stack := Stack1 }}
    end;
read_arg(#{ args  := Args  } = S, {arg, N})             -> {maps:get( N, Args,  {arg,    N}), S};
read_arg(#{ vars  := Vars  } = S, {var, N}) when N >= 0 -> {maps:get( N, Vars,  {var,    N}), S};
read_arg(#{ store := Store } = S, {var, N}) when N < 0  -> {maps:get(-N, Store, {store, -N}), S};
read_arg(#{ store := Store } = S, {store, N})           -> {maps:get( N, Store, {store,  N}), S};
read_arg(S, {immediate, V})                             -> {V, S}.

read_args(S, Args) ->
    {Vs, S1} =
        lists:foldl(fun(Arg, {Vs, S1}) ->
                        {V, S2} = read_arg(S1, Arg),
                        {[V | Vs], S2}
                    end, {[], S}, Args),
    {lists:reverse(Vs), S1}.

write_arg(none, _, S) -> S;
write_arg({stack, 0}, {stack, N}, #{ stack := {underflow, M} } = S) when N + 1 == M ->
    S#{ stack := {underflow, N} };
write_arg({store, N}, {store, N}, #{ store := Store } = S) -> S#{ store := maps:remove(N, Store) };
write_arg({stack, 0}, V, #{ stack := Stack } = S) -> S#{ stack := [V | Stack] };
write_arg({arg,   N}, V, #{ args  := Args  } = S) -> S#{ args  := Args#{ N => V } };
write_arg({var,   N}, V, #{ vars  := Vars  } = S) when N >= 0 -> S#{ vars  := Vars#{ N => V } };
write_arg({var,   N}, V, S) when N < 0  -> write_arg({store, -N}, V, S);
write_arg({store, N}, V, #{ store := Store } = S) -> S#{ store := Store#{ N => V } }.

add_side_effect(E, #{ effects := Eff } = S) ->
    S#{ effects := [E | Eff] }.

side_effect(Op, Vs, S) ->
    case is_side_effect(Op) of
        true  -> add_side_effect({Op, Vs}, S);
        false -> S
    end.

alt_tag(boolean, 0)      -> false;
alt_tag(boolean, 1)      -> true;
alt_tag(tuple,   0)      -> tuple;
alt_tag({variant, _}, I) -> {con, I}.

branches(_S, _Path, _Reads, missing, []) -> [];
branches(S, Path, Reads, missing, [C | Catchalls]) ->
    branches(S, Path, Reads, C, Catchalls);
branches(_S, Path, Reads, [switch_body | Code], _) ->
    [{lists:reverse(Path), [ {read, R} || R <- lists:reverse(Reads) ], Code}];
branches(S, Path, Reads, [{switch, _, _, _, _} = Switch], Catchalls) ->
    branches(S, Path, Reads, Switch, Catchalls);
branches(S, Path, Reads, {switch, Arg, Type, Alts, Def}, Catchalls) ->
    {V, S1} = read_arg(S, Arg),
    type_check(V, Type),
    Catchalls1 = [Def || Def /= missing] ++ Catchalls,
    [ {Path1, Rs, Code}
      || {I, Alt} <- ix(0, Alts),
         {Path1, Rs, Code} <- branches(S1, [alt_tag(Type, I) | Path], [Arg | Reads], Alt, Catchalls1) ].

branches(S, Switch) ->
    branches(S, [], [], Switch, []).

prune_branches(S, Alts) ->
    uniq(lists:flatmap(fun({Path, Reads, Code}) -> prune_branch(S, Path, Reads, Code, [], []) end, Alts)).

type_check(V, Type) ->
    Value = is_value(V),
    try
        case Type of
            _ when not Value -> ok;
            boolean          -> true = lists:member(V, [false, true]);
            tuple            -> {tuple, _} = V;
            {variant, Ar}    -> {variant, Ar1, _, _} = V,
                                true = length(Ar) == length(Ar1)
        end
    catch _:_ ->
        throw(type_error)
    end.

match_tag(Tag, V) ->
    Value = is_value(V),
    case {Tag, V} of
        {catchall, _}                  -> maybe;
        _ when not Value -> maybe;
        {false, _}                     -> Tag == V;
        {true,  _}                     -> Tag == V;
        {tuple, {tuple, _}}            -> true;
        {tuple, _}                     -> false;
        {{con, I}, {variant, _, I, _}} -> true;
        {{con, _}, _}                  -> false
    end.

prune_branch(S, [Tag | Path], [I = {read, R} | Reads], Code, AccP, AccC) ->
    {V, S1} = read_arg(S, R),
    case match_tag(Tag, V) of
        true  -> prune_branch(S1, Path, Reads, Code, AccP, [I || R == {stack, 0}] ++ AccC);
        false -> [];
        maybe -> prune_branch(S1, Path, Reads, Code, [Tag | AccP], [I || R == {stack, 0}] ++ AccC)
    end;
prune_branch(_, [], [], Code, AccP, AccC) ->
    [{lists:reverse(AccP), lists:reverse(AccC) ++ Code}].

step(S, {read, Arg}) ->
    {_, S1} = read_arg(S, Arg),
    S1;
step(S, loop) -> S;
step(S, Switch = {switch, _Arg, _Type, _Alts, _Def}) ->
    try branches(S, Switch) of
        Bs -> {fork, Bs}
    catch throw:type_error ->
        S#{ skip => true }
    end;
step(S, {'TUPLE', Dst, {immediate, N}}) ->
    step(S, list_to_tuple(['TUPLE', Dst | lists:duplicate(N, {stack, 0})]));
step(S, {'ABORT', Reg}) ->
    {Msg, S1} = read_arg(S, Reg),
    S1#{ abort => Msg };
step(S, I) ->
    {Op, Dst, Args} = op_view(I),
    {Vals, S1} = read_args(S, Args),
    write_arg(Dst, sym(Op, Vals),
    side_effect(Op, Vals, S1)).

-define(is_value(X), X == true orelse X == false).
-define(is_cmp(X), X == 'LT'  orelse X == 'GT'  orelse X == 'EQ' orelse
                   X == 'ELT' orelse X == 'EGT' orelse X == 'NEQ').

sym('STORE', [V]) -> V;
sym('POP',   [V]) -> V;
sym('PUSH',  [V]) -> V;
sym('IS_NIL', [{'CONS', _, _}]) -> false;
sym('IS_NIL', ['NIL']) -> true;
sym(Op, [X, Y]) when ?is_cmp(Op) ->
    Value = is_value(X) andalso is_value(Y),
    case Op of
        _ when not Value -> {Op, X, Y};
        'LT'             -> X < Y;
        'GT'             -> X > Y;
        'EQ'             -> X =:= Y;
        'ELT'            -> X =< Y;
        'EGT'            -> X >= Y;
        'NEQ'            -> X =/= Y
    end;
sym('ADD', [X, Y]) when is_integer(X), is_integer(Y) -> X + Y;
sym('ADD', [1, Y]) -> {'INC', Y};
sym('ADD', [X, 1]) -> {'INC', X};
sym('SUB', [X, 1]) -> {'DEC', X};
sym('SUB', [X, Y]) when is_integer(X), is_integer(Y) -> X - Y;
sym('MUL', [X, Y]) when is_integer(X), is_integer(Y) -> X * Y;
sym('DIV', [X, Y]) when is_integer(X), is_integer(Y), Y /= 0 -> X div Y;
sym('MOD', [X, Y]) when is_integer(X), is_integer(Y), Y /= 0 -> X rem Y;
sym('NOT', [false]) -> true;
sym('NOT', [true])  -> false;
sym(Op, [])       -> Op;
sym(Op, Vs)       -> list_to_tuple([Op | Vs]).

pp_state(S, Verbose) ->
    [ io:format("- ~p\n", [S]) || Verbose ].

sym_eval(S, LoopCount, P, Verbose) ->
    sym_eval(S, [], P, LoopCount, P, Verbose).

sym_eval(S = #{ abort := _ }, Trace, _, _, _, Verbose) ->
    pp_state(S, Verbose),
    [{lists:reverse(Trace), S}];
sym_eval(S, Trace, _, _, [], Verbose) ->
    pp_state(S, Verbose),
    [{lists:reverse(Trace), S}];
sym_eval(S, Trace, P0, LoopC, [I | Is], Verbose) ->
    pp_state(S, Verbose),
    [ io:format("~p\n", [I]) || Verbose ],
    S1 = step(S, I),
    case S1 of
        {fork, Alts}                 ->
            case prune_branches(S, Alts) of
                [] -> [{lists:reverse(Trace), S#{ abort => "Incomplete patterns" }}];
                Alts1 ->
                    lists:append([ sym_eval(S, [{switch, Path} | Trace], P0, LoopC, Alt ++ Is, Verbose)
                                   || {Path, Alt} <- Alts1 ])
            end;
        _ when I == loop, LoopC =< 0 -> pp_state(S1, Verbose), [{lists:reverse(Trace), S1}];
        _ when I == loop             -> sym_eval(S1, [loop | Trace], P0, LoopC - 1, P0, Verbose);
        _                            -> sym_eval(S1, Trace, P0, LoopC, Is, Verbose)
    end.

%% -- Properties -------------------------------------------------------------

optimize(Code) -> optimize(Code, []).
optimize(Code, Opts) ->
    {_, _, Code1} = aeso_fcode_to_fate:optimize_fun([], "test_fun", {[], {[], integer}, Code}, Opts),
    Code1.

prop_eval() ->
    in_parallel(
    ?LET(Verbose, parameter(verbose, false),
    ?FORALL(LoopCount, choose(0, 3),
    ?FORALL(P1, program_g(max_branches(LoopCount)),
    begin
        Opts = [ {debug, [opt_rules, opt]} || Verbose ],
        S0 = init_state(),
        P2 = optimize(P1, Opts),
        ?WHENFAIL(io:format("Optimized:\n  ~p\n", [P2]),
        try
            [ io:format("== Original ==\n") || Verbose ],
            S1 = sym_eval(S0, LoopCount, P1, Verbose),
            [ io:format("== Optimized ==\n") || Verbose ],
            S2 = sym_eval(S0, LoopCount, P2, Verbose),
            Size1 = code_size(P1),
            Size2 = code_size(P2),
            Branches = length(S1),
            ?IMPLIES(not lists:any(fun({_, S}) -> maps:is_key(skip, S) end, S1),
            measure(optimize, (1 + Size2) / (1 + Size1),
                conjunction([{skip, equals([], [ TS || {_, #{skip := _}} = TS <- S2 ])},
                             {branches, check_branches(Branches, P1)},
                             {size, ?WHENFAIL(io:format("~p > ~p\n", [Size2, Size1]), Size2 =< Size1)},
                             {state, compare_states(S1, S2)}])))
        catch K:Err ->
            equals({K, Err, erlang:get_stacktrace()}, ok)
        end)
    end)))).

check_branches(B, P) ->
    ?WHENFAIL(
       begin
           Bs = [ Trace || {Trace, _} <- sym_eval(init_state(), 0, P, false) ],
           io:format("Program branches: ~p\nTotal Branches:   ~p\nAll paths (no loops):\n  ~p\n",
                     [count_branches(P), B, Bs])
        end, B =< ?MaxBranches).

compare_states(Ss1, Ss2) when is_list(Ss1), is_list(Ss2) ->
    {Trace1, _} = lists:unzip(Ss1),
    {Trace2, _} = lists:unzip(Ss2),
    case compare_trace(Trace1, Trace2) of
        true  ->
            TSS = keyuniq(2, [ {T, {S1, S2}} || {{T, S1}, {_, S2}} <- lists:zip(Ss1, Ss2) ]),
            conjunction([ {Trace, compare_states(S1, S2)} || {Trace, {S1, S2}} <- TSS ]);
        false -> equals({trace, Trace1}, {trace, Trace2})
    end;
compare_states(#{ stack := Stack1, store := Store1, effects := Eff1 } = S1,
               #{ stack := Stack2, store := Store2, effects := Eff2 } = S2) ->
    Abort1 = maps:get(abort, S1, false),
    Abort2 = maps:get(abort, S2, false),
    case Abort1 == false andalso Abort2 == false of
        false -> equals({abort, Abort1}, {abort, Abort2});
        true  -> conjunction([{stack, equals(Stack1, Stack2)},
                              {store, equals(Store1, Store2)},
                              {effects, equals(lists:reverse(Eff1), lists:reverse(Eff2))}])
    end.

compare_trace(T1, T2) when length(T1) /= length(T2) -> false;
compare_trace(T1, T2) ->
    Flat = fun({switch, Tags}) -> Tags;
              (Tag)            -> [Tag] end,
    Cmp = fun({P1, P2}) -> lists:flatmap(Flat, P1) == lists:flatmap(Flat, P2) end,
    lists:all(Cmp, lists:zip(T1, T2)).

code_size(P) when is_list(P) ->
    lists:sum([ code_size(I) || I <- P ]);
code_size(missing) -> 0;
code_size({switch, _, _, Alts, Def}) ->
    1 + code_size([Def | Alts]);
code_size({'POP', {var, 9999}}) -> 0;   %% Don't count popping unused stack elems
code_size(_) -> 1.

ix(I, Xs) ->
    lists:zip(lists:seq(I, I + length(Xs) - 1), Xs).

ix(Xs) -> ix(1, Xs).

keyuniq(Ix, Xs) ->
    Xs -- (Xs -- lists:ukeysort(Ix, Xs)).

uniq(Xs) -> Xs -- (Xs -- lists:usort(Xs)).

