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

out_arg_g() ->
    oneof([{stack, 0},
           {arg,   choose(0, 2)},
           {var,   choose(0, 2)},
           {store, choose(1, 3)}]).

arg_g() -> out_arg_g().
    %% weighted_default({0, immediate_g()},
    %%                  {9, out_arg_g()}).

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
           {variant, eqc_gen:fmap(fun(N) -> lists:duplicate(N, any) end, choose(1, 3))}]).

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
        {switch, arg_g(), Type, Alts, Def})))).

smaller(K, G) -> ?SIZED(N, resize(N div K, G)).
longer_list(K, G) -> ?SIZED(N, resize(N * K, list(resize(N, G)))).

instr_g() ->
    frequency([{9, simple_instr_g()},
               {1, switch_g()}]).

code_g() -> longer_list(5, instr_g()).
coda_g() -> weighted_default({4, []}, {1, [loop]}).

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

op_view(I) when element(1, I) == 'PUSH';
                element(1, I) == 'CALL';
                element(1, I) == 'CALL_R';
                element(1, I) == 'CALL_GR' ->
    [Op | Args] = tuple_to_list(I),
    {Op, {stack, 0}, Args};
op_view(I) ->
    [Op | Args] = tuple_to_list(I),
    case {instruction(Op), Args} of
        {[out | _], [Dst | In]} -> {Op, Dst, In};
        _                       -> {Op, none, Args}
    end.

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

alt_tag(boolean, 1)      -> false;
alt_tag(boolean, 2)      -> true;
alt_tag(tuple,   1)      -> tuple;
alt_tag({variant, _}, I) -> {con, I}.

branches(_Path, _Reads, missing, []) -> [];
branches(Path, Reads, missing, [C | Catchalls]) ->
    branches(Path, Reads, C, Catchalls);
branches(Path, Reads, [switch_body | Code], _) ->
    [{lists:reverse(Path), [ {read, R} || R <- lists:reverse(Reads) ] ++ Code}];
branches(Path, Reads, [{switch, _, _, _, _} = Switch], Catchalls) ->
    branches(Path, Reads, Switch, Catchalls);
branches(Path, Reads, {switch, Arg, Type, Alts, Def}, Catchalls) ->
    Catchalls1 = [Def || Def /= missing] ++ Catchalls,
    [ {Path1, Code}
      || {I, Alt} <- ix(Alts),
         {Path1, Code} <- branches([alt_tag(Type, I) | Path], [Arg | Reads], Alt, Catchalls1) ].

branches(Switch) ->
    branches([], [], Switch, []).

step(S, {read, Arg}) ->
    {_, S1} = read_arg(S, Arg),
    S1;
step(S, loop) -> S;
step(S, Switch = {switch, _Arg, _Type, _Alts, _Def}) ->
    case branches(Switch) of
        [] -> S#{ abort => "Incomplete patterns" };
        Bs -> {fork, Bs}
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
sym('PUSH', [V])  -> V;
sym('IS_NIL', [{'CONS', _, _}]) -> false;
sym('IS_NIL', ['NIL']) -> true;
sym(Op, [X, Y]) when ?is_cmp(Op), ?is_value(X), ?is_value(Y) ->
    case Op of
        'LT'  -> X < Y;
        'GT'  -> X > Y;
        'EQ'  -> X =:= Y;
        'ELT' -> X =< Y;
        'EGT' -> X >= Y;
        'NEQ' -> X =/= Y
    end;
sym('NOT', [X]) when ?is_value(X) -> not X;
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
            lists:append([ sym_eval(S, [{switch, Path} | Trace], P0, LoopC, Alt, Verbose)
                           || {Path, Alt} <- Alts ]);
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
    ?FORALL({LoopCount, P}, {choose(0, 3), program_g()},
    begin
        Opts = [ {debug, [opt_rules, opt]} || Verbose ],
        S0 = init_state(),
        P1 = optimize(P, Opts),
        ?WHENFAIL(io:format("Optimized:\n  ~p\n", [P1]),
        try
            %% [ io:format("== Original ==\n") || Verbose ],
            S1 = sym_eval(S0, LoopCount, P, false),
            %% [ io:format("== Optimized ==\n") || Verbose ],
            S2 = sym_eval(S0, LoopCount, P1, false),
            measure(branches, length(S1),
                compare_states(S1, S2))
        catch K:Err ->
            equals({K, Err, erlang:get_stacktrace()}, ok)
        end)
    end))).

compare_states(Ss1, Ss2) when is_list(Ss1), is_list(Ss2) ->
    {Trace1, _} = lists:unzip(Ss1),
    {Trace2, _} = lists:unzip(Ss2),
    case Trace1 == Trace2 of
        true  ->
            TSS = keyuniq(2, [ {T, {S1, S2}} || {{T, S1}, {_, S2}} <- lists:zip(Ss1, Ss2) ]),
            conjunction([ {Trace, compare_states(S1, S2)} || {Trace, {S1, S2}} <- TSS ]);
        false -> equals(Trace1, Trace2)
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

ix(I, Xs) ->
    lists:zip(lists:seq(I, I + length(Xs) - 1), Xs).

ix(Xs) -> ix(1, Xs).

keyuniq(Ix, Xs) ->
    Xs -- (Xs -- lists:ukeysort(Ix, Xs)).

