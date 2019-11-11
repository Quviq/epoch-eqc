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

instr_g() ->
    simple_instr_g().

program_g() ->
    ?LET({Code, Loop}, {list(instr_g()), weighted_default({5, false}, {1, true})},
         return(Code ++ [loop || Loop])).

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

step(S, loop) -> S;
step(S, {'TUPLE', Dst, {immediate, N}}) ->
    step(S, list_to_tuple(['TUPLE', Dst | lists:duplicate(N, {stack, 0})]));
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
    sym_eval(S, P, LoopCount, P, Verbose).

sym_eval(S, _, _, [], Verbose) ->
    pp_state(S, Verbose),
    S;
sym_eval(S, P0, LoopC, [I | Is], Verbose) ->
    pp_state(S, Verbose),
    [ io:format("~p\n", [I]) || Verbose ],
    S1 = step(S, I),
    case I of
        loop when LoopC =< 0 ->
            pp_state(S1, Verbose),
            S1;
        loop ->
            sym_eval(S1, P0, LoopC - 1, P0, Verbose);
        _ -> sym_eval(S1, P0, LoopC, Is, Verbose)
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
            [ io:format("== Original ==\n") || Verbose ],
            S1 = sym_eval(S0, LoopCount, P, Verbose),
            [ io:format("== Optimized ==\n") || Verbose ],
            S2 = sym_eval(S0, LoopCount, P1, Verbose),
            compare_states(S1, S2)
        catch K:Err ->
            equals({K, Err, erlang:get_stacktrace()}, ok)
        end)
    end))).

compare_states(#{ stack := Stack1, store := Store1, effects := Eff1 },
               #{ stack := Stack2, store := Store2, effects := Eff2 }) ->
    conjunction([{stack, equals(Stack1, Stack2)},
                 {store, equals(Store1, Store2)},
                 {effects, equals(lists:reverse(Eff1), lists:reverse(Eff2))}]).

