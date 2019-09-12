%%% File        : aevm_builtin_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 9 Sep 2019 by Ulf Norell
-module(aevm_builtin_eqc).

-include_lib("eqc/include/eqc.hrl").

-compile([export_all, nowarn_export_all]).

-define(TRUNC(X), ((X) rem (1 bsl 256))).

new_state() -> put(state, #{ msize => 0, mem => #{} }).

%% -- Heap/Memory --
msize()     -> maps:get(msize, get(state)).
mload(Addr) -> maps:get(Addr, maps:get(mem, get(state))).
mstore(Addr, Word) ->
    if ?TRUNC(Word) /= Word -> error({word_overflow, Word}); true -> ok end,
    S  = get(state),
    M  = maps:get(mem, S),
    M1 = M#{ Addr => Word },
    S1 = S#{ mem := M1 },
    case Addr == maps:get(msize, S) of
        true  -> put(state, S1#{ msize := Addr + 32 });
        false -> put(state, S1)
    end.

write_tuple(Ws) ->
    Ptr = msize(),
    write_words(Ptr, Ws),
    Ptr.

write_words(_, []) -> ok;
write_words(Addr, [W | Ws]) ->
    mstore(Addr, W),
    write_words(Addr + 32, Ws).

%% -- Interpreter --
run(Builtin, Args, ResType) ->
    {_, _, Vars, Body, _} = aeso_builtins:builtin_function(Builtin),
    run(Vars, Body, Args, ResType).

run(Vars, Body, Args, ResType) ->
    new_state(),
    Env = maps:from_list(lists:zip([X || {X, _} <- Vars], [ to_aevm(Arg) || Arg <- Args ])),
    Res = interp(Env, Body),
    %% io:format("Result: ~p\nType: ~p\n", [Res, ResType]),
    from_aevm(Res, ResType).

to_aevm({bytes, Bin}) ->
    case to_words(Bin) of
        []  -> 0;
        [W] -> W;
        Ws  -> write_tuple(Ws)
    end;
to_aevm(String) when is_list(String) ->
    Ws = to_words(list_to_binary(String)),
    write_tuple([length(String) | Ws]).

from_aevm({ptr, Ptr}, T) -> from_aevm(mload(Ptr), T);
from_aevm(X, word) when is_integer(X) -> X;
from_aevm(W, {bytes, N}) when N =< 32, is_integer(W) ->
    <<Res:N/binary, _/binary>> = <<W:256>>,
    {bytes, Res};
from_aevm(Ptr, {bytes, N}) when N > 32 ->
    {bytes, get_bin(Ptr, N)};
from_aevm(_Ptr, {tuple, []}) ->
    {tuple, []};
from_aevm(Ptr, {tuple, [T | Ts]}) ->
    V = from_aevm({ptr, Ptr}, T),
    {tuple, Vs} = from_aevm(Ptr + 32, {tuple, Ts}),
    {tuple, [V | Vs]};
from_aevm(Ptr, string) when is_integer(Ptr) ->
    Len = mload(Ptr),
    binary_to_list(get_bin(Ptr + 32, Len)).

get_bin(Ptr, Len) ->
    Words = (Len + 31) div 32,
    from_words(Len, [ mload(Ptr + Off * 32) || Off <- lists:seq(0, Words - 1) ]).

interp(Env, {tuple, Es})       -> write_tuple([ interp(Env, E) || E <- Es ]);
interp(Env, {var_ref, X})      -> maps:get(X, Env);
interp(_Env, {integer, N})     -> N;
interp(Env, {binop, Op, A, B}) ->
    U = interp(Env, A),
    V = interp(Env, B),
    try op(Op, U, V)
    catch _:_ -> error({binop, Op, U, V})
    end;
interp(Env, {funcall, {var_ref, {builtin, BuiltinFun}}, Args0}) ->
    Args = [ interp(Env, A) || A <- Args0 ],
    {_, _, Vars, Body, _} = aeso_builtins:builtin_function(BuiltinFun),
    Env1 = maps:from_list(lists:zip([X || {X, _} <- Vars], Args)),
    Env2 = maps:merge(Env, Env1),
    interp(Env2, Body);
interp(Env, {ifte, E, True, False}) ->
    case interp(Env, E) of
        1 -> interp(Env, True);
        0 -> interp(Env, False)
    end;
interp(Env, {switch, Expr, Cs}) ->
    V = interp(Env, Expr),
    try switch(Env, V, Cs)
    catch throw:_ -> error({switch, Env, V, Cs})
    end;
interp(Env, {seq, Exprs}) ->
    seq(Env, Exprs);
interp(_Env, {inline_asm, ['MSIZE']}) ->
    msize();
interp(_Env, {inline_asm, []}) ->
    ok.

seq(Env, [E, {inline_asm, ['MSIZE', 'MSTORE' | _]} | Es]) ->
    V = interp(Env, E),
    mstore(msize(), V),
    seq(Env, Es);
seq(Env, [E, {inline_asm, ['POP']} | Es]) ->
    interp(Env, E),
    seq(Env, Es);
seq(Env, [E]) ->
    interp(Env, E);
seq(Env, [E | Es]) ->
    interp(Env, E),
    seq(Env, Es);
seq(_Env, []) ->
    ok.

switch(Env, V, [C | Cs]) ->
    case match(Env, V, C) of
        {Env1, Expr} -> interp(Env1, Expr);
        false        -> switch(Env, V, Cs)
    end;
switch(_Env, _V, []) ->
    throw(switch).

%% TODO: This is not general :-)
match(Env, V, {{var_ref, Var}, Expr}) ->
    {Env#{Var => V}, Expr};
match(Env, V, {{tuple, [{var_ref, Var}]}, Expr}) ->
    try mload(V) of
        V1 -> {Env#{Var => V1}, Expr}
    catch
        _:_ -> throw(match)
    end;
match(Env, V, {{tuple, [{var_ref, Var1}, {var_ref, Var2}]}, Expr}) ->
    try {mload(V), mload(V+32)} of
        {V1, V2} -> {Env#{Var1 => V1, Var2 => V2}, Expr}
    catch
        _:_ -> throw(match)
    end;
match(_Env, _V, _C) -> false.


op('+', A, B) -> ?TRUNC(A + B);
op('-', A, B) -> ?TRUNC(A - B);
op('*', A, B) -> ?TRUNC(A * B);
op('>', A, B) -> if A > B -> 1; true -> 0 end;
op('<', A, B) -> if A < B -> 1; true -> 0 end;
op('==', A, B) -> if A == B -> 1; true -> 0 end;
op('&&', A, B) -> if A > 0 andalso B > 0 -> 1; true -> 0 end;
op('||', A, B) -> if A == 0 andalso B == 0 -> 0; true -> 1 end;
op('byte', A, B) -> (B bsr (248-(A*8))) band 16#FF;
op('bsr', A, B) -> B bsr A;
op('bsl', A, B) -> ?TRUNC(B bsl A);
op('mod', A, B) -> A rem B;
op('!', A, B) ->
    case A rem 32 of
        0 -> mload(B + A);
        X ->
            W1 = mload(B + A - X),
            W2 = try mload(B + A + 32 - X) catch _:_ -> 0 end,
            <<_:X/binary, W:256, _/binary>> = <<W1:256, W2:256>>,
            W
    end.

%% -- Helper functions --
to_words(Bin) ->
    N      = byte_size(Bin),
    PadN   = (N + 31) div 32 * 32,
    Padded = <<Bin/binary, 0:(PadN - N)/unit:8>>,
    [ W || <<W:32/unit:8>> <= Padded ].

from_words(Len, Ws) ->
     binary:part(<< <<W:32/unit:8>> || W <- Ws >>, 0, Len).


%% -- Bytes.concat --

prop_concat() ->
    ?FORALL({A, B}, {choose(0, 127), choose(0, 127)},
    begin
        BinA = list_to_binary(lists:seq(1, A)),
        BinB = list_to_binary(lists:seq(A + 1, A + B)),
        ?WHENFAIL(io:format("~p\nFinal state: ~p\n",
                            [aeso_builtins:builtin_function({bytes_concat, A, B}), get(state)]),
        equals(run({bytes_concat, A, B}, [{bytes, BinA}, {bytes, BinB}], {bytes, A + B}),
               {bytes, <<BinA/binary, BinB/binary>>}))
    end).

%% -- Bytes.split --

prop_split() ->
    ?FORALL({A, B}, {choose(0, 127), choose(0, 127)},
    begin
        BinA = list_to_binary(lists:seq(1, A)),
        BinB = list_to_binary(lists:seq(A + 1, A + B)),
        ?WHENFAIL(io:format("~p\nFinal state: ~p\n",
                            [aeso_builtins:builtin_function({bytes_split, A, B}), get(state)]),
        equals(run({bytes_split, A, B}, [{bytes, <<BinA/binary, BinB/binary>>}],
                   {tuple, [{bytes, A}, {bytes, B}]}),
               {tuple, [{bytes, BinA}, {bytes, BinB}]}))
    end).

%% -- Bytes.to_str --
prop_bytes_to_str() ->
    ?FORALL(A, choose(0, 255),
    begin
        Bin = list_to_binary(lists:seq(1, A)),
        ?WHENFAIL(io:format("~p\n", [aeso_builtins:builtin_function({bytes_to_str, A})]),
        equals(run({bytes_to_str, A}, [{bytes, Bin}], string),
               aeu_hex:bin_to_hex(Bin)))
    end).

%% -- String.concat --
prop_str_concat() ->
    ?FORALL({A, B}, {choose(0, 127), choose(0, 127)},
    begin
        StrA = lists:seq(1, A),
        StrB = lists:seq(A + 1, A + B),
        ?WHENFAIL(io:format("~p\nFinal state: ~p\n",
                            [aeso_builtins:builtin_function(string_concat), get(state)]),
        equals(run(string_concat, [StrA, StrB], string), StrA ++ StrB))
    end).


prop_split_concat() ->
    ?FORALL(A, choose(0, 255),
    ?FORALL(B, choose(0, A),
    begin
        Bin = list_to_binary(lists:seq(1, A)),
        {Vars, Body, _} = split_concat(A, B),
        ?WHENFAIL(io:format("End state:\n~p\n", [get(state)]),
        equals(run(Vars, Body, [{bytes, Bin}], string),
               aeu_hex:bin_to_hex(Bin)))
    end)).

prop_eq_split_concat() ->
    ?FORALL(A, choose(0, 255),
    ?FORALL({B, C}, {choose(0, A), choose(0, A)},
    begin
        Bin = list_to_binary(lists:seq(1, A)),
        {Vars, Body, _} = eq_split_concat(A, B, C),
        ?WHENFAIL(io:format("End state:\n~p\n", [get(state)]),
        equals(run(Vars, Body, [{bytes, Bin}], word),
               1))
    end)).


%% -- Handcrafted "builtin" functions --

-define(call(Fun, Args), {funcall, {var_ref, {builtin, Fun}}, Args}).
-define(V(X), v(X)).
-define(LET_(V, E, B), {switch, E, [{v(V), B}]}).
-define(SPLIT(A, B, W, B1, B2, Body),
        {switch, ?call({bytes_split, A, B}, [?V(W)]),
           [{{tuple, [?V(B1), ?V(B2)]}, Body}]}).
-define(CONCAT_BYTES(A, B1, B, B2),
         ?call(string_concat, [?call({bytes_to_str, A}, [?V(B1)]),
                               ?call({bytes_to_str, B}, [?V(B2)])])).
v(X) when is_atom(X) -> v(atom_to_list(X));
v(X) when is_list(X) -> {var_ref, X}.

split_concat(N, X) ->
    Type = if N > 32 -> pointer; true -> word end,
    {[{"w", Type}],
     ?SPLIT(N - X, X, w, b1, b2, ?CONCAT_BYTES(N - X, b1, X, b2)),
     string}.


eq_split_concat(N, X, Y) ->
    Type = if N > 32 -> pointer; true -> word end,
    {[{"w", Type}],
     ?SPLIT(N - X, X, w, b1, b2,
     ?SPLIT(N - Y, Y, w, b3, b4,
     ?LET_(s1, ?CONCAT_BYTES(N - X, b1, X, b2),
     ?LET_(s2, ?CONCAT_BYTES(N - Y, b3, Y, b4),
        ?call(str_equal, [?V(s1), ?V(s2)])
         )))),
     word}.
