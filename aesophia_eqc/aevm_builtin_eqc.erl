%%% File        : aevm_builtin_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 9 Sep 2019 by Ulf Norell
-module(aevm_builtin_eqc).

-include_lib("eqc/include/eqc.hrl").

-compile([export_all, nowarn_export_all]).

run(Builtin, Args, ResType) ->
    {_, _, Vars, Body, _} = aeso_builtins:builtin_function(Builtin),
    Env = maps:from_list(lists:zip([X || {X, _} <- Vars], [ to_aevm(Arg) || Arg <- Args ])),
    from_aevm(interp(Env, Body), ResType).

to_aevm(Bin) when is_binary(Bin) ->
    case to_words(Bin) of
        []  -> 0;
        [W] -> W;
        Ws  -> list_to_tuple(Ws)
    end.

from_aevm(W, {bytes, N}) when N =< 32, is_integer(W) ->
    <<Res:N/binary, _/binary>> = <<W:256>>,
    Res;
from_aevm(E, {bytes, N}) when N > 32, is_tuple(E) ->
    <<Res:N/binary, _/binary>> = << <<W:256>> || W <- tuple_to_list(E) >>,
    Res;
from_aevm(E, {tuple, Ts}) when is_tuple(E), tuple_size(E) == length(Ts) ->
    list_to_tuple([ from_aevm(X, T) || {X, T} <- lists:zip(tuple_to_list(E), Ts) ]);
from_aevm(X, _) -> X.

to_words(Bin) ->
    N      = byte_size(Bin),
    PadN   = (N + 31) div 32 * 32,
    Padded = <<Bin/binary, 0:(PadN - N)/unit:8>>,
    [ W || <<W:32/unit:8>> <= Padded ].

interp(Env, {tuple, Es})       -> list_to_tuple([ interp(Env, E) || E <- Es ]);
interp(Env, {var_ref, X})      -> maps:get(X, Env);
interp(Env, {binop, Op, A, B}) ->
    U = interp(Env, A),
    V = interp(Env, B),
    try op(Op, U, V)
    catch _:_ -> error({binop, Op, U, V})
    end;
interp(_Env, {integer, N})     -> N.

-define(TRUNC(X), (X rem (1 bsl 256))).

op('+', A, B) -> ?TRUNC(A + B);
op('-', A, B) -> ?TRUNC(A - B);
op('*', A, B) -> ?TRUNC(A * B);
op('bsr', A, B) -> B bsr A;
op('bsl', A, B) -> ?TRUNC(B bsl A);
op('mod', A, B) -> A rem B;
op('!', A, T) when is_tuple(T) ->
    <<_:A/binary, Rest/binary>> = << <<W:256>> || W <- tuple_to_list(T) >>,
    case byte_size(Rest) of
        N when N >= 32 ->
            <<Res:256, _/binary>> = Rest,
            Res;
        N ->
            Pad = 32 - N,
            <<Res:256>> = <<Rest/binary, 0:Pad/unit:8>>,
            Res
    end.

%% -- Bytes.concat --

prop_concat() ->
    ?FORALL({A, B}, {choose(0, 127), choose(0, 127)},
    begin
        BinA = list_to_binary(lists:seq(1, A)),
        BinB = list_to_binary(lists:seq(A + 1, A + B)),
        ?WHENFAIL(io:format("~p\n", [aeso_builtins:builtin_function({bytes_concat, A, B})]),
        equals(run({bytes_concat, A, B}, [BinA, BinB], {bytes, A + B}),
               <<BinA/binary, BinB/binary>>))
    end).

%% -- Bytes.split --

prop_split() ->
    ?FORALL({A, B}, {choose(0, 127), choose(0, 127)},
    begin
        BinA = list_to_binary(lists:seq(1, A)),
        BinB = list_to_binary(lists:seq(A + 1, A + B)),
        ?WHENFAIL(io:format("~p\n", [aeso_builtins:builtin_function({bytes_split, A, B})]),
        equals(run({bytes_split, A, B}, [<<BinA/binary, BinB/binary>>], {tuple, [{bytes, A}, {bytes, B}]}),
               {BinA, BinB}))
    end).

