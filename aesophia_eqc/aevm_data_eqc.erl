%%% File        : aevm_data_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 28 May 2018 by Ulf Norell
-module(aevm_data_eqc).

-compile([export_all, nowarn_export_all]).
-include_lib("eqc/include/eqc.hrl").

-define(SANDBOX(Code), sandbox(fun() -> Code end)).

sandbox(Code) ->
    Parent = self(),
    Tag    = make_ref(),
    {Pid, Ref} = spawn_monitor(fun() -> Parent ! {Tag, Code()} end),
    receive
        {Tag, Res} -> erlang:demonitor(Ref, [flush]), {ok, Res};
        {'DOWN', Ref, process, Pid, Reason} -> {error, Reason}
    after 100 ->
        exit(Pid, kill),
        {error, loop}
    end.


type() -> type(true).
type(Map) -> ?LET(Depth, choose(0, 2), type(Depth, true, Map)).
type(Depth, TypeRep) -> type(Depth, TypeRep, true).
type(Depth, TypeRep, Map) ->
    oneof(
    [ elements([word, string] ++ [typerep || TypeRep]) ] ++
    [ ?LETSHRINK([T], [type(Depth - 1, TypeRep, Map)], {list, T})       || Depth > 0 ] ++
    [ ?LETSHRINK([T], [type(Depth - 1, TypeRep, Map)], {option, T})     || Depth > 0 ] ++
    [ ?LETSHRINK(Ts,  list(type(Depth - 1, TypeRep, Map)), {tuple, Ts}) || Depth > 0 ] ++
    [ ?LETSHRINK([K, V], vector(2, type(Depth - 1, TypeRep, Map)), {map, K, V}) || Map, Depth > 0 ] ++
    []
    ).

blob() ->
    ?LET(Blobs, list(oneof([ ?LET(Ws, words(), return(from_words(Ws)))
                           , binary() ])),
    return(list_to_binary(Blobs))).

words() -> list(word()).
word() ->
    frequency(
    [ {4, ?LET(N, nat(), 32 * N)}
    , {1, choose(0, 320)}
    , {2, -1}
    , {2, elements(["foo", "zzzzz"])} ]).

from_words(Ws) ->
    << <<(from_word(W))/binary>> || W <- Ws >>.

from_word(W) when is_integer(W) ->
    <<W:256>>;
from_word(S) when is_list(S) ->
    Len = length(S),
    Bin = <<(list_to_binary(S))/binary, 0:(32 - Len)/unit:8>>,
    <<Len:256, Bin/binary>>.

typerep() -> ?LET(Depth, choose(0, 2),
             ?LET(T, type(Depth, true), return(typerep(T)))).

typerep(word)          -> word;
typerep(string)        -> string;
typerep(typerep)       -> typerep;
typerep({tuple, Ts})   -> {tuple, typerep(Ts)};
typerep({list, T})     -> {list, typerep(T)};
typerep({variant, Cs}) -> {variant, typerep(Cs)};
typerep({option, T})   -> {variant, [[], [typerep(T)]]};
typerep({map, K, V})   -> {map, typerep(K), typerep(V)};
typerep([])            -> [];
typerep([T | Ts])      -> [typerep(T) | typerep(Ts)].

value(word) ->
    <<N:256>> = <<(-1):256>>,
    choose(0, N);
value(string) ->
    ?LET(N, choose(0, 128), binary(N));
value(typerep) ->
    typerep();
value({list, T}) ->
    list(value(T));
value({option, T}) ->
    weighted_default({1, none}, {3, {some, value(T)}});
value({tuple, Ts}) ->
    ?LET(Vs, [ value(T) || T <- Ts ], list_to_tuple(Vs));
value({map, K, V}) ->
    map(value(K), value(V));
value({variant, Cs}) ->
    ?LET(I, choose(0, length(Cs) - 1),
    {variant, I, [ value(T) || T <- lists:nth(I + 1, Cs) ]}).

typed_val() ->
    ?LET(T, type(), ?LET(V, value(T), return({T, V}))).


prop_binary_to_heap() ->
    ?FORALL(Type, type(),
    ?FORALL(Value, value(Type),
    ?FORALL(Offs, choose(0, 16),
    begin
      BaseAddr = Offs * 32,
      Binary = aeb_heap:to_binary(Value),
      Typerep = typerep(Type),
      case aevm_data:binary_to_heap(Typerep, Binary, 0, BaseAddr) of
        {ok, HeapValue} ->
          Ptr  = aeb_heap:heap_value_pointer(HeapValue),
          Heap = aeb_heap:heap_value_heap(HeapValue),
          FromHeap = aeb_heap:from_heap(Type, <<0:BaseAddr/unit:8, Heap/binary>>, Ptr),
          Binary1  = aevm_data:heap_to_binary(Typerep, aect_contracts_store:new(), HeapValue),
          ?WHENFAIL(io:format("Ptr = ~p\nHeap = ~p\n", [Ptr, aevm_test_utils:dump_words(Heap)]),
          conjunction(
            [ {from_heap, equals(FromHeap, {ok, Value})} || not aevm_data:has_maps(Typerep)] ++
            [ {heap_to_binary, equals(Binary1, {ok, Binary}) }]));
        Err = {error, _} -> equals(Err, ok)
      end
    end))).

prop_heap_to_binary() ->
    ?FORALL(Type,  type(false),
    ?FORALL(Value, value(Type),
    ?FORALL(Offs,  choose(0, 16),
    begin
      BaseAddr = Offs * 32,
      Typerep  = typerep(Type),
      <<Ptr:256, _/binary>> = Heap = aeb_heap:to_binary(Value, BaseAddr),
      HeapValue = aeb_heap:heap_value({maps, #{}, 0}, Ptr, Heap, BaseAddr),
      ?WHENFAIL(io:format("Heap = ~p\n", [aevm_test_utils:dump_words(Heap)]),
      case aevm_data:heap_to_binary(Typerep, aect_contracts_store:new(), HeapValue) of
        {ok, Binary} ->
          ?WHENFAIL(io:format("Binary = ~p\n", [aevm_test_utils:dump_words(Binary)]),
          equals(aeb_heap:from_binary(Type, Binary),
                 {ok, Value}));
        Err = {error, _} -> equals(Err, ok)
      end)
    end))).

