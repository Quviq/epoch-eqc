%%% @author Thomas Arts 
%%% @copyright (C) 2018, Thomas Arts
%%% @doc Use `rebar3 shell --apps ""` to get started
%%%
%%% @end
%%% Created : 13 Dec 2018 by Thomas Arts <thomas@SpaceGrey.lan>

-module(aefate_eqc).

-include_lib("eqc/include/eqc.hrl").

-compile([export_all, nowarn_export_all]).

prop_roundtrip() ->
    ?FORALL(FateData, fate_type(),
            measure(bytes, size(term_to_binary(FateData)),
                    begin
                        Serialized = aefa_encoding:serialize(FateData),
                        ?WHENFAIL(eqc:format("Serialized ~p to ~p~n", [FateData, Serialized]),
                                  equals(aefa_encoding:deserialize(Serialized), FateData))
                    end
                   )).

prop_format() ->
    ?FORALL(FateData, fate_type(),
            ?WHENFAIL(eqc:format("Trying to format ~p failed~n",[FateData]),
                      begin
                          String = aefa_data:format(FateData),
                          collect([FateData, unicode:characters_to_binary(String, latin1)], true)
                      end)).

fate_type() ->
    ?SIZED(Size, fate_type(Size, [map])).

fate_type(0, Options) ->
    ?LAZY(
       oneof([fate_integer(), 
              fate_boolean(), 
              fate_nil(), 
              fate_unit(),
              fate_string(),
              fate_address() ] ++ [ fate_void() || lists:member(void, Options)]));
fate_type(Size, Options) ->
    ?LETSHRINK([Smaller], [?LAZY(fate_type(Size div 5, Options))],
    oneof([?LAZY(fate_type(Size - 1, Options)),
           ?LAZY(fate_list( Smaller )),
           ?LAZY(fate_tuple( list( Smaller ))),
           ?LAZY(fate_variant( choose(0,255), fate_tuple(list( Smaller))))
          ] ++ 
              [
               ?LAZY(fate_map( fate_type(Size div 3, Options -- [map, void]),
                               Smaller))
              || lists:member(map, Options)
              ])).
            

fate_integer() -> oneof([int(), largeint()]).
fate_boolean() -> elements([true, false]).
fate_nil() -> [].
fate_unit() -> {tuple, {}}.
fate_string() -> oneof([utf8(), binary()]).
fate_address() -> {address, binary(256 div 8)}.
fate_void() -> void.

%% May shrink to fate_unit
fate_tuple(ListGen) ->
    {tuple, ?LET(Elements, ListGen, list_to_tuple(Elements))}.

fate_variant(IntGen, TupleGen) ->
    {variant, IntGen, TupleGen}.
  
fate_list(Gen) ->
    oneof([fate_nil(), ?SHRINK(list(Gen), [fate_nil()])]).

fate_map(KeyGen, ValGen) ->    
    map(KeyGen, ValGen).
