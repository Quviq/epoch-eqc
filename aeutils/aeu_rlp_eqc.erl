%%% File        : aeu_rlp_eqc.erl
%%% Author      : Hans Svensson
%%% Description :
%%% Created     : 19 Jan 2018 by Hans Svensson
-module(aeu_rlp_eqc).

-compile(export_all).

-include_lib("eqc/include/eqc.hrl").

gen_encodable() ->
    ?SIZED(Size, gen_encodable(Size)).

gen_encodable(0) ->
    binary();
gen_encodable(Size) ->
    frequency([{1, binary()},
               {1, non_empty(list(gen_encodable(Size div 3)))}]).

prop_roundtrip() ->
    ?FORALL(Encodable, gen_encodable(),
        equals(Encodable, aeu_rlp:decode(aeu_rlp:encode(Encodable)))
    ).

