-module(aec_pow_eqc).

-compile([export_all, no_warn_export_all]).

-include_lib("eqc/include/eqc.hrl").

-define(HIGHEST_TARGET_SCI, 16#2100ffff).
-define(HIGHEST_TARGET_INT, 16#ffff000000000000000000000000000000000000000000000000000000000000).

%% These are the targets that we consider valid. In general the scientific representation
%% should allow any bit pattern?!
gen_sci() ->
  frequency([{32,  ?LET({X, Y}, {choose(3, 16#20), choose(16#008000, 16#7fffff)}, (X bsl 24) + Y)},
             {1, ?LET(X, choose(16#8000,16#FFFF), (16#21 bsl 24) + X)}]).

prop_roundtrip_basic() ->
  ?FORALL(X, choose(1, ?HIGHEST_TARGET_INT),
  ?TIMEOUT(100,
  begin
    Sci = aec_pow:integer_to_scientific(X),
    equals(Sci, aec_pow:integer_to_scientific(aec_pow:scientific_to_integer(Sci)))
  end)).

prop_roundtrip() ->
  ?FORALL(Sci, gen_sci(),
  ?TIMEOUT(100,
    equals(Sci, aec_pow:integer_to_scientific(aec_pow:scientific_to_integer(Sci)))
  )).

%% Check that we can spot the difference between two different compactly represented
%% integers.
prop_precision() ->
  ?FORALL(Sc1, gen_sci(),
  begin
    Int = aec_pow:scientific_to_integer(Sc1),
    Sc2 = aec_pow:integer_to_scientific(Int - 1),
    D1 = aec_pow:target_to_difficulty(Sc1),
    D2 = aec_pow:target_to_difficulty(Sc2),
    ?WHENFAIL(
      io:format("Sc1: ~.16b\nSc2: ~.16b\nD1 : ~p\nD2 : ~p\n",
                [Sc1, Sc2, D1, D2]),
      equals(D1 < D2, true)
    )
  end).

prop_test_target() ->
  ?FORALL(Sci, gen_sci(),
  begin
    Int = aec_pow:scientific_to_integer(Sci),
    BSol1 = int_to_bin(Int + 1, 32),
    BSol2 = int_to_bin(Int - 1, 32),
    ?WHENFAIL(io:format("Sci: ~.16b\nI+1: ~.16b\nI-1: ~.16b\nB1: ~p\nB2: ~p\n", [Sci, Int+1, Int-1, BSol1, BSol2]),
    equals({true, false}, {aec_pow:test_target(BSol2, Sci), aec_pow:test_target(BSol1, Sci)}))
  end).

int_to_bin(X, Bytes) -> <<X:Bytes/big-unsigned-integer-unit:8>>.

