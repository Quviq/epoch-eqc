%%% File        : der_enc_eqc.erl
%%% Author      : Hans Svensson
%%% Description :
%%% Created     : 19 Jan 2018 by Hans Svensson
-module(der_enc_eqc).

-compile(export_all).

-include_lib("eqc/include/eqc.hrl").

-define(VALUE, <<1256285908694890:256>>).

prop_roundtrip1() ->
    ?FORALL({_Pub, Priv}, return(crypto:generate_key(ecdh, secp256k1)),
    begin
        DerSig = crypto:sign(ecdsa, sha256, {digest, aec_hash:hash(tx, ?VALUE)}, [Priv, secp256k1]),

        SophiaSig = der_sig_decode(DerSig),

        DerSig2 = der_sig_encode(SophiaSig),

        ?WHENFAIL(io:format("~p\n-> ~p\n  -> ~p\n", [DerSig, SophiaSig, DerSig2]),
                  DerSig == DerSig2)
    end).

prop_roundtrip2() ->
    ?FORALL({B1, B2}, {der_bin(32), der_bin(32)},
    begin
        SophiaSig = {B1, B2},
        DerSig = der_sig_encode(SophiaSig),
        SophiaSig2 = der_sig_decode(DerSig),

        ?WHENFAIL(io:format("~p\n-> ~p\n  -> ~p\n", [SophiaSig, DerSig, SophiaSig2]),
                  SophiaSig == SophiaSig2)
    end).

der_bin(Len) ->
    weighted_default(
      {9, binary(Len)},
      {1, ?LET(X, choose(1, 30), ?LET(Bx, binary(Len-X), return(<<0:(X*8), Bx/binary>>)))}).

der_sig_decode(<<16#30, _Len0:8, 16#02, Len1:8, Rest/binary>>) ->
    <<R:Len1/binary, 16#02, Len2:8, S/binary>> = Rest,
    {der_part_trunc(Len1, R), der_part_trunc(Len2, S)}.

der_part_trunc(33, <<0, Rest/binary>>)   -> Rest;
der_part_trunc(Len, Part) when Len =< 32 -> <<0:((32-Len)*8), Part/binary>>.

der_sig_encode({R0, S0}) ->
    {R1, S1} = {der_sig_part(R0), der_sig_part(S0)},
    {LR, LS} = {byte_size(R1), byte_size(S1)},
    <<16#30, (4 + LR + LS), 16#02, LR, R1/binary, 16#02, LS, S1/binary>>.

der_sig_part(P = <<1:1, _/bitstring>>) -> <<0:8, P/binary>>;
der_sig_part(<<0, Rest/binary>>)       -> der_sig_part(Rest);
der_sig_part(P)                        -> P.

