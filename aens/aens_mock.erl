%%% File        : aens_mock.erl
%%% Author      : Hans Svensson
-module(aens_mock).

-compile(export_all).
-compile(nowarn_export_all).

%% aec_tx_sign
data(S) -> S.
verify(_) -> ok.
serialize_to_binary(X) -> term_to_binary(X).

%% aec_target
verify(_, _) -> ok.

%% aec_governance
name_preclaim_expiration() ->
    5.

name_claim_burned_fee() ->
    3.

name_transfer_burned_fee() ->
    2.

name_update_burned_fee() ->
    1.

name_claim_max_expiration() ->
    10.

name_protection_period() ->
    5.

minimum_tx_fee() ->
    1.

blocks_to_check_difficulty_count() ->
    10.

block_mine_reward() -> 1.

name_claim_preclaim_delta() -> 1.
