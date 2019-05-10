-module(aec_dev_reward_eqc).

-include_lib("eqc/include/eqc.hrl").

-compile([export_all, nowarn_export_all]).

prop_split() ->
    ?FORALL(
       {BeneficiaryReward1,
        BeneficiaryReward2,
        BeneficiariesMap,
        UnallocatedShares},
       {gen_beneficiary_reward(),
        gen_beneficiary_reward(),
        gen_beneficiaries_map(),
        gen_unallocated_shares()},
       begin
           Beneficiaries = lists:sort(maps:to_list(BeneficiariesMap)),
           AllocatedShares = allocated_shares(Beneficiaries),
           TotalShares = AllocatedShares + UnallocatedShares,
           {{AdjustedReward1,
             AdjustedReward2},
            DevRewards} =
               aec_dev_reward:split_int(
                 BeneficiaryReward1,
                 BeneficiaryReward2,
                 AllocatedShares,
                 TotalShares,
                 Beneficiaries),
           is_reward(AdjustedReward1)
               andalso is_reward(AdjustedReward2)
               andalso (AdjustedReward1 =< BeneficiaryReward1)
               andalso (AdjustedReward2 =< BeneficiaryReward2)
               andalso (length(DevRewards) =:= length(Beneficiaries))
               andalso (lists:sort(
                          lists:map(fun({K, _}) -> K end, DevRewards))
                        =:=
                            lists:sort(
                              lists:map(fun beneficiary_pubkey/1, Beneficiaries)))
               andalso ([] =:= lists:filter(
                                 fun({_, R}) -> not is_reward(R) end,
                                 DevRewards))
               andalso ((AdjustedReward1
                         + AdjustedReward2
                         + lists:sum(
                             lists:map(fun({_, R}) -> R end, DevRewards)))
                        =:=
                            (BeneficiaryReward1
                             + BeneficiaryReward2))
       end).

gen_beneficiary_reward() ->
    choose(0, 123456789 * 1000000000000000000).

gen_beneficiaries_map() ->
    non_empty(map(gen_beneficiary_pubkey(), gen_beneficiary_share())).

gen_beneficiary_pubkey() ->
    binary(32).

gen_beneficiary_share() ->
    choose(1, 100000).

gen_unallocated_shares() ->
    choose(0, 1000000).

allocated_shares(Beneficiaries) ->
    lists:sum(lists:map(fun beneficiary_share/1, Beneficiaries)).

beneficiary_pubkey({K, _}) when is_binary(K) ->
    K.

beneficiary_share({_, S}) when is_integer(S), S > 0 ->
    S.

is_reward(X) ->
    is_integer(X) andalso X >= 0.
