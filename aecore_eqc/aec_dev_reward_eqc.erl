-module(aec_dev_reward_eqc).

-include_lib("eqc/include/eqc.hrl").

-compile([export_all, nowarn_export_all]).

prop_split() ->
    ?FORALL(
       {BeneficiaryReward1,
        BeneficiaryReward2,
        Beneficiaries,
        UnallocatedShares},
       {gen_beneficiary_reward(),
        gen_beneficiary_reward(),
        gen_beneficiaries(),
        gen_unallocated_shares()},
       begin
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
           conjunction([{reward, is_reward(AdjustedReward1)
                         andalso is_reward(AdjustedReward2)},
                        {adjusted,
                         (AdjustedReward1 =< BeneficiaryReward1)
                         andalso (AdjustedReward2 =< BeneficiaryReward2)},
                        {all_beneficiaries_rewarded,
                         length(DevRewards) =:= length(Beneficiaries)},
                        {keys_correct,
                         lists:sort(
                           lists:map(fun({K, _}) -> K end, DevRewards))
                         =:=
                             lists:sort(
                               lists:map(fun beneficiary_pubkey/1, Beneficiaries))},
                        {all_rewards_valid,
                         [] =:= lists:filter(
                                  fun({_, R}) -> not is_reward(R) end,
                                  DevRewards)},
                        {total, (AdjustedReward1
                                 + AdjustedReward2
                                 + lists:sum(
                                     lists:map(fun({_, R}) -> R end, DevRewards)))
                         =:=
                             (BeneficiaryReward1
                              + BeneficiaryReward2)}])
       end)).

gen_beneficiary_reward() ->
    choose(0, 123456789 * 1000000000000000000).

gen_beneficiaries() ->
    ?LET(Beneficiaries, non_empty(list({gen_beneficiary_pubkey(), gen_beneficiary_share()})),
         lists:sort(Beneficiaries)).

gen_beneficiary_pubkey() ->
    noshrink(binary(32)).

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
