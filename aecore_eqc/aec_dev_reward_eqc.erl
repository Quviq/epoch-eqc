-module(aec_dev_reward_eqc).

-include_lib("eqc/include/eqc.hrl").

-compile([export_all, nowarn_export_all]).

prop_split() ->
    in_parallel(
    ?FORALL(PubKeys, non_empty(list(gen_beneficiary_pubkey())),
    ?FORALL(
       {BeneficiaryReward1,
        BeneficiaryReward2,
        Beneficiaries,
        UnallocatedShares},
       {gen_beneficiary_reward(),
        gen_beneficiary_reward(),
        gen_beneficiaries(PubKeys),
        gen_unallocated_shares()},
       begin
           AllocatedShares = allocated_shares(Beneficiaries),
           BeneficiaryKeys = lists:map(fun beneficiary_pubkey/1, Beneficiaries),
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
           measure(nr_beneficiaries, length(Beneficiaries),
           measure(dup_beneficiaries, length(BeneficiaryKeys) - length(lists:usort(BeneficiaryKeys)),
           ?WHENFAIL(eqc:format("split: ~p with adjusted rewards ~p + ~p\n",
                                [DevRewards, AdjustedReward1, AdjustedReward2]),
           conjunction([{reward, is_reward(AdjustedReward1)
                         andalso is_reward(AdjustedReward2)},
                        {adjusted,
                         (AdjustedReward1 =< BeneficiaryReward1)
                         andalso (AdjustedReward2 =< BeneficiaryReward2)},
                        {all_beneficiaries_rewarded,
                         lists:sort(
                           lists:map(fun({K, _}) -> K end, DevRewards))
                         =:=
                             lists:sort(BeneficiaryKeys)},
                        {all_rewards_valid,
                         [] =:= lists:filter(
                                  fun({_, R}) -> not is_reward(R) end,
                                  DevRewards)},
                        %% {got_rewarded, equals(Beneficiaries, DevRewards)},
                        {paid_out,
                         %% some have to be paid
                         (BeneficiaryReward1 + BeneficiaryReward2 =< TotalShares) orelse
                         lists:sum(lists:map(fun({_, R}) -> R end, DevRewards)) > 0
                         },
                        {total, (AdjustedReward1
                                 + AdjustedReward2
                                 + lists:sum(
                                     lists:map(fun({_, R}) -> R end, DevRewards)))
                         =:=
                             (BeneficiaryReward1
                              + BeneficiaryReward2)}]))))
       end))).

gen_beneficiary_reward() ->
    choose(0, 10000).
    %% choose(0, 123456789 * 1000000000000000000).

gen_beneficiaries(PubKeys) ->
    %% Make duplicates likely
    ?LET(Keys, non_empty(sublist(PubKeys ++ PubKeys)),
         [ {PubKey, gen_beneficiary_share()} || PubKey <- Keys ]).

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
