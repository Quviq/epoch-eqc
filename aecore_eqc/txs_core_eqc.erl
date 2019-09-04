%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Thomas Arts
%%% @doc Refactoredf txs_eqc now use wrap_call
%%%
%%%       TODO:
%%%          - better shrinking for channel Ids (they contain the nonce...) - use good/bad tagging?
%%%          - add oracle names to the state such that we can use names with oracles
%%%          - add names to oracle txs
%%%          - tune distribution (all EXIT differences should show up in features)
%%% @end
%%% Created : 23 Jan 2019 by Thomas Arts

-module(txs_core_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).
-define(PatronAmount, 1000000000000000000000001).  %% read from file

-record(account,  {key, amount, nonce}).

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{keys => #{}, fees => []}.

patron() ->
    #{ public := Pubkey, secret := Privkey } =
                     #{public =>
                           <<227,81,22,143,182,219,118,194,214,164,169,153,6,190,90,
                             72,72,11,74,195,160,239,10,12,98,144,86,254,51,110,216,
                             22>>,
                       secret =>
                           <<156,127,9,241,107,48,249,188,92,91,80,218,172,41,140,
                             147,102,228,17,21,148,192,27,47,228,212,93,153,220,174,
                             52,19,227,81,22,143,182,219,118,194,214,164,169,153,6,
                             190,90,72,72,11,74,195,160,239,10,12,98,144,86,254,51,
                             110,216,22>>},
    {Pubkey, Privkey, ?PatronAmount}.


%% -- Operations -------------------------------------------------------------

%% This should be generated automatically!
%% and in fact is not necessary here at all if we just remove _call from mine.

wrap_call(S, {call, ?MODULE, mine, Args}) ->
    try {ok, mine_call(S, Args)}
    catch _:Reason ->
        {error, {'EXIT', Reason}, []}
    end;
wrap_call(_S, {call, Mod, Cmd, Args}) ->
    try {ok, apply(Mod, Cmd, Args)}
    catch _:Reason ->
        {error, {'EXIT', Reason}, []}
    end.


%% --- Operation: init ---
init_pre(S) ->
    not maps:is_key(accounts, S).

init_args(_S) ->
    [].

init() ->
    put(trees, initial_trees()),
    ok.

initial_trees() ->
    {PA, _Secret, PAmount} = patron(),
    trees_with_accounts([{account, PA, PAmount}]).

init_next(S, _Value, []) ->
    {PA, Secret, PAmount} = patron(),
    S#{height   => 0,
       accounts => [#account{key = PA, amount = PAmount, nonce = 1}],
       keys => maps:put(PA, Secret, maps:get(keys, S))}.

%% --- Operation: newkey ---
newkey_args(_S) ->
    #{ public := Pubkey, secret := Privkey } = enacl:sign_keypair(),
    [Pubkey, Privkey].

newkey(PubKey, _) ->
    PubKey.

newkey_next(S, Value, [_Pubkey, Privkey]) ->
    #{keys := Keys} = S,
    S#{keys => Keys#{Value => Privkey}}.



%% In this model we do not pay beneficiaries (that's on a higher level)
%% Thus no update needed when we reach aec_governance:beneficiary_reward_delay()
%% --- Operation: mine ---
mine_pre(S) ->
    maps:is_key(accounts, S).

mine_args(_) ->
    [?LET(Blocks, frequency([{10, 1}, {1, 10}, {1, 100}, {1, 1000}, {1, 10000}, {1, 25000}]),
          ?SHRINK(Blocks, [choose(1, Blocks) || Blocks =/= 1]))].

mine_call(#{height := Height}, [Blocks]) ->
    Trees  = get(trees),
    Trees1 = lists:foldl(
        fun(H, T) -> aec_trees:perform_pre_transformations(T, H + 1) end,
        Trees, lists:seq(Height, Height + Blocks - 1)),
    put(trees, Trees1),
    ok.

mine_next(#{height := Height} = S, _Value, [Blocks]) ->
    S#{height   => Height + Blocks}.

mine_features(_S, [_B], _Res) ->
    [mining].


%% --- Operation: balance ---
balance_pre(S) ->
    maps:is_key(accounts, S).

balance_args(_S) ->
    [].

balance() ->
    TreesTotal =
        case get(trees) of
            undefined -> #{};
            Trees -> aec_trees:sum_total_coin(Trees)
        end,
    lists:sum(maps:values(TreesTotal)).

balance_post(S, [], Res) ->
    FeeTotal = lists:sum([ Fee || {Fee, _} <- maps:get(fees, S, [])]),
    eq(Res, ?PatronAmount - FeeTotal).


%% ------------- helper functions ---------------------

trees_with_accounts(Accounts) ->
    trees_with_accounts(Accounts, aec_trees:new_without_backend()).

trees_with_accounts([], Trees) ->
    Trees;
trees_with_accounts([{account, Acc, Amount}|Rest], Trees) ->
    Account = aec_accounts:new(Acc, Amount),
    AccountTrees = aec_accounts_trees:enter(Account, aec_trees:accounts(Trees)),
    trees_with_accounts(Rest, aec_trees:set_accounts(Trees, AccountTrees)).
