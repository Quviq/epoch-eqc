%%% Author      : Hans Svensson
%%% Description :
%%% Created     : 17 Jan 2018 by Hans Svensson
-module(aeu_mp_trees_eqc).

-compile(export_all).

-include_lib("eqc/include/eqc.hrl").

%% -- Generators -------------------------------------------------------------
gen_data() ->
    ?LET(Keys, list(gen_key()),
         ?LET(Vals, vector(length(Keys), gen_value()),
              #{ keys => Keys, data => lists:zip(Keys, Vals) })).

gen_nibble() -> choose(16#0, 16#F).

gen_key() -> ?LET(Xs, non_empty(list(gen_nibble())),
                  return(<< <<X:4>> || X <- Xs >>)).

gen_put_key([]) -> gen_key();
gen_put_key(Existing) ->
    frequency([{1, gen_key()},
               {1, ?LET({K, N}, {elements(Existing), gen_nibble()}, return(<<K/bitstring, N:4>>))}]).

gen_delete_key([]) -> gen_key();
gen_delete_key(Existing) ->
    frequency([{1, gen_key()},
               {1 + length(Existing) div 2, elements(Existing)}]).

gen_value() -> weighted_default({5, gen_decodable()}, {1, binary(36)}).

gen_decodable() -> ?SIZED(Size, gen_decodable(Size)).

gen_decodable(0) ->
    binary(2);
gen_decodable(Size) ->
    frequency([{2, non_empty(binary())},
               {1, non_empty(list(gen_decodable(Size div 3)))}]).

gen_tree() ->
    ?LET({Keys, Ops}, gen_ops(),
         begin
            {ok, Tree} = build_tree(Ops),
            {Keys, Ops, Tree}
         end).

gen_ops() ->
    ?LET(NOps, noshrink(weighted_default({1, choose(0, 10)}, {3, choose(5, 20)})),
         ?LET(Ops, gen_ops(NOps), ?SHRINK(Ops, [eqc_gen:shrink_list(Ops)]))).

gen_ops(NOps) ->
    gen_ops(NOps, [], []).

gen_ops(0, _Keys, Ops) -> return(lists:reverse(Ops));
gen_ops(N, Keys, Ops) ->
    frequency(
        [{2, ?LET({K, V}, {gen_put_key(Keys), gen_value()}, gen_ops(N-1, lists:umerge(Keys, [K]), [{put, K, V} | Ops]))},
         {1, ?LET(K, gen_delete_key(Keys), gen_ops(N-1, Keys -- [K], [{delete, K} | Ops]))}]).

gen_scrambled_lists(N, Ls) ->
    vector(N, shuffle(Ls)).

%% -- Properties -------------------------------------------------------------
prop_all_trees_ok() ->
    ?FORALL(Ops, gen_ops(),
    begin
        Tree = build_tree(Ops),
        ?WHENFAIL(eqc:format("Tree: ~p\n", [Tree]),
            case Tree of
                {ok, _} -> true;
                _Err    -> false
            end)
    end).

prop_get() ->
    ?FORALL(Ops, gen_ops(),
    begin
        {ok, Tree} = build_tree(Ops),
        Ref        = build_ref(Ops),
        Keys       = lists:usort([ K || {K, _} <- Ref ]),
        Res        = lists:usort([ check_get(Key, Tree, Ref) || Key <- Keys ]) -- [ok],
        equals(Res, [])
    end).

prop_get_neg() ->
    ?FORALL(Ops, gen_ops(),
    begin
        Keys = ops_keys(Ops),
        ?FORALL(Key, ?SUCHTHAT(K, gen_put_key(Keys), not lists:member(K, Keys)),
        begin
            {ok, Tree} = build_tree(Ops),
            equals(tree_get(Key, Tree), <<>>)
        end)
    end).


prop_insert_delete() ->
    ?FORALL(Ops, gen_ops(),
    ?FORALL({K, V}, {gen_key(), gen_value()},
    ?IMPLIES(not lists:member(K, ops_keys(Ops)),
    begin
        {ok, Tree} = build_tree(Ops),
        Tree1      = tree_delete(K, tree_put(K, V, Tree)),
        equals(tree_hash(Tree), tree_hash(Tree1))
    end))).

prop_twice() ->
    ?FORALL(Ops, gen_ops(),
    begin
        {ok, Tree1} = build_tree(Ops),
        {ok, Tree2} = build_tree(Ops, Tree1),
        equals(tree_hash(Tree1), tree_hash(Tree2))
    end).

prop_idempotence() ->
    ?FORALL(Ops, gen_ops(),
    ?FORALL(N, choose(2, 100),
    ?FORALL(ScrambledOpss, gen_scrambled_lists(N, Ops),
    begin
        Trees = [ {Os, safe_build_tree(Os)} || Os <- ScrambledOpss ],
        Refs  = [ lists:sort(build_ref(Os)) || Os <- ScrambledOpss ],
        RTs = lists:sort([ {Ref, tree_hash(T), Os} || {Ref, {Os, T}} <- lists:zip(Refs, Trees) ]),
        GRTs = eqc_cover:group(1, RTs),
        measure(grps, length(GRTs), measure(overlap, N - length(GRTs), check_groups(GRTs)))
    end))).

check_groups([]) -> true;
check_groups([{Ref, HashOps} | GRTs]) ->
    case lists:ukeysort(1, HashOps) of
        [_] -> check_groups(GRTs);
        [{H1, Os1}, {H2, Os2} | _] ->
            ?WHENFAIL(eqc:format("~p =/= ~p\nOps1: ~p\nOps2: ~p\nGroup: ~p\n", [H1, H2, Os1, Os2, Ref]), false)
    end.

property_weight(_, prop_idempotence) -> 5;
property_weight(_, _) -> 1.

%% -- Helper functions -------------------------------------------------------
tree_put(K, V, Tree) ->
    aeu_mp_trees:put(K, V, Tree).

tree_delete(K, Tree) ->
    aeu_mp_trees:delete(K, Tree).

tree_get(K, Tree) ->
    aeu_mp_trees:get(K, Tree).

tree_hash(Tree) ->
    aeu_mp_trees:root_hash(Tree).

ops_keys(Ops) ->
    lists:usort([ K || {K, _} <- build_ref(Ops) ]).

check_get(K, Tree, Ref) ->
    case {tree_get(K, Tree), lists:keyfind(K, 1, Ref)} of
        {Bin, {_, Bin}} -> ok;
        {Res1, {_, Res2}} -> {Res1, '=/', Res2}
    end.

safe_build_tree(Ops) ->
    case build_tree(Ops) of
        {ok, Tree} -> Tree;
        Error      -> eqc:format("Build Tree failed!\nOps: ~p\n\nError: ~p\n", [Ops, Error]),
                      error({build_tree_failed, Ops})
    end.

build_tree(Ops) ->
    build_tree(Ops, aeu_mp_trees:new()).

build_tree([], Tree) -> {ok, Tree};
build_tree([Op | Ops], Tree) ->
    try
        Tree1 =
            case Op of
                {put, K, V} -> tree_put(K, V, Tree);
                {delete, K} -> tree_delete(K, Tree)
            end,
        build_tree(Ops, Tree1)
    catch E:R ->
        {error, Op, {E, R, erlang:get_stacktrace()}}
    end.

build_ref(Ops) -> build_ref(Ops, []).
build_ref([], Ref) -> Ref;
build_ref([{put, K, V} | Ops], Ref) -> build_ref(Ops, lists:keystore(K, 1, Ref, {K, V}));
build_ref([{delete, K} | Ops], Ref) -> build_ref(Ops, lists:keydelete(K, 1, Ref)).


test() ->
    Ops = [{put,<<15:4>>,<<0>>},
           {put,<<253,0:4>>,<<0>>},
           {put,<<"ý">>,<<0>>},
           {delete,<<15:4>>},
           {delete,<<"ý">>} ],
    build_tree(Ops).

