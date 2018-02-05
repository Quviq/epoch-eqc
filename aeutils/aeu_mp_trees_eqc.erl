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
    ?LET(Ops, gen_ops(),
         begin
            {ok, Tree} = build_tree(Ops),
            {ops_keys(Ops), Tree}
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

alter_proof(DB) ->
    Dict = aeu_mp_trees_db:get_cache(DB),
    ?LET({Hash, Node}, elements(dict:to_list(Dict)),
    begin
        NewNode =
            case Node of
                [X, Y] ->
                    [<<X/binary, 0>>, Y]; %% Leaf or Ext
                Branch ->
                    case lists:reverse(Branch) of
                        [<<>>|Rev] -> lists:reverse([<<1>>|Rev]);
                        [_|Rev] -> lists:reverse([<<>>|Rev])
                    end
            end,
        BogusDB = aeu_mp_trees_db:put(Hash, NewNode, DB),
        {Hash, BogusDB}
    end).


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


prop_check_proof() ->
    ?FORALL(Ops, gen_ops(),
    ?FORALL(Key, weighted_default({1, gen_key()}, {5, gen_put_key(ops_keys(Ops))}),
    begin
        {ok, Tree} = build_tree(Ops),
        {Val, ProofDB} = tree_construct_proof(Key, Tree),
        Hash = aeu_mp_trees:root_hash(Tree),
        equals(aeu_mp_trees:verify_proof(Key, Val, Hash, ProofDB), ok)
    end)).

prop_check_invalid_proof() ->
    ?FORALL({Keys, Tree}, gen_tree(),
    ?IMPLIES(Keys =/= [],
    ?FORALL(Key, elements(Keys),
    begin
        {Val, ProofDB} = tree_construct_proof(Key, Tree),
        Hash = aeu_mp_trees:root_hash(Tree),
        ?FORALL({BadHash, BadProofDB}, alter_proof(ProofDB),
        conjunction(
            [{bad_hash,  check_invalid_proof(bad_proof, Key, Val, change_binary(Hash), ProofDB)},
             {bad_value, check_invalid_proof({bad_value, Val}, Key, change_binary(Val), Hash, ProofDB)},
             {bad_db   , check_invalid_proof({bad_hash, BadHash}, Key, Val, Hash, BadProofDB)}]))
    end))).

check_invalid_proof(Expected, Key, Val, Hash, ProofDB) ->
    equals(aeu_mp_trees:verify_proof(Key, Val, Hash, ProofDB), Expected).

property_weight(_, prop_idempotence) -> 5;
property_weight(_, _) -> 1.

prop_iterator() ->
    ?FORALL({Keys, Tree}, gen_tree(),
    begin
        Iter = aeu_mp_trees:iterator(Tree),
        IterKeys = iterate(Iter),
        equals(IterKeys, Keys)
    end).

prop_iterator_next() ->
    ?FORALL({Keys, Tree}, gen_tree(),
    ?IMPLIES(length(Keys) > 1,
    begin
        KeyPairs = lists:zip(lists:droplast(Keys), tl(Keys)),

        F = fun({K1, K2}) ->
                I = aeu_mp_trees:iterator_from(K1, Tree),
                {K2, _, _} = aeu_mp_trees:iterator_next(I)
            end,
        [ F(X) || X <- KeyPairs ],
        true
    end)).

prop_iterator_from() ->
    ?FORALL({_Keys, Tree}, gen_tree(),
    ?FORALL(Key, gen_key(),
    begin
        aeu_mp_trees:iterator_from(Key, Tree),
        true
    end)).

prop_iterator_from_next() ->
    ?FORALL({_Keys, Tree}, gen_tree(),
    ?FORALL(Key, gen_key(),
    begin
        I = aeu_mp_trees:iterator_from(Key, Tree),
        try
            aeu_mp_trees:iterator_next(I),
            true
        catch E:R ->
            ?WHENFAIL(eqc:format("I: ~p\nSt: {~p, ~p, ~p}\n", [I, E, R, erlang:get_stacktrace()]), false)
        end
    end)).

prop_iterator_from_next2() ->
    ?FORALL({Keys, Tree}, gen_tree(),
    ?FORALL(Key, gen_key(),
    begin
        Iter = aeu_mp_trees:iterator_from(Key, Tree),
        case aeu_mp_trees:iterator_next(Iter) of
            {Key1, _, _} -> lists:member(Key1, Keys);
            _ -> true
        end
    end)).

prop_iterator_depth() ->
    ?FORALL({Keys0, Tree}, gen_tree(),
    ?FORALL(MaxDepth, choose(1,4),
    begin
        Iter = aeu_mp_trees:iterator(Tree, [{max_path_length, MaxDepth}]),
        IterKeys = iterate(Iter),
        Keys = [ K || K <- Keys0, bit_size(K) div 4 =< MaxDepth ],
        equals(IterKeys, Keys)
    end)).


%% -- Helper functions -------------------------------------------------------
tree_put(K, V, Tree) ->
    aeu_mp_trees:put(K, V, Tree).

tree_delete(K, Tree) ->
    aeu_mp_trees:delete(K, Tree).

tree_get(K, Tree) ->
    aeu_mp_trees:get(K, Tree).

tree_hash(Tree) ->
    aeu_mp_trees:root_hash(Tree).

tree_construct_proof(Key, Tree) ->
    aeu_mp_trees:construct_proof(Key, aeu_mp_trees_db:new(dict_db_spec()), Tree).

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


change_binary([B|Bs]) -> [change_binary(B) | Bs];
change_binary(<<X:8, Rest/bitstring>>) ->
    Y = X + 1,
    <<Y:8, Rest/bitstring>>.

dict_db_spec() ->
    #{ handle => dict:new()
     , cache  => dict:new()
     , get    => {?MODULE, dict_db_get}
     , put    => {?MODULE, dict_db_put}
     , commit => {?MODULE, dict_db_commit}
     }.

dict_db_get(Key, Dict) ->
    {value, dict:fetch(Key, Dict)}.

dict_db_put(Key, Val, Dict) ->
    dict:store(Key, Val, Dict).

dict_db_commit(Cache, DB) ->
    {ok, dict:new(), dict:merge(fun(_, _, Val) -> Val end, Cache, DB)}.

iterate(Iter) ->
    case aeu_mp_trees:iterator_next(Iter) of
        {Key, _Val, NextIter} -> [Key | iterate(NextIter)];
        '$end_of_table' -> []
    end.
