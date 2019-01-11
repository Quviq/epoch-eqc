%%% Author      : Hans Svensson
%%% Description :
%%% Created     : 17 Jan 2018 by Hans Svensson
-module(aeu_mp_trees_eqc).

-compile(export_all).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-import(eqc_statem, [tag/2]).

%% -- Generators -------------------------------------------------------------

gen_data() ->
    ?LET(Keys, list(gen_key()),
         ?LET(Vals, vector(length(Keys), gen_value()),
              #{ keys => Keys, data => lists:zip(Keys, Vals) })).

gen_nibble() -> choose(16#0, 16#F).

gen_key() -> ?LET(Xs, non_empty(list(gen_nibble())),
                  return(nibbles(Xs))).

gen_fixed_len_key(Len) -> ?LET(Xs, vector(Len, gen_nibble()),
                               return(nibbles(Xs))).

nibbles(Xs) -> << <<X:4>> || X <- Xs >>.

gen_put_key([]) -> gen_key();
gen_put_key(Existing) ->
    frequency([{1, gen_key()},
               {1, ?LET({K, Ns}, {elements(Existing), list(gen_nibble())},
                        return(<<K/bitstring, (nibbles(Ns))/bitstring>>))}]).

gen_delete_key([]) -> gen_key();
gen_delete_key(Existing) ->
    frequency([{1, gen_key()},
               {1 + length(Existing) div 2, elements(Existing)}]).

gen_subtree_key(Existing) ->
    frequency([{1, <<>>},
               {5, gen_delete_key(Existing)}]).

gen_value() ->
    frequency([{1, <<>>},
               {9, weighted_default({5, gen_decodable()}, {1, binary(36)})}]).

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

long_list(N, Gen) ->
    ?SIZED(X, resize(N * X, list(Gen))).

gen_syllable() ->
    elements(
        ["ing", "er", "a", "ly", "ed", "i", "es", "re", "tion", "in", "e",
         "con", "y", "ter", "ex", "al", "de", "com", "o", "di", "en", "an",
         "ty", "ry", "u", "ti", "ri", "be", "per", "to", "pro", "ac", "ad",
         "ar", "ers", "ment", "or", "tions", "ble", "der", "ma", "na", "si",
         "un", "at", "dis", "ca", "cal", "man", "ap", "po", "sion", "vi", "el",
         "est", "la", "lar", "pa", "ture", "for", "is", "mer", "pe", "ra", "so",
         "ta", "as", "col", "fi", "ful", "ger", "low", "ni", "par", "son",
         "tle", "day", "ny", "pen", "pre", "tive", "car", "ci", "mo", "on",
         "ous", "pi", "se", "ten", "tor", "ver", "ber", "can", "dy", "et", "it",
         "mu", "no", "ple", "cu", "fac", "fer", "gen", "ic", "land", "light",
         "ob", "of", "pos", "tain", "den", "ings", "mag", "ments", "set",
         "some", "sub", "sur", "ters", "tu", "af", "au", "cy", "fa", "im", "li",
         "lo", "men", "min", "mon", "op", "out", "rec", "ro", "sen", "side",
         "tal", "tic", "ties", "ward", "age", "ba", "but", "cit", "cle", "co",
         "cov", "da", "dif", "ence", "ern", "eve", "hap", "ies", "ket", "lec",
         "main", "mar", "mis", "my", "nal", "ness", "ning", "nu", "oc", "pres",
         "sup", "te", "ted", "tem", "tin", "tri", "tro", "up"]).

gen_word() ->
    ?LET(Xs, ?SUCHTHAT(Ys, noshrink(eqc_gen:list(4, gen_syllable())), length(Ys) > 1),
    return(lists:append(Xs))).

gen_tree_id() -> gen_word().

gen_iterator_opts() ->
    weighted_default(
        {5, none},
        {1, eqc_gen:list(1, {max_path_length, choose(1, 20)})}).

%% -- State ------------------------------------------------------------------

-type(sym(A)) :: {var, integer()} | A.

-record(state, {trees = #{} :: #{id() => tree()},
                snapshots = [] :: [snapshot()] }).
-record(tree, { contents    = []    :: [{key(), val()}],
                db          = []    :: [{key(), val()}],
                cache       = []    :: [sym(hash())],
                db_hashes   = []    :: [sym(hash())],
                is_readonly = false :: boolean(),
                prefix      = <<>>  :: key() }).

-type tree() :: #tree{}.
-type id()  :: string().
-type key() :: binary().
-type val() :: iolist().
-type hash() :: string().
-type snapshot() :: {sym(hash()), [{key(), val()}]}.

get_tree(Id, S) -> maps:get(Id, S#state.trees).

get_data(Id, S) -> (get_tree(Id, S))#tree.contents.
get_db(Id, S) -> (get_tree(Id, S))#tree.db.

get_tree(Id) -> get({mp_tree, Id}).
put_tree(Id, Tree) -> put({mp_tree, Id}, Tree).

gen_tree_id(S) ->
    elements(maps:keys(S#state.trees)).

gen_tree_id_with_keys(S) ->
    ?LET(Id, gen_tree_id(S),
    return({Id, tree_keys(get_tree(Id, S))})).

is_tree(Id, S) -> maps:is_key(Id, S#state.trees).

is_readonly(Id, S) ->
    (get_tree(Id, S))#tree.is_readonly.

is_key(Key, Id, S) ->
    lists:keymember(Key, 1, get_data(Id, S)).

set_tree(Id, Tree, S) ->
    S#state{ trees = (S#state.trees)#{ Id => Tree } }.

on_tree(Id, Fun, S) ->
    Tree = get_tree(Id, S),
    set_tree(Id, Fun(Tree), S).

on_data(Id, Fun, S) ->
    on_tree(Id, fun(T) -> T#tree{ contents = Fun(T#tree.contents) } end, S).

tree_keys(#tree{contents = Xs}) -> [ K || {K, _} <- Xs ].

get_snapshot(Hash, S) ->
    proplists:get_value(Hash, S#state.snapshots).

add_snapshot(Hash, Id, S) ->
    Tree = get_tree(Id, S),
    case lists:sort(Tree#tree.contents) of
        []   -> S;
        Data ->
            case lists:keyfind(Data, 2, S#state.snapshots) of
                {Hash1, _} ->
                    set_tree(Id, Tree#tree{ cache = [Hash1 | Tree#tree.cache -- [Hash1]] }, S);
                false ->
                    set_tree(Id, Tree#tree{ cache = [Hash | Tree#tree.cache] },
                             S#state{ snapshots = [{Hash, Data} | S#state.snapshots] })
            end
    end.

hashes(S) -> [ H || {H, _} <- S#state.snapshots ].

reachable_hashes(T, S) ->
    reachable_hashes(cache, T, S) ++ reachable_hashes(db, T, S).

reachable_hashes(cache, T, S) ->
    [ H || H <- T#tree.cache, is_reachable(H, T, S) ];
reachable_hashes(db, T, S) ->
    [ H || H <- T#tree.db_hashes, is_reachable(H, T, S) ].

is_reachable(Hash, Tree, S) ->
    lists:sort(Tree#tree.contents) == get_snapshot(Hash, S).

initial_state() -> #state{}.

%% -- Commands ---------------------------------------------------------------

%% --- new ---

new_args(_S) -> [gen_tree_id()].

new_pre(S) -> #{} == S#state.trees.

new_pre(S, [Id]) -> not is_tree(Id, S).

new(Id) ->
    put_tree(Id, aeu_mp_trees:new()),
    ok.

new_next(S, _V, [Id]) ->
    set_tree(Id, #tree{}, S).

%% --- put ---

put_pre(S) -> #{} /= S#state.trees.

put_args(S) ->
    ?LET({Id, Keys}, gen_tree_id_with_keys(S),
    [gen_put_key(Keys), gen_value(), return(Id)]).

put_pre(S, [_Key, _Val, Id]) ->
    is_tree(Id, S) andalso
    not is_readonly(Id, S).

put(Key, Val, Id) ->
    NewTree = aeu_mp_trees:put(Key, Val, get_tree(Id)),
    put_tree(Id, NewTree),
    root_hash58(NewTree).

put_next(S, V, [Key, <<>>, Id]) ->
    delete_next(S, V, [Key, Id]);
put_next(S, V, [Key, Val, Id]) ->
    S1 = on_data(Id, fun(Data) -> [{Key, Val} | lists:keydelete(Key, 1, Data)] end, S),
    add_snapshot(V, Id, S1).

%% --- get ---

get_args(S) ->
    ?LET({Id, Keys}, gen_tree_id_with_keys(S),
    [gen_delete_key(Keys), return(Id)]).

get_pre(S) -> #{} /= S#state.trees.
get_pre(S, [_Key, Id]) -> is_tree(Id, S).

get(Key, Id) ->
    aeu_mp_trees:get(Key, get_tree(Id)).

get_post(S, [Key, Id], V) ->
    eq(V, proplists:get_value(Key, get_data(Id, S), <<>>)).

%% --- delete ---

delete_args(S) ->
    ?LET({Id, Keys}, gen_tree_id_with_keys(S),
    [gen_delete_key(Keys), return(Id)]).

delete_pre(S) -> #{} /= S#state.trees.
delete_pre(S, [_Key, Id]) ->
    is_tree(Id, S) andalso not is_readonly(Id, S).

delete(Key, Id) ->
    NewTree = aeu_mp_trees:delete(Key, get_tree(Id)),
    put_tree(Id, NewTree),
    root_hash58(NewTree).

delete_next(S, V, [Key, Id]) ->
    S1 = on_data(Id, fun(Data) -> lists:keydelete(Key, 1, Data) end, S),
    add_snapshot(V, Id, S1).

%% --- to_list ---

to_list_args(S) ->
    [gen_tree_id(S), gen_iterator_opts()].

to_list_pre(S) -> #{} /= S#state.trees.
to_list_pre(S, [Id, _Opts]) -> is_tree(Id, S).

to_list(Id, Opts) ->
    It = case Opts of
            none -> aeu_mp_trees:iterator(get_tree(Id));
            _    -> aeu_mp_trees:iterator(get_tree(Id), Opts)
         end,
    iterator_to_list(It).

to_list_post(S, [Id, Opts], V) ->
    eq(V, lists:sort([ E || E = {K, _} <- get_data(Id, S),
                            bit_size(K) div 4 =< max_len(Opts)])).

max_len(none) -> infinity;
max_len(Opts) -> proplists:get_value(max_path_length, Opts, infinity).

%% --- to_list_from ---

to_list_from_args(S) ->
    ?LET({Id, Keys}, gen_tree_id_with_keys(S),
    [gen_delete_key(Keys), return(Id), gen_iterator_opts()]).    %% TODO: better key gen?

to_list_from_pre(S) -> #{} /= S#state.trees.
to_list_from_pre(S, [_Key, Id, _Opts]) -> is_tree(Id, S).

to_list_from(Key, Id, Opts) ->
    It = case Opts of
            none -> aeu_mp_trees:iterator_from(Key, get_tree(Id));
            _    -> aeu_mp_trees:iterator_from(Key, get_tree(Id), Opts)
         end,
    iterator_to_list(It).

to_list_from_post(S, [Key, Id, Opts], V) ->
    eq(V, lists:sort([ E || E = {K, _} <- get_data(Id, S),
                            K > Key, bit_size(K) div 4 =< max_len(Opts) ])).

%% --- to_sublist ---

to_sublist_args(S) ->
    ?LET({Id, Keys}, gen_tree_id_with_keys(S),
    [gen_delete_key(Keys), return(Id)]).    %% TODO: better key gen?

to_sublist_pre(S) -> #{} /= S#state.trees.
to_sublist_pre(S, [_Key, Id]) -> is_tree(Id, S).

to_sublist(Key, Id) ->
    It = aeu_mp_trees:iterator_from(Key, get_tree(Id), [{with_prefix, Key}]),
    iterator_to_list(It).

to_sublist_post(S, [Key, Id], V) ->
    eq(V, lists:sort([ E || E = {K, _} <- get_data(Id, S),
                            strict_prefix(Key, K) ])).

%% --- root_hash ---

root_hash_args(S) -> [gen_tree_id(S)].

root_hash_pre(S) -> #{} /= S#state.trees.
root_hash_pre(S, [Id]) ->
    is_tree(Id, S) andalso
    not is_readonly(Id, S) andalso
    [] /= get_data(Id, S).

root_hash(Id) ->
    base58:binary_to_base58(aeu_mp_trees:root_hash(get_tree(Id))).

root_hash_post(S, [Id], Res) ->
    Tree   = get_tree(Id, S),
    Prefix = Tree#tree.prefix,
    Fresh  = safe_build_tree([ {put, <<Prefix/bits, K/bits>>, V} || {K, V} <- Tree#tree.contents ]),
    eq(Res, base58:binary_to_base58(aeu_mp_trees:root_hash(Fresh))).

%% --- restore ---

restore_args(S) -> [gen_tree_id(S), elements(hashes(S))].

restore_pre(S) ->
    #{} /= S#state.trees andalso
    []  /= S#state.snapshots.

restore_pre(S, [Id, Hash]) ->
    is_tree(Id, S) andalso
    not is_readonly(Id, S) andalso
    lists:member(Hash, hashes(S)).

restore(Id, Hash) ->
    Tree = get_tree(Id),
    try
        put_tree(Id, aeu_mp_trees:new(from_base58(Hash), aeu_mp_trees:db(Tree))),
        true
    catch _:{hash_not_present_in_db, _} ->
        false
    end.

restore_next(S, _V, [Id, Hash]) ->
    Tree = get_tree(Id, S),
    case restore_ok(S, Id, Hash) of
        false -> S;
        true  ->
            set_tree(Id, Tree#tree{ contents = get_snapshot(Hash, S) }, S)
    end.

restore_ok(S, Id, Hash) ->
    Tree = get_tree(Id, S),
    lists:member(Hash, Tree#tree.cache ++ Tree#tree.db_hashes).

restore_post(S, [Id, Hash], V) ->
  eq(V, restore_ok(S, Id, Hash)).

%% --- subtree ---

subtree_args(S) ->
    ?LET({Id, Keys}, gen_tree_id_with_keys(S),
    [gen_tree_id(), gen_subtree_key(Keys), return(Id)]).

subtree_pre(S) -> #{} /= S#state.trees.
subtree_pre(S, [New, Key, Id]) ->
    is_tree(Id, S) andalso
    not is_tree(New, S) andalso
    (is_key(Key, Id, S) orelse
     Key == <<>> andalso (get_tree(Id, S))#tree.is_readonly).

subtree(NewId, Key, Id) ->
    case aeu_mp_trees:read_only_subtree(Key, get_tree(Id)) of
        {ok, Tree} -> put_tree(NewId, Tree), true;
        {error, no_such_subtree} -> false
    end.

subtree_next(S, _V, [NewId, Key, Id]) ->
    case subtree_ok(S, Key, Id) of
        false -> S;
        true ->
            Data = get_data(Id, S),
            NewData = [ {K1, V} || {K, V} <- Data, {ok, K1} <- [strip_prefix(Key, K)] ],
            Subtree = #tree{ is_readonly = true, prefix = Key, contents = NewData },
            set_tree(NewId, Subtree, S)
    end.

subtree_post(S, [_NewId, Key, Id], V) ->
    eq(V, subtree_ok(S, Key, Id)).

subtree_ok(_, _, _) -> true.

%% --- commit ---

commit_args(S) -> [gen_tree_id(S)].

commit_pre(S) -> #{} /= S#state.trees.
commit_pre(S, [Id]) -> is_tree(Id, S) andalso not is_readonly(Id, S).

commit(Id) ->
    put_tree(Id, aeu_mp_trees:commit_reachable_to_db(get_tree(Id))),
    ok.

commit_next(S, _V, [Id]) ->
  on_tree(Id, fun(T) -> T#tree{ db        = T#tree.contents,
                                cache     = [],
                                db_hashes = reachable_hashes(cache, T, S) ++ T#tree.db_hashes } end, S).

%% --- gc_cache ---

gc_cache_args(S) -> [gen_tree_id(S)].

gc_cache_pre(S) -> #{} /= S#state.trees.
gc_cache_pre(S, [Id]) -> is_tree(Id, S) andalso not is_readonly(Id, S).

gc_cache(Id) ->
    put_tree(Id, aeu_mp_trees:gc_cache(get_tree(Id))),
    ok.

gc_cache_next(S, _V, [Id]) ->
    on_tree(Id, fun(T) -> T#tree{ cache = reachable_hashes(cache, T, S) } end, S).

%% --- new_from_reachable ---

new_from_reachable_args(S) -> [gen_tree_id(), gen_tree_id(S)].

new_from_reachable_pre(S) -> #{} /= S#state.trees.
new_from_reachable_pre(S, [NewId, Id]) ->
    is_tree(Id, S) andalso
    not is_tree(NewId, S) andalso
    [] /= get_data(Id, S).

new_from_reachable(NewId, Id) ->
    NewTree = new_from_reachable(get_tree(Id)),
    put_tree(NewId, NewTree),
    ok.

reachable_hashes(Tree) ->
    VisitFun = fun(Hash, BinNode, Acc) -> {continue, [{Hash, BinNode} | Acc]} end,
    aeu_mp_trees:visit_reachable_hashes(Tree, [], VisitFun).

new_from_hashes(Root, DBHashes) ->
    DB = lists:foldl(fun({Hash, BinNode}, DB) -> aeu_mp_trees_db:put(Hash, BinNode, DB) end,
                     new_dict_db(), DBHashes),
    aeu_mp_trees:new(Root, DB).

new_from_reachable(Tree) ->
    Root = aeu_mp_trees:root_hash(Tree),
    new_from_hashes(Root, reachable_hashes(Tree)).

new_from_reachable_next(S, _V, [NewId, Id]) ->
    T = get_tree(Id, S),
    set_tree(NewId, T#tree{ db = [],
                            db_hashes = [],
                            cache = reachable_hashes(T, S) }, S).

new_from_reachable_post(S, [_NewId, Id], _) ->
    %% Check that we can't delete anything from the database without breaking
    %% the tree.
    Tree        = get_tree(Id),
    Root        = tree_hash(Tree),
    DBHashes    = reachable_hashes(Tree),
    {Hashes, _} = lists:unzip(DBHashes),
    Data        = lists:sort(get_data(Id, S)),
    BrokenTree  = fun(Hash) -> new_from_hashes(Root, lists:keydelete(Hash, 1, DBHashes)) end,
    IsBroken    = fun(Hash) ->
            try lists:sort(to_list(BrokenTree(Hash), none)) of
                Data                                    -> same_tree;
                Data1 when length(Data1) < length(Data) -> true;
                Data1                                   -> {same_size, Data1}
            catch _:_ -> true end
        end,
    eq([], [ {to_base58(Hash), Why} || Hash <- Hashes, Why <- [IsBroken(Hash)], Why /= true ]).

%% --- unfold ---

unfold_tree_args(S) -> [gen_tree_id(S)].

unfold_tree_pre(S) -> #{} /= S#state.trees.
unfold_tree_pre(S, [Id]) -> is_tree(Id, S).

unfold_tree(Id) ->
    Tree = get_tree(Id),
    do_unfold([{node, <<>>, dummy}], Tree, []).

unfold_tree_post(S, [Id], V) ->
    {Keys, _} = lists:unzip(get_data(Id, S)),       %% BUG: Unfold drops "interior" keys
    Missing = [ K || K <- Keys -- V, not lists:any(fun(K1) -> strict_prefix(K, K1) end, Keys) ],
    Extra   = V -- Keys,
    conj([tag(extra, eq(Extra, [])),
          tag(missing, eq(Missing, []))]).

do_unfold([], _Tree, Acc) -> lists:reverse(Acc);
do_unfold([Node | Nodes], Tree, Acc) ->
    case Node of
        {leaf, Path} -> do_unfold(Nodes, Tree, [Path | Acc]);
        {node, Path, Enc} ->
            do_unfold(aeu_mp_trees:unfold(Path, Enc, Tree) ++ Nodes, Tree, Acc)
    end.

%% -- Common ----------------------------------------------------------------

weight(_, put)                -> 5;
weight(_, get)                -> 5;
weight(_, delete)             -> 3;
weight(_, new_from_reachable) -> 3;
weight(_, subtree)            -> 3;
weight(_, to_list)            -> 3;
weight(_, to_list_from)       -> 3;
weight(_, to_sublist)         -> 3;
weight(_, new)                -> 1;
weight(_, root_hash)          -> 1;
weight(_, commit)             -> 1;
weight(_, gc_cache)           -> 1;
weight(_, unfold)             -> 1;
weight(_, _)                  -> 3.

%% -- Properties -------------------------------------------------------------

prop_ok() ->
  ?FORALL(Cmds, commands(?MODULE),
  begin
    erase(),
    HSR={_, _, Res} = run_commands(Cmds),
    pretty_commands(?MODULE, Cmds, HSR,
    check_command_names(?MODULE, Cmds,
      Res == ok))
  end).

%% -- Old properties ---------------------------------------------------------

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

prop_iterator_next1() ->
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

prop_iterator_from_next1() ->
    ?FORALL({_Keys, Tree}, ?SIZED(C, resize(2*C, gen_tree())),
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

prop_subtrees() ->
    ?FORALL({Keys, Tree}, gen_tree(),
    begin
        lists:foldl(
            fun(K, {ok, _}) -> aeu_mp_trees:read_only_subtree(K, Tree);
               (_K, Err)    -> Err end, ok, Keys) == ok
    end).

%% Tobias idea - create a number of keys w. length 4 bytes, split them at 2
%% bytes and insert all the prefix keys. Now iterate over all subtrees at the
%% prefix keys and you should get exactly all (suffix) keys.
prop_iterator_subtrees() ->
    ?FORALL(Keys0, non_empty(long_list(10, gen_fixed_len_key(8))),
    begin
        Keys = lists:usort(Keys0),

        Tree0 = lists:foldl(fun(K, T) -> tree_put(K, <<1>>, T) end, aeu_mp_trees:new(), Keys),

        {ShortKeys0, ShortVals} =
            lists:unzip([ {<<Prefix:16>>, Rest} || <<Prefix:16, Rest/binary>> <- Keys ]),

        ShortKeys = lists:usort(ShortKeys0),

        Tree1 = lists:foldl(fun(K, T) -> tree_put(K, <<1>>, T) end, Tree0, ShortKeys),

        SubTrees = [ T || K <- ShortKeys, {ok, T} <- [aeu_mp_trees:read_only_subtree(K, Tree1)] ],

        Elems = lists:concat([ iterate(aeu_mp_trees:iterator(ST)) || ST <- SubTrees ]),

        equals(Elems, ShortVals)
    end).

%% Compute the subtree values from the list, and check that it matches.
prop_subtrees2() ->
    ?FORALL({Keys, Tree}, gen_tree(),
    begin
        SubTrees = find_subtrees(Keys),
        [true] == lists:usort([true] ++ [ check_subtree(ST, Tree) || ST <- SubTrees ])
    end).


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
    aeu_mp_trees:construct_proof(Key, new_dict_db(), Tree).

root_hash58(Tree) ->
    base58:binary_to_base58(aeu_mp_trees:root_hash(Tree)).

to_base58(S)   -> base58:binary_to_base58(S).
from_base58(S) -> base58:base58_to_binary(S).

new_dict_db() -> aeu_mp_trees_db:new(dict_db_spec()).

iterator_to_list(It) ->
    Iter = fun Iter(I, Acc) ->
                case aeu_mp_trees:iterator_next(I) of
                    '$end_of_table' -> lists:reverse(Acc);
                    {Key, Val, Next} ->
                        Iter(Next, [{Key, Val} | Acc])
                end end,
    Iter(It, []).

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
     , drop_cache => {?MODULE, dict_db_drop_cache}
     }.

dict_db_get(Key, Dict) ->
    case dict:find(Key, Dict) of
        {ok, Val} -> {value, Val};
        error -> none
    end.

dict_db_put(Key, Val, Dict) ->
    dict:store(Key, Val, Dict).

dict_db_drop_cache(_) -> dict:new().

iterate(Iter) ->
    case aeu_mp_trees:iterator_next(Iter) of
        {Key, _Val, NextIter} -> [Key | iterate(NextIter)];
        '$end_of_table' -> []
    end.

check_subtree({K, Vs}, Tree) ->
    {ok, ST} = aeu_mp_trees:read_only_subtree(K, Tree),
    Vs1 = iterate(aeu_mp_trees:iterator(ST)),
    Vs == Vs1.

find_subtrees(Keys) ->
    find_subtrees(Keys, Keys).

find_subtrees([K | Ks], All) ->
    [{K, subkeys(K, erlang:bit_size(K), All -- [K])} | find_subtrees(Ks, All)];
find_subtrees([], _) -> [].

subkeys(K, L, [K2 | Keys]) ->
    case K2 of
        <<K:L/bitstring, Rest/bitstring>> -> [Rest | subkeys(K, L, Keys)];
        _ -> subkeys(K, L, Keys)
    end;
subkeys(_, _, []) -> [].

is_prefix(Prefix, Key) -> Prefix == Key orelse strict_prefix(Prefix, Key).

strict_prefix(Prefix, Key) ->
    case strip_prefix(Prefix, Key) of
        {ok, _} -> true;
        {error, not_a_prefix} -> false
    end.

strip_prefix(Key, Key) -> {error, not_a_prefix};
strip_prefix(<<>>, Key) ->
    {ok, Key};
strip_prefix(Prefix, Key) ->
    S = bit_size(Prefix),
    case Key of
        <<Prefix:S/bits, Rest/bits>> -> {ok, Rest};
        _ -> {error, not_a_prefix}
    end.
