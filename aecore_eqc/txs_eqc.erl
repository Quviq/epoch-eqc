-module(txs_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-include("txs_eqc.hrl").

-compile([export_all, nowarn_export_all]).

-define(PatronAmount, 1000000000000000000000). % 1000 AE.

tx_models() ->
  [ txs_spend_eqc
  , txs_channels_eqc
  %% , txs_contracts_eqc
  %% , txs_names_eqc
  %% , txs_oracles_eqc
  , txs_ga_eqc
  %% , txs_paying_for_eqc
  ].

initial_state(HFs) ->
  IS = #{fees => [], hard_forks => HFs,
         height => 1, protocol => txs_utils:protocol_at_height(HFs, 1)},
  lists:foldl(fun(M, S) -> eqc_statem:apply(M, initial_state, [S]) end,
              IS, tx_models()).

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

%% --- Operation: init ---
init_pre(S) ->
  not maps:is_key(accounts, S) andalso not maps:is_key(keys, S).

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
  KeyId    = next_id(key),
  Keys     = #{ KeyId     => #key{ private = Secret, public = PA } },
  Accounts = #{ account_0 => #account{ key = KeyId, amount = PAmount } },
  S#{accounts => Accounts, keys => Keys}.

%% --- Operation: newkey ---
newkey_pre(S) ->
  maps:is_key(keys, S).

newkey_args(_S) ->
  #{ public := Pubkey, secret := Privkey } = enacl:sign_keypair(),
  [next_id(key), {Pubkey, Privkey}].

newkey(_, _) ->
  ok.

newkey_next(S, _Value, [KeyId, {Pubkey, Privkey}]) ->
  add_key(S, KeyId, Pubkey, Privkey).

add_key(S = #{keys := Keys}, KeyId, Pub, Priv) ->
  S#{ keys := Keys#{ KeyId => #key{public = Pub, private = Priv} } }.

%% --- Operation: mine ---
mine_pre(S) ->
  maps:is_key(accounts, S).

mine_args(_) ->
  [?LET(Blocks, frequency([{10, 1}, {1, 10}, {1, 100}, {2, 480}, {1, 1000}, {1, 10000}, {1, 25000}]),
        ?SHRINK(Blocks, [choose(1, Blocks) || Blocks =/= 1]))].

mine_call(#{height := Height}, [Blocks]) ->
  Trees  = get(trees),
  Trees1 = pre_transformations(Height + Blocks, Trees),
  put(trees, Trees1),
  ok.

pre_transformations(Height, Trees) ->
  Trees0 = aect_call_state_tree:prune(Height, Trees),
  Trees1 = aeo_state_tree:prune(Height, Trees0),
  aens_state_tree:prune(Height, Trees1).

mine_next(#{height := Height, hard_forks := Forks} = S0, Value, [Blocks]) ->
  S1 = case lists:member(txs_names_eqc, tx_models()) of
         true  -> txs_names_eqc:mine_next(S0, Value, [Blocks]);
         false -> S0 end,
  S2 = case lists:member(txs_oracles_eqc, tx_models()) of
         true  -> txs_oracles_eqc:mine_next(S1, Value, [Blocks]);
         false -> S1 end,
  S2#{height   => Height + Blocks,
      protocol => tx_utils:protocol_at_height(Forks, Height + Blocks)}.

mine_features(_S, [_B], _Res) ->
  [].

%% --- Operation: tx ---

tx_pre(S) ->
  maps:is_key(accounts, S).

tx_args(S) ->
  gen_tx(S).

tx_pre(S, [M, Tx, TxData]) ->
  is_consistent(S, TxData) andalso
  try apply(M, ?pre(Tx), [S, TxData])
  catch _:_ -> true end.

tx_call(S = #{height := Height, protocol := P}, [M, Tx, TxData]) ->
  {ok, UTx} = apply(M, ?tx(Tx), [S, TxData]),
  try apply_transaction(Height, P, UTx)
  catch _:Reason -> {error, Reason, erlang:get_stacktrace()} end.

tx_next(S, Value, [M, Tx, TxData]) ->
  apply(M, ?next(Tx), [S, Value, TxData]).

tx_post(S, [M, Tx, TxData], Res) ->
  apply(M, ?post(Tx), [S, TxData, Res]).

tx_features(S, [M, Tx, TxData], Res) ->
  [{tx, Tx}]
    ++ apply(M, ?features(Tx), [S, TxData, Res]).

apply_transaction(_Height, _P, no_tx) ->
  ok;
apply_transaction(Height, P, Tx) ->
  Env0     = aetx_env:tx_env(Height, P),
  Env      = aetx_env:set_signed_tx(Env0, {value, aetx_sign:new(Tx, [])}),

  Trees    = get(trees),

  case aetx:process(Tx, Trees, Env) of
    {ok, NewTrees, _NewEnv} ->
      put(trees, NewTrees),
      ok;
    Other ->
      Other
  end.

wrap_call(S, {call, _, Cmd, Args}) ->
  CmdCall = list_to_atom(lists:concat([Cmd, "_call"])),
  try
    case lists:member({CmdCall, 2}, ?MODULE:module_info(exports)) of
      true ->
        {ok, apply(?MODULE, CmdCall, [S, Args])};
      _ ->
        {ok, apply(?MODULE, Cmd, Args)}
    end
  catch _:Reason ->
      {error, {'EXIT', Reason, erlang:get_stacktrace()}, []}
  end.

%% --- Generators ---------------------------------
gen_tx(S) ->
  Active = tx_models() -- ( [txs_ga_eqc || maps:is_key(ga, S)] ++
                            [txs_paying_for_eqc || maps:is_key(paying_for, S) ] ),
  ?LET({call, M, F, Args},
       frequency(
         lists:append([eqc_statem:apply(M, command_list, [S]) || M <- Active])),
       [M, F, Args]).

weight(_S, tx)   -> 200;
weight(_S, mine) -> 50;
weight(#{keys := Keys}, newkey) ->
  case maps:size(Keys) < 5 of
    true  -> 50;
    false -> 1 end;
weight(_S, _)    -> 1.

%% --- Property -----------------------------------
prop_txs() ->
  %% Forks = #{1=> 0, 2 => 3, 3 => 6, 4 => 9},
  %% Forks = #{1=> 0, 2 => 10, 3 => 20, 4 => 100, 5 => 1000},
  Forks = #{1 => 0, 5 => 1},
  prop_txs(Forks).

prop_txs(Forks) ->
    propsetup(Forks,
    eqc:dont_print_counterexample(
    in_parallel(
    ?FORALL(Cmds, more_commands(5, commands(?MODULE, initial_state(Forks))),
    begin
        put(trees, undefined),
        {H, S, Res} = run_commands(Cmds),
        Height = maps:get(height, S, 0),
        Accounts = maps:get(accounts, S, #{}),
        Oracles  = maps:get(oracles, S, #{}),
        Total    = trees_total(),
        FeeTotal = lists:sum([ Fee || {Fee, _} <- maps:get(fees, S, [])]),
        check_command_names(Cmds,
            measure(length__, commands_length(Cmds),
            measure(height__, Height,
            measure(accounts, maps:size(Accounts),
            measure(oracles_, maps:size(Oracles),
            measure(queries_, maps:size(maps:get(queries, S, #{})),
            features(call_features(H),
            stats(call_features(H),
                  pretty_commands(?MODULE, Cmds, {H, S, Res},
                                  conjunction([{result, Res == ok},
                                               {accounts, check_accounts(S)},
                                               {total, check_total(Total, FeeTotal)}])
                                 )))))))))
    end)))).

check_accounts(S) ->
  case {get(trees), maps:to_list(maps:get(accounts, S, #{}))} of
    {undefined, []} -> true;
    {Trees0, As} ->
      Trees = aec_trees:accounts(Trees0),
      case lists:usort([check_account(S, Id, A, Trees) || {Id, A} <- As ]) -- [ok] of
        []   -> true;
        Errs -> ?WHENFAIL(eqc:format("~p\n", [Errs]), false)
      end
  end.

check_account(S, Id, #account{ amount = Amount, nonce = Nonce, key = Key }, Trees) ->
  #key{public = Pubkey} = maps:get(Key, maps:get(keys, S)),
  case aec_accounts_trees:lookup(Pubkey, Trees) of
    none when Amount == 0, Nonce == 1 ->
      ok;
    none ->
      {no_account_in_tree, Id, expected, Amount, nonce, Nonce};
    {value, Account} ->
      case aec_accounts:balance(Account) of
        Amount    -> ok;
        NotAmount ->
          {wrong_balance, Id, {diff, NotAmount - Amount}, got, NotAmount, expected, Amount}
      end
  end.

check_total(Total, FeeTotal) ->
  ?WHENFAIL(eqc:format("Total: ~p Expected: ~p Diff: ~p\n",
                       [Total, ?PatronAmount - FeeTotal, Total - (?PatronAmount - FeeTotal)]),
            Total == 0 orelse (Total == ?PatronAmount - FeeTotal)).

trees_total() ->
    TreesTotal =
        case get(trees) of
            undefined -> #{};
            Trees -> aec_trees:sum_total_coin(Trees)
        end,
    %% io:format("TT: ~p\n", [TreesTotal]),
    lists:sum(maps:values(TreesTotal)).

stats(Features, Prop) ->
  {_Atoms, Rest} = lists:partition(fun is_atom/1, Features),
  Feats = lists:flatten([tx, correct, spend, mine] ++
                        [ [contract_create, contract_call]
                          || lists:member(txs_contracts_eqc, tx_models()) ] ++
                        [ [sc_create, sc_deposit, sc_withdraw, sc_close_mutual,
                           sc_snapshot_solo, sc_close_solo, sc_settle,
                           sc_slash, sc_offchain]
                          || lists:member(txs_channels_eqc, tx_models()) ] ++
                        [ [ga_attach, ga_meta, ga_meta_inner]
                          || lists:member(txs_ga_eqc, tx_models()) ] ++
                        [ [paying_for, paying_for_inner]
                          || lists:member(txs_paying_for_eqc, tx_models()) ] ++
                        [ [register_oracle, extend_oracle, query_oracle, response_oracle]
                          || lists:member(txs_oracles_eqc, tx_models()) ] ++
                        [ [ns_preclaim, ns_claim, ns_revoke, ns_transfer, ns_update]
                          || lists:member(txs_names_eqc, tx_models()) ]),
  %% aggregate(with_title(atoms), Atoms, aggregate_feats(Feats, Rest, Prop)).
  aggregate_feats(Feats, Rest, Prop).

aggregate_feats([], _, Prop) -> Prop;
aggregate_feats([Tag | Kinds], Features, Prop) ->
    {Tuples, Rest} = lists:partition(fun(X) -> element(1, X) == Tag end, Features),
    aggregate(with_title(Tag), Tuples, aggregate_feats(Kinds, Rest, Prop)).

%% --- Helper functions ---

is_consistent(S, Tx) ->
  Accs0   = maps:values(maps:get(accounts, S, #{})),
  Sym     = get_symbolic(Tx),

  KeyIds1 = [ A#account.key || A <- Accs0 ], %% Keys in accounts
  KeyIds2 = [ K || ?KEY(K) <- Sym ],         %% Keys
  KeyIds3 = [ K || {_, ?KEY(K)} <- Sym ],    %% Keys in new accounts
  KeyIds  = KeyIds1 ++ KeyIds2 ++ KeyIds3,
  Keys   = maps:get(keys, S, #{}),

  AccIds = [ A || ?ACCOUNT(A) <- Sym ],
  Accs   = maps:get(accounts, S, #{}),

  ConIds = [ C || ?CONTRACT(C) <- Sym ],
  Cons   = maps:get(contracts, S, #{}),

  OrcIds = [ O || ?ORACLE(O) <- Sym ],
  Orcs   = maps:get(oracles, S, #{}),

  QryIds = [ Q || ?QUERY(Q) <- Sym ],
  Qrys   = maps:get(queries, S, #{}),

  ChnIds = [ C || ?CHANNEL(C) <- Sym ],
  Chns   = maps:get(channels, S, #{}),

  %% io:format("is_consistent?\n~p ~p\n~p ~p\n~p ~p\n", [KeyIds, Keys, AccIds, Accs, KeyIds3, KeyIds1]),
  lists:all(fun(K) -> maps:is_key(K, Keys) end, KeyIds)
    andalso lists:all(fun(A) -> maps:is_key(A, Accs) end, AccIds)
    andalso lists:all(fun(C) -> maps:is_key(C, Cons) end, ConIds)
    andalso lists:all(fun(O) -> maps:is_key(O, Orcs) end, OrcIds)
    andalso lists:all(fun(Q) -> maps:is_key(Q, Qrys) end, QryIds)
    andalso lists:all(fun(C) -> maps:is_key(C, Chns) end, ChnIds)
    andalso (KeyIds3 -- KeyIds1) == KeyIds3.

get_symbolic(?KEY(X))      -> [?KEY(X)];
get_symbolic({A, ?KEY(X)}) -> [{A, ?KEY(X)}];
get_symbolic(?ACCOUNT(X))  -> [?ACCOUNT(X)];
get_symbolic(?CONTRACT(X)) -> [?CONTRACT(X)];
get_symbolic(?ORACLE(X))   -> [?ORACLE(X)];
get_symbolic(?QUERY(X))    -> [?QUERY(X)];
get_symbolic(?CHANNEL(X))  -> [?CHANNEL(X)];
get_symbolic(X) when is_map(X) ->
  get_symbolic(maps:to_list(X));
get_symbolic(Xs) when is_list(Xs) ->
  lists:flatmap(fun get_symbolic/1, Xs);
get_symbolic(X) when is_tuple(X) ->
  get_symbolic(tuple_to_list(X));
get_symbolic(_) -> [].

trees_with_accounts(Accounts) ->
    trees_with_accounts(Accounts, aec_trees:new_without_backend()).

trees_with_accounts([], Trees) ->
    Trees;
trees_with_accounts([{account, Acc, Amount}|Rest], Trees) ->
    Account = aec_accounts:new(Acc, Amount),
    AccountTrees = aec_accounts_trees:enter(Account, aec_trees:accounts(Trees)),
    trees_with_accounts(Rest, aec_trees:set_accounts(Trees, AccountTrees)).

propsetup(Forks, Prop) ->
    ?SETUP(
    fun() ->
            _ = application:load(aecore),
            application:load(aesophia),  %% Since we do in_parallel, we may have a race in line 86 of aesophia_compiler
            [ txs_contracts_eqc:compile_contracts() || lists:member(txs_contracts_eqc, tx_models())
                                                       orelse lists:member(txs_channels_eqc, tx_models())
                                                       orelse lists:member(txs_ga_eqc, tx_models()) ],
            HardForksTeardown = setup_hard_forks(Forks),
            DataDirTeardown = setup_data_dir(),
            fun() ->
                    DataDirTeardown(),
                    HardForksTeardown()
            end
    end, Prop).

setup_data_dir() ->
    %% make sure we can run in eqc/aecore_eqc
    {ok, Dir} = file:get_cwd(),
    %% Not asserting that configuration parameter is undefined so to ease experimenting in Erlang shell.
    case lists:reverse(filename:split(Dir)) of
        [_, "eqc" | _] ->
            application:set_env(setup, data_dir, "../../data");
        _ ->
            application:set_env(setup, data_dir, "data")
    end,
    fun() ->
            ok = application:unset_env(setup, data_dir)
    end.

setup_hard_forks(Forks) ->
    X = maps:from_list([ {integer_to_binary(K), V} || {K, V} <- maps:to_list(Forks)]),
    %% Not asserting that configuration parameter is undefined so to ease experimenting in Erlang shell.
    ok = application:set_env(aecore, hard_forks, X),
    fun() ->
            ok = application:unset_env(aecore, hard_forks)
    end.
