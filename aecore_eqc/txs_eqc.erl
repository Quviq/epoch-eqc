-module(txs_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-include("txs_eqc.hrl").
%% -import(eqc_statem, [more_commands/2, run_commands/1, check_command_names/2,
%%                      commands_length/1, call_features/1 ]).
%% -import(eqc_merge_statem, [ pretty_commands/4  %% Overwrite with specific pretty_commands
%%                     ]).

-compile([export_all, nowarn_export_all]).

-define(PatronAmount, 1000000000000000000000). % 1000 AE.

tx_models() ->
  [ txs_spend_eqc
  %% , txs_contracts_eqc
  %% , txs_names_eqc
  %% , txs_oracles_eqc
  , txs_ga_eqc
  ].

initial_state(HFs) ->
  lists:foldl(fun(M, S) -> eqc_statem:apply(M, initial_state, [S]) end,
              #{keys => #{}, fees => [], hard_forks => HFs}, tx_models()).

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
  S#{height   => 1, protocol => 1,
     accounts => [#account{key = PA, amount = PAmount}],
     keys => maps:put(PA, Secret, maps:get(keys, S))}.

%% --- Operation: newkey ---
newkey_args(_S) ->
    #{ public := Pubkey, secret := Privkey } = enacl:sign_keypair(),
    [Pubkey, Privkey].

newkey(_, _) ->
    ok.

newkey_next(S = #{keys := Keys}, _Value, [Pubkey, Privkey]) ->
    S#{keys => Keys#{Pubkey => Privkey}}.

%% --- Operation: mine ---
mine_pre(S) ->
  maps:is_key(accounts, S).

mine_args(_) ->
  [?LET(Blocks, frequency([{20, 1}, {1, 10}, {1, 100}, {2, 480}, {1, 1000}, {1, 10000}, {1, 25000}]),
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

mine_next(#{height := Height, hard_forks := Forks} = S, Value, [Blocks]) ->
  %% S1 = txs_names_eqc:mine_next(
  %%        txs_oracles_eqc:mine_next(S, Value, [Blocks]),
  %%        Value, [Blocks]),
  S1 = S,
  S1#{height   => Height + Blocks,
      protocol => tx_utils:protocol_at_height(Forks, Height + Blocks)}.

mine_features(_S, [_B], _Res) ->
  [].

%% --- Operation: tx ---
-define(pre(Tx), list_to_atom(lists:concat([Tx, "_pre"]))).
-define(tx(Tx), list_to_atom(lists:concat([Tx, "_tx"]))).
-define(next(Tx), list_to_atom(lists:concat([Tx, "_next"]))).
-define(post(Tx), list_to_atom(lists:concat([Tx, "_post"]))).
-define(features(Tx), list_to_atom(lists:concat([Tx, "_features"]))).

tx_pre(S) ->
  maps:is_key(accounts, S).

tx_args(S) ->
  gen_tx(S).

tx_pre(S, [M, Tx, TxData]) ->
  try apply(M, ?pre(Tx), [S, TxData])
  catch _:_ -> true end.

tx_call(S = #{height := Height}, [M, Tx, TxData]) ->
  {ok, UTx} = apply(M, ?tx(Tx), [S, TxData]),
  try apply_transaction(Height, UTx)
  catch _:Reason -> {error, Reason} end.

tx_next(S, Value, [M, Tx, TxData]) ->
  apply(M, ?next(Tx), [S, Value, TxData]).

tx_post(S, [M, Tx, TxData], Res) ->
  apply(M, ?post(Tx), [S, TxData, Res]).

tx_features(S, [M, Tx, TxData], Res) ->
  [{tx, Tx}]
    ++ apply(M, ?features(Tx), [S, TxData, Res]).

apply_transaction(Height, Tx) ->
  Env      = aetx_env:tx_env(Height),
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
  ?LET({call, M, F, Args},
       frequency(lists:append([eqc_statem:apply(M, command_list, [S]) || M <- tx_models()])),
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
  Forks = #{1=> 0, 2 => 3, 3 => 6, 4 => 9},
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
        Accounts = maps:get(accounts, S, []),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            measure(accounts, length(Accounts),
            features(call_features(H),
            stats(call_features(H),
                  pretty_commands(?MODULE, Cmds, {H, S, Res}, Res == ok)))))))
    end)))).

stats(Features, Prop) ->
  {Atoms, Rest} = lists:partition(fun is_atom/1, Features),
  aggregate(with_title(atoms), Atoms, aggregate_feats([tx, correct, spend], Rest, Prop)).

aggregate_feats([], _, Prop) -> Prop;
aggregate_feats([Tag | Kinds], Features, Prop) ->
    {Tuples, Rest} = lists:partition(fun(X) -> element(1, X) == Tag end, Features),
    aggregate(with_title(Tag), Tuples, aggregate_feats(Kinds, Rest, Prop)).

%% --- Helper functions ---

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
