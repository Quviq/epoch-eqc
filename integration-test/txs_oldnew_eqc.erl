%%% @author Thomas Arts
%%% @doc
%%%
%%%      Start a second epoch node with old code using something like:
%%%            ./rebar3 as test shell --sname oldepoch@localhost --apps ""
%%%            we need the test profile to assure that the cookie is set to aeternity_cookie
%%%            The test profile has a name and a cookie set in {dist_node, ...}
%%%
%%%       TODO:
%%%          - better shrinking for channel Ids (they contain the nonce...) - use good/bad tagging?
%%%          - add oracle names to the state such that we can use names with oracles
%%%          - add names to oracle txs
%%%          - add contract txs (quite a lot of work, I fear)
%%%          - tune distribution (all EXIT differences should show up in features)
%%%          - mock aec_governance values to test for name revoke re-use etc.
%%% @end
%%% Created : 23 Jan 2019 by Thomas Arts

-module(txs_oldnew_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-eqc_group_commands(false).

-compile([export_all, nowarn_export_all]).
-define(REMOTE_NODE, 'oldepoch@localhost').
-define(NAMEFRAGS, ["foo", "bar", "baz"]).

%% -- State and state functions ----------------------------------------------
initial_state() ->
    txs_eqc:initial_state().

command(S) ->
    ?LET({call, txs_eqc, F, Args}, txs_eqc:command(S),
         {call, ?MODULE, F, Args}).

precondition(S, {call, _M, F, Args}) ->
    txs_eqc:precondition(S, {call, txs_eqc, F, Args}).

adapt(S, {call, _M, F, Args}) ->
    txs_eqc:adapt(S, {call, txs_eqc, F, Args}).

next_state(S, V, {call, _M, F, Args}) ->
    txs_eqc:next_state(S, V, {call, txs_eqc, F, Args}).

postcondition(S, {call, _M, F, Args}, Res) ->
    case Res of
        {'EXIT', _} -> aec_hard_forks:protocol_effective_at_height(maps:get(height, S, 0)) > 1 orelse
                           valid_mismatch(Res);
        _ ->  txs_eqc:postcondition(S, {call, txs_eqc, F, Args}, Res)
    end.

call_features(S, {call, _M, F, Args}, Res) ->
    txs_eqc:call_features(S, {call, txs_eqc, F, Args}, Res).

all_command_names() ->
    txs_eqc:all_command_names().

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
init(_Height) ->
    {PA, PAmount} = txs_eqc:patron(),
    Trees = rpc(aec_trees, new_without_backend, [], fun hash_equal/2),
    EmptyAccountTree = rpc(aec_trees, accounts, [Trees]),
    Account = rpc(aec_accounts, new, [PA, PAmount]),
    AccountTree = rpc(aec_accounts_trees, enter, [Account, EmptyAccountTree]),
    InitialTrees = rpc(aec_trees, set_accounts, [Trees, AccountTree], fun hash_equal/2),
    put(trees, InitialTrees),
    InitialTrees,
    ok.

%% --- Operation: mine ---
mine(Height) ->
    Trees = get(trees),
    NewTrees = rpc(aec_trees, perform_pre_transformations, [Trees, Height + 1], fun hash_equal/2),
    put(trees, NewTrees),
    NewTrees,
    ok.

multi_mine(Height, Blocks) ->
    Trees  = get(trees),
    Trees1 = lists:foldl(
        fun(H, T) -> aec_trees:perform_pre_transformations(T, H + 1) end,
        Trees, lists:seq(Height, Height + Blocks - 1)),

    put(trees, Trees1),
    ok.

%% --- Operation: spend ---
spend(Height, _Sender, _Receiver, Tx) ->
    apply_transaction(Height, aec_spend_tx, Tx).

%% --- Operation: register_oracle ---
register_oracle(Height, _Sender, Tx) ->
    apply_transaction(Height, aeo_register_tx, Tx).

%% --- Operation: extend_oracle ---
extend_oracle(Height, _Oracle, Tx) ->
    apply_transaction(Height, aeo_extend_tx, Tx).

%% --- Operation: query_oracle ---
query_oracle(Height, _Sender, _Oracle, Tx) ->
    apply_transaction(Height, aeo_query_tx, Tx).

%% --- Operation: response_oracle ---
response_oracle(Height, _QueryId, Tx) ->
    apply_transaction(Height, aeo_response_tx, Tx).

%% --- Operation: channel_create ---
channel_create(Height, _Initiator, _Responder, Tx) ->
    apply_transaction(Height, aesc_create_tx, Tx).

%% --- Operation: channel_deposit ---
channel_deposit(Height, _Channeld, _Party, Tx) ->
    apply_transaction(Height, aesc_deposit_tx, Tx).

%% --- Operation: channel_withdraw ---
channel_withdraw(Height, _Channeld, _Party, Tx) ->
    apply_transaction(Height, aesc_withdraw_tx, Tx).

%% --- Operation: channel_close_mutual ---
channel_close_mutual(Height, _Channeld, _Party, Tx) ->
    apply_transaction(Height, aesc_close_mutual_tx, Tx).

%% --- Operation: ns_preclaim ---
ns_preclaim(Height, _Sender, {_Name,_Salt}, Tx) ->
    apply_transaction(Height, aens_preclaim_tx, Tx).
%% --- Operation: claim ---
ns_claim(Height, _Sender, Tx) ->
    apply_transaction(Height, aens_claim_tx, Tx).

%% --- Operation: claim_update ---
ns_update(Height, _Name, _Sender, _NameAccount, Tx) ->
    apply_transaction(Height, aens_update_tx, Tx).

%% --- Operation: ns_revoke ---
ns_revoke(Height, _Sender, _Name, Tx) ->
    apply_transaction(Height, aens_revoke_tx, Tx).

%% --- Operation: ns_transfer ---
ns_transfer(Height, _Sender, _Receiver, _Name, Tx) ->
    apply_transaction(Height, aens_transfer_tx, Tx).

contract_create(Height, {_, _Sender}, {File, Args, _GasFun, _}, CompilerVersion, Tx) ->
    {ok, Contract} = aect_test_utils:read_contract(File),
    {ok, Code}     = aect_test_utils:compile_contract(CompilerVersion, File),
    {ok, CallData} = aect_sophia:encode_call_data(Contract, <<"init">>, Args),
    NTx = maps:update_with(vm_version, fun(sophia_1) -> 1;
                                          (solidity) -> 2;
                                          (sophia_2) -> 3;
                                          (N) -> N
                                       end, Tx),
    apply_transaction(Height, aect_create_tx, NTx#{code => Code, call_data => CallData}).

%% -- Property ---------------------------------------------------------------

prop_tx_primops() ->
   %% eqc:dont_print_counterexample(
    in_parallel(
    ?FORALL(Cmds, commands(?MODULE),
    begin
        pong = net_adm:ping(?REMOTE_NODE),
        rpc(application, load, [aecore]),
        rpc(application, set_env, [aecore, hard_forks,
                                   #{<<"1">> => 0, <<"2">> => 3}]),

        {H, S, Res} = run_commands(Cmds),
        Height = maps:get(height, S, 0),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            features(call_features(H),
            aggregate_feats([atoms, correct | all_command_names()], call_features(H),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok))))))
    end)).

aggregate_feats([], [], Prop) -> Prop;
aggregate_feats([atoms | Kinds], Features, Prop) ->
    {Atoms, Rest} = lists:partition(fun is_atom/1, Features),
    aggregate(with_title(atoms), Atoms, aggregate_feats(Kinds, Rest, Prop));
aggregate_feats([Tag | Kinds], Features, Prop) ->
    {Tuples, Rest} = lists:partition(fun(X) -> is_tuple(X) andalso element(1, X) == Tag end, Features),
    aggregate(with_title(Tag), [ Arg || {_, Arg} <- Tuples ], aggregate_feats(Kinds, Rest, Prop)).

bugs() -> bugs(10).

bugs(N) -> bugs(N, []).

bugs(Time, Bugs) ->
    more_bugs(eqc:testing_time(Time, prop_tx_primops()), 20, Bugs).

%% -- State update and query functions ---------------------------------------


strict_equal(X, Y) ->
     case X == Y of
         true -> X;
         false -> exit({different, X, Y})
     end.

hash_equal(X, Y) ->
     case {X, Y} of
         {{ok, L}, {ok, R}} ->
             case aec_trees:hash(L) == aec_trees:hash(R) of
                 true -> X;
                 false -> exit({hash_differs, X, Y})
             end;
         {E, E} -> E;
         {L, R} when is_tuple(L) andalso element(1, L)==trees,
                is_tuple(R) andalso element(1, R)==trees->
             %% Compare two trees
             case aec_trees:hash(L) == aec_trees:hash(R) of
                 true -> X;
                 false -> exit({hash_differs, X, Y})
             end;
         _ -> exit({different, X, Y})
     end.

rpc(Module, Fun, Args) ->
    rpc(Module, Fun, Args, fun(X,Y) -> strict_equal(X, Y) end).

rpc(Module, Fun, Args, InterpretResult) ->
    Local = rpc:call(node(), Module, Fun, Args, 1000),
    Remote = rpc:call(?REMOTE_NODE, Module, Fun, Args, 1000),
    eq_rpc(Local, Remote, InterpretResult).

eq_rpc(Local, Remote) ->
    eq_rpc(Local, Remote, fun hash_equal/2).

eq_rpc(Local, Remote, InterpretResult) ->
    case {Local, Remote} of
        {{badrpc, {'EXIT', {E1, ST}}},{badrpc, {'EXIT', {E2, _}}}} when E1 == E2 ->
            {'EXIT', {E1, ST}};
        _ ->
            InterpretResult(Local, Remote)
    end.

apply_transaction(Height, aect_create_tx, TxArgs0) ->
    TxArgs = untag_nonce(TxArgs0),
    {ok, RemoteTx} = rpc:call(?REMOTE_NODE, aect_create_tx, new, [TxArgs]),
    {ok, Tx} = aect_create_tx:new(TxArgs),
    apply_tx(Height, RemoteTx, Tx);
apply_transaction(Height, TxMod, TxArgs0) ->
    TxArgs = untag_nonce(TxArgs0),
    {ok, Tx} = rpc(TxMod, new, [TxArgs]),
    apply_tx(Height, Tx, Tx).

apply_tx(Height, RemoteTx, LocalTx) ->
    EnvRemote = rpc:call(?REMOTE_NODE, aetx_env, tx_env, [Height]),
    Env = aetx_env:tx_env(Height),
    Trees = get(trees),

    Remote = case rpc:call(?REMOTE_NODE, aetx, check, [RemoteTx, Trees, EnvRemote], 1000) of
                {ok, RemoteTrees} -> rpc:call(?REMOTE_NODE, aetx, process, [RemoteTx, RemoteTrees, EnvRemote], 1000);
                RemoteErr         -> RemoteErr
            end,
    Local = case rpc:call(node(), aetx, process, [LocalTx, Trees, Env], 1000) of
                {ok, Ts, _} -> {ok, Ts};
                Ret -> Ret
            end,

    case catch eq_rpc(Local, Remote) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

untag_nonce(M = #{nonce := {_Tag, N}}) -> M#{nonce := N};
untag_nonce(M)                         -> M.

valid_mismatch({'EXIT',{different, {error, account_nonce_too_low},
                        {error, _}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_nonce_too_high},
                         {error, _}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_not_found},
                         {error, _}}}) -> true;
valid_mismatch({'EXIT', {different, {error, insufficient_funds},
                         {error, multiple_namespaces}}}) -> true;
valid_mismatch({'EXIT', {different, {error, name_does_not_exist},
                         {error, name_not_found}}}) ->  true;
valid_mismatch({'EXIT', {different, {error, name_does_not_exist},
                         {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, pointer_id_not_found},
                         {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, name_revoked},
                         {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT',{different, {error, illegal_vm_version},
                        {badrpc, _}}}) -> true;

%% Close mutual
valid_mismatch(_) -> false.

%% -- Generators -------------------------------------------------------------
