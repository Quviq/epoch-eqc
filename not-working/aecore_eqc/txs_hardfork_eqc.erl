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

-module(txs_hardfork_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-eqc_group_commands(false).

-compile([export_all, nowarn_export_all]).

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
    txs_eqc:postcondition(S, {call, txs_eqc, F, Args}, Res).

call_features(S, {call, _M, F, Args}, Res) ->
    txs_eqc:call_features(S, {call, txs_eqc, F, Args}, Res).

all_command_names() ->
    txs_eqc:all_command_names().

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
init(Height) ->
    txs_eqc:init(Height).

%% --- Operation: mine ---
mine(Height) ->
    txs_eqc:mine(Height).

multi_mine(Height, Blocks) ->
    txs_eqc:multi_mine(Height, Blocks).

%% --- Operation: spend ---
spend(Height, _Sender, _Receiver, Tx) ->
    txs_eqc:apply_transaction(Height, aec_spend_tx, Tx).

%% --- Operation: register_oracle ---
register_oracle(Height, _Sender, Tx) ->
    txs_eqc:apply_transaction(Height, aeo_register_tx, Tx).

%% --- Operation: extend_oracle ---
extend_oracle(Height, _Oracle, Tx) ->
    txs_eqc:apply_transaction(Height, aeo_extend_tx, Tx).

%% --- Operation: query_oracle ---
query_oracle(Height, _Sender, _Oracle, Tx) ->
    txs_eqc:apply_transaction(Height, aeo_query_tx, Tx).

%% --- Operation: response_oracle ---
response_oracle(Height, _QueryId, Tx) ->
    txs_eqc:apply_transaction(Height, aeo_response_tx, Tx).

%% --- Operation: channel_create ---
channel_create(Height, _Initiator, _Responder, Tx) ->
    txs_eqc:apply_transaction(Height, aesc_create_tx, Tx).

%% --- Operation: channel_deposit ---
channel_deposit(Height, _Channeld, _Party, Tx) ->
    txs_eqc:apply_transaction(Height, aesc_deposit_tx, Tx).

%% --- Operation: channel_withdraw ---
channel_withdraw(Height, _Channeld, _Party, Tx) ->
    txs_eqc:apply_transaction(Height, aesc_withdraw_tx, Tx).

%% --- Operation: channel_close_mutual ---
channel_close_mutual(Height, _Channeld, _Party, Tx) ->
    txs_eqc:apply_transaction(Height, aesc_close_mutual_tx, Tx).

%% --- Operation: ns_preclaim ---
ns_preclaim(Height, _Sender, {_Name,_Salt}, Tx) ->
    txs_eqc:apply_transaction(Height, aens_preclaim_tx, Tx).
%% --- Operation: claim ---
ns_claim(Height, _Sender, Tx) ->
    txs_eqc:apply_transaction(Height, aens_claim_tx, Tx).

%% --- Operation: claim_update ---
ns_update(Height, _Name, _Sender, _NameAccount, Tx) ->
    txs_eqc:apply_transaction(Height, aens_update_tx, Tx).

%% --- Operation: ns_revoke ---
ns_revoke(Height, _Sender, _Name, Tx) ->
    txs_eqc:apply_transaction(Height, aens_revoke_tx, Tx).

%% --- Operation: ns_transfer ---
ns_transfer(Height, _Sender, _Receiver, _Name, Tx) ->
    txs_eqc:apply_transaction(Height, aens_transfer_tx, Tx).

%% --- Operation: create_contract ---
contract_create(Height, {_, _Sender}, Name, CompilerVersion, Tx) ->
    NewTx = txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
    txs_eqc:apply_transaction(Height, aect_create_tx, NewTx).

%% -- Property ---------------------------------------------------------------

prop_txs() ->
    ?SETUP(
    fun() ->
        _ = application:load(aecore),
        undefined = application:get_env(aecore, hard_forks),
        ok = application:set_env(aecore, hard_forks, #{<<"1">> => 0, <<"2">> => 3}),
        undefined = application:get_env(setup, data_dir),
        ok = application:set_env(setup, data_dir, "data"),
        fun() ->
            ok = application:unset_env(setup, data_dir),
            ok = application:unset_env(aecore, hard_forks)
        end
    end,
   %% eqc:dont_print_counterexample(
    in_parallel(
    ?FORALL(Cmds, commands(?MODULE),
    begin
        {H, S, Res} = run_commands(Cmds),
        Height = maps:get(height, S, 0),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            features(call_features(H),
            aggregate_feats([atoms, correct, protocol | all_command_names()], call_features(H),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok))))))
    end))).

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
    more_bugs(eqc:testing_time(Time, prop_txs()), 20, Bugs).

%% -- State update and query functions ---------------------------------------



