%%% @author Thomas Arts
%%% @doc Sign transactions
%%%
%%% @end
%%% Created : 27 Mar 2019 by Thomas Arts

-module(txs_sign_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-eqc_group_commands(false).
-define(PatronAmount, 100000000000001).  %% read from file?


-compile([export_all, nowarn_export_all]).


%% -- State and state functions ----------------------------------------------
initial_state() ->
    txs_eqc:initial_state().

command(S) ->
    ?LET(Cmd, txs_eqc:command(S),
         case Cmd of
             {call, txs_eqc, F, Args} ->
                 case lists:member(F, [init, newkey, mine, multi_mine]) of
                     true -> Cmd;
                     false -> {call, ?MODULE, F, [ ?LET(Incorrect,sublist(maps:values(maps:get(keys, S, #{}))),
                                                        gen_signers(signers(S, F, Args), Incorrect)) | Args]}
                 end;
             _ -> Cmd
         end).

gen_signers(Correct, Incorrect) ->
    case lists:sort(Correct) == lists:sort(Incorrect) of
        true ->
            {correct, Correct};
        false ->
           weighted_default({99, {correct, Correct}}, {1, {faulty, Incorrect}})
    end.

precondition(S, {call, txs_eqc, F, Args}) ->
    txs_eqc:precondition(S, {call, txs_eqc, F, Args});
precondition(S, {call, ?MODULE, F, [{_, Signers} | Args]}) ->
    lists:all(fun(Signer) ->
                      lists:member(Signer, maps:values(maps:get(keys, S, #{})))
              end, Signers) andalso
        txs_eqc:precondition(S, {call, txs_eqc, F, Args}).

adapt(S, {call, txs_eqc, F, Args}) ->
    case txs_eqc:adapt(S, {call, txs_eqc, F, Args}) of
        false -> false;
        NewArgs ->
            {call, txs_eqc, F, NewArgs}
    end;
adapt(S, {call, ?MODULE, F, [Signers | Args]}) ->
    case txs_eqc:adapt(S, {call, txs_eqc, F, Args}) of
        false   -> false;
        NewArgs -> {call, ?MODULE, F, [Signers | NewArgs]}
    end.

next_state(S, V, {call, txs_eqc, F, Args}) ->
    txs_eqc:next_state(S, V, {call, txs_eqc, F, Args});
next_state(S, V, {call, ?MODULE, F, [{correct, _Signers} | Args]}) ->
    txs_eqc:next_state(S, V, {call, txs_eqc, F, Args});
next_state(S, _V, {call, ?MODULE, _F, [{faulty, _Signers} | _Args]}) ->
    S.

postcondition(S, {call, txs_eqc, F, Args}, Res) ->
    txs_eqc:postcondition(S, {call, txs_eqc, F, Args}, Res);
postcondition(S, {call, ?MODULE, F, [{correct, _Signers} | Args]}, Res) ->
    txs_eqc:postcondition(S, {call, txs_eqc, F, Args}, Res);
postcondition(_S, {call, ?MODULE, _F, [{faulty, _Signers} | _Args]}, Res) ->
    eq(Res, {error, signatures}).

call_features(S, {call, txs_eqc, F, Args}, Res) ->
    txs_eqc:call_features(S, {call, txs_eqc, F, Args}, Res);
call_features(S, {call, ?MODULE, F, [{correct, _Signers} | Args]}, Res) ->
    txs_eqc:call_features(S, {call, txs_eqc, F, Args}, Res);
call_features(_S, {call, ?MODULE, _, [{faulty, _Signers} | _Args]}, Res) ->
    [{correct, false}, {spend, Res}].


all_command_names() ->
    txs_eqc:all_command_names().

%% -- Operations -------------------------------------------------------------

spend(Signers, Height, {_, _Sender}, _Receiver, Tx) ->
    apply_transaction(Signers, Height, aec_spend_tx, Tx).

register_oracle(Signers, Height, {_, _Sender}, Tx) ->
    apply_transaction(Signers, Height, aeo_register_tx, Tx).

extend_oracle(Signers, Height, _Oracle, Tx) ->
    apply_transaction(Signers, Height, aeo_extend_tx, Tx).

query_oracle(Signers, Height, {_, _Sender}, _Oracle, Tx) ->
    apply_transaction(Signers, Height, aeo_query_tx, Tx).

response_oracle(Signers, Height, QueryId, Tx) ->
    NewTx = txs_eqc:response_oracle_tx(QueryId, Tx),
    apply_transaction(Signers, Height, aeo_response_tx, NewTx).

channel_create(Signers, Height, _Initiator, _Responder, Tx) ->
    NewTx = txs_eqc:channel_create_tx(Tx),
    apply_transaction(Signers, Height, aesc_create_tx, NewTx).

channel_deposit(Signers, Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_deposit_tx(ChannelId, Party, channel_add_id(ChannelId, Tx)),
    apply_transaction(Signers, Height, aesc_deposit_tx, NewTx).

channel_withdraw(Signers, Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_withdraw_tx(ChannelId, Party, channel_add_id(ChannelId, Tx)),
    apply_transaction(Signers, Height, aesc_withdraw_tx, NewTx).

channel_close_mutual(Signers, Height, ChannelId, _Party, Tx) ->
    NewTx = channel_add_id(ChannelId, Tx),
    apply_transaction(Signers, Height, aesc_close_mutual_tx, NewTx).

%% Describe this channel_id trick!
channel_close_solo(Signers, Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_close_solo_tx(ChannelId, Party, channel_add_id(ChannelId, Tx)),
    apply_transaction(Signers, Height, aesc_close_solo_tx, NewTx).

channel_add_id({Initiator, N, Responder}, Tx) ->
     Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder))}.

ns_preclaim(Signers, Height, _Sender, {_Name,_Salt}, Tx) ->
    apply_transaction(Signers, Height, aens_preclaim_tx, Tx).

ns_claim(Signers, Height, _Sender, Tx) ->
    apply_transaction(Signers, Height, aens_claim_tx, Tx).

ns_update(Signers, Height, _Name, _Sender, _NameAccount, Tx) ->
    apply_transaction(Signers, Height, aens_update_tx, Tx).

ns_transfer(Signers, Height, _Sender, _Receiver, _Name, Tx) ->
    apply_transaction(Signers, Height, aens_transfer_tx, Tx).

ns_revoke(Signers, Height, {_, _Sender}, _Name, Tx) ->
    apply_transaction(Signers, Height, aens_revoke_tx, Tx).

contract_create(Signers, Height, {_, _Sender}, Name, CompilerVersion, Tx) ->
    NewTx =  txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
    apply_transaction(Signers, Height, aect_create_tx, NewTx).

contract_call(Signers, Height, _, Contract, Tx) ->
    NewTx = txs_eqc:contract_call_tx(Contract, Tx),
    apply_transaction(Signers, Height, aect_call_tx, NewTx).


origin(F, Args) when F == extend_oracle; F == channel_create ->
    lists:nth(2, Args);
origin(response_oracle, Args) ->
    {_Sender, _Nonce, Oracle} = lists:nth(2, Args),
    Oracle;
origin(F, Args) when F == channel_deposit; F == channel_withdraw;
                     F == channel_close_mutual; F == channel_close_solo;
                     F == channel_settle ->
    Party = lists:nth(3, Args),
    {Initiator, _, Responder} = lists:nth(2, Args),
    case Party of initiator -> Initiator; responder -> Responder end;
origin(ns_update, Args) ->
    {_SenderTag, Sender} = lists:nth(3, Args),
    Sender;
origin(_Kind, Args) ->
    {_SenderTag, Sender} = lists:nth(2, Args),
    Sender.

signers(S, F, Args) ->
    Origin = origin(F, Args),
    [maps:get(Origin, maps:get(keys, S))].


%% -- Property ---------------------------------------------------------------

%% NOte that weight for sub model is still computed by that weight function.
%% weight for adding a new command should be organized in frequency in command generator

prop_txs() ->
    prop_txs(3).

prop_txs(Fork) ->
    application:load(aecore),
    application:set_env(aecore, hard_forks,
                                   #{<<"1">> => 0, <<"2">> => Fork, <<"3">> => 2*Fork}),
    application:load(aesophia),  %% Since we do in_parallel, we may have a race in line 86 of aesophia_compiler
    txs_eqc:compile_contracts(),
    ?SETUP(fun() ->
                   {ok, Dir} = file:get_cwd(),
                   DataDir = application:get_env(setup, data_dir),
                   case lists:reverse(filename:split(Dir)) of
                       [_, "eqc" | _] ->
                           application:set_env(setup, data_dir, "../../data");
                       _ ->
                           application:set_env(setup, data_dir, "data")
                   end,
                   fun() ->
                           application:set_env(setup, data_dir, DataDir)
                   end
           end,
    eqc:dont_print_counterexample(
    in_parallel(
    ?FORALL(Cmds, commands(?MODULE),
    begin
        put(trees, undefined),
        {H, S, Res} = run_commands(Cmds),
        Height = maps:get(height, S, 0),
        TreesTotal =
            case get(trees) of
                undefined -> #{};
                Trees -> aec_trees:sum_total_coin(Trees)
            end,
        Total = lists:sum(maps:values(TreesTotal)),
        FeeTotal =  lists:sum([ Fee || {Fee, _} <- maps:get(fees, S, [])]),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            features(call_features(H),
            txs_eqc:aggregate_feats([atoms, correct, protocol, contract_call_fun | all_command_names()], call_features(H),
                ?WHENFAIL(eqc:format("Total = ~p~nFeeTotal = ~p~n", [TreesTotal, FeeTotal]),
                          pretty_commands(?MODULE, Cmds, {H, S, Res},
                              conjunction([{result, Res == ok},
                                           {total, Total == 0 orelse equals(Total, ?PatronAmount - FeeTotal)}]))))))))
    end)))).


%% -----

%% apply_transaction(Signers, Height, Kind, Tx) ->
%%     io:format("Signing with ~p\n", [Signers]),
%%     txs_eqc:apply_transaction(Height, Kind, Tx);
apply_transaction({_Tag, Signers}, Height, Kind, Tx) ->
    Env      = aetx_env:tx_env(Height),
    Trees    = get(trees),
    AeTx     = txs_eqc:create_aetx(Kind, Tx),
    BinTx = aec_governance:add_network_id(aetx:serialize_to_binary(AeTx)),
    Signatures = [ enacl:sign_detached(BinTx, Signer) || Signer <- Signers ],
    SignedTx = aetx_sign:new(AeTx, Signatures),
    case aec_trees:apply_txs_on_state_trees([SignedTx], Trees, Env) of
        {ok, _ValidTxs, InvalidTxs, NewTrees, _} ->
            put(trees, NewTrees),
            case InvalidTxs of
                [] -> ok;
                _  -> {error, signatures}
            end;
        Other ->
            Other
    end.
