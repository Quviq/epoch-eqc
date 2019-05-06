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

%%-define(TXS, txs_eqc).
-define(TXS, txs_ga_eqc).

-compile([export_all, nowarn_export_all]).


%% -- State and state functions ----------------------------------------------
initial_state() ->
    ?TXS:initial_state().

command(S) ->
    ?LET(Cmd, ?TXS:command(S),
         case Cmd of
             {call, M, F, Args} ->
                 case lists:member(F, [init, newkey, mine, multi_mine]) of
                     true -> Cmd;
                     false -> {call, ?MODULE, F, [ M, ?LET(Incorrect,sublist(maps:values(maps:get(keys, S, #{}))),
                                                        gen_signers(signers(S, F, Args), Incorrect)) | Args]}
                 end;
             _ -> Cmd
         end).


precondition(S, {call, ?MODULE, F, [M, {correct, Signers} | Args]}) ->
    lists:all(fun(Signer) ->
                      lists:member(Signer, maps:values(maps:get(keys, S, #{})))
              end, Signers) andalso
        lists:sort(signers(S, F, Args)) == lists:sort(Signers) andalso
        ?TXS:precondition(S, {call, M, F, Args});
precondition(S, {call, ?MODULE, F, [M, {_, Signers} | Args]}) ->  %% faulty signers
    lists:all(fun(Signer) ->
                      lists:member(Signer, maps:values(maps:get(keys, S, #{})))
              end, Signers) andalso
        lists:sort(signers(S, F, Args)) /= lists:sort(Signers) andalso
        ?TXS:precondition(S, {call, M, F, Args});
precondition(S, {call, M, F, Args}) when M /= ?MODULE ->
    ?TXS:precondition(S, {call, M, F, Args}).


adapt(S, {call, ?MODULE, F, [M, {Tag, Signers} | Args]}) ->
    case ?TXS:adapt(S, {call, M, F, Args}) of
        false -> false;
        NewArgs ->
            case Tag of
                correct ->
                    [ M, {correct, signers(S, F, NewArgs)} | NewArgs];
                _ ->
                    [ M, {Tag, Signers} | NewArgs]
            end
    end;
adapt(S, {call, M, F, Args}) ->
    ?TXS:adapt(S, {call, M, F, Args}).

next_state(S, _V, {call, ?MODULE, _F, [_M, {faulty, _Signers} | _Args]}) ->
    S;
next_state(S, V, {call, ?MODULE, F, [M, {correct, _Signers} | Args]}) ->
    ?TXS:next_state(S, V, {call, M, F, Args});
next_state(S, V, {call, M, F, Args}) ->
    ?TXS:next_state(S, V, {call, M, F, Args}).


postcondition(_S, {call, ?MODULE, _F, [_M, {faulty, _Signers} | _Args]}, Res) ->
    eq(Res, {error, signature_check_failed});
postcondition(S, {call, ?MODULE, F, [M, {correct, _Signers} | Args]}, Res) ->
    ?TXS:postcondition(S, {call, M, F, Args}, Res);
postcondition(S, {call, M, F, Args}, Res) ->
    ?TXS:postcondition(S, {call, M, F, Args}, Res).


call_features(S, {call, ?MODULE, F, [M, {correct, _Signers} | Args]}, Res) ->
    ?TXS:call_features(S, {call, M, F, Args}, Res);
call_features(_S, {call, ?MODULE, F, [_M, {faulty, _Signers} | _Args]}, Res) ->
    [{correct, false}, {F, Res}];
call_features(S, {call, M, F, Args}, Res) ->
    ?TXS:call_features(S, {call, M, F, Args}, Res).



all_command_names() ->
    ?TXS:all_command_names().

has_correct_signers(S, {call, ?MODULE, F, [_M, {_Tag, Signers} | Args]}) ->
    lists:sort(signers(S, F, Args)) == lists:sort(Signers);
has_correct_signers(_S, _) ->
    true.

%% -- Operations -------------------------------------------------------------

spend(_, Signers, Height, {_, _Sender}, _Receiver, Tx) ->
    apply_transaction(Signers, Height, aec_spend_tx, Tx).

register_oracle(_, Signers, Height, {_, _Sender}, Tx) ->
    apply_transaction(Signers, Height, aeo_register_tx, Tx).

extend_oracle(_, Signers, Height, _Oracle, Tx) ->
    apply_transaction(Signers, Height, aeo_extend_tx, Tx).

query_oracle(_, Signers, Height, {_, _Sender}, _Oracle, Tx) ->
    apply_transaction(Signers, Height, aeo_query_tx, Tx).

response_oracle(_, Signers, Height, QueryId, Tx) ->
    %% possibly use M and call M:response_oracle_tx(QueryId, Tx)
    NewTx = txs_eqc:response_oracle_tx(QueryId, Tx),
    apply_transaction(Signers, Height, aeo_response_tx, NewTx).

channel_create(_, Signers, Height, _Initiator, _Responder, Tx) ->
    NewTx = txs_eqc:channel_create_tx(Tx),
    apply_transaction(Signers, Height, aesc_create_tx, NewTx).

channel_deposit(_, Signers, Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_deposit_tx(ChannelId, Party, channel_add_id(ChannelId, Tx)),
    apply_transaction(Signers, Height, aesc_deposit_tx, NewTx).

channel_withdraw(_, Signers, Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_withdraw_tx(ChannelId, Party, channel_add_id(ChannelId, Tx)),
    apply_transaction(Signers, Height, aesc_withdraw_tx, NewTx).

channel_close_mutual(_, Signers, Height, ChannelId, _Party, Tx) ->
    NewTx = channel_add_id(ChannelId, Tx),
    apply_transaction(Signers, Height, aesc_close_mutual_tx, NewTx).

channel_settle(_, Signers, Height, ChannelId, _Party, Tx) ->
    NewTx = channel_add_id(ChannelId, Tx),
    apply_transaction(Signers, Height, aesc_settle_tx, NewTx).

%% Describe this channel_id trick!
channel_close_solo(_, Signers, Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_close_solo_tx(ChannelId, Party, channel_add_id(ChannelId, Tx)),
    apply_transaction(Signers, Height, aesc_close_solo_tx, NewTx).

channel_add_id({Initiator, N, Responder}, Tx) ->
     Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder))}.

ns_preclaim(_, Signers, Height, _Sender, {_Name,_Salt}, Tx) ->
    apply_transaction(Signers, Height, aens_preclaim_tx, Tx).

ns_claim(_, Signers, Height, _Sender, Tx) ->
    apply_transaction(Signers, Height, aens_claim_tx, Tx).

ns_update(_, Signers, Height, _Name, _Sender, _NameAccount, Tx) ->
    apply_transaction(Signers, Height, aens_update_tx, Tx).

ns_transfer(_, Signers, Height, _Sender, _Receiver, _Name, Tx) ->
    apply_transaction(Signers, Height, aens_transfer_tx, Tx).

ns_revoke(_, Signers, Height, {_, _Sender}, _Name, Tx) ->
    apply_transaction(Signers, Height, aens_revoke_tx, Tx).

contract_create(_, Signers, Height, {_, _Sender}, Name, CompilerVersion, Tx) ->
    NewTx =  txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
    apply_transaction(Signers, Height, aect_create_tx, NewTx).

contract_call(_, Signers, Height, _, Contract, Tx) ->
    NewTx = txs_eqc:contract_call_tx(Contract, Tx),
    apply_transaction(Signers, Height, aect_call_tx, NewTx).

ga_attach(_, Signers, Height, _, Name, CompilerVersion, Tx) ->
    NewTx = ?TXS:ga_attach_tx(Name, CompilerVersion, Tx),
    apply_transaction(Signers, Height, aega_attach_tx, NewTx).


%%% helper functions

gen_signers(Correct, Incorrect) ->
    case lists:sort(Correct) == lists:sort(Incorrect) of
        true ->
            {correct, Correct};
        false ->
           weighted_default({95, {correct, Correct}}, {5, {faulty, Incorrect}})
    end.

signers(F, Args) when F == extend_oracle ->
    [lists:nth(2, Args)];
signers(F, Args) when F == channel_create  ->
    [lists:nth(2, Args), lists:nth(3, Args)];
signers(response_oracle, Args) ->
    {_Sender, _Nonce, Oracle} = lists:nth(2, Args),
    [Oracle];
signers(F, Args) when F == channel_deposit; F == channel_withdraw;
                     F == channel_close_mutual; F == channel_close_solo;
                     F == channel_settle ->
    Party = lists:nth(3, Args),
    {Initiator, _, Responder} = lists:nth(2, Args),
    Sender = case Party of initiator -> Initiator; responder -> Responder end,
    case F of
        channel_close_solo -> [Sender];
        channel_settle -> [Sender];
        _ -> [Initiator, Responder]
    end;
signers(ns_update, Args) ->
    {_SenderTag, Sender} = lists:nth(3, Args),
    [Sender];
signers(_Kind, Args) ->
    %% io:format("Kind ~p ~p\n", [_Kind, Args]),
    {_SenderTag, Sender} = lists:nth(2, Args),
    [Sender].


signers(S, F, Args) ->
    [maps:get(Signer, maps:get(keys, S)) || Signer <- signers(F, Args)].


%% -- Property ---------------------------------------------------------------

%% NOte that weight for sub model is still computed by that weight function.
%% weight for adding a new command should be organized in frequency in command generator

prop_txs() ->
    prop_txs(3).

prop_txs(Fork) ->
    application:load(aesophia),  %% Since we do in_parallel, we may have a race in line 86 of aesophia_compiler
    ?TXS:propsetup(Fork,
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

apply_transaction({_Tag, Signers}, Height, Kind, Tx) ->
    Env      = aetx_env:tx_env(Height),
    Trees    = get(trees),
    AeTx     = txs_eqc:create_aetx(Kind, Tx),
    BinTx = aec_governance:add_network_id(aetx:serialize_to_binary(AeTx)),
    Signatures = [ enacl:sign_detached(BinTx, Signer) || Signer <- Signers ],
    SignedTx = aetx_sign:new(AeTx, Signatures),
    %% When we use strict, we see errors returned, otherwise only invalid txs returned
    case aec_trees:apply_txs_on_state_trees_strict([SignedTx], Trees, Env) of
        {ok, _ValidTxs, InvalidTxs, NewTrees, _} ->
            put(trees, NewTrees),
            case InvalidTxs of
                [] -> ok;
                _  -> {error, signatures}
            end;
        Other ->
            Other
    end.
