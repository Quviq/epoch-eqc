%%% @author Thomas Arts
%%% @doc Model to introduce a state variable defining the fault injection on the next signing.
%%%
%%%      Not ethat Generalized accounts have no signature, thus dropping it woud not be an error
%%%      signing it actually would
%%%       This needs to be compenstated for in ???
%%% @end
%%% Created : 2 Aug 2019 by Thomas Arts

-module(txs_sign_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).


%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{next_signing => correct}.

signing_args(_S) ->
    [frequency([{99, correct},
                {1, drop_first_signature},
                {1, drop_last_signature},
                {1, replace_first},
                {1, replace_last}
               ])].

signing(Injection) ->
    Injection.

signing_next(S, _, [Injection]) ->
    S#{next_signing => Injection}.

signing_features(_S, [Injection], _Res) ->
    [{signing, Injection}].



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

channel_slash(_, Signers, Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_slash_tx(ChannelId, Party, channel_add_id(ChannelId, Tx)),
    apply_transaction(Signers, Height, aesc_slash_tx, NewTx).

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
    NewTx = txs_ga_eqc:ga_attach_tx(Name, CompilerVersion, Tx),
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
                     F == channel_settle; F == channel_slash ->
    Party = lists:nth(3, Args),
    {Initiator, _, Responder} = lists:nth(2, Args),
    Sender = case Party of initiator -> Initiator; responder -> Responder end,
    case F of
        channel_close_solo -> [Sender];
        channel_slash -> [Sender];
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
    %%TODO check that non of the signers is a GA account, because they need to sign differently
    [maps:get(Signer, maps:get(keys, S)) || Signer <- signers(F, Args),
                                            maps:get(Signer, maps:get(keys, S), undefined) =/= undefined
                                            ].


%% -- Property ---------------------------------------------------------------

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
