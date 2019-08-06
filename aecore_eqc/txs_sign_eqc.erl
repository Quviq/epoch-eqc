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

signing_pre(S, [Fault]) ->
    lists:member(Fault, [correct, drop_first_signature, drop_last_signature]) orelse
        maps:size(maps:get(keys, S, #{})) > 1.

signing(Injection) ->
    Injection.

signing_next(S, _, [Injection]) ->
    S#{next_signing => Injection}.

signing_features(_S, [Injection], _Res) ->
    [{signing, Injection}].



%% -- Operations -------------------------------------------------------------


%%% helper functions

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
