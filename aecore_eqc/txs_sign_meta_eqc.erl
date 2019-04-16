%%% @author Thomas Arts
%%% @doc Meta model for performing generalized_account meta transactions
%%%
%%% @end
%%% Created : 16 Apr 2019 by Thomas Arts

-module(txs_sign_meta_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-eqc_group_commands(false).
-define(PatronAmount, 100000000000001).  %% read from file?

-define(TXS, txs_sign_eqc).  %% make sure sign points to txs_ga_eqc !

-compile([export_all, nowarn_export_all]).


%% -- State and state functions ----------------------------------------------
initial_state() ->
    txs_eqc:initial_state().

command(S) ->
    ?LET(Cmd, ?TXS:command(S),
         case Cmd of
             {call, M, F, Args} ->
                 case lists:member(F, [init, newkey, mine, multi_mine]) of
                     true -> Cmd;
                     false -> {call, ?MODULE, F, [ M, gen_as_meta(S, origin(F, Args)) | Args]}
                 end;
             _ -> Cmd
         end).


precondition(S, {call, ?MODULE, F, [M, AsMeta | Args]}) ->
    (AsMeta == false orelse lists:member(AsMeta, maps:get(gaccounts, S))) andalso
        txs_sign_eqc:has_correct_signers(S, {call, M, F, Args}) andalso
        lists:member(F, [spend, ga_attach]) andalso
        ?TXS:precondition(S, {call, M, F, Args});
precondition(S, {call, M, F, Args}) ->
    ?TXS:precondition(S, {call, M, F, Args}).

adapt(S, {call, ?MODULE, F, [M, AsMeta | Args]}) ->
    case ?TXS:adapt(S, {call, M, F, Args}) of
        false -> false;
        NewArgs ->
            [M, adapt_meta(S, AsMeta) | NewArgs]
    end;
adapt(S, {call, M, F, Args}) ->
    ?TXS:adapt(S, {call, M, F, Args}).

adapt_meta(_S, false) ->
    false;
adapt_meta(S, GAccount) ->
    txs_ga_eqc:find_account(S, txs_ga_eqc:id(GAccount)).

next_state(S, V, {call, ?MODULE, F, [M, false | Args]}) ->
    ?TXS:next_state(S, V, {call, M, F, Args});
next_state(S, V, {call, ?MODULE, F, [M, GAccount | Args]}) ->
    Id = txs_ga_eqc:id(GAccount),
    case authorizes_meta(S, GAccount, F, Args) of
        false -> S;
        true ->
            AuthFee = auth_fee(txs_ga_eqc:name(GAccount)),
            AuthData = auth_data(txs_ga_eqc:name(GAccount), txs_ga_eqc:nonce(GAccount)),
            AuthS = txs_eqc:reserve_fee(AuthFee,
                                        txs_ga_eqc:ga_bump_and_charge(GAccount, AuthFee, S)),
            case  Id == origin(F, Args) andalso F =/= ga_attach of
                false ->
                    %% Outermost should be same as innermost (ticket exists)
                    AuthS;
                true ->
                    %% GA account is origin.
                    %% do the transaction as original one
                    %% Problem here is that I don't want the check whether it is a generalized account
                    %% So rather directly call the inner txs_eqc:next:state... but need to peal of the things added by txs_sign
                    GAccounts = [ GA || GA <- maps:get(gaccounts, S), txs_ga_eqc:id(GA) =/= Id],
                    ToNormalS = maps:merge(AuthS, #{gaccounts => GAccounts}),
                    NewS = maps:merge(?TXS:next_state(ToNormalS, V, {call, M, F, Args}), #{gaccounts => maps:get(gaccounts, AuthS)}),
                    case AuthS == NewS of
                        true -> AuthS;
                        false ->
                            Nonce = maps:get(nonce, txs_eqc:untag_nonce(lists:last(Args))),
                            AuthNonce = {call, aega_meta_tx, auth_id, [Id, AuthData]},
                            case F of
                                contract_create ->
                                    OldId = {call, aect_contracts, compute_contract_pubkey, [Id, Nonce]},
                                    NewId = {call, aect_contracts, compute_contract_pubkey, [Id, AuthNonce]},
                                    txs_eqc:update_contract_id(OldId, NewId, NewS);
                                register_oracle ->
                                    NewS;
                                channel_create ->
                                    {_, RespPK} = aeser_id:specialize(maps:get(responder_id, lists:last(Args))),
                                    OldId = {Id, Nonce, RespPK},
                                    NewId =  {Id, AuthNonce, RespPK},
                                    %% io:format("Change ~p\nInto ~p\nIn: ~p\n", [OldId, NewId, maps:get(channels, NewS)]),
                                    txs_eqc:update_channel_id(OldId, NewId, NewS);
                                query_oracle ->
                                    {_, OraclePK} = aeser_id:specialize(maps:get(oracle_id, lists:last(Args))),
                                    OldId = {Id, Nonce, OraclePK},
                                    NewId = {Id, AuthNonce, OraclePK},
                                    %% io:format("Change ~p\nInto ~p\nIn: ~p\n", [OldId, NewId, maps:get(queries, NewS)]),
                                    txs_eqc:update_query_id(OldId, NewId, NewS);
                                _ ->
                                    NewS
                    end
            end
            end
    end;
next_state(S, V, {call, M, F, Args}) ->
    ?TXS:next_state(S, V, {call, M, F, Args}).

postcondition(S, {call, ?MODULE, F, [M, AsMeta | Args]}, Res) ->
    Origin = origin(F, Args),
    case AsMeta of
        false ->
            case txs_ga_eqc:basic_account(S, Origin) of
                true ->
                    ?TXS:postcondition(S, {call, M, F, Args}, Res);
                false ->
                    case Res of
                        ok         -> eq(ok, {error, '_'});
                        {error, _} -> true
                    end
            end;
        _ ->
            case authorizes_meta(S, AsMeta, F, Args) of
                true ->
                    %% but we might not have succeeded with operation
                    %% postcondition of  ?TXS:postcondition(S, {call, M, F, Args}, Res) would reveal that
                    eq(Res, ok);
                false ->
                    case Res of
                        ok         -> eq(ok, {error, '_'});
                        {error, _} -> true
                    end
            end
    end;
postcondition(S, {call, M, F, Args}, Res) ->
    ?TXS:postcondition(S, {call, M, F, Args}, Res).


call_features(S, {call, ?MODULE, F, [M, false | Args]}, Res) ->
    ?TXS:call_features(S, {call, M, F, Args}, Res);
call_features(S, {call, ?MODULE, F, [_M, GAccount | Args]}, _Res) ->
    Authorized = authorizes_meta(S, GAccount, F, Args),
    Correct = (txs_ga_eqc:id(GAccount) == origin(F, Args)),  %% and more, but how?
    [{correct,  if Authorized andalso Correct -> ga_meta; true -> false end}] ++
    [{ga_meta, different_inner} ||  Authorized andalso txs_ga_eqc:id(GAccount) /= origin(F, Args)] ++
    [{ga_meta, F} || Authorized andalso Correct ];  %% This is hard... cannot actually see whether inner Tx was successful or not due to Res possibly incorrect
call_features(S, {call, M, F, Args}, Res) ->
    ?TXS:call_features(S, {call, M, F, Args}, Res).


all_command_names() ->
    ?TXS:all_command_names().

%% -- Operations -------------------------------------------------------------
response_oracle_tx({_Sender, Nonce, _} = QueryId, Tx) when is_integer(Nonce) ->
    txs_eqc:response_oracle_tx(QueryId, Tx);
response_oracle_tx({_Sender, AuthId, Oracle}, Tx) when is_binary(AuthId) ->
    Tx#{query_id => aeo_query:ga_id(AuthId, Oracle)}.

channel_add_id(_AsMeta, {Initiator, N, Responder}, Tx) ->
     Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder))}.



spend(_, AsMeta, _, Signers, Height, _Sender, _Receiver, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aec_spend_tx, Tx).


register_oracle(_, AsMeta, _, Signers, Height, _Sender, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aeo_register_tx, Tx).

extend_oracle(_, AsMeta, _, Signers,Height, _Oracle, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aeo_extend_tx, Tx).

query_oracle(_, AsMeta, _, Signers,Height, _Sender, _Oracle, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aeo_query_tx, Tx).

response_oracle(_, AsMeta, _, Signers,Height, QueryId, Tx) ->
    NewTx = response_oracle_tx(QueryId, Tx),
    apply_transaction(AsMeta, Signers, Height, aeo_response_tx, NewTx).


channel_create(_, AsMeta, _, Signers,Height, _Initiator, _Responder, Tx) ->
    NewTx = txs_eqc:channel_create_tx(Tx),
    apply_transaction(AsMeta, Signers, Height, aesc_create_tx, NewTx).

channel_deposit(_, AsMeta, _, Signers,Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_deposit_tx(ChannelId, Party, channel_add_id(AsMeta, ChannelId, Tx)),
    apply_transaction(AsMeta, Signers, Height, aesc_deposit_tx, NewTx).

channel_withdraw(_, AsMeta, _, Signers,Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_withdraw_tx(ChannelId, Party, channel_add_id(AsMeta, ChannelId, Tx)),
    apply_transaction(AsMeta, Signers, Height, aesc_withdraw_tx, NewTx).

channel_close_mutual(_, AsMeta, _, Signers,Height, ChannelId, _Party, Tx) ->
    NewTx = channel_add_id(AsMeta, ChannelId, Tx),
    apply_transaction(AsMeta, Signers, Height, aesc_close_mutual_tx, NewTx).

channel_close_solo(_, AsMeta, _, Signers,Height, ChannelId, Party, Tx) ->
    NewTx = txs_eqc:channel_close_solo_tx(ChannelId, Party, channel_add_id(AsMeta, ChannelId, Tx)),
    apply_transaction(AsMeta, Signers, Height, aesc_close_solo_tx, NewTx).


ns_preclaim(_, AsMeta, _, Signers,Height, _Sender, {_Name,_Salt}, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aens_preclaim_tx, Tx).

ns_claim(_, AsMeta, _, Signers,Height, _Sender, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aens_claim_tx, Tx).

ns_update(_, AsMeta, _, Signers,Height, _Name, _Sender, _NameAccount, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aens_update_tx, Tx).

ns_transfer(_, AsMeta, _, Signers,Height, _Sender, _Receiver, _Name, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aens_transfer_tx, Tx).

ns_revoke(_, AsMeta, _, Signers, Height, _Sender, _Name, Tx) ->
    apply_transaction(AsMeta, Signers, Height, aens_revoke_tx, Tx).


contract_create(_, AsMeta, _, Signers,Height, _Sender, Name, CompilerVersion, Tx) ->
    NewTx =  txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
    apply_transaction(AsMeta, Signers, Height, aect_create_tx, NewTx).

contract_call(_, AsMeta, _, Signers,Height, _, Contract, Tx) ->
    NewTx = txs_eqc:contract_call_tx(Contract, Tx),
    apply_transaction(AsMeta, Signers, Height, aect_call_tx, NewTx).

ga_attach(_, AsMeta, _, Signers, Height, _, Name, CompilerVersion, Tx) ->
    NewTx = txs_ga_eqc:ga_attach_tx(Name, CompilerVersion, Tx),
    apply_transaction(AsMeta, Signers, Height, aega_attach_tx, NewTx).

%% ---------------------------------------------------------------------------


origin(F, [_, _ | Args]) ->
    %% io:format("Checking origin ~p in ~p\n", [F, Args]),
    txs_ga_eqc:origin(F, Args).


%% Must have enough funds to do authorization
%% otherwise:  {error, insufficient_funds}
authorizes_meta(S, GAccount, _F, _Args) ->
    txs_eqc:check_balance(S, txs_ga_eqc:id(GAccount), auth_fee(txs_ga_eqc:name(GAccount))).

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
            txs_eqc:aggregate_feats([atoms, correct, protocol, contract_call_fun, ga_meta | all_command_names()], call_features(H),
                ?WHENFAIL(eqc:format("Total = ~p~nFeeTotal = ~p~n", [TreesTotal, FeeTotal]),
                          pretty_commands(?MODULE, Cmds, {H, S, Res},
                              conjunction([{result, Res == ok},
                                           {total, Total == 0 orelse equals(Total, ?PatronAmount - FeeTotal)}]))))))))
    end)))).


%% -----

gen_as_meta(S, Origin) ->
    case txs_ga_eqc:find_account(S, Origin) of
        false -> false;
        GA -> ?SHRINK(weighted_default({90, GA}, {10, elements(maps:get(gaccounts, S))}),
                      [false])
    end.

auth_fee(Name) ->
    #{auth_fun := AuthFun, functions := Funs} = txs_eqc:contract(Name),
    {_, _, Gas, _} = lists:keyfind(AuthFun, 1, Funs),
    500000 * 1000000 + Gas * 1000000.

auth_data(Name, Nonce) ->
    #{src := Contract, auth_fun := AuthFun} = txs_eqc:contract(Name),
    {ok, CallData, _, _} = aeso_compiler:create_calldata(binary_to_list(Contract),
                                                         binary_to_list(AuthFun),
                                                         [integer_to_list(Nonce)]),
    CallData.

apply_transaction(false, Signers, Height, Kind, Tx) ->
    ?TXS:apply_transaction(Signers, Height, Kind, Tx);
apply_transaction(GAccount, {correct, Signers}, Height, Kind, Tx) ->
    Nonce = txs_ga_eqc:nonce(GAccount),
    Name = txs_ga_eqc:name(GAccount),
    AuthData = auth_data(Name, Nonce),
    ActualSigners = [ <<SK:(32*8), PK/binary>> || <<SK:(32*8), PK/binary>> <- Signers,
                                                  PK =/= txs_ga_eqc:id(GAccount)],
    TxNonce =
        case maps:get(nonce, Tx) of
            {good, _} -> 0;
            {bad, _}  -> 2010102 %% one should not be able to post a signed tx with bad nonce and get fee subtracted
                         %% make a test case replay attack as well as too high nonce.
        end,

    AeTx       = txs_eqc:create_aetx(Kind, Tx#{nonce => TxNonce}),
    BinTx      = aec_governance:add_network_id(aetx:serialize_to_binary(AeTx)),
    Signatures = [ enacl:sign_detached(BinTx, Signer) || Signer <- ActualSigners ],
    SignedTx   = aetx_sign:new(AeTx, Signatures),

    NewTx = #{ga_id       => aeser_id:create(account, txs_ga_eqc:id(GAccount)),
              auth_data   => AuthData,
              abi_version => 1,
              gas         => 5000,
              gas_price   => 1000000,
              fee         => 500000 * 1000000,
              tx          => SignedTx
             },
    txs_eqc:apply_transaction(Height, aega_meta_tx, NewTx).

%% apply_transaction({_Tag, Signers}, Height, Kind, Tx) ->
%%     Env      = aetx_env:tx_env(Height),
%%     Trees    = get(trees),
%%     AeTx     = txs_eqc:create_aetx(Kind, Tx),
%%     BinTx = aec_governance:add_network_id(aetx:serialize_to_binary(AeTx)),
%%     Signatures = [ enacl:sign_detached(BinTx, Signer) || Signer <- Signers ],
%%     SignedTx = aetx_sign:new(AeTx, Signatures),
%%     %% When we use strict, we see errors returned, otherwise only invalid txs returned
%%     case aec_trees:apply_txs_on_state_trees_strict([SignedTx], Trees, Env) of
%%         {ok, _ValidTxs, InvalidTxs, NewTrees, _} ->
%%             put(trees, NewTrees),
%%             case InvalidTxs of
%%                 [] -> ok;
%%                 _  -> {error, signatures}
%%             end;
%%         Other ->
%%             Other
%%     end.

%% State channel transacrtions need to be signed by 2 parties
sign_aetx(Signers, Kind, Tx) ->
    %% Only signature length is asserted it seems
    aetx_sign:new(txs_eqc:create_aetx(Kind, Tx), [ <<Sig/binary, Sig/binary>> || Sig <- Signers ]).


correct_nonce(false, S, Sender, Tx) ->
    txs_eqc:correct_nonce(S, Sender, Tx);
correct_nonce(GAccount, _S, Sender, _) ->
    %% Actual nonce check is done when precondition checks that this value is in the state
    %% Possibly an adapt should be used to actually make shrinking more effective
    Sender == txs_ga_eqc:id(GAccount).
