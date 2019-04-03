%%% @author Thomas Arts
%%% @doc Meta model for performing generalized_account meta transactions
%%%
%%% @end
%%% Created : 27 Mar 2019 by Thomas Arts

-module(txs_meta_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-eqc_group_commands(false).
-define(PatronAmount, 100000000000001).  %% read from file?


-compile([export_all, nowarn_export_all]).

-record(gaccount, {id, nonce, name, vm, abi, protocol}).


%% -- State and state functions ----------------------------------------------
initial_state() ->
    txs_eqc:initial_state().

command(S) ->
    ?LET(Cmd, frequency([{2, txs_eqc:command(S)},
                         {case maps:get(height, S, 0) > 0 of
                              true -> 1;
                              false -> 0
                          end, ?LAZY({call, ?MODULE, ga_attach, [ gen_as_meta(S)
                                                                  | ga_attach_args(S) ]})}]),
         case Cmd of
             {call, txs_eqc, F, Args} ->
                 case lists:member(F, [init, mine, multi_mine]) of
                     true -> Cmd;
                     false -> {call, ?MODULE, F, [ gen_as_meta(S) | Args]}
                 end;
             _ -> Cmd  %% we added meta already
         end).

ga_attach_args(#{height := Height, accounts := Accounts}) ->
    Name = "authorize_nonce",
    ?LET({SenderTag, Sender}, txs_eqc:gen_account(1, 100, Accounts),
         begin
             #{gasfun := GasFun, basefee := Fixed} = txs_eqc:contract(Name),
             [Height, {SenderTag, txs_eqc:account_key(Sender)}, Name,
              frequency([{10, 1}, {30, 2}]),
              #{owner_id => aeser_id:create(account, txs_eqc:account_key(Sender)),
                vm_version  => frequency([{1, elements([0,5])}, {1, aevm_sophia_1}, {1, aevm_sophia_2}, {50, aevm_sophia_3}]),
                abi_version => weighted_default({49, 1}, {1, elements([0,3])}),
                fee => txs_eqc:gen_fee_above(Height, Fixed),
                gas_price => frequency([{1,0}, {10, 1}, {89, txs_eqc:minimum_gas_price(Height)}]),
                gas => frequency([{7, GasFun(Height)}, {1, GasFun(Height) - 1}, {1, GasFun(Height) + 100}, {1, 10}]),
                nonce => txs_eqc:gen_nonce(Sender)
               }]
         end).

precondition(S, {call, txs_eqc, F, Args}) ->
    txs_eqc:precondition(S, {call, txs_eqc, F, Args});
precondition(S, {call, ?MODULE, ga_attach, [AsMeta, Height, {_, Sender}, _, _, Tx]}) ->
    maps:get(height, S, 0) > 0 andalso maps:get(accounts, S, []) =/= [] andalso
    (AsMeta == false orelse lists:member(AsMeta, maps:get(gaccounts, S))) andalso
        txs_eqc:correct_height(S, Height) andalso txs_eqc:valid_nonce(S, Sender, Tx);
precondition(S, {call, ?MODULE, F, [AsMeta | Args]}) ->
    (AsMeta == false orelse lists:member(AsMeta, maps:get(gaccounts, S))) andalso
        txs_eqc:precondition(S, {call, txs_eqc, F, Args}).

adapt(S, {call, txs_eqc, F, Args}) ->
    case txs_eqc:adapt(S, {call, txs_eqc, F, Args}) of
        false -> false;
        NewArgs ->
            {call, txs_eqc, F, NewArgs}
    end;
adapt(S, {call, ?MODULE, ga_attach, [AsMeta, Height, {STag, Sender}, Contract, CompilerVersion, Tx]}) ->
    case  maps:get(height, S, 0) > 0 andalso maps:get(accounts, S, []) =/= [] of
        false -> false;
        true ->
            {call, ?MODULE, ga_attach, [adapt_meta(S, AsMeta), maps:get(height, S, Height), {STag, Sender}, Contract, CompilerVersion,
                                        txs_eqc:adapt_nonce(S, Sender, Tx)]}
    end;
adapt(S, {call, ?MODULE, F, [false | Args]}) ->
    case txs_eqc:adapt(S, {call, txs_eqc, F, Args}) of
        false   -> false;
        NewArgs -> {call, ?MODULE, F, [false | NewArgs]}
    end;
adapt(S, {call, ?MODULE, F, [GAccount | Args]}) ->
    case txs_eqc:adapt(S, {call, txs_eqc, F, Args}) of
        false -> false;
        NewArgs ->
            {call, ?MODULE, F, [adapt_meta(S, GAccount) | NewArgs]}
    end.

adapt_meta(_S, false) ->
    false;
adapt_meta(S, #gaccount{id = Id}) ->
    lists:keyfind(Id, #gaccount.id, maps:get(gaccounts, S, [])).


next_state(S, V, {call, txs_eqc, F, Args}) ->
    txs_eqc:next_state(S, V, {call, txs_eqc, F, Args});
next_state(S, V, {call, ?MODULE, ga_attach, [false |_ ] = Args}) ->
     case ga_attach_valid(S, Args) of
         false -> S;
         true -> ga_attach_next(S, V, Args)
     end;
next_state(S, _V, {call, ?MODULE, ga_attach, [GAccount, Args]}) ->
    case authorizes_meta(S, GAccount, ga_attach, Args) of
        false -> S;
        true ->
            %% Take fee and gas of inner transaction, because we can!
            AuthFee = auth_fee(GAccount#gaccount.name),
            txs_eqc:reserve_fee(AuthFee,
            ga_bump_and_charge(GAccount, AuthFee, S))
    end;
next_state(S, V, {call, ?MODULE, F, [false | Args]}) ->
    case account_type_ok(false, S, origin(F, Args)) of
        true -> txs_eqc:next_state(S, V, {call, txs_eqc, F, Args});
        false -> S
    end;
next_state(S, V, {call, ?MODULE, F, [GAccount | Args]}) ->
    %% if AsMeta is true and valid, we update
    case authorizes_meta(S, GAccount, F, Args) of
        false -> S;
        true ->
            AuthFee = auth_fee(GAccount#gaccount.name),
            AuthData = auth_data(GAccount#gaccount.name, GAccount#gaccount.nonce),
            AuthS = txs_eqc:reserve_fee(AuthFee,
                                        ga_bump_and_charge(GAccount, AuthFee, S)),
            case is_meta_valid(S, GAccount, F, Args) of
                false ->
                    AuthS;
                true ->
                    NewS = txs_eqc:next_state(AuthS, V, {call, txs_eqc, F, Args}),
                    case AuthS == NewS of
                        true -> NewS;
                        false ->
                            Nonce = maps:get(nonce, txs_eqc:untag_nonce(lists:last(Args))),
                            AuthNonce = aega_meta_tx:auth_id(GAccount#gaccount.id, AuthData),
                    case F of
                        contract_create ->
                                    OldId = aect_contracts:compute_contract_pubkey(GAccount#gaccount.id, Nonce),
                            NewId =  aect_contracts:compute_contract_pubkey(GAccount#gaccount.id, AuthNonce),
                            txs_eqc:update_contract_id(OldId, NewId, NewS);
                        register_oracle ->
                            NewS;
                        channel_create ->
                                    {_, RespPK} = aeser_id:specialize(maps:get(responder_id, lists:last(Args))),
                                    OldId = {GAccount#gaccount.id, Nonce, RespPK},
                                    NewId =  {GAccount#gaccount.id, AuthNonce, RespPK},
                                    %% io:format("Change ~p\nInto ~p\nIn: ~p\n", [OldId, NewId, maps:get(channels, NewS)]),
                                    txs_eqc:update_channel_id(OldId, NewId, NewS);
                        query_oracle ->
                                    {_, OraclePK} = aeser_id:specialize(maps:get(oracle_id, lists:last(Args))),
                                    OldId = {GAccount#gaccount.id, Nonce, OraclePK},
                                    NewId = {GAccount#gaccount.id, AuthNonce, OraclePK},
                                    %% io:format("Change ~p\nInto ~p\nIn: ~p\n", [OldId, NewId, maps:get(queries, NewS)]),
                                    txs_eqc:update_query_id(OldId, NewId, NewS);
                        _ ->
                            NewS
                    end
            end
            end
    end.

postcondition(S, {call, txs_eqc, F, Args}, Res) ->
    txs_eqc:postcondition(S, {call, txs_eqc, F, Args}, Res);
postcondition(S, {call, ?MODULE, ga_attach, [false | _] = Args}, Res) ->
    Correct = ga_attach_valid(S, Args),
    case Res of
        {error, _} when Correct -> eq(Res, ok);
        {error, _}              -> true;
        ok when Correct         -> true;
        ok                      -> eq(ok, {error, '_'})
    end;
postcondition(S, {call, ?MODULE, F, [AsMeta | Args]}, Res) ->
    Origin = origin(F, Args),
    case AsMeta of
        false ->
            case account_type_ok(AsMeta, S, Origin) of
                true ->
                    txs_eqc:postcondition(S, {call, txs_eqc, F, Args}, Res);
                false ->
                    case Res of
                        ok         -> eq(ok, {error, '_'});
                        {error, _} -> true
                    end
            end;
        _ ->
            case authorizes_meta(S, AsMeta, F, Args) of
                true ->
                    eq(Res, ok);  %% but we might not have succeeded with operation
                false ->
                    case Res of
                        ok         -> eq(ok, {error, '_'});
                        {error, _} -> true
                    end
            end
    end.

call_features(S, {call, txs_eqc, F, Args}, Res) ->
    txs_eqc:call_features(S, {call, txs_eqc, F, Args}, Res);
call_features(S, {call, ?MODULE, ga_attach, [AsMeta, Height, _, Name, _CompilerVersion, Tx] = Args}, _Res) ->
    #{gasfun := GasFun} = txs_eqc:contract(Name),
    Correct = ga_attach_valid(S, Args) andalso maps:get(gas, Tx) >= GasFun(Height),
    [{correct,  if Correct -> ga_attach; true -> false end} ] ++
        [ {ga_meta, ga_attach} || AsMeta =/= false ];
call_features(S, {call, ?MODULE, F, [AsMeta | Args]}, Res) ->
    Correct = (AsMeta =/= false andalso is_meta_valid(S, AsMeta, F, Args)),
    [{correct,  if Correct -> F; true -> false end} || AsMeta =/= false] ++
    [ {ga_meta, F} || AsMeta =/= false ] ++
        txs_eqc:call_features(S, {call, txs_eqc, F, Args}, Res).


all_command_names() ->
    [ga_attach | txs_eqc:all_command_names()].

%% -- Operations -------------------------------------------------------------

spend(AsMeta, Height, _Sender, _Receiver, Tx) ->
    apply_transaction(AsMeta, Height, aec_spend_tx, Tx).

register_oracle(AsMeta, Height, _Sender, Tx) ->
    apply_transaction(AsMeta, Height, aeo_register_tx, Tx).

extend_oracle(AsMeta, Height, _Oracle, Tx) ->
    apply_transaction(AsMeta, Height, aeo_extend_tx, Tx).

query_oracle(AsMeta, Height, _Sender, _Oracle, Tx) ->
    apply_transaction(AsMeta, Height, aeo_query_tx, Tx).

response_oracle(AsMeta, Height, _QueryId, Tx) ->
    apply_transaction(AsMeta, Height, aeo_response_tx, Tx).

channel_create(AsMeta, Height, _Initiator, _Responder, Tx) ->
    NewTx = txs_eqc:channel_create_tx(Tx),
    apply_transaction(AsMeta, Height, aesc_create_tx, NewTx).

channel_deposit(AsMeta, Height, ChannelId, _Party, Tx) ->
    NewTx = channel_add_id(AsMeta, ChannelId, Tx),
    apply_transaction(AsMeta, Height, aesc_deposit_tx, NewTx).

channel_withdraw(AsMeta, Height, ChannelId, _Party, Tx) ->
    NewTx = channel_add_id(AsMeta, ChannelId, Tx),
    apply_transaction(AsMeta, Height, aesc_withdraw_tx, NewTx).

channel_close_mutual(AsMeta, Height, ChannelId, _Party, Tx) ->
    NewTx = channel_add_id(AsMeta, ChannelId, Tx),
    apply_transaction(AsMeta, Height, aesc_close_mutual_tx, NewTx).

channel_close_solo(AsMeta, Height, ChannelId, _Party, Tx) ->
    NewTx = channel_add_id(AsMeta, ChannelId, Tx),
    apply_transaction(AsMeta, Height, aesc_close_solo_tx, NewTx).

channel_add_id(_AsMeta, {Initiator, N, Responder}, Tx) ->
     Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder))}.


ns_preclaim(AsMeta, Height, _Sender, {_Name,_Salt}, Tx) ->
    apply_transaction(AsMeta, Height, aens_preclaim_tx, Tx).

ns_claim(AsMeta, Height, _Sender, Tx) ->
    apply_transaction(AsMeta, Height, aens_claim_tx, Tx).

ns_update(AsMeta, Height, _Name, _Sender, _NameAccount, Tx) ->
    apply_transaction(AsMeta, Height, aens_update_tx, Tx).

ns_transfer(AsMeta, Height, _Sender, _Receiver, _Name, Tx) ->
    apply_transaction(AsMeta, Height, aens_transfer_tx, Tx).

ns_revoke(AsMeta, Height, _Sender, _Name, Tx) ->
    apply_transaction(AsMeta, Height, aens_revoke_tx, Tx).

contract_create(AsMeta, Height, {_, _Sender}, Name, CompilerVersion, Tx) ->
    NewTx =  txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
    apply_transaction(AsMeta, Height, aect_create_tx, NewTx).

contract_call(AsMeta, Height, _, Contract, Tx) ->
    NewTx = txs_eqc:contract_call_tx(Contract, Tx),
    apply_transaction(AsMeta, Height, aect_call_tx, NewTx).

ga_attach(AsMeta, Height, _, Name, CompilerVersion, Tx) ->
    NewTx = ga_attach_tx(Name, CompilerVersion, Tx),
    apply_transaction(AsMeta, Height, aega_attach_tx, NewTx).

ga_attach_tx(Name, CompilerVersion, Tx) ->
    NewTx = txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
    #{auth_fun := AuthFun, functions := Funs} = txs_eqc:contract(Name),
    {_, _, _, AuthHash} = lists:keyfind(AuthFun, 1, Funs),
    NewTx#{auth_fun => AuthHash}.

name_to_mod() ->
    #{spend => aec_spend_tx,
      register_oracle => aeo_register_tx,
      extend_oracle => aeo_extend_tx,
      query_oracle => aeo_query_tx,
      response_oracle => aeo_response_tx,
      channel_create => aesc_create_tx,
      channel_deposit => aesc_deposit_tx,
      channel_withdraw => aesc_withdraw_tx,
      channel_close_mutual => aesc_close_mutual_tx,
      ns_preclaim => aens_preclaim_tx,
      ns_claim => aens_claim_tx,
      ns_update => aens_update_tx,
      ns_transfer => aens_transfer_tx,
      ns_revoke => aens_revoke_tx,
      contract_create => aect_create_tx,
      contract_call => aect_call_tx,
      ga_attach => aega_attach_tx}.

%% ---------------------------------------------------------------------------

ga_attach_valid(S, [AsMeta, Height, {_, Sender}, Name, CompilerVersion, Tx]) ->
    #{gasfun := GasFun, basefee := Fixed} = txs_eqc:contract(Name),
    Protocol = aec_hard_forks:protocol_effective_at_height(Height),
    txs_eqc:is_account(S, Sender) andalso
    account_type_ok(AsMeta, S, Sender)
    andalso correct_nonce(AsMeta, S, Sender, Tx)
    andalso txs_eqc:check_balance(S, Sender, maps:get(fee, Tx) + GasFun(Height) * maps:get(gas_price, Tx))
    andalso txs_eqc:valid_contract_fee(Height, Fixed, Tx)
    andalso  Protocol == 3
    andalso lists:member({maps:get(vm_version, Tx), maps:get(abi_version, Tx)},
                         [{aevm_sophia_3, 1}])
    andalso lists:member(CompilerVersion, [1, 2]).


ga_attach_next(S, _V, [_AsMeta, Height, {_, Sender}, Name, _, Tx]) ->
    #{gasfun := GasFun} = txs_eqc:contract(Name),
    #{ fee := Fee, gas_price := GasPrice,
       gas := Gas, vm_version := Vm, abi_version := Abi} = Tx,
    case Gas >= GasFun(Height) of
        true ->
            txs_eqc:reserve_fee(Fee + GasFun(Height) * GasPrice,
            txs_eqc:bump_and_charge(Sender,
                                    Fee + GasFun(Height) * GasPrice,
                                    txs_eqc:add(gaccounts,
                                                #gaccount{id = Sender,
                                                          name = Name,
                                                          vm = Vm,
                                                          abi = Abi,
                                                          nonce = 0,
                                                          protocol = aec_hard_forks:protocol_effective_at_height(Height)}, S)));
        false ->
            %% out of gas
            txs_eqc:reserve_fee(Fee + Gas * GasPrice,
            txs_eqc:bump_and_charge(Sender,
                                    Fee + Gas * GasPrice, S))
    end.

is_valid(S, F, [AsMeta | Args]) ->
    account_type_ok(AsMeta, S, origin(F, Args)).

origin(F, Args) when F == extend_oracle; F == channel_create ->
    lists:nth(2, Args);
origin(response_oracle, Args) ->
    {_Sender, _Nonce, Oracle} = lists:nth(2, Args),
    Oracle;
origin(F, Args) when F == channel_deposit; F == channel_withdraw;
                     F == channel_close_mutual; F == channel_close_solo ->
    Party = lists:nth(3, Args),
    {Initiator, _, Responder} = lists:nth(2, Args),
    case Party of initiator -> Initiator; responder -> Responder end;
origin(ns_update, Args) ->
    {_SenderTag, Sender} = lists:nth(3, Args),
    Sender;
origin(_, Args) ->
    {_SenderTag, Sender} = lists:nth(2, Args),
    Sender.

is_meta_valid(S, false, F, Args) ->
    Origin = origin(F, Args),
    not lists:keymember(Origin, #gaccount.id, maps:get(gaccounts, S));
is_meta_valid(S, #gaccount{id = Id}, F, Args) ->
    Origin = origin(F, Args),
    lists:keymember(Origin, #gaccount.id, maps:get(gaccounts, S)) andalso
        Id == Origin.

%% Must have enough funds to do authorization
%% otherwise:  {error, insufficient_funds}
authorizes_meta(S, GAccount, _F, _Args) ->
    txs_eqc:check_balance(S, GAccount#gaccount.id, auth_fee(GAccount#gaccount.name)).

%% -- Property ---------------------------------------------------------------

%% NOte that weight for sub model is still computed by that weight function.
%% weight for adding a new command should be organized in frequency in command generator

prop_txs() ->
    prop_txs(2).

prop_txs(Fork) ->
    application:load(aecore),
    application:set_env(aecore, hard_forks,
                                   #{<<"1">> => 0, <<"2">> => Fork, <<"3">> => 2*Fork}),
    application:load(aesophia),  %% Since we do in_parallel, we may have a race in line 86 of aesophia_compiler
    txs_eqc:compile_contracts(),
    ?SETUP(
    fun() ->
        meck:new(aec_fork_block_settings, [passthrough]),
        meck:expect(aec_fork_block_settings, file_name,
                        fun(R) -> "../../" ++ meck:passthrough([R]) end),
        fun() -> meck:unload(aec_fork_block_settings) end
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

gen_as_meta(S) ->
    case maps:get(gaccounts, S) of
        [] -> false;
        GAs  -> weighted_default({10, false}, {90, elements(GAs)})
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

apply_transaction(false, Height, Kind, Tx) ->
    txs_eqc:apply_transaction(Height, Kind, Tx);
apply_transaction(GAccount, Height, Kind, Tx) ->
    Nonce = GAccount#gaccount.nonce,
    Name = GAccount#gaccount.name,
    AuthData = auth_data(Name, Nonce),
    TxNonce =
        case maps:get(nonce, Tx) of
            {good, _} -> {good, 0};
            {bad, _}  -> {bad, 1}
        end,
    NewTx = #{ga_id       => aeser_id:create(account, GAccount#gaccount.id),
              auth_data   => AuthData,
              abi_version => 1,
              gas         => 5000,
              gas_price   => 1000000,
              fee         => 500000 * 1000000,
              tx          => txs_eqc:create_aetx(Kind, Tx#{nonce => TxNonce})
             },
    txs_eqc:apply_transaction(Height, aega_meta_tx, NewTx).


ga_bump_and_charge(#gaccount{id = Key, nonce = Nonce} = GAccount, Fee, S) ->
    Gaccounts = (maps:get(gaccounts, S) -- [GAccount]) ++ [GAccount#gaccount{nonce = Nonce + 1}],
    txs_eqc:charge(Key, Fee, S#{gaccounts => Gaccounts}).

account_type_ok(false, S, Sender) ->
    not lists:keymember(Sender, #gaccount.id, maps:get(gaccounts, S));
account_type_ok(_, S, Sender) ->
    lists:keymember(Sender, #gaccount.id, maps:get(gaccounts, S)).

correct_nonce(false, S, Sender, Tx) ->
    txs_eqc:correct_nonce(S, Sender, Tx);
correct_nonce(GAccount, _S, Sender, _) ->
    %% Actual nonce check is done when precodition checks that this valud is in the state
    %% Possibly an adapt should be used to actually make shrinking more effective
    Sender == GAccount#gaccount.id.
