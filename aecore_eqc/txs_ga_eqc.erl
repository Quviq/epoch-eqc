%%% @author Thomas Arts
%%% @doc Meta model for attaching generalized_accounts
%%%
%%% @end
%%% Created : 27 Mar 2019 by Thomas Arts

-module(txs_ga_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-eqc_group_commands(false).
-define(PatronAmount, 100000000000001).  %% read from file?

-define(TXS, txs_eqc).

-compile([export_all, nowarn_export_all]).

-record(gaccount, {id, nonce, name, vm, abi, protocol}).


%% -- State and state functions ----------------------------------------------
initial_state() ->
    txs_eqc:initial_state().

command(S) ->
    frequency([{20, ?TXS:command(S)},
                         {case maps:get(height, S, 0) of
                              0 -> 0;
                              H when H < 5 -> 1;
                              _ -> 2
                          end, ?LAZY({call, ?MODULE, ga_attach, ga_attach_args(S)})}]).

ga_attach_args(#{height := Height} = S) ->
    Name = "authorize_nonce",
    ?LET({SenderTag, Sender}, txs_eqc:gen_account(1, 100, S),
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


precondition(S, {call, ?MODULE, ga_attach, [Height, {_, Sender}, _, _, Tx]}) ->
    maps:get(height, S, 0) > 0 andalso maps:get(accounts, S, []) =/= [] andalso
        txs_eqc:correct_height(S, Height) andalso txs_eqc:valid_nonce(S, Sender, Tx);
precondition(S, {call, M, F, Args}) ->
    ?TXS:precondition(S, {call, M, F, Args}).


adapt(S, {call, ?MODULE, ga_attach, [Height, {STag, Sender}, Contract, CompilerVersion, Tx]}) ->
    case  maps:get(height, S, 0) > 0 andalso maps:get(accounts, S, []) =/= [] of
        false -> false;
        true ->
            {call, ?MODULE, ga_attach, [maps:get(height, S, Height), {STag, Sender}, Contract, CompilerVersion,
                                        txs_eqc:adapt_nonce(S, Sender, Tx)]}
    end;
adapt(S, {call, M, F, Args}) ->
    case ?TXS:adapt(S, {call, M, F, Args}) of
        false -> false;
        NewArgs ->
            {call, M, F, NewArgs}
    end.


next_state(S, V, {call, ?MODULE, ga_attach, Args}) ->
     case ga_attach_valid(S, Args) of
         false -> S;
         true -> ga_attach_next(S, V, Args)
     end;
next_state(S, V, {call, M, F, Args}) ->
    case lists:member(F, [init, newkey, mine, multi_mine]) of
        true -> ?TXS:next_state(S, V, {call, M, F, Args});
        false ->
            case basic_account(S, origin(F, Args)) of
                true -> ?TXS:next_state(S, V, {call, M, F, Args});
                false -> S
            end
    end.


postcondition(S, {call, ?MODULE, ga_attach, Args}, Res) ->
    Correct = ga_attach_valid(S, Args),
    case Res of
        {error, _} when Correct -> eq(Res, ok);
        {error, _}              -> true;
        ok when Correct         -> true;
        ok                      -> eq(ok, {error, '_'})
    end;
postcondition(S, {call, M, F, Args}, Res) when F == init; F == newkey; F == mine; F == multi_mine ->
    ?TXS:postcondition(S, {call, M, F, Args}, Res);
postcondition(S, {call, M, F, Args}, Res) ->
    BasicAccount = basic_account(S, origin(F, Args)),
    case {Res, ?TXS:postcondition(S, {call, M, F, Args}, Res)} of
        {ok, true}          -> BasicAccount;
        {{error, _}, true}  -> true;              %% got an error and expected an error
        {{error, _}, _}     -> not BasicAccount;  %% got unexpected error, must be non-basic
        {_, Other} -> Other
    end.


call_features(S, {call, ?MODULE, ga_attach, [ Height, _, Name, _CompilerVersion, Tx] = Args}, Res) ->
    #{gasfun := GasFun} = txs_eqc:contract(Name),
    Correct = ga_attach_valid(S, Args) andalso maps:get(gas, Tx) >= GasFun(Height),
    [{correct,  if Correct -> ga_attach; true -> false end} ] ++
        [ {ga_attach, Res} ];
call_features(S, {call, M, F, Args}, Res) ->
    ?TXS:call_features(S, {call, M, F, Args}, Res).


all_command_names() ->
    [ga_attach | ?TXS:all_command_names()].

%% -- Operations -------------------------------------------------------------

%% spend(AsMeta, Height, {_, Sender}, _Receiver, Tx) ->
%%     apply_transaction(AsMeta, [{origin, Sender}], Height, aec_spend_tx, Tx).

%% register_oracle(AsMeta, Height, {_, Sender}, Tx) ->
%%     apply_transaction(AsMeta, [{origin, Sender}], Height, aeo_register_tx, Tx).

%% extend_oracle(AsMeta, Height, Oracle, Tx) ->
%%     apply_transaction(AsMeta, [Oracle], Height, aeo_extend_tx, Tx).

%% query_oracle(AsMeta, Height, {_, Sender}, _Oracle, Tx) ->
%%     apply_transaction(AsMeta, [{origin, Sender}], Height, aeo_query_tx, Tx).

%% response_oracle(AsMeta, Height, QueryId, Tx) ->
%%     NewTx = response_oracle_tx(AsMeta, QueryId, Tx),
%%     apply_transaction(AsMeta, [], Height, aeo_response_tx, NewTx).

%% response_oracle_tx(_, {_Sender, Nonce, _} = QueryId, Tx) when is_integer(Nonce) ->
%%     txs_eqc:response_oracle_tx(QueryId, Tx);
%% response_oracle_tx(_, {_Sender, AuthId, Oracle}, Tx) when is_binary(AuthId) ->
%%     Tx#{query_id => aeo_query:ga_id(AuthId, Oracle)}.

%% channel_create(AsMeta, Height, Initiator, Responder, Tx) ->
%%     NewTx = txs_eqc:channel_create_tx(Tx),
%%     apply_transaction(AsMeta, [{origin, Initiator}, Responder], Height, aesc_create_tx, NewTx).

%% channel_deposit(AsMeta, Height, {In, _, Resp} = ChannelId, Party, Tx) ->
%%     Signer = if Party == initiator -> Resp; true -> In end,
%%     NewTx = txs_eqc:channel_deposit_tx(ChannelId, Party, channel_add_id(AsMeta, ChannelId, Tx)),
%%     apply_transaction(AsMeta, [Signer], Height, aesc_deposit_tx, NewTx).

%% channel_withdraw(AsMeta, Height, {In, _, Resp} = ChannelId, Party, Tx) ->
%%     Signer = if Party == initiator -> Resp; true -> In end,
%%     NewTx = txs_eqc:channel_withdraw_tx(ChannelId, Party, channel_add_id(AsMeta, ChannelId, Tx)),
%%     apply_transaction(AsMeta, [Signer], Height, aesc_withdraw_tx, NewTx).

%% channel_close_mutual(AsMeta, Height, {In, _, Resp} = ChannelId, Party, Tx) ->
%%     Signer = if Party == initiator -> Resp; true -> In end,
%%     NewTx = channel_add_id(AsMeta, ChannelId, Tx),
%%     apply_transaction(AsMeta, [Signer], Height, aesc_close_mutual_tx, NewTx).

%% channel_close_solo(AsMeta, Height, {_In, _, _Resp} = ChannelId, Party, Tx) ->
%%     %% Signer = if Party == initiator -> maps:get(responder, Tx); true -> maps:get(initiator, Tx) end,
%%     NewTx = txs_eqc:channel_close_solo_tx(ChannelId, Party, channel_add_id(AsMeta, ChannelId, Tx)),
%%     apply_transaction(AsMeta, [], Height, aesc_close_solo_tx, NewTx).

%% channel_add_id(_AsMeta, {Initiator, N, Responder}, Tx) ->
%%      Tx#{channel_id =>
%%             aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder))}.


%% ns_preclaim(AsMeta, Height, _Sender, {_Name,_Salt}, Tx) ->
%%     apply_transaction(AsMeta, [], Height, aens_preclaim_tx, Tx).

%% ns_claim(AsMeta, Height, _Sender, Tx) ->
%%     apply_transaction(AsMeta, [], Height, aens_claim_tx, Tx).

%% ns_update(AsMeta, Height, _Name, _Sender, _NameAccount, Tx) ->
%%     apply_transaction(AsMeta, [], Height, aens_update_tx, Tx).

%% ns_transfer(AsMeta, Height, _Sender, _Receiver, _Name, Tx) ->
%%     apply_transaction(AsMeta, [], Height, aens_transfer_tx, Tx).

%% ns_revoke(AsMeta, Height, {_, Sender}, _Name, Tx) ->
%%     apply_transaction(AsMeta, [Sender], Height, aens_revoke_tx, Tx).

%% contract_create(AsMeta, Height, {_, Sender}, Name, CompilerVersion, Tx) ->
%%     NewTx =  txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
%%     apply_transaction(AsMeta, [Sender], Height, aect_create_tx, NewTx).

%% contract_call(AsMeta, Height, _, Contract, Tx) ->
%%     NewTx = txs_eqc:contract_call_tx(Contract, Tx),
%%     apply_transaction(AsMeta, [], Height, aect_call_tx, NewTx).

ga_attach(Height, _, Name, CompilerVersion, Tx) ->
    NewTx = ga_attach_tx(Name, CompilerVersion, Tx),
    ?TXS:apply_transaction(Height, aega_attach_tx, NewTx).

ga_attach_tx(Name, CompilerVersion, Tx) ->
    NewTx = txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
    #{auth_fun := AuthFun, functions := Funs} = txs_eqc:contract(Name),
    {_, _, _, AuthHash} = lists:keyfind(AuthFun, 1, Funs),
    NewTx#{auth_fun => AuthHash}.

%% ---------------------------------------------------------------------------

ga_attach_valid(S, [Height, {_, Sender}, Name, CompilerVersion, Tx]) ->
    #{gasfun := GasFun, basefee := Fixed} = txs_eqc:contract(Name),
    Protocol = aec_hard_forks:protocol_effective_at_height(Height),
    txs_eqc:is_account(S, Sender) andalso
    basic_account(S, Sender)
    andalso txs_eqc:correct_nonce(S, Sender, Tx)
    andalso txs_eqc:check_balance(S, Sender, maps:get(fee, Tx) + GasFun(Height) * maps:get(gas_price, Tx))
    andalso txs_eqc:valid_contract_fee(Height, Fixed, Tx)
    andalso  Protocol == 3
    andalso lists:member({maps:get(vm_version, Tx), maps:get(abi_version, Tx)},
                         [{aevm_sophia_3, 1}])
    andalso lists:member(CompilerVersion, [1, 2]).


ga_attach_next(S, _V, [Height, {_, Sender}, Name, _, Tx]) ->
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

basic_account(S, Sender) ->
    not lists:keymember(Sender, #gaccount.id, maps:get(gaccounts, S)).
