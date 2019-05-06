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

%% This is a typical ADD operation meta model

%% -- State and state functions ----------------------------------------------
%% Should be a map merge of all underlying initial states.
initial_state() ->
    ?TXS:initial_state().

command(S) ->
    frequency([{20, ?TXS:command(S)} ] ++
              [{1, ?LAZY({call, ?MODULE, ga_attach, ga_attach_args(S)})} || ga_attach_pre(S)]).

precondition(S, {call, ?MODULE, ga_attach, Args}) ->
    ga_attach_pre(S) andalso ga_attach_pre(S, Args);
precondition(S, {call, M, F, Args}) ->
    M:precondition(S, {call, M, F, Args}).

adapt(S, {call, ?MODULE, ga_attach, Args}) ->
    ga_attach_adapt(S, Args);
adapt(S, {call, M, F, Args}) ->
    M:adapt(S, {call, M, F, Args}).

%% We do something in next state for all basic Txs... this is where expressing
%% as one model no longer possible.

next_state(S, V, {call, ?MODULE, ga_attach, Args}) ->
    ga_attach_next(S, V, Args);
next_state(S, V, {call, M, F, Args}) ->
    case lists:member(F, [init, newkey, mine, multi_mine]) of
        true -> M:next_state(S, V, {call, M, F, Args});
        false ->
            case basic_account(S, origin(F, Args)) of
                true -> M:next_state(S, V, {call, M, F, Args});
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
    M:postcondition(S, {call, M, F, Args}, Res);
postcondition(S, {call, M, F, Args}, Res) ->
    BasicAccount = basic_account(S, origin(F, Args)),
    case {Res, M:postcondition(S, {call, M, F, Args}, Res)} of
        {ok, true}          -> BasicAccount;
        {{error, _}, true}  -> true;              %% got an error and expected an error
        {{error, _}, _}     -> not BasicAccount;  %% got unexpected error, must be non-basic
        {_, Other} -> Other
    end.


call_features(S, {call, ?MODULE, ga_attach, Args}, Res) ->
    ga_attach_features(S, Args, Res);
call_features(S, {call, M, F, Args}, Res) ->
    M:call_features(S, {call, M, F, Args}, Res).



all_command_names() ->
    [ga_attach | ?TXS:all_command_names()].

%% --- Operations


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


ga_attach_pre(S) ->
    maps:get(height, S, 0) > 0.

ga_attach_pre(S, [Height, {_, Sender}, _, _, Tx]) ->
   maps:get(accounts, S, []) =/= [] andalso
        txs_eqc:correct_height(S, Height) andalso txs_eqc:valid_nonce(S, Sender, Tx).

ga_attach_valid(S, [Height, {_, Sender}, Name, CompilerVersion, Tx]) ->
    #{gasfun := GasFun, basefee := Fixed} = txs_eqc:contract(Name),
    Protocol = aec_hard_forks:protocol_effective_at_height(Height),
    txs_eqc:is_account(S, Sender) andalso
    basic_account(S, Sender)
    andalso txs_eqc:correct_nonce(S, Sender, Tx)
    andalso txs_eqc:check_balance(S, Sender, maps:get(fee, Tx) + GasFun(Height) * maps:get(gas_price, Tx))
    andalso txs_eqc:valid_contract_fee(Height, Fixed, Tx)
    andalso Protocol == 3
    andalso lists:member({maps:get(vm_version, Tx), maps:get(abi_version, Tx)},
                         [{aevm_sophia_3, 1}])
    andalso lists:member(CompilerVersion, [1, 2]).

ga_attach_adapt(S, [_, {STag, Sender}, Contract, CompilerVersion, Tx]) ->
    case maps:get(height, S, 0) of
        0 -> false;
        Height ->
            [Height, {STag, Sender}, Contract, CompilerVersion,
             txs_eqc:adapt_nonce(S, Sender, Tx)]
    end.

ga_attach(Height, _, Name, CompilerVersion, Tx) ->
    NewTx = ga_attach_tx(Name, CompilerVersion, Tx),
    ?TXS:apply_transaction(Height, aega_attach_tx, NewTx).

ga_attach_tx(Name, CompilerVersion, Tx) ->
    NewTx = txs_eqc:contract_create_tx(Name, CompilerVersion, Tx),
    #{auth_fun := AuthFun, functions := Funs} = txs_eqc:contract(Name),
    {_, _, _, AuthHash} = lists:keyfind(AuthFun, 1, Funs),
    NewTx#{auth_fun => AuthHash}.

ga_attach_next(S, _V, [Height, {_, Sender}, Name, _, Tx] = Args) ->
     case ga_attach_valid(S, Args) of
         false -> S;
         true ->
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
             end
     end.

ga_attach_features(S, [ Height, _, Name, _CompilerVersion, Tx] = Args, Res) ->
    #{gasfun := GasFun} = txs_eqc:contract(Name),
    Correct = ga_attach_valid(S, Args) andalso maps:get(gas, Tx) >= GasFun(Height),
    [{correct,  if Correct -> ga_attach; true -> false end} ] ++
        [ {ga_attach, Res} ].

%% -------------------------

origin(F, Args) when F == extend_oracle; F == channel_create ->
    lists:nth(2, Args);
origin(response_oracle, Args) ->
    {_Sender, _Nonce, Oracle} = lists:nth(2, Args),
    Oracle;
origin(F, Args) when F == channel_deposit; F == channel_withdraw;
                     F == channel_close_mutual; F == channel_close_solo;
                     F == channel_settle; F == channel_slash ->
    Party = lists:nth(3, Args),
    {Initiator, _, Responder} = lists:nth(2, Args),
    case Party of initiator -> Initiator; responder -> Responder end;
origin(ns_update, Args) ->
    {_SenderTag, Sender} = lists:nth(3, Args),
    Sender;
origin(_Kind, Args) ->
    {_SenderTag, Sender} = lists:nth(2, Args),
    Sender.

%% -- gaccount data structure
id(#gaccount{id = Id}) -> Id.
name(#gaccount{name = Name}) -> Name.
nonce(#gaccount{nonce = Nonce}) -> Nonce.

find_account(S, Id) ->
    lists:keyfind(Id, #gaccount.id, maps:get(gaccounts, S, [])).

ga_bump_and_charge(#gaccount{id = Key, nonce = Nonce} = GAccount, Fee, S) ->
    Gaccounts = (maps:get(gaccounts, S) -- [GAccount]) ++ [GAccount#gaccount{nonce = Nonce + 1}],
    txs_eqc:charge(Key, Fee, S#{gaccounts => Gaccounts}).


%% -- Property ---------------------------------------------------------------

%% NOte that weight for sub model is still computed by that weight function.
%% weight for adding a new command should be organized in frequency in command generator

prop_txs() ->
    prop_txs(3).

prop_txs(Fork) ->
    application:load(aesophia),  %% Since we do in_parallel, we may have a race in line 86 of aesophia_compiler
    propsetup(Fork,
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
    end))).


%% -----

basic_account(S, Sender) ->
    not lists:keymember(Sender, #gaccount.id, maps:get(gaccounts, S)).

%% Keep this as separate function to make it possiblke to run
%% txs_sign_eqc both on top of txs_eqc and txs_ga_eqc
propsetup(Fork, Prop) ->
    ?TXS:propsetup(Fork, Prop).
