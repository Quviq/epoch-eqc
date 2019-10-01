%%% @author Thomas Arts <thomas@SpaceGrey.lan>
%%% @copyright (C) 2019, Thomas Arts
%%% @doc
%%%
%%% @end
%%% Created : 30 Sep 2019 by Thomas Arts <thomas@SpaceGrey.lan>

-module(aesc_fsm_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_component.hrl").

-compile([export_all, nowarn_export_all]).

%% -- State ------------------------------------------------------------------
initial_state() ->
    #{}.

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
    true.

precondition_common(_S, _Call) ->
    true.

%% postcondition_common(S, Call, Res) ->
%%     eq(Res, return_value(S, Call)). %% Check all return values

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
initiate_pre(_S) ->
    true.

initiate_args(_S) ->
    ?LET([InitiatorAccount, ResponderAccount], [fake_account_gen(<<"alice">>),
                                                fake_account_gen(<<"bob">>)],
    ?LET(Faulty, weighted_default({90, false}, {10, true}),
    [<<"myhost.com">>, 16123, #{initiator => aec_accounts:pubkey(InitiatorAccount),
                                responder => aec_accounts:pubkey(ResponderAccount),
                                lock_period => choose(0, 20),
                                initiator_amount => choose(0, 100),
                                responder_amount => choose(0, 100),
                                channel_reserve => choose(0, 20),
                                push_amount => choose(0, 20)
                               },
     #{faulty => Faulty,
       alice => InitiatorAccount,
       bob => ResponderAccount}])).

initiate_pre(_S, [_Host, _Port, #{initiator_amount := InitiatorAmount,
                                  responder_amount := ResponderAmount,
                                  channel_reserve := Reserve,
                                  push_amount := PushAmount
                                 }, _]) ->
    (InitiatorAmount - PushAmount) >= Reserve andalso
        (ResponderAmount + PushAmount) >= Reserve.


initiate(Host, Port, Opts, _) ->
    case aesc_fsm:initiate(Host, Port, Opts) of
        {ok, Pid} ->
            Pid;
        Error ->
            Error
    end.

initiate_callouts(_S, [Host, Port, Opts, #{faulty := Faulty,
                                           alice := InitiatorAccount,
                                           bob := ResponderAccount}]) ->
    ?MATCH_GEN(Connection, oneof([{error, not_connected} || Faulty] ++ [{ok, noise_id}])),
    ?MATCH(AReturn,
           ?CALLOUT(aec_chain, get_account, [maps:get(initiator, Opts)],
                    oneof([{error, something} || Faulty ] ++ [ {value, InitiatorAccount} ]))),
    ?MATCH(BReturn,
           ?CALLOUT(aec_chain, get_account, [maps:get(responder, Opts)],
                    oneof([{error, something} || Faulty] ++ [ {value, ResponderAccount} ]))),
    ?WHEN(BReturn =/= {error, something} andalso AReturn =/= {error, something},
          ?SEQ([
                ?CALLOUT(aesc_session_noise, connect, [Host, Port, []], Connection),
                ?WHEN(Connection =/= {error, not_connected},
                      ?SEQ([
                            ?CALLOUT(aec_chain, genesis_hash, [], <<"123">>),
                            ?CALLOUT(aesc_session_noise, channel_open, [?WILDCARD, ?WILDCARD], ok)]))
               ])).

initiate_next(S, _Value, _Args) ->
    S.

%% if reserve is 0 or low, we can still open
initiate_post(_S, [_, _, #{channel_reserve := _Reserve}, #{faulty := Faulty}], Res) ->
    is_pid(Res) orelse Faulty.


%% --- ... more operations

%% -- Property ---------------------------------------------------------------
%% invariant(_S) ->
%% true.

weight(_S, start) -> 1;
weight(_S, _Cmd) -> 10.

prop_fsm() ->
    eqc:dont_print_counterexample(
    ?SETUP(
        fun() ->
                %% Setup mocking, etc.
                eqc_mocking:start_mocking(api_spec()),
                %% Return the teardwown function
                fun() -> ok end
        end,
    ?FORALL(Cmds, commands(?MODULE),
    begin
        %% stop the server if running
        start_supervisor(),
        {H, S, Res} = run_commands(Cmds),
        cleanup(),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok)))
    end))).

start_supervisor() ->
    case whereis(aesc_fsm_sup) of
        undefined -> ok;
        Pid -> exit(Pid, kill)
    end,
    {ok, Supervisor} = aesc_fsm_sup:start_link(),
    unlink(Supervisor).

cleanup() ->
    case whereis(aesc_fsm_sup) of
        undefined -> ok;
        Pid -> exit(Pid, kill)
    end.

fake_account_gen(Owner) ->
    Pad = 32 - size(Owner),
    ?LET(Generalized, bool(),
         {account,
          aeser_id:create(account, <<Owner/binary, 0:Pad/unit:8>>),
          nat(), %% balance
          if Generalized -> 0; true -> 1 end, %% nonce
          0, %% flags
          oneof([undefined || not Generalized] ++
                    [aeser_id:create(contract, <<"this is a top contract">>) ||  Generalized]),  %% ga_contract :: undefined | aeser_id:id(),
          oneof([undefined || not Generalized] ++
                    [ <<"fun_hash">> || Generalized ])}).

%% -- API-spec ---------------------------------------------------------------
api_spec() ->
    #api_spec{ language = erlang, mocking = eqc_mocking,
               modules = [ lager_spec(), noise_layer_spec(), aec_chain_spec() ] }.

lager_spec() ->
    #api_module{ name = lager, fallback = lager_mock }.

noise_layer_spec() ->
    #api_module{
       name = aesc_session_noise,
       functions =
           [ #api_fun{ name = channel_open, arity = 2, matched = all, fallback = false}
           , #api_fun{ name = connect, arity = 3, matched = all, fallback = false}
           ] }.

aec_chain_spec() ->
    #api_module{
       name = aec_chain,
       functions =
           [ #api_fun{ name = get_account, arity = 1},
             #api_fun{ name = genesis_hash, arity = 0}
           ] }.
