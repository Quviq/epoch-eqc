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
    #{chain => [aec_headers:new_key_header(0, <<"prevhash">>, <<"0 PrevKeyHash">>, <<"genesis">>, <<"miner">>, <<"beneficiary">>,
                                          2000, 0, 0, 0, 1)]
     }.

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
    ?LET(Faulty, weighted_default({99, false}, {1, true}),
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


initiate(Host, Port, Opts, #{faulty := Faulty}) ->
    case aesc_fsm:initiate(Host, Port, Opts) of
        {ok, Pid} when not Faulty ->
            Pid;
        {ok, Pid} when Faulty ->
            exit(Pid, kill),
            {error, faulty};
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
                      ?APPLY(noise_open_channel, []))
               ])).

noise_open_channel_callouts(S, []) ->
    ?CALLOUT(aec_chain, genesis_hash, [], <<"123">>),
    ?MATCH({Map, ok}, ?CALLOUT(aesc_session_noise, channel_open, [?WILDCARD, ?VAR], ok)),
    ?APPLY(store_channel_id, [Map]).

store_channel_id_next(S, _Value, [Map]) ->
    S#{temporary_channel_id => {call, maps, get, [temporary_channel_id, Map]}}.

initiate_next(S, Value, [_, _, _, #{faulty := Faulty,
                                     alice := InitiatorAccount,
                                     bob := ResponderAccount}]) ->
    case Faulty of
        true -> S;
        false ->
            S#{ alice => InitiatorAccount,
                bob => ResponderAccount,
                fsm => Value,
                state => initialized }
    end.

%% if reserve is 0 or low, we can still open
initiate_post(_S, [_, _, #{channel_reserve := _Reserve}, #{faulty := Faulty}], Res) ->
    is_pid(Res) orelse Faulty.

initiate_features(_S, [_Host, _Port, _Opts, #{faulty := Faulty}], Res) ->
    [ successful_faulty || Res == {error, faulty} ] ++
        [ faulty || Faulty ] ++
        [ successful || not Faulty ].


%% --- Operation: chain_mismatch ---
chain_mismatch_pre(S) ->
    maps:get(state, S, undefined) == initialized andalso
        maps:is_key(temporary_channel_id, S).

chain_mismatch_args(#{fsm := Fsm} = S) ->
    [Fsm, #{ chain_hash             => <<"non-genesis">>
           , temporary_channel_id   => maps:get(temporary_channel_id, S)
           , initiator_amount       => 0
           , responder_amount       => 0
           , channel_reserve        => 0
           , initiator              => alice
           , responder              => bob } ].

chain_mismatch_pre(_S, [_, _]) ->
    true.

chain_mismatch(Fsm, ArgMap) ->
    aesc_fsm:message(Fsm, {channel_accept, ArgMap}).

chain_mismatch_callouts(#{chain := Chain}, [Fsm, ArgMap]) ->
    GenesisHeader = lists:last(Chain),
    ?CALLOUT(aec_chain, genesis_hash, [], aec_headers:root_hash(GenesisHeader)),
    ?SEND(?SELF, ?WILDCARD),  %% error
    ?SEND(?SELF, ?WILDCARD).  %% died

chain_mismatch_next(S, _Value, [_, _]) ->
    maps:with([chain], S).

%% chain_mismatch_process(_S, [Fsm, ArgMap]) ->
%%     worker.

chain_mismatch_post(_S, [_, _], Res) ->
    eq(Res, ok).


%% --- ... more operations

%% -- Property ---------------------------------------------------------------
%% invariant(_S) ->
%% true.

weight(_S, initialize) -> 1;
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
            aggregate(call_features(H),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok))))
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
               modules = [ lager_spec(), noise_layer_spec(),
                           aec_chain_spec(),
                           aec_next_nonce_spec(),
                           aetx_env_spec() ] }.

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
             #api_fun{ name = top_header, arity = 0},
             #api_fun{ name = get_key_header_by_height, arity = 1},
             #api_fun{ name = genesis_hash, arity = 0}
           ] }.

aec_next_nonce_spec() ->
    #api_module{
       name = aec_next_nonce,
       functions =
           [ #api_fun{ name = pick_for_account, arity = 1}
           ] }.

aetx_env_spec() ->
    #api_module{
       name = aetx_env,
       functions =
           [ #api_fun{ name = tx_env_and_trees_from_hash, arity = 2},
             #api_fun{ name = height, arity = 1}
           ] }.
