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
    #{ chain => [aec_headers:new_key_header(0, <<"prevhash">>, <<"0 PrevKeyHash">>, <<"genesis">>, <<"miner">>, <<"beneficiary">>,
                                          2000, 0, 0, 0, default, 1)]
     , protocol => 4
     }.

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
    true.

precondition_common(_S, _Call) ->
    true.

%% postcondition_common(S, Call, Res) ->
%%     eq(Res, return_value(S, Call)). %% Check all return values

%% -- Operations -------------------------------------------------------------

%% --- Operation: accounts ---
accounts_pre(S) ->
    not maps:is_key(alice, S).

accounts_args(_S) ->
    [#{alice => fake_account_gen(<<"alice">>),
       bob => fake_account_gen(<<"bob">>)}].

accounts(Accs) ->
    ok.

accounts_next(S, _Value, [Accounts]) ->
    maps:merge(S, Accounts).



%% --- Operation: init ---
initiate_pre(S) ->
    maps:is_key(alice, S).

initiate_args(S) ->
    ?LET(Faulty, weighted_default({99, false}, {0, true}),
         ["myhost.com", 16123, #{initiator => alice,
                                 responder => bob,
                                lock_period => choose(0, 20),
                                initiator_amount => choose(0, 100),
                                responder_amount => choose(0, 100),
                                channel_reserve => choose(0, 20),
                                push_amount => choose(0, 20)
                               },
     #{faulty => Faulty,
            alice => maps:get(alice, S),
            bob => maps:get(bob, S)  %% Needed because components have no wrap_call
           }]).

initiate_pre(_S, [_Host, _Port, #{initiator_amount := InitiatorAmount,
                                  responder_amount := ResponderAmount,
                                  channel_reserve := Reserve,
                                  push_amount := PushAmount
                                 }, _]) ->
    (InitiatorAmount - PushAmount) >= Reserve andalso
        (ResponderAmount + PushAmount) >= Reserve.

initiate(Host, Port, #{initiator := I, responder := R} = SymOpts, #{faulty := Faulty} = Symbolic) ->
    %% Should read it from S, but no wrap_call in component framework
    Opts = SymOpts#{initiator => aec_accounts:pubkey(maps:get(I, Symbolic)),
                    responder => aec_accounts:pubkey(maps:get(R, Symbolic))},
    case aesc_client:initiate(list_to_binary(Host), Port, Opts) of
        {ok, Pid} when not Faulty ->
            Pid;
        {ok, Pid} when Faulty ->
            exit(Pid, kill),
            {error, faulty};
        Error ->
            Error
    end.

initiate_callouts(S, [Host, Port, #{initiator := I, responder := R}, #{faulty := Faulty}]) ->
    IAccount = maps:get(I, S),
    RAccount = maps:get(R, S),
    ?MATCH_GEN(Connection, oneof([{error, not_connected} || Faulty] ++ [{ok, noise_id}])),
    ?MATCH(AReturn,
           ?CALLOUT(aec_chain, get_account, [aec_accounts:pubkey(IAccount)],
                    oneof([{error, something} || Faulty ] ++ [ {value, IAccount} ]))),
    ?MATCH(BReturn,
           ?CALLOUT(aec_chain, get_account, [aec_accounts:pubkey(RAccount)],
                    oneof([{error, something} || Faulty] ++ [ {value, RAccount} ]))),
    ?CALLOUT(aesc_limits, allow_new, [],
            oneof([{error, exists} || Faulty ] ++ [ ok ])),
    ?WHEN(BReturn =/= {error, something} andalso AReturn =/= {error, something},
          ?SEQ([
                ?CALLOUT(aesc_session_noise, connect, [list_to_binary(Host), Port, []], Connection),
                ?WHEN(Connection =/= {error, not_connected},
                      ?SEQ([?APPLY(noise_open_channel, []),
                            ?SEND(?SELF, {aesc_fsm, ?WILDCARD, ?WILDCARD})]))
               ])).

noise_open_channel_callouts(S, []) ->
    ?CALLOUT(aec_chain, genesis_hash, [], <<"123">>),
    ?MATCH({Map, ok}, ?CALLOUT(aesc_session_noise, channel_open, [?WILDCARD, ?VAR], ok)),
    ?APPLY(store_channel_id, [Map]).

store_channel_id_next(S, _Value, [Map]) ->
    S#{temporary_channel_id => {call, maps, get, [temporary_channel_id, Map]}}.

initiate_next(S, Value, [_, _, _, #{faulty := Faulty}]) ->
    case Faulty of
        true -> S;
        false ->
            S#{ fsm => Value,
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
        maps:get(accepted, S, false) == false andalso
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
    ?OPTIONAL(?CALLOUT(aec_chain, genesis_hash, [],
                       aec_headers:root_hash(GenesisHeader))),
    ?SEND(?SELF, {aesc_fsm, ?WILDCARD, #{info => ?WILDCARD, tag => error, type => report}}),
    ?OPTIONAL(?SEND(?SELF, ?WILDCARD)).

chain_mismatch_next(S, _Value, [_, _]) ->
    maps:with([chain, protocol], S).

%% chain_mismatch_process(_S, [Fsm, ArgMap]) ->
%%     worker.

chain_mismatch_post(_S, [_, _], Res) ->
    eq(Res, ok).


%% --- Operation: channel_accept ---
channel_accept_pre(S) ->
    maps:get(state, S, undefined) == initialized andalso
        maps:get(accepted, S, false) == false andalso
        maps:is_key(temporary_channel_id, S).

channel_accept_args(#{fsm := Fsm, chain := Chain} = S) ->
    GenesisHeader = lists:last(Chain),
    [Fsm, #{ chain_hash             => aec_headers:root_hash(GenesisHeader)
           , temporary_channel_id   => maps:get(temporary_channel_id, S)
           , initiator_amount       => 0
           , responder_amount       => 0
           , channel_reserve        => 0
           , initiator              => alice
           , responder              => bob },
    #{alice => maps:get(alice, S), bob => maps:get(bob, S)}
    ].

channel_accept_pre(_S, [_Fsm, _Args, _]) ->
    true.

channel_accept(Fsm, #{initiator := I, responder := R}  = SymbMap, Symbolic) ->
    ArgMap = SymbMap#{initiator => aec_accounts:pubkey(maps:get(I, Symbolic)),
                      responder => aec_accounts:pubkey(maps:get(R, Symbolic))},
    aesc_fsm:message(Fsm, {channel_accept, ArgMap}).

channel_accept_callouts(#{chain := Chain} = S, [Fsm, #{initiator := I, responder := R} = ArgMap, _]) ->
    GenesisHeader = lists:last(Chain),
    %% I create my own representation of environment and whenever code
    %% is using that without calling aetx_env, code will crash as it should!
    Trees = [],
    PinnedHeight = 0,
    IAccount = maps:get(I, S),
    IAccountType = aec_accounts:type(IAccount),
    RAccount = maps:get(R, S),
    RAccountType = aec_accounts:type(RAccount),
    Protocol = maps:get(protocol, S),
    ?OPTIONAL(?CALLOUT(aec_chain, genesis_hash, [], aec_headers:root_hash(GenesisHeader))),
    ?PAR([?SEQ([
                ?CALLOUT(aec_chain, get_account, [aec_accounts:pubkey(IAccount)], {value, maps:get(alice, S)}),
                ?WHEN(IAccountType =:= basic,
                      ?CALLOUT(aec_next_nonce, pick_for_account,
                               [aec_accounts:pubkey(IAccount)], {ok, nonce(maps:get(alice, S))})),
                ?CALLOUT(aec_chain, top_header, [], hd(Chain)),
                ?CALLOUT(aec_chain, get_key_header_by_height, [PinnedHeight], {ok, GenesisHeader}), %% This needs to be a different one
                %% This header is now serialized and hashed
                %% aesc:fsm should be refactored to find the key header instead and use this key header to
                %% build the env instead of first serializing and then deserializing.... too complex
                ?CALLOUT(aetx_env, tx_env_and_trees_from_hash, [aetx_contract, ?WILDCARD], {#{height => PinnedHeight,
                                                                                                   consensus_version => Protocol}, Trees}),
                ?CALLOUT(aetx_env, height, [?WILDCARD], PinnedHeight),
                ?CALLOUT(aetx_env, consensus_version, [?WILDCARD], Protocol),
                ?CALLOUT(aetx_env, height, [?WILDCARD], PinnedHeight),
                ?CALLOUT(aec_chain, top_header, [], hd(Chain)),
                ?CALLOUT(aec_chain, top_header, [], hd(Chain)),
                ?CALLOUT(aec_chain, top_header, [], hd(Chain))
               ]),
          ?SEND(?SELF,  {aesc_fsm, ?WILDCARD, #{info => channel_accept, tag => info, type => report}}),
          ?SEND(?SELF,  {aesc_fsm, ?WILDCARD, #{info => ?WILDCARD, tag => create_tx, type => sign}})]).

channel_accept_next(S, _Value, [_Fsm, _Args, _]) ->
    S#{accepted => true}.

channel_accept_post(_S, [_Fsm, _Args, _], Res) ->
    eq(Res, ok).

nonce({account, _, _, Nonce, _, _, _}) ->
    Nonce.


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
                {ok, _} = eqc_mocking:start_mocking(api_spec()),
                ok = lager_mock:start(),
                %% Return the teardwown function
                fun() ->
                        eqc_mocking:stop_mocking(),
                        lager_mock:print(),
                        lager_mock:stop(),
                        ok
                end
        end,
    ?FORALL(Cmds, commands(?MODULE),
    begin
        setup(),
        {H, S, Res} = run_commands(Cmds),
        cleanup(),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            aggregate(call_features(H),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok))))
    end))).

start_supervisor() ->
    {ok, Supervisor} = aesc_fsm_sup:start_link(),
    unlink(Supervisor).

setup() ->
    %% ensure we start clean
    cleanup(),
    %% stop the server if running
    application:start(gproc),
    start_supervisor(),
    ok.

cleanup() ->
    Processes = [aesc_fsm_sup],
    lists:map(
     fun(Name) ->
        case whereis(Name) of
            undefined -> ok;
            Pid -> exit(Pid, kill)
        end
     end, Processes),
    ok.

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
    #api_spec{ language = erlang
             , mocking = eqc_mocking
             , modules = [ noise_layer_spec()
                         , aec_chain_spec()
                         , aec_next_nonce_spec()
                         , aetx_env_spec()
                         , lager_spec()
                         , aesc_limit_spec()
                         ]
             }.

lager_spec() ->
    #api_module{ name = lager
               , fallback = lager_mock
               }.

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
             #api_fun{ name = height, arity = 1},
             #api_fun{ name = consensus_version, arity = 1}
           ] }.

aesc_limit_spec() ->
    #api_module{ name = aesc_limits,
                 functions =
                 [ #api_fun{ name = allow_new, arity = 0}
                 ]
               }.
