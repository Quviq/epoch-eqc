%%% @author Thomas Arts <thomas@ThomasComputer.local>
%%% @copyright (C) 2017, Thomas Arts
%%% @doc Assumption for the moment, the "local peer address" is the address
%%%      under which other nodes can reach us. We do may need to know this address
%%%      to include in outgoing messages: the "from" as it where.
%%%      Try to make the software in aehttp to add the local peer, such that we
%%%      don't need the admin here.
%%%
%%%       TODO:
%%%          - This test is known not to work. It requires at least update from http to noise.
%%%
%%% @end
%%% Created : 12 Dec 2017 by Thomas Arts <thomas@ThomasComputer.local>

-module(aec_sync_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_component.hrl").

-compile([export_all, nowarn_export_all]).
-define(SUT, aec_sync).

%% -- State ------------------------------------------------------------------
-record(state,{ aec_peers_pid
              , aec_sync_pid    %% pids of aec_sync and aec_peers processes
              , peers = []
              , blocked = [] :: [{Scheme::http, Host::nonempty_string(), Port::non_neg_integer()}]
              , trusted = [] :: [{Scheme::http, Host::nonempty_string(), Port::non_neg_integer()}]
              , queue = []
              , errored = []
              , tried_connect = []
              , time = 0
              }).

initial_state() ->
  #state{}.

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(S, start_peers) ->
  S#state.aec_peers_pid == undefined;
command_precondition_common(S, start) ->  %% only allow start in order
  S#state.aec_peers_pid =/= undefined andalso S#state.aec_sync_pid == undefined;
command_precondition_common(S, _Cmd) ->
  %% later we allow sync operations with unstarted aec_peers (in case it has crashed)
  S#state.aec_peers_pid =/= undefined andalso S#state.aec_sync_pid =/= undefined.

%% -- Operations -------------------------------------------------------------

%% --- Operation: start_peers ---
start_peers_args(_S) ->
  [].

start_peers() ->
  {ok, PeersPid} = aec_peers:start_link(),
  unlink(PeersPid),
  timer:sleep(10),
  PeersPid.

start_peers_process(_S, _Args) ->
  worker.

start_peers_next(S, V, []) ->
    S#state{ aec_peers_pid = V }.

start_peers_post(_S, _Args, Res) ->
  is_pid(Res).


%% --- Operation: start ---

-define(PEER, peer).
-define(BLOCKED, blocked).

%% Don't start with peers that are also blocked
start_args(_S) ->
  [ ?LET(Peers, list({elements([?PEER, ?BLOCKED]), uri()}),
         [ {Tag, P} || {Tag, P} <- Peers,
                       not (Tag == ?BLOCKED andalso lists:member({?PEER, P}, Peers))]) ].

start(Peers) ->
  application:set_env(aecore, peers, [ pp(Peer) || {?PEER, Peer} <- Peers]),
  application:set_env(aecore, blocked_peers, [ pp(Peer) || {?BLOCKED, Peer} <- Peers]),
  {ok, Pid} = ?SUT:start_link(),
  unlink(Pid),
  timer:sleep(100),
  Pid.

start_callouts(_S, [Peers]) ->
  ?PAR([?APPLY(connect, [ Peer ])  || {?PEER, Peer} <- lists:sort(Peers), Peer =/= error]).


start_next(S, V, [Peers]) ->
    S#state{ aec_sync_pid = V
           , blocked = lists:usort([ {_,_,_} = Peer || {?BLOCKED, Peer} <- Peers, Peer =/= error])
           , trusted = lists:usort([ {_,_,_} = Peer || {?PEER, Peer} <- Peers, Peer =/= error,
                                                        not local_peer(Peer) ])
           }.

start_post(_S, _Args, Res) ->
  is_pid(Res).

start_process(_S, _Args) ->
  worker.


%% --- Operation: is_blocked ---
is_blocked_pre(S) ->
  S#state.aec_peers_pid =/= undefined.

is_blocked_args(_S) ->
  [uri()].

is_blocked(Peer) ->
  aec_peers:is_blocked(pp(Peer)).

is_blocked_post(S, [Peer], Res) ->
  eq(Res, (Peer == error) orelse lists:member(Peer, S#state.blocked)).

is_blocked_features(S, [Peer], _Res) ->
  [{is_blocked, lists:member(Peer, S#state.blocked)}].






%% --- Operation: stop ---
%%
%% TODO stop them independently

%% stop_args(_S) ->
%%   [].

stop() ->
  [ catch gen_server:stop(Pid) || Pid <- [aec_sync, aec_peers] ],
  timer:sleep(100).

stop_next(S, _Value, []) ->
  S#state{ aec_peers_pid = undefined
         , aec_sync_pid = undefined
         }.

%% --- Operation: connect ---

can_be_added(S, Uri) ->
  not (Uri == error orelse lists:member(Uri, S#state.blocked) orelse local_peer(Uri)).

connect_peer_args(S) ->
  [oneof([uri()|S#state.errored])].

connect_peer(Uri) ->
  Peer = pp(Uri),
  ?SUT:connect_peer(Peer),
  timer:sleep(100).

%% We do not test the parser
connect_peer_callouts(S, [Uri]) ->
  ?WHEN(S#state.aec_sync_pid =/= undefined,
        ?APPLY(connect, [Uri])).

connect_peer_post(_S, [_Peer], Res) ->
  eq(Res, ok).

connect_callouts(S, [Uri]) ->
  ?WHEN(can_be_added(S, Uri) andalso not lists:member(Uri, S#state.peers),
        begin
          BinUri = list_to_binary(pp(Uri)),
          ?CALLOUT(jobs, enqueue, [sync_jobs, {ping, BinUri}], ok),
          ?APPLY(add_peer, [Uri]),
          ?APPLY(enqueue, [Uri, {ping, BinUri}])
        end).

connect_features(S, [Uri], _Res) ->
  [ {connecting_to_blocked_peer, Uri} || lists:member(Uri, S#state.blocked) ] ++
   [ {connect_to_self, Uri} || myhost() == Uri ] ++
    [ {connect_to_existing_peer, Uri} || lists:member(Uri, S#state.peers) ] ++
    [ {connect_to_errored_peer, Uri} || lists:member(Uri, S#state.errored) ] ++
    [ connect ].

enqueue_next(S, _, [Uri, Task]) ->
  S#state{ queue = S#state.queue ++ [{Uri, Task}],
           tried_connect = S#state.tried_connect ++ [Uri] }.

add_peer_next(S, _, [Uri]) ->
  case can_be_added(S, Uri) of
    true ->
      S#state{ peers = (S#state.peers -- [Uri]) ++ [Uri] };
    false ->
      S
  end.


%% --- Operation: sync_worker ---
sync_worker_pre(S) ->
  S#state.queue =/= [].

sync_worker_args(S) ->
  {Uri, Task} = hd(S#state.queue),
  [Uri, Task, frequency([{2,ok}, {1,block}, 
                         %% High probability recurrent error
                         {case lists:member(Uri, S#state.errored) of
                            true -> 4;
                            false -> 1
                          end, error}])].

sync_worker_pre(S, [Uri, Task, _]) ->
  %% we don't allow them out of order for now
  hd(S#state.queue) == {Uri, Task}.

sync_worker(_Uri, _Task, _) ->
  ?SUT:sync_worker().

sync_worker_callouts(S, [Uri, Task, Response]) ->
  %% Note that tag of job is not symbolic
  ?MATCH([{_, TheJob}], ?CALLOUT(jobs, dequeue, [sync_jobs, 1], [{S#state.time, Task}])),
  ?APPLY(timer_inc, []),
  case TheJob of
    {ping, _BinUri} ->
      ?APPLY(ping, [Uri, Response])
  end.

sync_worker_next(S, _Value, [_Uri, _Task, _]) ->
  S#state{ queue = tl(S#state.queue) }.

sync_worker_post(_S, [_, _, _], _Res) ->
  true.

sync_worker_process(_S, [_Uri, _Task, _]) ->
  worker.

sync_worker_features(S, [Uri, _Task, Response], _Res) ->
  [{response, Response}] ++
   [ sync_errored || lists:member(Uri, S#state.errored)] ++
   [ repeated_error || Response == error, lists:member(Uri, S#state.errored)].


%% --- Operation: all_peers ---
%% Errored peers are still in the list of peers
%% but not when error time has expired
all_peers_args(_S) ->
  [].

all_peers() ->
  aec_peers:all().

all_peers_post(S, [], Res) ->
  eq(lists:sort([binary_to_list(P) || {P, _} <- Res]),
     lists:sort([ pp(P) || P <- S#state.peers ])).


%% --- Operation: get_random ---
get_random_args(_S) ->
  [oneof([all, nat()]), list(uri())].

get_random(N, Exclude) ->
  case Exclude of
    [] -> aec_peers:get_random(N);
    _ ->  aec_peers:get_random(N, [pp(Uri) || Uri <- Exclude])
  end.

get_random_post(S, [N, Exclude], Res) ->
  RealExclude = [ Ex || Ex <- Exclude ] ++ S#state.errored,
  eqc_statem:conj([not lists:any(fun(Ex) ->
                                     lists:member(pp(Ex), Res)
                                 end, RealExclude),
                   case N == all of
                     false when length(Res) =< N -> true;
                     false -> too_many_returned;
                     true ->
                       eq(lists:sort([binary_to_list(P) || P <- Res]),
                          lists:sort([ pp(P) || P <- lists:usort(S#state.peers 
                                                                  ++ S#state.trusted)  %% gossip blocked trusted peers
                                     ] -- [ pp(Ex) || Ex <- RealExclude ]))
                   end
                  ]).

%% --- Operation: block_peer ---

block_args(_S) ->
  [ uri() ].

block(Uri) ->
  aec_peers:block_peer(pp(Uri)).

%% We cannot block trusted notes
block_next(S, _Value, [Uri]) ->
  S#state{ blocked = (S#state.blocked -- [Uri]) ++ [Uri] -- S#state.trusted,
           peers = S#state.peers -- [Uri
                                     || not lists:member(Uri, S#state.trusted)]}.

block_features(S, [Uri], _Res) ->
  [ {block, errored} || lists:member(Uri, S#state.errored) ] ++
    [ {block, trusted} || lists:member(Uri, S#state.trusted) ].


%% --- Operation: unblock ---
unblock_args(_S) ->
  [uri()].

unblock(Uri) ->
  aec_peers:unblock_peer(pp(Uri)).

unblock_next(S, _Value, [Uri]) ->
   S#state{ blocked = (S#state.blocked -- [Uri]) }.


%% --- Operation: remove ---
remove_args(_S) ->
  [uri()].

remove(Uri) ->
  aec_peers:remove(pp(Uri)).

remove_next(S, _Value, [Uri]) ->
   S#state{ blocked = S#state.blocked -- [Uri],
            peers = S#state.peers -- [Uri],
            trusted =  S#state.trusted -- [Uri]}.






%% --- ... more operations

-define(SHARE, 32).

ping_callouts(_S, [Uri, Response]) ->
  ?MATCH(Local, ?APPLY(local_ping_object, [])),
  ?MATCH_GEN(ManyPeers, ?LET(N, choose(?SHARE+1,40), [ {http, "12.3.4.5", I} || I <- lists:seq(1,N) ])),
  ?MATCH_GEN(Remote,
             #{best_hash => oneof([maps:get(best_hash, Local), <<1,2,3,4>>]),
               difficulty => difficulty(),
               genesis_hash => oneof([maps:get(genesis_hash, Local), <<1,2,3,4>>]),
               peers => ?LET(Peers, list(?SHARE, uri()), [ pp(P) || P<-Peers]),
               source => oneof([list_to_binary(pp(Uri)), <<"blubber">>])}),
  ?MATCH_GEN(ClientReturn,
             case Response of
               error ->
                 oneof([{error, didntwork}, 
                        {ok, oneof([200, choose(0,900)]), #{<<"reason">> => <<"didn't work">>}}
                       ]);
               block ->
                 oneof([{ok, 409, #{<<"reason">> => <<"Different genesis">> }},
                        {ok, 403, #{<<"reason">> => <<"Not allowed">> }},
                        {ok, 200, #{<<"best_hash">> => encode(maps:get(best_hash, Remote)),
                                    <<"difficulty">> => maps:get(difficulty, Remote),
                                    <<"genesis_hash">> => encode(maps:get(genesis_hash, Remote)),
                                    <<"peers">> => [ list_to_binary(pp(P)) || P <- ManyPeers ],
                                    <<"pong">> => <<"pong">>,
                                    <<"share">> => ?SHARE,
                                    <<"source">> => list_to_binary(pp(Uri)) }}]);
               ok ->
                 {ok, 200, #{<<"best_hash">> => encode(maps:get(best_hash, Remote)),
                             <<"difficulty">> => maps:get(difficulty, Remote),
                             <<"genesis_hash">> => encode(maps:get(genesis_hash, Remote)),
                             <<"peers">> => [ list_to_binary(P) || P <- maps:get(peers, Remote) ],
                             <<"pong">> => <<"pong">>,
                             <<"share">> => ?SHARE,
                             <<"source">> => list_to_binary(pp(Uri)) }}
             end),
  %% Note that the parameters in the request have encoded hashes
  ?CALLOUT(aeu_http_client, request, [?WILDCARD, 'Ping', ?WILDCARD], ClientReturn),
  ?WHEN(Response == ok,
        begin
          ?APPLY(add_peer, [Uri]),
          ?MATCH(Res, ?APPLY(compare_ping_objects, [Local, Remote])),
          ?WHEN(Res == ok,
                ?APPLY(ping_peers, [Uri, maps:get(peers, Remote)])),
          ?WHEN(Res == {error, violation},
                %% We decide that the response is incorrect
                %% (attacker did not reject ours)
                ?APPLY(block, [Uri]))
        end).

ping_next(S, Value, [Uri, block]) ->
  block_next(S, Value, [Uri]);
ping_next(S, _Value, [Uri, error]) ->
  %% Only when it is a valid peer it can be errored
  case lists:member(Uri, S#state.peers) of
    true ->
      S#state{ errored = (S#state.errored -- [Uri]) ++ [Uri]};
    false ->
      S
  end;
ping_next(S, _Value, [Uri, ok]) ->
  %% do not add peers here, if they don't block they are added in callouts
  S#state{ errored = S#state.errored -- [Uri]}.


%% Only ping unknown valid Uri's that are provided by new peer.
ping_peers_callouts(S, [Uri, Peers]) ->
  KnownPeers = [ Uri | S#state.peers ++ S#state.blocked ],
  PeersToPing =
    lists:usort([UriPeer || Peer <- Peers, UriPeer <- parse(Peer), %% Empty list if invalid
                            not lists:member(UriPeer, KnownPeers),
                            not local_peer(UriPeer) ]),
  ?PAR([ ?APPLY(connect, [UriPeer]) || UriPeer <- PeersToPing ]).

local_ping_object_callouts(_S, []) ->
  ?MATCH(GenHash, ?CALLOUT(aec_conductor, genesis_hash, [], <<4,3,2,1,0>>)),
  ?MATCH(TopHeader, ?CALLOUT(aec_conductor, top_header_hash, [], oneof([<<0,1,0,1,0>>,<<1,0,1,0,1>>]))),
  ?MATCH_GEN(Difficulty, difficulty()),
  ?CALLOUT(aec_conductor, get_total_difficulty, [], {ok, Difficulty}),
  ?MATCH_GEN(Map, #{best_hash => TopHeader,
                    difficulty => Difficulty,
                    genesis_hash => GenHash}),
  ?RET(Map).

local_ping_object_features(_S, [], _Res) ->
  [local_ping_object].

compare_ping_objects_callouts(_S, [Local, Remote]) ->
  case maps:get(genesis_hash, Local) == maps:get(genesis_hash, Remote) of
    true ->
      case  maps:get(best_hash, Local) == maps:get(best_hash, Remote) orelse
        maps:get(difficulty, Local) > maps:get(difficulty, Remote) of
        true ->
          ?CALLOUT(jobs, enqueue, [sync_jobs, {server_get_missing, ?WILDCARD}], ok);
        false ->
          ?CALLOUT(jobs, enqueue, [sync_jobs, {start_sync, ?WILDCARD}], ok)
      end,
      ?CALLOUT(jobs, enqueue, [sync_jobs, {fetch_mempool, ?WILDCARD}], ok),
      ?RET(ok);
    false ->
      ?RET({error, violation})
  end.

compare_ping_objects_features(_S, _Args, Res) ->
  [ {compare_ping_objects, Res} ].


timer_inc_next(S, _, []) ->
  S#state{time = S#state.time + 1}.

timer_expire_pre(S) ->
  S#state.errored =/= [].

timer_expire_args(S) ->
  %% is always a full peer
  [elements(S#state.errored)].

timer_expire_pre(S, [Uri]) ->
  %% Timer only calls aec_sync if possible
  can_be_added(S, Uri).

timer_expire(Uri) ->
  aec_sync:schedule_ping(aeu_requests:pp_uri(Uri)),
  timer:sleep(10).

timer_expire_callouts(S, [Uri]) ->
  BinUri = list_to_binary(pp(Uri)),
  ?CALLOUT(jobs, enqueue, [sync_jobs, {ping, BinUri}], ok),
  ?APPLY(enqueue, [Uri, {ping, BinUri}]).

timer_expire_features(_S, [Uri], _Res) ->
  [].



%% -- Property ---------------------------------------------------------------
%% invariant(S) ->
%%   [ Peer || Peer <- S#state.peers, lists:member(Peer, S#state.blocked)] == [].

weight(_S, start) -> 1;
weight(_S, sync_worker) -> 8;
weight(_S, _Cmd) -> 1.

prop_sync() ->
  prop_sync(false).

prop_sync(Verbose) ->
  eqc:dont_print_counterexample(
    ?SETUP(
       fun() ->
           %% Setup mocking, etc.
           eqc_mocking:start_mocking(api_spec()),
           error_logger:tty(Verbose),
           if Verbose -> application:ensure_all_started(lager),
                         lager:set_loglevel(lager_console_backend, debug);
              true -> ok
           end,
           application:set_env(aecore, peer_error_expiry, 1),  
                %% put to 1 to find that model not yet covers removing of errored nodes 
           %% Return the teardwown function
           fun() ->
               if Verbose -> application:stop(lager);
                  true -> ok
               end,
               error_logger:tty(true),
               cleanup([]) end
       end,
       ?FORALL(Cmds, commands(?MODULE),
               begin
                 ok = application:ensure_started(gproc),
                 %% simulate that aehttp is running
                 gproc:reg({n,l,{epoch, app, aehttp}}),
                 {H, S, Res} = run_commands(Cmds),
                 NoCrash =
                   lists:all(fun(X) when is_pid(X) ->
                                 erlang:is_process_alive(X);
                                (X) ->
                                 X == undefined
                             end,
                             [S#state.aec_peers_pid, S#state.aec_sync_pid]),
                 cleanup([S#state.aec_peers_pid, S#state.aec_sync_pid]),
                 application:stop(gproc),
                 check_command_names(Cmds,
                   measure(length, commands_length(Cmds),
                   aggregate(call_features(H),
                   pretty_commands(?MODULE, Cmds, {H, S, Res},
                        conjunction(
                          [{result, Res == ok},
                           {crash, NoCrash},
                           {queue, is_list(S#state.queue)}])))))
               end))).


cleanup(Pids) ->
  [ catch stop() ] ++
    [ exit(Pid, kill) || Pid <- Pids, is_pid(Pid) ].

bugs() -> bugs(10).

bugs(N) -> bugs(N, []).

bugs(Time, Bugs) ->
  more_bugs(eqc:testing_time(Time, prop_sync()), 20, Bugs).

encode(Bin) ->
  aeser_api_encoder:encode(key_block_hash, Bin).

%% -- API-spec ---------------------------------------------------------------
api_spec() -> #api_spec{ language = erlang, mocking = eqc_mocking,
                         modules = [ aehttp_app_spec(),
                                     jobs_spec(),
                                     aec_conductor_spec(),
                                     aeu_http_client_spec(),
                                     aec_keys_spec()
                                   ] }.

aeu_requests_spec() ->
  #api_module{
     name = aeu_requests,
     functions =
       [ #api_fun{ name = ping, arity = 1},
         #api_fun{ name = parse_uri, arity = 1},
         #api_fun{ name = pp_uri, arity = 1}
       ]}.

aehttp_app_spec() ->
  #api_module{
     name = aehttp_app,
     functions =
       [ #api_fun{ name = local_peer_uri, arity = 0}
       ]}.

aeu_http_client_spec() ->
  #api_module{
     name = aeu_http_client,
     functions =
       [ #api_fun{ name = request, arity = 3}
       ]}.

jobs_spec() ->
  #api_module{
     name = jobs,
     functions =
       [ #api_fun{ name = enqueue, arity = 2},
         #api_fun{ name = dequeue, arity = 2}
       ] }.

aec_conductor_spec() ->
  #api_module{
     name = aec_conductor,
     functions =
       [ #api_fun{ name = genesis_hash, arity = 0},
         #api_fun{ name = top_header_hash, arity = 0},
         #api_fun{ name = get_total_difficulty, arity = 0}
       ] }.

aec_keys_spec() ->
  #api_module{
     name = aec_keys, fallback = aec_keys_mock,
     functions =
       [
       ] }.

%% -- Generators -------------------------------------------------------------

uri() ->
  elements([{http, "129.1.2.3", 3013}, {http, "129.1.2.3", 3012}, {http, "192.1.1.0", 80}, {http, "my_computer", 80},
            {http, "localhost", 3013}, {http, "127.0.0.1", 3013}, {http, "localhost", 8043}, error ]).

myhost() ->
  {ok, Host} = inet:gethostname(),
  {http, Host, 3013}.

local_peer({http, Host, Port}) ->
  {http, LocalHost, LocalPort} = myhost(),
  Port == LocalPort andalso lists:member(Host, ["127.0.0.1", "localhost", LocalHost]).

pp(error) ->
  "http:blafoo";
pp({http, String}) ->
  lists:concat(["http://", String]);
pp({http, String, Port}) ->
  lists:concat(["http://", String, ":", Port]).

parse(String) ->
  case http_uri:parse(String) of
    {ok, {Scheme, _UserInfo, Host, Port, _Path, _Query, _Fragment}} ->
      [{Scheme, Host, Port}];
    {ok, {Scheme, _UserInfo, Host, Port, _Path, _Query}} ->
      [{Scheme, Host, Port}];
    {error, _Reason} ->
      []
  end.

difficulty() ->
  elements([4.0, 5.0]).

full_peer({Scheme, Host}) -> {Scheme, Host, 80};
full_peer(Uri) -> Uri.
