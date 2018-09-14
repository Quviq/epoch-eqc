%%% @author Thomas Arts 
%%% @doc Testing state channel fsm at system test level.
%%%
%%%      The idea is that these tests could run on UAT as well.
%%%      For that reason, we cannot assume any specific height or nonces of the root account.
%%%      The Patron is the account that has a lot of tokens and we start by reading 
%%%      that account and creating working accounts from it.
%%%
%%%      Running: rebar3 as system_test, test shell
%%%
%%%
%%% @end
%%% Created : 17 May 2018 by Thomas Arts 
%%% Updated :  5 Sep 2018 by Thomas Arts

-module(state_channel_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

%% -- State and state functions ----------------------------------------------
-record(state,{nodes = [], accounts = [], nonce_delta = 1, 
               running = [], http_ready = [],
               channels = [],
               height = 0,
               tx_hashes = [], %% symbolic !
               users = []
              }).

-record(user, {name, balance, nonce}).

-record(account, { pubkey,
                   balance,
                   privkey,
                   nonce = 0}).

-record(channel, {status, %% open | created (on chain)
                  id, 
                  port,
                  initiator,
                  total,
                  responder,
                  lock_period,
                  channel_reserve,
                  push_amount,
                  ttl,
                  round = 0  %% this is also placeholder for computing state hash
                 }). 

-define(DELTA_TTL, 10).  %% times 5? minutes on UAT

initial_state() ->
  #state{}.

postcondition_common(_S, _Call, {'EXIT', _}) ->
    false;
postcondition_common(_S, _Call, _Res) ->
    true.

%% -- Generators -------------------------------------------------------------

systems(N) ->
  [ list_to_atom(lists:concat([node, Name])) || Name <- lists:seq(1,N) ].

%% Absolute TTLs are hard to test, thinking required
gen_ttl(Height) ->
  ?LET(TTL, choose(0, 20), Height + (20 - TTL)).

ttl(S, N) when is_integer(N) ->
  {S#state.height, N};
ttl(S, {_H, Gen}) ->
  {S#state.height, Gen};
ttl(_S, optional) ->
  optional.


at_most(X) ->
  noshrink(choose(0, max(0, X))).
  

%% -- Operations -------------------------------------------------------------

%% --- Operation: start ---
start_pre(S) ->
  length(S#state.nodes) > length(S#state.running).

start_args(S) ->
  [elements([ Name || Name <- S#state.nodes, 
                      not lists:member(Name, S#state.running)])].

start_pre(S, [Node]) ->
  not lists:member(Node, S#state.running).

start(Node) ->
  aest_nodes_mgr:start_node(Node).

start_next(S, _Value, [Node]) ->
  S#state{ running = S#state.running ++ [Node]}.

%% --- Operation: patron ---
http_ready_pre(S) ->
  S#state.running =/= [].

http_ready_args(S) ->
  [elements(S#state.running)].

http_ready_pre(S, [Node]) ->
  lists:member(Node, S#state.running) andalso not lists:member(Node, S#state.http_ready).

http_ready(Node) ->
  try 
      %% possibly add {node_startup_time, 20000} to options list
      aest_nodes:wait_for_startup([Node], 0, [{ct_log,  false}]),
      aest_nodes:get_top(Node)
  catch _:Reason ->
      {'EXIT', Reason}
  end.

http_ready_next(S, Value, [Node]) ->
  S#state{http_ready = S#state.http_ready ++ [Node],
          height = {call, ?MODULE, top_height, [Value, S#state.height]} }.


%% --- Operation: stop ---
stop_pre(S) ->
  S#state.running =/= [].

%% stop_args(S) ->
%%   [elements(S#state.running)].

stop_pre(S, [Node]) ->
  lists:member(Node, S#state.running).

stop(Node) ->
  aest_nodes_mgr:stop_node(Node, infinity).

stop_next(S, _Value, [Node]) ->
  S#state{running = S#state.running -- [Node],
          http_ready = S#state.http_ready -- [Node]}.

%% --- add_account ---
add_account_pre(S) ->
  S#state.http_ready =/= [].

add_account_args(S) ->
  noshrink(
  [elements(S#state.http_ready), 
   patron, S#state.nonce_delta, account_gen(oneof([71, 200, 500, 1000])), 
   fee(), ttl(S, ?DELTA_TTL), <<"quickcheck">>]).

add_account_pre(S, [Node, _Sender, Nonce, {Name, _Balance}, Fee, TTL, _Payload]) ->
  not lists:keymember(Name, #user.name, S#state.accounts) andalso
    lists:member(Node, S#state.http_ready) andalso 
    check_ttl(S, TTL) andalso
    S#state.nonce_delta == Nonce andalso
    %% and valid
    Fee >= aec_governance:minimum_tx_fee().

add_account_adapt(S, [Node, Sender, _Nonce, NewAccount, Fee, TTL, Payload]) ->
  [Node, Sender, S#state.nonce_delta, NewAccount, Fee, ttl(S, TTL), Payload].

add_account(Node, From, Nonce, {Name, Balance}, Fee, {SeenHeight, DeltaTTL}, Payload) ->
  #{ public := PubKey, secret := PrivKey} = enacl:sign_keypair(),
  Receiver = #account{ pubkey = PubKey, balance = Balance, privkey = PrivKey },
  ets:insert(accounts, {Name, Receiver}),
  [{_, Sender}] = ets:lookup(accounts, From),
  #{tx_hash := TxHash} = 
        aest_nodes:post_spend_tx(Node, 
                                 #{pubkey => Sender#account.pubkey,
                                   privkey =>Sender#account.privkey}, 
                                 #{pubkey => Receiver#account.pubkey}, 
                                 Sender#account.nonce + Nonce, 
                                 #{ amount    => Receiver#account.balance,   %% we create it with this much
                                    fee       => Fee,
                                    payload   => Payload}),
    TxHash.

add_account_next(S, Value, [_Node, _Sender, _Nonce, {Name, Balance}, _Fee, _TTL, _Payload]) ->
  %% We assume there are always enough tokens in patron account
  S#state{ accounts = S#state.accounts ++ [#user{name = Name, balance = Balance, nonce = 0}],
           tx_hashes = [Value | S#state.tx_hashes],
           nonce_delta = S#state.nonce_delta + 1}.

add_account_features(S, [_Node, _Sender, _Nonce, _Receiver, _Fee, {SeenHeight, DeltaTTL}, _Payload], _Res) ->
  [ {accounts, length(S#state.accounts) + 1},
    {accounts, ttl_delta_overshoot, (SeenHeight + DeltaTTL) - S#state.height} ] .


%% --- create_account (within 5 seconds) ---
create_account_pre(S) ->
  S#state.http_ready =/= [].

create_account_args(S) ->
  noshrink(
  [elements(S#state.http_ready), 
   patron, S#state.nonce_delta, account_gen(oneof([71, 200, 500, 1000])), 
   fee(), ttl(S, ?DELTA_TTL), <<"quickcheck create account">>]).

create_account_pre(S, [Node, _Sender, Nonce, {Name, _Balance}, Fee, TTL, _Payload]) ->
  not lists:keymember(Name, #user.name, S#state.accounts) andalso
    lists:member(Node, S#state.http_ready) andalso 
    check_ttl(S, TTL) andalso
    S#state.nonce_delta == Nonce andalso
    %% and valid
    Fee >= aec_governance:minimum_tx_fee().

create_account_adapt(S, [Node, Sender, _Nonce, NewAccount, Fee, TTL, Payload]) ->
  [Node, Sender, S#state.nonce_delta, NewAccount, Fee, ttl(S, TTL), Payload].

create_account(Node, From, Nonce, {Name, Balance}, Fee, {SeenHeight, DeltaTTL}, Payload) ->
  #{ public := PubKey, secret := PrivKey} = enacl:sign_keypair(),
  Receiver = #account{ pubkey = PubKey, balance = Balance, privkey = PrivKey },
  ets:insert(accounts, {Name, Receiver}),
  [{_, Sender}] = ets:lookup(accounts, From),
  #{tx_hash := TxHash} = 
        aest_nodes:post_spend_tx(Node, 
                                 #{pubkey => Sender#account.pubkey,
                                   privkey =>Sender#account.privkey}, 
                                 #{pubkey => Receiver#account.pubkey}, 
                                 Sender#account.nonce + Nonce, 
                                 #{ amount    => Receiver#account.balance,   %% we create it with this much
                                    fee       => Fee,
                                    payload   => Payload}),
  aest_nodes:wait_tx_on_chain(Node, TxHash, 5000). %% This is the difference to an add, we wait until it's there

create_account_next(S, Value, [_Node, _Sender, _Nonce, {Name, Balance}, _Fee, _TTL, _Payload]) ->
  %% We assume there are always enough tokens in patron account
  S#state{ accounts = S#state.accounts ++ [#user{name = Name, balance = Balance, nonce = 0}],
           nonce_delta = S#state.nonce_delta + 1}.

create_account_post(_S, [_Node, _Sender, _Nonce, _Receiver, _Fee, _TTL, _Payload], Res) ->
  eq(Res, ok).



%% --- Operation: pingpong ---
pingpong_pre(S) ->
  S#state.http_ready =/= [] andalso length(S#state.accounts) > 1.

pingpong_args(S) ->
  ?LET({[Account1, Account2 | _], Fee, TTL},
       {shuffle(S#state.accounts), fee(), ttl(S, ?DELTA_TTL)},
       [elements(S#state.http_ready), 
        #{from => Account1#user.name, 
          from_nonce => Account1#user.nonce + 1, 
          to => Account2#user.name,
          to_nonce => Account2#user.nonce + 1,
          fee => Fee, ttl => TTL}]).
       
pingpong_pre(S, [Node, #{from := From, from_nonce := FNonce, to := To,
                         to_nonce := TNonce, ttl := TTL} = Tx]) ->
  Account1 = lists:keyfind(From, #user.name, S#state.accounts),
  Account2 = lists:keyfind(To, #user.name, S#state.accounts),
  lists:member(Node, S#state.http_ready) andalso 
    Account1 /= false andalso Account2 /= false andalso
    Account1#user.nonce + 1 == FNonce andalso
    Account2#user.nonce + 1 == TNonce andalso
    check_ttl(S, TTL) andalso 
    pingpong_valid(S, [Node, Tx]).

pingpong_valid(S, [_Node, #{from := From, to := To, fee := Fee}]) ->
  Account1 = lists:keyfind(From, #user.name, S#state.accounts),
  Account2 = lists:keyfind(To, #user.name, S#state.accounts),
  Fee >= aec_governance:minimum_tx_fee() andalso
    Account1#user.balance >= Fee + 1 andalso
    Account2#user.balance >= Fee.

%% Adaption seems to break symbiolic call in _next !! fix QuickCheck
%% pingpong_adapt(S, [Node, #{from := From, to := To, ttl := TTL} = Tx]) ->
%%   case {lists:keyfind(From, #user.name, S#state.accounts), 
%%         lists:keyfind(To, #user.name, S#state.accounts)} of
%%     {false, _} -> false;
%%     {_, false} -> false;
%%     {Account1, Account2} ->
%%       [Node, Tx#{from_nonce => Account1#user.nonce + 1, to_nonce =>
%%                    Account2#user.nonce, ttl => ttl(S, TTL)}]
%%   end.

pingpong(Node, #{fee := Fee} = Tx) ->
  [{_, Account1}] = ets:lookup(accounts, maps:get(from, Tx)),
  [{_, Account2}] = ets:lookup(accounts, maps:get(to, Tx)),
  Payload = integer_to_list(aeu_time:now_in_msecs()) ++ " quickcheck",
  TTL = case maps:get(ttl, Tx, 0) of
            optional -> 0; %% not supported yet
            {H, Delta} -> H + Delta
        end,
  #{tx_hash := PingTx} = 
        aest_nodes:post_spend_tx(Node, 
                                 #{pubkey =>  Account1#account.pubkey,
                                   privkey => Account1#account.privkey}, 
                                 #{pubkey => Account2#account.pubkey}, 
                                 maps:get(from_nonce, Tx), 
                                 #{ amount    => 1,   %% we create it with this much
                                    fee       => Fee,
                                    ttl       => TTL,
                                    payload   => iolist_to_binary([Payload, " ping"])}),
  #{tx_hash := PongTx} = 
        aest_nodes:post_spend_tx(Node, 
                                 #{pubkey =>  Account2#account.pubkey,
                                   privkey => Account2#account.privkey}, 
                                 #{pubkey => Account1#account.pubkey}, 
                                 maps:get(to_nonce, Tx), 
                                 #{ amount    => 1,   %% we create it with this much
                                    fee       => Fee,
                                    ttl       => TTL,
                                    payload   => iolist_to_binary([Payload, " pong"])}),
  [PingTx, PongTx].

pingpong_next(S, Value, [_Node, #{from := From, from_nonce := FN, 
                                   to := To, to_nonce := TN, fee := Fee}]) ->
  Account1 = lists:keyfind(From, #user.name, S#state.accounts),
  Account2 = lists:keyfind(To, #user.name, S#state.accounts),
  Accounts = 
    lists:keyreplace(Account1#user.name, #user.name,
                     lists:keyreplace(Account2#user.name, #user.name, 
                                      S#state.accounts, 
                                      Account2#user{ balance =
                                   Account2#user.balance - Fee, nonce = TN }),
                     Account1#user{ balance = Account1#user.balance - Fee,
                                    nonce = FN }),
  S#state{accounts = Accounts,
          tx_hashes = {call, lists, append, [Value , S#state.tx_hashes]}}.

pingpong_post(_S, [_Account1, _Account2], Res) ->
  case Res of
    [ _, _] -> true;
    _ ->
      Res
  end.

%% --- Operation: open_channel ---
open_channel_pre(S) ->
  false andalso S#state.http_ready =/= [] andalso length(S#state.accounts) > 1.

open_channel_args(S) ->
  ?LET({Initiator, Fee}, {elements(S#state.accounts), fee()},
  ?LET({Responder, Reserve},
       {elements(S#state.accounts -- [Initiator]), 
        at_most(Initiator#user.balance)},
       [elements(S#state.http_ready),
        #{initiator => Initiator#user.name, 
          responder => Responder#user.name,
          initiator_amount => at_most(Initiator#user.balance - Fee),
          responder_amount => at_most(Responder#user.balance),
          lock_period => choose(0,5), %% lock period
          ttl => ttl(S, ?DELTA_TTL), %% ttl (we need height for this)
          fee => Fee, %% fee
          channel_reserve => Reserve,
          push_amount => noshrink(choose(0,200)),
          nonce => Initiator#user.nonce + 1}
       ])).

open_channel_pre(S, [Node, #{initiator := Initiator, responder := Responder, 
                             nonce := Nonce, ttl := TTL} = Tx]) ->
  InAccount = lists:keyfind(Initiator, #user.name, S#state.accounts),
  RespAccount = lists:keyfind(Responder, #user.name, S#state.accounts),
  lists:member(Node, S#state.http_ready) andalso 
    InAccount /= false andalso RespAccount /= false andalso
    InAccount#user.nonce + 1 == Nonce andalso 
    check_ttl(S, TTL) andalso 
    open_channel_valid(S, [Node, Tx]).

open_channel_valid(S, [_Node, #{initiator := Initiator, responder := Responder, 
                                fee := Fee} = Tx]) ->
  InAccount = lists:keyfind(Initiator, #user.name, S#state.accounts),
  RespAccount = lists:keyfind(Responder, #user.name, S#state.accounts),
  Responder =/= Initiator andalso
    Fee >= aec_governance:minimum_tx_fee() andalso 
    InAccount#user.balance >= maps:get(initiator_amount, Tx) + Fee andalso
    maps:get(initiator_amount, Tx) >= maps:get(channel_reserve, Tx) andalso
    maps:get(responder_amount, Tx) >= maps:get(channel_reserve, Tx) andalso
    RespAccount#user.balance >= maps:get(responder_amount, Tx).


open_channel_adapt(S, [Node, #{initiator := Initiator,  ttl := TTL} = Tx]) ->
  case lists:keyfind(Initiator, #user.name, S#state.accounts) of
    false -> false;
    InAccount ->
      [Node, Tx#{nonce => InAccount#user.nonce + 1, ttl => ttl(S, TTL)}]
  end.

open_channel(Node, #{initiator := In, responder := Resp} = Tx) ->
  [{_, Initiator}] = ets:lookup(accounts, In),
  [{_, Responder}] = ets:lookup(accounts, Resp),
  Round = 0,
  EncodedTx =
    optional_ttl(Tx#{initiator => aec_base58c:encode(account_pubkey, Initiator#account.pubkey),
                     responder => aec_base58c:encode(account_pubkey, Responder#account.pubkey),
                     state_hash => aec_base58c:encode(state, <<Round:256>>)}),
  case request(Node, 'PostChannelCreate', EncodedTx) of
    {ok, 200, #{tx := TxObject}} ->
      {ok, Bin} = aec_base58c:safe_decode(transaction, TxObject),
      InitiatorSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                [Initiator#account.privkey]),
      ResponderSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                [Responder#account.privkey]),
      BothSigned = 
        aetx_sign:add_signatures(ResponderSignedTx, aetx_sign:signatures(InitiatorSignedTx)),
      Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(BothSigned)),
      request(Node, 'PostTx', #{tx => Transaction});
    Error ->
      Error
  end.

open_channel_next(S, Value, [_Node, #{initiator := In, responder := Resp,
                                      fee := Fee, nonce := Nonce} = Tx]) ->
  Initiator = lists:keyfind(In, #user.name, S#state.accounts),
  Responder = lists:keyfind(Resp, #user.name, S#state.accounts),
  Accounts = 
    lists:keyreplace(Resp, #user.name,
                     lists:keyreplace(In, #user.name, 
                                      S#state.accounts, 
                                      Initiator#user{ balance = Initiator#user.balance - Fee - maps:get(initiator_amount, Tx),
                                                      nonce = Nonce }),
                     Responder#user{ balance = Responder#user.balance - maps:get(responder_amount, Tx)}),
  S#state{ channels = S#state.channels ++ [ #channel{status = open,
                                                     id = {In, Nonce, Resp},
                                                     initiator = In,
                                                     responder = Resp,
                                                     total = maps:get(initiator_amount, Tx) + maps:get(responder_amount, Tx),
                                                     lock_period = maps:get(lock_period, Tx),
                                                     channel_reserve = maps:get(channel_reserve, Tx),
                                                     push_amount = maps:get(push_amount, Tx),
                                                     ttl = maps:get(ttl, Tx)} ],
           tx_hashes = [{call, ?MODULE, ok200, [Value, tx_hash]} | S#state.tx_hashes],
           accounts = Accounts }.

open_channel_post(_S, [_Node, _], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> 
      Res
  end.

open_channel_features(S, [_Node, #{responder := Resp} = Tx], _) ->
  Responder = lists:keyfind(Resp, #user.name, S#state.accounts),
  [ {open_channel, responder_balance_less_responder_amount} ||
    not (Responder#user.balance >= maps:get(responder_amount, Tx)) ].

channel_account(_S, false, _) ->
  false;
channel_account(S, #channel{responder = From}, responder) ->
  lists:keyfind(From, #user.name, S#state.accounts);
channel_account(S, #channel{initiator = From}, initiator) ->  
  lists:keyfind(From, #user.name, S#state.accounts);
channel_account(S, Id, Party) when is_tuple(Id) ->
  Channel = lists:keyfind(Id, #channel.id, S#state.channels),
  channel_account(S, Channel, Party).



%% --- Operation: deposit ---
deposit_pre(S) ->
  S#state.http_ready =/= [] andalso 
    lists:keymember(created, #channel.status, S#state.channels).

deposit_args(S) ->
  ?LET({Channel, Party}, {elements([ Ch || #channel{status = created} = Ch <- S#state.channels]), 
                          oneof([initiator, responder])},
       begin
         From = channel_account(S, Channel, Party),
         [elements(S#state.http_ready),
          #{from => Party,
            channel_id => Channel#channel.id,
            amount => at_most(From#user.balance),
            ttl => ttl(S, ?DELTA_TTL),
            fee => fee(),
            nonce => From#user.nonce + 1,
            round => Channel#channel.round + 1 }
         ]
       end).

deposit_pre(S, [Node,
                #{channel_id := Ch, from := Party, nonce := Nonce, ttl := TTL} = Tx]) ->
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  Account = channel_account(S, Channel, Party),
  lists:member(Node, S#state.http_ready) andalso
    Channel /= false andalso
    Channel#channel.status == created andalso 
    Account /= false andalso Account#user.nonce + 1 == Nonce andalso
    check_ttl(S, TTL) andalso
    deposit_valid(S, Tx).

deposit_valid(S, #{channel_id := Ch, from := Party, amount := Amount, fee := Fee}) ->
  Account = channel_account(S, Ch, Party),
  Fee >= aec_governance:minimum_tx_fee() andalso 
    Account#user.balance >= Amount + Fee.

%% channel.round is monotonically increasing, no need to adapt when leaving out some
deposit_adapt(S, [Node, #{from := Party, channel_id := Ch, ttl := TTL} = Tx]) ->
  case channel_account(S, Ch, Party) of
    false -> false;
    Account ->
      [Node, Tx#{nonce => Account#user.nonce + 1, ttl => ttl(S, TTL)}]
  end.

deposit(Node, #{from := Party, channel_id := Ch, round := Round} = Tx) ->
  {Initiator, OrgNonce, Responder} = Ch,
  [{_, In}] = ets:lookup(accounts, Initiator), 
  [{_, Resp}] = ets:lookup(accounts, Responder), 
  Id = aesc_channels:id(In#account.pubkey, OrgNonce, Resp#account.pubkey),
  From = if Party == initiator -> In;
            Party == responder -> Resp
         end,
  EncodedTx = 
    optional_ttl(Tx#{from => aec_base58c:encode(account_pubkey, From#account.pubkey),
                     channel_id => aec_base58c:encode(channel, Id),
                     state_hash => aec_base58c:encode(state, <<Round:256>>)}),
  case request(Node, 'PostChannelDeposit', EncodedTx) of
    {ok, 200, #{tx := TxObject}} ->
      {ok, Bin} = aec_base58c:safe_decode(transaction, TxObject),
      InitiatorSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                [In#account.privkey]),
      ResponderSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                [Resp#account.privkey]),
      BothSigned = 
        aetx_sign:add_signatures(ResponderSignedTx, aetx_sign:signatures(InitiatorSignedTx)),
      Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(BothSigned)),
      request(Node, 'PostTx', #{tx => Transaction});
    Error ->
      Error
  end.

%% Due to adapt, Channel is the one we have in the state
deposit_next(S, Value, [_Node, #{channel_id := Ch, from := Party, fee := Fee, amount := Amount, 
                                 nonce := Nonce, round := Round}]) ->
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  Account = channel_account(S, Channel, Party),
  Accounts = 
    lists:keyreplace(Account#user.name, #user.name, 
                     S#state.accounts, 
                     Account#user{ balance = Account#user.balance - (Fee + Amount),
                                   nonce = Nonce }),
  NewChannel = Channel#channel{total = Channel#channel.total + Amount, round = Round},
  Channels = lists:keyreplace(Ch, #channel.id, S#state.channels, NewChannel),
  S#state{ channels = Channels,
           tx_hashes = [{call, ?MODULE, ok200, [Value, tx_hash]} | S#state.tx_hashes],
           accounts = Accounts }.

deposit_post(_S, [_Node, _], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> 
      Res
  end.

deposit_features(_S, [_, #{from := Party}], _Res) ->
  [{channel_deposit, Party}].

%% --- Operation: withdraw ---
withdraw_pre(S) ->
  S#state.http_ready =/= [] andalso 
    lists:keymember(created, #channel.status, S#state.channels).

withdraw_args(S) ->
  ?LET({Channel, Party, Fee}, {elements([ Ch || #channel{status = created} = Ch <- S#state.channels]), 
                               oneof([initiator, responder]), fee()},
       begin
         From = channel_account(S, Channel, Party),
         [elements(S#state.http_ready),
          #{to => Party,
            channel_id => Channel#channel.id,
            amount => at_most(Channel#channel.total),
            ttl => ttl(S, ?DELTA_TTL),
            fee => Fee,
            nonce => From#user.nonce + 1,
            round => Channel#channel.round }
         ]
       end).

withdraw_pre(S, [Node,
                #{channel_id := Ch, to := Party, nonce := Nonce, ttl := TTL} = Tx]) ->
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  Account = channel_account(S, Channel, Party),
  lists:member(Node, S#state.http_ready) andalso
    Channel /= false andalso
    Channel#channel.status == created andalso 
    Account /= false andalso Account#user.nonce + 1 == Nonce andalso
    check_ttl(S, TTL) andalso
    withdraw_valid(S, Tx).

withdraw_valid(S, #{channel_id := Ch, to := Party, amount := Amount, fee := Fee}) ->
  Account = channel_account(S, Ch, Party),
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  Fee >= aec_governance:minimum_tx_fee() andalso 
    Account#user.balance >= Fee andalso
    Channel#channel.total =< Amount.

withdraw_adapt(S, [Node, #{to := Party, channel_id := Ch, ttl := TTL} = Tx]) ->
  case channel_account(S, Ch, Party) of
    false -> false;
    Account ->
      [Node, Tx#{nonce => Account#user.nonce + 1, ttl => ttl(S, TTL)}]
  end.

withdraw(Node, #{to := Party, channel_id := Ch, round := Round} = Tx) ->
  {Initiator, OrgNonce, Responder} = Ch,
  [{_, In}] = ets:lookup(accounts, Initiator), 
  [{_, Resp}] = ets:lookup(accounts, Responder), 
  Id = aesc_channels:id(In#account.pubkey, OrgNonce, Resp#account.pubkey),
  From = if Party == initiator -> In;
            Party == responder -> Resp
         end,
  EncodedTx = 
    optional_ttl(Tx#{to => aec_base58c:encode(account_pubkey, From#account.pubkey),
                     channel_id => aec_base58c:encode(channel, Id),
                     state_hash => aec_base58c:encode(state, <<Round:256>>)}),
  case request(Node, 'PostChannelWithdrawal', EncodedTx) of
    {ok, 200, #{tx := TxObject}} ->
      {ok, Bin} = aec_base58c:safe_decode(transaction, TxObject),
      InitiatorSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                [In#account.privkey]),
      ResponderSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                [Resp#account.privkey]),
      BothSigned = 
        aetx_sign:add_signatures(ResponderSignedTx, aetx_sign:signatures(InitiatorSignedTx)),
      Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(BothSigned)),
      request(Node, 'PostTx', #{tx => Transaction});
    Error ->
      Error
  end.

%% Due to adapt, Channel is the one we have in the state
withdraw_next(S, Value, [_Node, #{channel_id := Ch, to := Party, fee := Fee, amount := Amount, 
                                  nonce := Nonce, round := Round}]) ->
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  Account = channel_account(S, Channel, Party),
  Accounts = 
    lists:keyreplace(Account#user.name, #user.name, 
                     S#state.accounts, 
                     Account#user{ balance = Account#user.balance - Fee + Amount,
                                   nonce = Nonce }),
  NewChannel =
    Channel#channel{total = Channel#channel.total - Amount, round = Round},
  Channels = lists:keyreplace(Ch, #channel.id, S#state.channels, NewChannel),
  S#state{ channels = Channels,
           tx_hashes = [{call, ?MODULE, ok200, [Value, tx_hash]} | S#state.tx_hashes],
           accounts = Accounts }.

withdraw_post(_S, [_Node, _], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> 
      Res
  end.

withdraw_features(_S, [_, #{to := Party}], _Res) ->
  [{channel_withdraw, Party}].



%% --- Operation: close_mutual ---
close_mutual_pre(S) ->
  S#state.http_ready =/= [] andalso 
    lists:keymember(created, #channel.status, S#state.channels).

close_mutual_args(S) ->
  ?LET({Channel, Fee}, {elements([ Ch || #channel{status = created} = Ch <- S#state.channels]), fee()},
       begin
         Account = channel_account(S, Channel, initiator),
           ?LET(Settle, at_most(Channel#channel.total - Fee),
                [elements(S#state.http_ready),
                 #{channel_id => Channel#channel.id,
                   initiator_amount => Settle,
                   responder_amount => Channel#channel.total - Fee - Settle ,
                   ttl => ttl(S, ?DELTA_TTL), %% ttl (we need height for this)
                   fee => Fee,
                   nonce => Account#user.nonce + 1}
                ])
       end).

close_mutual_pre(S, [Node, 
                     #{channel_id := Ch, nonce := Nonce, ttl := TTL} = Tx]) ->
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  Account = channel_account(S, Channel, initiator),
  lists:member(Node, S#state.http_ready) andalso
    Channel /= false andalso Channel#channel.status == created andalso
    Account /= false andalso Account#user.nonce + 1 == Nonce andalso
    check_ttl(S, TTL) andalso
    close_mutual_valid(Channel, Tx).

%% New InAmount + RespAmout + Fee == Channel.inanmount + Channel.respamount
close_mutual_valid(Channel, #{initiator_amount := InAmount, responder_amount := RespAmount, fee := Fee}) ->
  Fee >= aec_governance:minimum_tx_fee() andalso 
  InAmount + RespAmount >= Fee andalso
    Channel#channel.total == InAmount + RespAmount + Fee.

%% If the channel does not exist, we cannot replace it
%% Adapting Channel Id and other values results in too complex code
close_mutual_adapt(S, [Node, #{channel_id := Ch, ttl := TTL} = Tx]) ->
  case channel_account(S, Ch, initiator) of
    false -> false;
    Account ->
      [Node, Tx#{nonce => Account#user.nonce + 1, ttl => ttl(S, TTL)}]
  end.

close_mutual(Node, #{channel_id := Ch} = Tx) ->
  {Initiator, OrgNonce, Responder} = Ch,
  [{_, In}] = ets:lookup(accounts, Initiator), 
  [{_, Resp}] = ets:lookup(accounts, Responder), 
  Id = aesc_channels:id(In#account.pubkey, OrgNonce, Resp#account.pubkey),
  EncodedTx =
    optional_ttl(Tx#{channel_id => aec_base58c:encode(channel, Id)}),
  case request(Node, 'PostChannelCloseMutual', EncodedTx) of
    {ok, 200, #{tx := TxObject}} ->
      {ok, Bin} = aec_base58c:safe_decode(transaction, TxObject),
      InitiatorSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                [In#account.privkey]),
      ResponderSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                [Resp#account.privkey]),
      BothSigned = 
        aetx_sign:add_signatures(ResponderSignedTx, aetx_sign:signatures(InitiatorSignedTx)),
      Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(BothSigned)),
      request(Node, 'PostTx', #{tx => Transaction});
    Error ->
      Error
  end.

close_mutual_next(S, Value, [_Node,  #{channel_id := Ch, nonce := Nonce, 
                                       initiator_amount := IA, responder_amount := RA}]) ->
  Initiator = channel_account(S, Ch, initiator),
  Responder = channel_account(S, Ch, responder),
  Accounts =
    lists:keyreplace(Responder#user.name, #user.name,
    lists:keyreplace(Initiator#user.name, #user.name, 
                     S#state.accounts, 
                     Initiator#user{ balance = Initiator#user.balance + IA,
                                     nonce = Nonce }),
                     Responder#user{ balance = Responder#user.balance + RA } ),
  S#state{ channels = lists:keydelete(Ch, #channel.id, S#state.channels),
           tx_hashes = [{call, ?MODULE, ok200, [Value, tx_hash]} | S#state.tx_hashes],
           accounts = Accounts }.

close_mutual_post(_S, [_Node, _], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> 
      Res
  end.

close_mutual_features(_S, [_, #{initiator_amount := InAmount, responder_amount := RespAmount, fee := Fee}], _Res) ->
  [{close_mutual, even} ||  (InAmount + RespAmount ) rem 2 == 0 ] ++
    [{close_mutual, odd} ||  (InAmount + RespAmount ) rem 2 == 1 ] ++ 
    [{close_mutual, to_initiator} ||  RespAmount < floor(Fee/2) ] ++
    [{close_mutual, to_responder} ||  InAmount < floor(Fee/2) ].




%% --- Operation: close_solo ---
close_solo_pre(S) ->
  S#state.http_ready =/= [] andalso 
    lists:keymember(created, #channel.status, S#state.channels).

close_solo_args(S) ->
  ?LET({Channel, Fee, Party}, {elements([ Ch || #channel{status = created} = Ch <- S#state.channels]), fee(), 
                        oneof([initiator, responder])},
       begin
         Account = channel_account(S, Channel, Party),
         [elements(S#state.http_ready),
          #{channel_id => Channel#channel.id,
            from => Party,
            payload => <<>>,  %% this means cloased according to last on_chain transaction (i.e. Channel)
            ttl => ttl(S, ?DELTA_TTL), %% ttl (we need height for this)
            poi => 2,
            fee => Fee,
            nonce => Account#user.nonce + 1}
         ]
       end).

close_solo_pre(S, [Node, #{channel_id := Ch, nonce := Nonce, ttl := TTL, from := Party} = Tx]) ->
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  Account = channel_account(S, Channel, Party),
  lists:member(Node, S#state.http_ready) andalso
    Channel /= false andalso  %% Channel#channel.status == created andalso
    Account /= false andalso Account#user.nonce + 1 == Nonce andalso
    check_ttl(S, TTL) andalso
    close_solo_valid(Channel, Tx).

close_solo_valid(_Channel, #{fee := Fee}) ->
  Fee >= aec_governance:minimum_tx_fee().

%% poi may have to be replaced!
close_solo_adapt(S, [Node, #{channel_id := Ch, ttl := TTL} = Tx]) ->
  case channel_account(S, Ch, initiator) of
    false -> false;
    Account ->
      [Node, Tx#{nonce => Account#user.nonce + 1, ttl => ttl(S, TTL)}]
  end.

close_solo(Node, #{channel_id := Ch, from := Party, poi := Poi} = Tx) ->
  {Initiator, OrgNonce, Responder} = Ch,
  [{_, In}] = ets:lookup(accounts, Initiator), 
  [{_, Resp}] = ets:lookup(accounts, Responder),
  Id = aesc_channels:id(In#account.pubkey, OrgNonce, Resp#account.pubkey),
  ProofOfInclusion = poi([{In#account.pubkey, 12},
                          {Resp#account.pubkey, 14}]),
  From = if Party == initiator -> In;
            Party == responder -> Resp
         end,
  EncodedTx = 
    optional_ttl(Tx#{from => aec_base58c:encode(account_pubkey, From#account.pubkey),
                     channel_id => aec_base58c:encode(channel, Id),
                     poi => aec_base58c:encode(poi, <<Poi:16>>)}
                ),
  case request(Node, 'PostChannelCloseSolo', EncodedTx) of
    {ok, 200, #{tx := TxObject}} ->
      {ok, Bin} = aec_base58c:safe_decode(transaction, TxObject),
      FromSignedTx = aec_test_utils:sign(aetx:deserialize_from_binary(Bin), 
                                    [From#account.privkey]),
      Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(FromSignedTx)),
      request(Node, 'PostTx', #{tx => Transaction});
    Error ->
      Error
  end.

close_solo_next(S, _Value, [_Node, _Tx]) ->
  S.

close_solo_post(_S, [_Node, _Tx], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> 
      Res
  end.

close_solo_features(S, [_Node, #{channel_id := Ch, fee := Fee}], _Res) ->
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  [ fee_more_than_total || Fee > Channel#channel.total ].


poi(Accounts) ->  
  aesc_test_utils:proof_of_inclusion(Accounts).



%% --- Operation: balance ---
balance_pre(S) ->
  S#state.http_ready =/= [] andalso S#state.accounts =/= [].

balance_args(S) ->
  [ elements(S#state.http_ready), ?LET(A, oneof(S#state.accounts), A#user.name), weighted_default({9, false}, {1, true}) ].

balance_pre(S, [Node, Name, _]) ->
  lists:member(Node, S#state.http_ready) andalso lists:keymember(Name, #user.name, S#state.accounts).

balance(Node, Name, FaultInject) ->
    [{_, #account{pubkey = PubKey}}] = ets:lookup(accounts, Name),
    try
        #{Node := #{PubKey := Balance}} = aest_nodes:wait_for_value({balance, PubKey, 0}, [Node], 20000, [{fault_inject, #{pubkey => PubKey}} || FaultInject]),
        Balance
    catch
        _:Reason ->
            case FaultInject andalso Reason == timeout of
                true  -> undefined;
                false -> {'EXIT', Reason}
            end
    end.


%% --- Operation: waitforblock ---
%% Only wait if there are transactions in the mempool.
waitforblock_pre(S) ->
  S#state.http_ready =/= [].

waitforblock_args(S) ->
  [elements(S#state.http_ready), S#state.tx_hashes].

waitforblock_pre(S, [Node, Hashes]) ->
  lists:member(Node, S#state.http_ready) andalso Hashes == S#state.tx_hashes.

waitforblock_adapt(S, [Node, _Hashes]) ->
  [Node, S#state.tx_hashes].
  
waitforblock(Node, Hashes) ->
    try 
        aest_nodes:wait_for_value({txs_on_chain, Hashes}, [Node], 10000, []),
        #{ height := H } = aest_nodes:get_top(Node), 
        H
    catch _:Reason ->
        {'EXIT', Reason}
    end.

%% Now some transactions should be on chain
waitforblock_next(S, Value, [_Node, _]) ->
  Channels =
    [ case Channel#channel.status of
        open ->
          Channel#channel{status = created};
        _ -> Channel
      end || Channel <- S#state.channels ],
  S#state{channels = Channels, 
          height = Value %% postcondition guarantees that this is an integer at runtime.
         }.

waitforblock_post(_S, [_Node, _], Res) ->
  is_integer(Res).

waitforblock_features(S, [_Node, _], _Res) ->
  [ channel_created_on_chain || lists:keymember(open, #channel.status, S#state.channels) ].


%% --- Operation: transaction_pool ---
transaction_pool_pre(S) ->
  S#state.http_ready =/= [].

transaction_pool_args(S) ->
  [elements(S#state.http_ready)].

transaction_pool_pre(S, [Node]) ->
  lists:member(Node, S#state.http_ready).

transaction_pool(Node) ->
    Transactions = aest_nodes:get_mempool(Node),
    %% I might have saved them encoded in memory, need to re-encode if I want to compare
    Txs = [ Tx || #{tx := Tx} <- Transactions ],
    Txs.

%% transaction_pool(Node) ->
%%   case request(Node, 'GetTxs', #{}) of
%%     {ok, 200, Transactions} ->
%%       Txs = [ begin
%%                 {transaction, Trans} = aec_base58c:decode(T),
%%                 %% Not sure all transactions in pool must be signed???
%%                 aetx_sign:tx(aetx_sign:deserialize_from_binary(Trans))
%%               end || #{tx := T} <- Transactions ],
%%       Txs;
%%     Res ->
%%       Res
%%   end.

transaction_pool_post(_S, [_Node], Res) ->
  is_list(Res).



%% --- Operation: top ---
top_pre(S) ->
  S#state.http_ready =/= [].

top_args(S) ->
  [elements(S#state.http_ready)].

top_pre(S, [Node]) ->
  lists:member(Node, S#state.http_ready).

top(Node) ->
    aest_nodes:get_top(Node).

top_next(S, Value, [_Node]) ->
  S#state{height = {call, ?MODULE, top_height, [Value, S#state.height]} }.

top_post(_S, [_Node], Res) ->
  case Res of 
    #{ height := _ }  -> true;
    _ -> eq(Res, ok)
  end.


%%% -----------------------------------------------------------------------

final_balances([], _) ->
  undefined;
final_balances(Nodes, Accounts) ->
  Balances = [ {Account#user.name, balance(Node, Account#user.name, false), Account#user.balance} 
               || Node <- Nodes, Account <- Accounts ],
  lists:usort(Balances).

%% Return all transactions that we genearated but are not yet on chain
final_transactions([], _) ->
  [];
final_transactions([Node|_], Hashes) ->
  aest_nodes:get_mempool(Node).


try_get_nonce(Node, PubKey) ->
    case request(Node, 'GetAccountByPubkey', #{pubkey => aec_base58c:encode(account_pubkey, PubKey)}) of
        {ok, 200, #{nonce := Nonce}} -> 
            Nonce;
        Reason -> 
            eqc:format("error getting patron nonce ~p -> ~p\n", [Node, Reason]),
            0
    end.



tag(_Tag, true) -> true;
tag(Tag, false) -> Tag;
tag(Tag, Other) -> {Tag, Other}. 

weight(S, open_channel) -> if length(S#state.accounts) > 1 -> 100; true -> 0 end;
weight(S, deposit) -> if length(S#state.channels) > 0 -> 50; true -> 0 end;
weight(S, withdraw) -> if length(S#state.channels) > 0 -> 80; true -> 0 end;
weight(_S, add_account) -> 10;
weight(_S, create_account) -> 1;  %% tests timing
weight(_S, pingpong) -> 200;
weight(S, close_mutual) -> if length(S#state.channels) > 0 -> 10; true -> 0 end;
weight(_S, start) -> 1;
weight(_S, stop) -> 0;
weight(_S, _) -> 1.


%% -- Generators -------------------------------------------------------------
gen_key_pair() ->
    return(crypto:generate_key(ecdh, crypto:ec_curve(secp256k1))).

account_gen(NatGen) ->
    ?LET({[Name], Balance}, {eqc_erlang_program:words(1), NatGen}, {Name, Balance}).

check_ttl(S, {Height, _}) ->
  Height == S#state.height;
check_ttl(_S, optional) ->
  true.

optional_ttl(Tx) ->
  case maps:get(ttl, Tx) of
    optional -> 
      maps:without([ttl], Tx);
    {Height, DTTL} ->
      Tx#{ttl => Height + DTTL}
  end.

fee() ->
  choose(1,5).

%% -- Property ---------------------------------------------------------------

%% UAT keys: https://github.com/aeternity/testnet-keys/tree/master/accounts/UAT_sender_account
prop_transactions() ->
  prop_patron(10000, #account{ pubkey = <<206,167,173,228,112,201,249,157,157,78,64,8,128,168,111,
                                                 29,73,187,68,75,98,241,26,158,187,100,187,207,235,115,
                                                 254,243>>,
                                      privkey = <<230,169,29,99,60,119,207,87,113,50,157,51,84,179,188,
                                                  239,27,197,224,50,196,61,112,182,211,90,249,35,206,30,
                                                  183,77,206,167,173,228,112,201,249,157,157,78,64,8,128,
                                                  168,111,29,73,187,68,75,98,241,26,158,187,100,187,207,
                                                  235,115,254,243>>,
                                      balance = 1000000 %% ensure at least this much in patron account
                                   }, aest_docker).

prop_uat() ->
  prop_patron(7*60*1000, #account{ pubkey = <<206,167,173,228,112,201,249,157,157,78,64,8,128,168,111,
                                                 29,73,187,68,75,98,241,26,158,187,100,187,207,235,115,
                                                 254,243>>,
                                      privkey = <<230,169,29,99,60,119,207,87,113,50,157,51,84,179,188,
                                                  239,27,197,224,50,196,61,112,182,211,90,249,35,206,30,
                                                  183,77,206,167,173,228,112,201,249,157,157,78,64,8,128,
                                                  168,111,29,73,187,68,75,98,241,26,158,187,100,187,207,
                                                  235,115,254,243>>,
                                      balance = 1000000 %% ensure at least this much in patron account
                                   }, aest_uat).

%% One could run this with an arbitrary generated account 
prop_patron(FinalSleep, Patron, Backend) ->
  eqc:dont_print_counterexample(
  ?LET(Shrinking, parameter(shrinking, false),
  ?FORALL([NodeName|_] = Nodes, systems(1),
  ?FORALL(Cmds, more_commands(3, commands(?MODULE, #state{nodes = Nodes, running = [NodeName]})),
  ?SOMETIMES(if not (Shrinking orelse Backend == aest_uat) -> 2; 
                true -> 1 end,
  begin
    %% file:write_file("exs.txt", io_lib:format("Cmds = ~p\n", [Cmds]), [append]),
    DataDir = filename:absname("data"),
    Genesis = filename:join(DataDir, "accounts.json"),
    JSON = 
      jsx:encode(
        [ { aec_base58c:encode(account_pubkey, Patron#account.pubkey), Patron#account.balance } ]),
    ok = filelib:ensure_dir(Genesis),
    ok = file:write_file(Genesis, JSON),
    aest_nodes_mgr:start_link([Backend], #{ data_dir => DataDir
                                          , temp_dir => "/tmp"
                                          %%, log_fun => fun(Fmt, As) -> io:format(Fmt ++ ["\n\n"], As) end}
                                          , log_fun => fun(Fmt, _As) -> io:format("#") end}
                             ),
    aest_nodes_mgr:setup_nodes(
      aest_nodes:cluster(Nodes, #{ genesis => Genesis,
                                   source => {pull, "aeternity/epoch:local"},
                                   backend => Backend })),
    start(NodeName),
    http_ready(NodeName),
    PatronNonce = try_get_nonce(NodeName, Patron#account.pubkey),
    eqc:format("Patron nonce ~p\n", [PatronNonce]),
    Table = ets:new(accounts, [named_table]),
    ets:insert(accounts, {patron, Patron#account{nonce = PatronNonce}}),

    {H, S, Res} = run_commands(Cmds, [{patron_nonce, PatronNonce + 1}]),
   
    eqc:format("final state ~p\n", [S]),
    WaitForChain = (catch aest_nodes:wait_for_value({txs_on_chain, eqc_symbolic:eval(S#state.tx_hashes)}, S#state.http_ready, FinalSleep, [])),
    %% If this times out, then we have transactions in the mempool

    FinalTransactions = final_transactions(S#state.http_ready, S#state.tx_hashes),
    eqc:format("Transaction pool: ~p\n", [FinalTransactions]),

    FinalBalances = final_balances(S#state.http_ready, S#state.accounts),
    eqc:format("Balances ~p\n", [FinalBalances]),

    ets:delete(Table),
    aest_nodes_mgr:stop(),
    if Backend =/= aest_uat -> timer:sleep(10000);
       true -> ok
    end,

    check_command_names(Cmds,
      measure(length, commands_length(Cmds),
      measure(spend_tx, length([ 1 || {_, add_account, _} <- command_names(Cmds)]),
      aggregate(call_features(H),
        pretty_commands(?MODULE, Cmds, {H, S, Res},
                        conjunction([{result, Res == ok},
                                     {transactions, equals([ Tx || Tx <- FinalTransactions ], [])}
                                    ]))))))
  end))))).

prop_commands(Cmd) ->
  ?FORALL(Cmds, commands(?MODULE, #state{nodes = [node1], running = [node1]}),
          not lists:keymember(Cmd, 2, command_names(Cmds))).

check(Cmd) ->
  [Cmds] = eqc:counterexample(eqc:numtests(2000, prop_commands(Cmd))),
  io:format("------------------------------------------------------------\n"),
  eqc:check(prop_transactions(), [[node1], Cmds, [{result, true}, {transactions, []}]]).

%% -- helper functions

request(Node, Id, Params) ->
  aest_nodes:request(Node, Id, Params).

wait_blocks(Node, N, Timeout) ->
  Top = aest_nodes:get_top(Node),
  H = maps:get(height, Top),
  aest_nodes:wait_for_value({height, H + N}, [Node], Timeout, [{ct_log,  false}]).

wait_blocks(Node, N, Hashes, Timeout) ->
  Pool = final_transactions([Node], Hashes),
  Top = aest_nodes:get_top(Node),
  H = maps:get(height, Top),
  case Pool of
    [] ->
      %% We're done, no transactions hanging
      H;
    _ ->
      wait_blocks(Node, H+N, Timeout)
  end.

ok200(Resp, Field) ->
  case ok200(Resp) of
    M when is_map(M) ->
      maps:get(Field, M, undefined);
    _ -> undefined
  end.
                     
ok200({ok, 200, Value}) ->
  Value;
ok200(_) ->
  undefined.

ok200s(Es, Field) when is_list(Es) ->
  [ ok200(E, Field) || E <- Es ].


top_height(#{height := H}, _LastSeen) ->
  H;
top_height(_, LastSeen) ->
  LastSeen.

sign(Tx, PrivKey) ->
  Bin = aetx:serialize_to_binary(Tx),
  Signatures = [ enacl:sign_detached(Bin, PrivKey) ],
  aetx_sign:new(Tx, Signatures).
