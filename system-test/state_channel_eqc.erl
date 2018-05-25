%%% @author Thomas Arts 
%%% @doc Testing state channel fsm at system test level.
%%%
%%%      The idea is that these tests could run on UAT as well.
%%%      For that reason, we cannot assume any specific height or nonces of the root account.
%%%      The Patron is the account that has a lot of tokens and we start by reading 
%%%      that account and creating working accounts from it.
%%%
%%%      run_commands environment contains {patron, PatronAccount} refered to as
%%%      {var, patron} in the test case. This makes it possible to re-run a test
%%%      on a different (or longer) chain.
%%%
%%% @end
%%% Created : 17 May 2018 by Thomas Arts 

-module(state_channel_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

%% -- State and state functions ----------------------------------------------
-record(state,{nodes = [], accounts = [], nonce_delta = 1, 
               running = [], http_ready = [],
               channels = [],
               height = 0
              }).

-record(account, { pubkey,
                   balance,
                   privkey,
                   nonce = 0}).

-record(channel, {status, %% open | created (on chain) 
                  tx_hash, %% symbolic! 
                  id, 
                  port, tx}). 


initial_state() ->
  #state{}.

balance_of(PubKey, Accounts) ->
  case lists:keyfind(PubKey, #account.pubkey, Accounts) of
    Account when is_record(Account, account) ->
      Account#account.balance;
    false ->
      0
  end.

nonce_of(PubKey, Accounts) ->
  case lists:keyfind(PubKey, #account.pubkey, Accounts) of
    Account when is_record(Account, account) ->
      Account#account.nonce;
    false ->
      0
  end.


%% -- Generators -------------------------------------------------------------

systems(N) ->
  [ list_to_atom(lists:concat([node, Name])) || Name <- lists:seq(1,N) ].

%% Absolute TTLs are hard to test, thinking required
gen_ttl(Height) ->
  ?LET(TTL, choose(0, 20), Height + (20 - TTL)).

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
  gettop(Node, 0, erlang:system_time(millisecond) + 8000).

http_ready_next(S, Value, [Node]) ->
  S#state{http_ready = S#state.http_ready ++ [Node],
          height = {call, ?MODULE, top_height, [Value, S#state.height]} }.

http_ready_post(_S, [_Node], Res) ->
  case Res of
    {ok, 200, _} -> true;
    _ -> false
  end.


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
   {var, patron}, S#state.nonce_delta, account_gen(elements([5, 71, 200, 500, 1000, 0])), 
   choose(1,5), <<"quickcheck">>]).

add_account_pre(S, [Node, _Sender, Nonce, _Receiver, Fee, _Payload]) ->
  Fee >= aec_governance:minimum_tx_fee() andalso 
    lists:member(Node, S#state.http_ready) andalso S#state.nonce_delta == Nonce.

add_account_adapt(S, [Node, Sender, _Nonce, Receiver, Fee, Payload]) ->
  [Node, Sender, S#state.nonce_delta, Receiver, Fee, Payload].

add_account(Node, Sender, Nonce, Receiver, Fee, Payload) ->
  {ok, Tx} =
    aec_spend_tx:new(#{ sender    => Sender#account.pubkey,
                        recipient => Receiver#account.pubkey,
                        amount    => Receiver#account.balance,   %% we create it with this much
                        fee       => Fee,
                        payload   => Payload,
                        nonce     => Sender#account.nonce + Nonce
                        }),
  SignedTx = aetx_sign:sign(Tx, Sender#account.privkey),
  Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(SignedTx)),
  request(Node, 'PostTx', #{tx => Transaction}).

add_account_next(S, _V, [_Node, _Sender, _Nonce, Receiver, _Fee, _Payload]) ->
  %% We assume there are always enough tokens in patron account
  S#state{ accounts = S#state.accounts ++ [Receiver],
           nonce_delta = S#state.nonce_delta + 1}.

add_account_post(_S, [_Node, _Sender, _Nonce, _Receiver, _Fee, _Payload], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> false
  end.

add_account_features(S, [_Node, _Sender, _Nonce, _Receiver, _Fee, _Payload], _Res) ->
  [ {accounts, length(S#state.accounts) + 1} ].



%% --- Operation: open_channel ---
open_channel_pre(S) ->
  S#state.http_ready =/= [] andalso length(S#state.accounts) > 1.

open_channel_args(S) ->
  ?LET({Initiator, Fee}, {elements(S#state.accounts), choose(1,5)},
  ?LET({Responder, Reserve},
       {elements(S#state.accounts -- [Initiator]), 
        at_most(Initiator#account.balance)},
       [elements(S#state.http_ready),
        #{initiator => Initiator, 
          responder => Responder,
          initiator_amount => at_most(Initiator#account.balance - Fee),
          responder_amount => at_most(Responder#account.balance),
          lock_period => choose(0,5), %% lock period
          ttl => 1000, %% ttl (we need height for this)
          fee => Fee, %% fee
          channel_reserve => Reserve,
          push_amount => noshrink(choose(0,200)),
          nonce => Initiator#account.nonce + 1}
       ])).

open_channel_pre(S, [Node, #{initiator := Initiator, responder := Responder, 
                             fee := Fee} = Tx]) ->
  InAccount = lists:keyfind(Initiator#account.pubkey, #account.pubkey, S#state.accounts),
  RespAccount = lists:keyfind(Responder#account.pubkey, #account.pubkey, S#state.accounts),
  Responder#account.pubkey =/= Initiator#account.pubkey andalso
    Fee >= aec_governance:minimum_tx_fee() andalso 
    lists:member(Node, S#state.http_ready) andalso 
    InAccount /= false andalso RespAccount /= false andalso
    open_channel_valid(Tx#{initiator => InAccount, responder => RespAccount}).

open_channel_valid(#{initiator := Initiator, responder := Responder, 
                         fee := Fee, nonce := Nonce} = Tx) ->
  Initiator#account.balance >= maps:get(initiator_amount, Tx) + Fee andalso
    maps:get(initiator_amount, Tx) >= maps:get(channel_reserve, Tx) andalso
    maps:get(responder_amount, Tx) >= maps:get(channel_reserve, Tx) andalso
    Responder#account.balance >= maps:get(responder_amount, Tx)  andalso
    Initiator#account.nonce + 1 == Nonce.


open_channel_adapt(S, [Node, #{initiator := Initiator, responder := Responder} = Tx]) ->
  InAccount = lists:keyfind(Initiator#account.pubkey, #account.pubkey, S#state.accounts),
  RespAccount = lists:keyfind(Responder#account.pubkey, #account.pubkey, S#state.accounts),
  case {InAccount, RespAccount} of
    {false, _} -> false;
    {_, false} -> false;
    _ ->
      [Node, Tx#{initiator => InAccount, responder => RespAccount, 
                 nonce => InAccount#account.nonce + 1}]
  end.

open_channel(Node, #{initiator := Initiator, responder := Responder} = Tx) ->
  EncodedTx = Tx#{initiator => aec_base58c:encode(account_pubkey, Initiator#account.pubkey),
                  responder => aec_base58c:encode(account_pubkey, Responder#account.pubkey)},
  case request(Node, 'PostChannelCreate', EncodedTx) of
    {ok, 200, #{tx := TxObject}} ->
      {ok, Bin} = aec_base58c:safe_decode(transaction, TxObject),
      InitiatorSignedTx = aetx_sign:sign(aetx:deserialize_from_binary(Bin), 
                                [Initiator#account.privkey]),
      ResponderSignedTx = aetx_sign:sign(aetx:deserialize_from_binary(Bin), 
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
  Initiator = lists:keyfind(In#account.pubkey, #account.pubkey, S#state.accounts),
  Responder = lists:keyfind(Resp#account.pubkey, #account.pubkey, S#state.accounts),
  Accounts = 
    lists:keyreplace(Responder#account.pubkey, #account.pubkey,
                     lists:keyreplace(Initiator#account.pubkey, #account.pubkey, 
                                      S#state.accounts, 
                                      Initiator#account{ balance = Initiator#account.balance - Fee - maps:get(initiator_amount, Tx),
                                                         nonce = Nonce }),
                     Responder#account{ balance = Responder#account.balance - maps:get(responder_amount, Tx)}),
  S#state{ channels = S#state.channels ++ [ #channel{status = open,
                                                     tx_hash = {call, ?MODULE, ok200, [Value, tx_hash]},
                                                     id =  aesc_channels:id(In#account.pubkey, Nonce, Resp#account.pubkey),
                                                     tx = Tx} ],
           accounts = Accounts }.

open_channel_post(_S, [_Node, _], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> 
      Res
  end.

open_channel_features(_S, [_Node, #{responder := Responder} = Tx], _) ->
  [ {open_channel, responder_balance_less_responder_amount} ||
    not (Responder#account.balance >= maps:get(responder_amount, Tx)) ].

%% --- Operation: deposit ---
deposit_pre(S) ->
  S#state.http_ready =/= [] andalso 
    lists:keymember(created, #channel.status, S#state.channels).

deposit_args(S) ->
  ?LET({Channel, Party}, {elements([ Ch || #channel{status = created} = Ch <- S#state.channels]), 
                          oneof([initiator, responder])},
       begin
         From = maps:get(Party, Channel#channel.tx),
         [elements(S#state.http_ready), Channel, Party,
          #{from => From,
            channel_id => Channel#channel.id,
            amount => at_most(From#account.balance),
            ttl => 200, %% ttl (we need height for this)
            fee => choose(1,5),
            nonce => From#account.nonce + 1}
         ]
       end).

deposit_pre(S, [Node, _Channel, _Party, 
                #{channel_id := Ch, from := From, fee := Fee, nonce := Nonce} = Tx]) ->
  Channel = lists:keyfind(Ch, #channel.id, S#state.channels),
  Account = lists:keyfind(From#account.pubkey, #account.pubkey, S#state.accounts),
  Fee >= aec_governance:minimum_tx_fee() andalso 
    lists:member(Node, S#state.http_ready) andalso
    Channel /= false andalso Channel#channel.status == created andalso
    Account /= false andalso Account#account.nonce + 1 == Nonce andalso
    deposit_valid(Tx#{from => Account}).

deposit_valid(#{from := From, amount := Amount, fee := Fee}) ->
  From#account.balance >= Amount + Fee.

deposit_adapt(S, [Node, _Channel, Party, #{from := From, channel_id := Ch} = Tx]) ->
  case lists:keyfind(From#account.pubkey, #account.pubkey, S#state.accounts) of
    false -> false;
    Account ->
      [Node, lists:keyfind(Ch, #channel.id, S#state.channels), Party, 
       Tx#{from => Account, nonce => Account#account.nonce + 1}]
  end.

%% Channel is passed on, because we need secret keys and here we have no state
deposit(Node, Channel, _Party, #{from := From} = Tx) ->
  #{initiator := Initiator, responder := Responder} = Channel#channel.tx,
  EncodedTx = Tx#{from => aec_base58c:encode(account_pubkey, From#account.pubkey),
                  channel_id => aec_base58c:encode(channel, Channel#channel.id)},
  case request(Node, 'PostChannelDeposit', EncodedTx) of
    {ok, 200, #{tx := TxObject}} ->
      {ok, Bin} = aec_base58c:safe_decode(transaction, TxObject),
      InitiatorSignedTx = aetx_sign:sign(aetx:deserialize_from_binary(Bin), 
                                [Initiator#account.privkey]),
      ResponderSignedTx = aetx_sign:sign(aetx:deserialize_from_binary(Bin), 
                                [Responder#account.privkey]),
      BothSigned = 
        aetx_sign:add_signatures(ResponderSignedTx, aetx_sign:signatures(InitiatorSignedTx)),
      Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(BothSigned)),
      request(Node, 'PostTx', #{tx => Transaction});
    Error ->
      Error
  end.

deposit_next(S, _Value, [_Node, Channel, Party, #{fee := Fee, nonce := Nonce}]) ->
  From = maps:get(Party, Channel#channel.tx),
  Account = lists:keyfind(From#account.pubkey, #account.pubkey, S#state.accounts),
  Accounts = 
    lists:keyreplace(Account#account.pubkey, #account.pubkey, 
                     S#state.accounts, 
                     Account#account{ balance = Account#account.balance - Fee,
                                      nonce = Nonce }),
  S#state{ %% todo update channel amounts
    accounts = Accounts }.

deposit_post(_S, [_Node, _, _, _], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> 
      Res
  end.

deposit_features(_S, [_, _, Party, _], _Res) ->
  [{deposit, Party}].


%% --- Operation: close_mutual ---
close_mutual_pre(S) ->
  S#state.http_ready =/= [] andalso 
    lists:keymember(created, #channel.status, S#state.channels).

close_mutual_args(S) ->
  ?LET(Channel, elements([ Ch || #channel{status = created} = Ch <- S#state.channels]),
       begin
         #{initiator_amount := InAmount,
           responder_amount := RespAmount,
           initiator := Initiator} = Channel#channel.tx,
         Account = lists:keyfind(Initiator#account.pubkey, #account.pubkey, S#state.accounts),
         [elements(S#state.http_ready), Channel,
          #{channel_id => Channel#channel.id,
            initiator_amount => at_most(InAmount + RespAmount),
            responder_amount => at_most(InAmount + RespAmount + 100),
            ttl => 200, %% ttl (we need height for this)
            fee => choose(1,5),
            nonce => Account#account.nonce + 1}
         ]
       end).

close_mutual_pre(S, [Node, Channel, 
                     #{channel_id := Ch, fee := Fee, nonce := Nonce} = Tx]) ->
  ChannelInS = lists:keyfind(Ch, #channel.id, S#state.channels),
  #{initiator := From} = Channel#channel.tx,
  Account = lists:keyfind(From#account.pubkey, #account.pubkey, S#state.accounts),
  Fee >= aec_governance:minimum_tx_fee() andalso 
    lists:member(Node, S#state.http_ready) andalso
    ChannelInS /= false andalso ChannelInS#channel.status == created andalso
    Account /= false andalso Account#account.nonce + 1 == Nonce andalso
    close_mutual_valid(Tx).

close_mutual_valid(#{initiator_amount := InAmount, responder_amount := RespAmount, fee := Fee}) ->
  InAmount + RespAmount >= Fee.

%% If the channel does not exist, we cannot replace it
close_mutual_adapt(S, [Node, Channel, Tx]) ->
  #{initiator := From} = Channel#channel.tx, 
  case lists:keyfind(From#account.pubkey, #account.pubkey, S#state.accounts) of
    false -> false;
    Account ->
      [Node, Channel,
       Tx#{nonce => Account#account.nonce + 1}]
  end.

%% Channel is passed on, because we need secret keys and here we have no state
close_mutual(Node, Channel, Tx) ->
  #{initiator := Initiator, responder := Responder} = Channel#channel.tx,
  EncodedTx = Tx#{channel_id => aec_base58c:encode(channel, Channel#channel.id)},
  case request(Node, 'PostChannelCloseMutual', EncodedTx) of
    {ok, 200, #{tx := TxObject}} ->
      {ok, Bin} = aec_base58c:safe_decode(transaction, TxObject),
      InitiatorSignedTx = aetx_sign:sign(aetx:deserialize_from_binary(Bin), 
                                [Initiator#account.privkey]),
      ResponderSignedTx = aetx_sign:sign(aetx:deserialize_from_binary(Bin), 
                                [Responder#account.privkey]),
      BothSigned = 
        aetx_sign:add_signatures(ResponderSignedTx, aetx_sign:signatures(InitiatorSignedTx)),
      Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(BothSigned)),
      request(Node, 'PostTx', #{tx => Transaction});
    Error ->
      Error
  end.

close_mutual_next(S, _Value, [_Node, Channel, #{fee := Fee, nonce := Nonce}]) ->
  #{initiator := From} = Channel#channel.tx,
  Account = lists:keyfind(From#account.pubkey, #account.pubkey, S#state.accounts),
  Accounts = 
    lists:keyreplace(Account#account.pubkey, #account.pubkey, 
                     S#state.accounts, 
                     Account#account{ balance = Account#account.balance - Fee,
                                      nonce = Nonce }),
  S#state{ %% todo update channel amounts and close channel
    accounts = Accounts }.

close_mutual_post(_S, [_Node, _, _], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> false;
    _ -> 
      Res
  end.

close_mutual_features(_S, [_, _, #{initiator_amount := InAmount, responder_amount := RespAmount, fee := Fee}], _Res) ->
  [{close_mutual, even} ||  (InAmount + RespAmount ) rem 2 == 0 ] ++
    [{close_mutual, odd} ||  (InAmount + RespAmount ) rem 2 == 1 ] ++ 
    [{close_mutual, to_initiator} ||  RespAmount < floor(Fee/2) ] ++
    [{close_mutual, to_responder} ||  InAmount < floor(Fee/2) ].



%% one could add deposit of open, but not created channel, this may or may not return an error channel_id not found.


%% --- Operation: balance ---
balance_pre(S) ->
  S#state.http_ready =/= [] andalso S#state.accounts =/= [].

balance_args(S) ->
  [ elements(S#state.http_ready), 
    ?LET(Account, oneof(S#state.accounts), Account#account.pubkey) ].

balance_pre(S, [Node, PubKey]) ->
  lists:member(Node, S#state.http_ready) andalso lists:keymember(PubKey, #account.pubkey, S#state.accounts).

balance(Node, PubKey) ->
  request(Node, 'GetAccountBalance',  #{account_pubkey => aec_base58c:encode(account_pubkey, PubKey)}).

balance_post(_S, [_, _PubKey], Res) ->
  case Res of
    {ok, 200, #{balance := _B}} ->
      true;  %% We don't know what the actual balance is.
    {ok, 404, #{reason := <<"Account not found">>}} ->
      true;  %% unless we mine extensively, this could happen
    Other ->
      Other
  end.

%% --- Operation: txs ---
txs_pre(S) ->
  S#state.http_ready =/= [] andalso S#state.accounts =/= [].

txs_args(S) ->
  [ elements(S#state.http_ready), 
    ?LET(Account, oneof(S#state.accounts), Account#account.pubkey) ].

txs_pre(S, [Node, PubKey]) ->
  lists:member(Node, S#state.http_ready) andalso lists:keymember(PubKey, #account.pubkey, S#state.accounts).

txs(Node, PubKey) ->
  request(Node, 'GetAccountTransactions',  #{account_pubkey => aec_base58c:encode(account_pubkey, PubKey),
                                             tx_encoding => json
                                            }).

txs_post(_S,  [_Node, _PubKey], Res) ->
  case Res of
    {ok, 200, #{transactions := Txs}} ->
      is_list(Txs);  %% We don't know what the actual transactions are.
    {ok, 404, #{reason := <<"Account not found">>}} ->
      true;  %% unless we mine extensively, this could happen
    Other ->
      Other
  end.

%% --- Operation: waitforblock ---
waitforblock_pre(S) ->
  S#state.http_ready =/= [].

waitforblock_args(S) ->
  [elements(S#state.http_ready)].

waitforblock_pre(S, [Node]) ->
  lists:member(Node, S#state.http_ready).

waitforblock(Node) ->
  ok200(wait_blocks(Node, 1, 60*5*1000), height).

%% Now some transactions should be on chain
waitforblock_next(S, Value, [_Node]) ->
  Channels =
    [ case Channel#channel.status of
        open ->
          Channel#channel{status = created};
        _ -> Channel
      end || Channel <- S#state.channels ],
  S#state{channels = Channels, 
          height = Value %% postcondition guarantees that this is an integer at runtime.
         }.

waitforblock_post(_S, [_Node], Res) ->
  is_integer(Res).

waitforblock_features(S, [_Node], _Res) ->
  [ channel_created_on_chain || lists:keymember(open, #channel.status, S#state.channels) ].


%% --- Operation: transaction_pool ---
transaction_pool_pre(S) ->
  S#state.http_ready =/= [].

transaction_pool_args(S) ->
  [elements(S#state.http_ready)].

transaction_pool_pre(S, [Node]) ->
  lists:member(Node, S#state.http_ready).

transaction_pool(Node) ->
  case request(Node, 'GetTxs', #{}) of
    {ok, 200, Transactions} ->
      Txs = [ begin
                {transaction, Trans} = aec_base58c:decode(T),
                %% Not sure all transactions in pool must be signed???
                aetx_sign:tx(aetx_sign:deserialize_from_binary(Trans))
              end || #{tx := T} <- Transactions ],
      %% io:format("\n\nTransactions ~p\nTxs ~p\n\n", [Transactions, Txs]),
      Txs;
    Res ->
      Res
  end.

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
  request(Node, 'GetTop', #{}).

top_next(S, Value, [_Node]) ->
  S#state{height = {call, ?MODULE, top_height, [Value, S#state.height]} }.

top_post(_S, [_Node], Res) ->
  case Res of 
    {ok, 200, _} -> true;
    _ -> eq(Res, ok)
  end.




%%% -----------------------------------------------------------------------

final_balances([], _) ->
  {undefined, []};
final_balances(Nodes, PubKeys) ->
  TxPools = lists:append([ transaction_pool(Node) || Node <- Nodes ]),
  Balances = [ balance(Node, PubKey) || Node <- Nodes, PubKey <- PubKeys ],
  {lists:usort(Balances), lists:usort(TxPools)}.

try_get_nonce(Node, PubKey) ->
  try
    {ok, 200, #{transactions := Txs}} = txs(Node, PubKey),
    case Txs of
      [] -> 0;
      [#{tx := Tx}|_] -> 
        maps:get(nonce, Tx)
    end
  catch
    _:Reason -> 
      eqc:format("error getting patron nonce ~p -> ~p\n", [Node, Reason]),
      0
  end.


tag(_Tag, true) -> true;
tag(Tag, false) -> Tag;
tag(Tag, Other) -> {Tag, Other}. 

weight(_S, open_channel) -> 10;
weight(_S, deposit) -> 5;
weight(_S, add_account) -> 5;
weight(_S, close_mutual) -> 3;
weight(_S, start) -> 1;
weight(_S, stop) -> 0;
weight(_S, _) -> 1.


%% -- Generators -------------------------------------------------------------
gen_key_pair() ->
    return(crypto:generate_key(ecdh, crypto:ec_curve(secp256k1))).

account_gen(NatGen) ->
    ?LET(Balance, NatGen,
         begin
           #{ public := PubKey, secret := PrivKey} = enacl:sign_keypair(),
           #account{ pubkey = PubKey, balance = Balance, privkey = PrivKey }
         end).

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
  prop_patron(10000, #account{ pubkey = <<206,167,173,228,112,201,249,157,157,78,64,8,128,168,111,
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
%% Patron = noshrink(account_gen(1000000))
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
    aest_nodes_mgr:start_link([Backend], #{data_dir => DataDir,
                                           temp_dir => "/tmp"}),
    aest_nodes_mgr:setup_nodes(
      aest_nodes:cluster(Nodes, #{ genesis => Genesis,
                                   source => {pull, "aeternity/epoch:local"},
                                   backend => Backend })),
    start(NodeName),
    http_ready(NodeName),
    PatronNonce = try_get_nonce(NodeName, Patron#account.pubkey),
    eqc:format("Patron nonce ~p\n", [PatronNonce]),

    {H, S, Res} = run_commands(Cmds, [{patron, Patron#account{nonce = PatronNonce}}]),
    wait_blocks(NodeName, 2, FinalSleep),

    {FinalBalances, TransactionPool} = final_balances(S#state.http_ready, [ A#account.pubkey || A <-S#state.accounts]),
    eqc:format("Balances ~p\n", [FinalBalances]),

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
                                     {transactions, equals([ Tx || Tx <- TransactionPool ], [])}
                                    ]))))))
  end))))).

prop_commands() ->
  ?FORALL(Cmds, commands(?MODULE, #state{nodes = [node1]}),
          not lists:keymember(close_mutual, 2, command_names(Cmds))).

%% -- helper functions

request(Node, Id, Params) ->
  aehttp_client:request(Id, Params, 
                        [{ext_http, aest_nodes_mgr:get_service_address(Node, ext_http)}, 
                         {ct_log, fun(Fmt, Args) -> io:format(Fmt++["\n"], Args) end }]).


wait_blocks(Node, N, Timeout) ->
  {ok, 200, Top} = gettop(Node, 0, erlang:system_time(millisecond) + Timeout),
  H = maps:get(height, Top),
  gettop(Node, H+N, erlang:system_time(millisecond) + Timeout).

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

gettop(Node, Height, Timeout) ->
  case top(Node) of
    {ok, 200, #{height := H} = Top} when H >= Height -> 
      {ok, 200, Top};
    Res ->
      case erlang:system_time(millisecond) > Timeout of
        true -> Res;
        false ->
          timer:sleep(100),
          gettop(Node, Height, Timeout)
      end
  end.
    
top_height({ok, 200, #{height := H}}, _LastSeen) ->
  H;
top_height(_, LastSeen) ->
  LastSeen.
