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
  ?LET([Initiator, Responder, Fee], 
       [elements(S#state.accounts), elements(S#state.accounts), choose(1,5)],
       [elements(S#state.http_ready), 
        #{initiator => Initiator, 
          responder => Responder,
          initiator_amount => noshrink(choose(0, max(0, Initiator#account.balance - Fee))),
          responder_amount => noshrink(choose(0, max(0, Responder#account.balance))),
          lock_period => choose(0,5), %% lock period
          ttl => 1000, %% ttl (we need height for this)
          fee => Fee, %% fee
          channel_reserve => noshrink(choose(0,200)),
          push_amount => noshrink(choose(0,200)),
          nonce => Initiator#account.nonce + 1}
       ]).

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
    %% Responder#account.balance >= maps:get(responder_amount, Tx)  andalso
    Initiator#account.nonce + 1 == Nonce.


open_channel_adapt(S, [Node, #{initiator := Initiator} = Tx]) ->
  case lists:keyfind(Initiator#account.pubkey, #account.pubkey, S#state.accounts) of
    false -> false;
    InAccount ->
      [Node, Tx#{nonce => InAccount#account.nonce + 1}]
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
  S#state{ channels = S#state.channels ++ [ {open, Value, Tx} ],
           accounts = Accounts }.

open_channel_post(_S, [_Node, _], Res) ->
  case Res of
    {ok, 200, #{tx_hash := _}} -> true;
    _ -> 
      Res
  end.

open_channel_features(_S, [Node, #{responder := Responder, 
                                   fee := Fee, nonce := Nonce} = Tx], _) ->
  [ {open_channel, responder_balance_less_responder_amount} ||
    not (Responder#account.balance >= maps:get(responder_amount, Tx)) ].



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

top_next(S, Value, [Node]) ->
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
      [Tx|_] -> 
        %% io:format("Tx decoded = ~p\n", [jsx:decode(Tx)]),
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
weight(_S, add_account) -> 5;
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
  ?FORALL([NodeName|_] = Nodes, systems(1),
  ?FORALL(Cmds, commands(?MODULE, #state{nodes = Nodes, running = [NodeName]}),
  begin
    file:write_file("exs.txt", io_lib:format("Cmds = ~p\n", [Cmds]), [append]),
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
                                   backend => aest_docker })),
    start(NodeName),
    http_ready(NodeName),
    PatronNonce = try_get_nonce(NodeName, Patron#account.pubkey),
    eqc:format("Patron nonce ~p\n", [PatronNonce]),

    {H, S, Res} = run_commands(Cmds, [{patron, Patron#account{nonce = PatronNonce}}]),
    timer:sleep(FinalSleep),

    {FinalBalances, TransactionPool} = final_balances(S#state.http_ready, [ A#account.pubkey || A <-S#state.accounts]),
    eqc:format("Balances ~p\n", [FinalBalances]),

    aest_nodes_mgr:stop(),
    timer:sleep(8000),

    check_command_names(Cmds,
      measure(length, commands_length(Cmds),
      measure(spend_tx, length([ 1 || {_, add_account, _} <- command_names(Cmds)]),
      aggregate(call_features(H),
        pretty_commands(?MODULE, Cmds, {H, S, Res},
                        conjunction([{result, Res == ok},
                                     {transactions, equals([ Tx || Tx <- TransactionPool ], [])}
                                    ]))))))
  end))).

%% -- helper functions

request(Node, Id, Params) ->
  aehttp_client:request(Id, Params, 
                        [{ext_http, aest_nodes_mgr:get_service_address(Node, ext_http)}, 
                         {ct_log, fun(Fmt, Args) -> io:format(Fmt++["\n"], Args) end }]).



