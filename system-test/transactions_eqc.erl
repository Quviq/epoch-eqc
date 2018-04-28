%%% @author Thomas Arts 
%%% @doc We test whether transactions posted on one node can be picked up by miner on
%%%      a different node.
%%%
%%% @end
%%% Created : 14 Mar 2018 by Thomas Arts 

-module(transactions_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

%% -- State and state functions ----------------------------------------------
-record(state,{nodes = [], accounts = [], running = []}).

-record(account, { pubkey, 
                   balance,
                   privkey,
                   nonce = 0}).


initial_state() ->
  #state{}.

%% -- Generators -------------------------------------------------------------

systems(N) ->
  Names = [ list_to_atom(lists:concat([node, Name])) || Name <- lists:seq(1,N) ],
  [ #{name => Name,
      peers => ?LET(Disconnect, sublist(Names), Names -- [Name | Disconnect]),
      source => {pull, oneof(["aeternity/epoch:local"])}
     } || Name <- Names ].

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
  true.

precondition_common(_S, _Call) ->
  true.

postcondition_common(_S, _Call, _Res) ->
  true.

%% -- Operations -------------------------------------------------------------

%% --- Operation: start ---
start_pre(S) ->
  length(S#state.nodes) > length(S#state.running).

start_args(S) ->
  [elements([ Name || #{name := Name} <- S#state.nodes, 
                      not lists:member(Name, S#state.running)])].

start_pre(S, [Node]) ->
  not lists:member(Node, S#state.running).

start(Node) ->
  aest_nodes_mgr:start_node(Node),
  timer:sleep(2000). %% http interface needs time to start

start_next(S, _Value, [Node]) ->
  S#state{running = S#state.running ++ [Node]}.

%% --- Operation: stop ---
stop_pre(S) ->
  S#state.running =/= [].

stop_args(S) ->
  [elements(S#state.running)].

stop_pre(S, [Node]) ->
  lists:member(Node, S#state.running).

stop(Node) ->
  aest_nodes_mgr:stop_node(Node, infinity).

stop_next(S, _Value, [Node]) ->
  S#state{running = S#state.running -- [Node]}.

%% --- add_account ---
add_account_pre(S) ->
  S#state.running =/= [].

add_account_args(S) ->
  [elements(S#state.accounts), account_gen(elements([5, 10, 23, 71, 200])), 
   choose(1,5), elements(S#state.running)].

add_account_pre(S, [Sender, _Receiver, _Fee, Node]) ->
  lists:member(Sender, S#state.accounts) andalso
    lists:member(Node, S#state.running).

%% Doesn't work if S#state.running is []
%% add_account_adapt(S, [Sender, Receiver, Fee, Node]) ->
%%   [Sender, Receiver, Fee, hd(S#state.running)].

add_account(Sender, Receiver, Fee, Node) ->
  {ok, Tx} =
    aec_spend_tx:new(#{ sender    => Sender#account.pubkey,
                        recipient => Receiver#account.pubkey,
                        amount    => Receiver#account.balance,   %% we create it with this much
                        fee       => Fee,
                        nonce     => Sender#account.nonce + 1 }),
  SignedTx = aetx_sign:sign(Tx, Sender#account.privkey),
  Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(SignedTx)),
  Host = aest_nodes_mgr:get_service_address(Node, ext_http),
  URL = binary_to_list(iolist_to_binary([Host, "v2/tx"])),
  io:format("POST ~p ~p ", [URL, Tx]),
  case httpc:request(post, {URL, [], "application/json", jsx:encode(#{tx => Transaction})}, [], []) of
    {ok, {{"HTTP/1.1", 200, "OK"}, _, Body}} ->
      io:format(" -> ~p\n", [Body]),
      ok;
    Res ->
      io:format(" -> ~p\n", [Res]),
      Res
  end.


add_account_next(S, _V, [From = #account{ balance = PB, nonce = PN },
                         NewAccount = #account{ balance = NB }, Fee, _Node]) ->
  case PB >= NB + Fee of
    false -> S;  %% not enough balance
    true ->
      Accounts = lists:keydelete(From#account.privkey, #account.privkey, S#state.accounts),
      S#state{ accounts = Accounts ++ [ From#account{ balance = PB - NB - Fee, nonce = PN + 1 } ] ++ [NewAccount]}
  end.

add_account_post(_S, [_Sender, _Receiver, _Fee, _Node], Res) ->
  eq(Res, ok).

%% --- Operation: transaction_pool ---
transaction_pool_pre(S) ->
  S#state.running /= [].

transaction_pool_args(S) ->
  [elements(S#state.running)].

transaction_pool_pre(S, [Node]) ->
  lists:member(Node, S#state.running).

transaction_pool(Node) ->
  Host = aest_nodes_mgr:get_service_address(Node, ext_http),
  URL = binary_to_list(iolist_to_binary([Host, "v2/transactions"])),
  io:format("GET ~p ", [URL]),
  case httpc:request(get, {URL, []}, [], []) of
    {ok, {{"HTTP/1.1", 200, "OK"}, _, Body}} ->
      io:format(" -> ~p\n", [Body]),
      Transactions = jsx:decode(iolist_to_binary(Body)),
      Txs = [ begin
                {transaction, Trans} = aec_base58c:decode(T),
                %% Not sure all transactions in pool must be signed???
                aetx_sign:tx(aetx_sign:deserialize_from_binary(Trans))
              end || [{<<"tx">>, T}] <- Transactions ],
      Txs;
    Res ->
      io:format(" -> ~p\n", [Res]),
      Res
  end.


transaction_pool_post(_S, [Node], Res) ->
  is_list(Res).





%% --- Operation: wait ---
%% wait_args(_S) ->
%%   [1000].

%% wait(MSec) ->
%%   timer:sleep(MSec).


%% --- Operation: top ---
top_pre(S) ->
  S#state.running =/= [].

top_args(S) ->
  [elements(S#state.running)].

top_pre(S, [Node]) ->
  lists:member(Node, S#state.running).

top(Node) ->
  Host = aest_nodes_mgr:get_service_address(Node, ext_http),
  URL = binary_to_list(iolist_to_binary([Host, "v2/top"])),
  io:format("GET ~p ", [URL]),
  case httpc:request(get, {URL, []}, [], []) of
    {ok, {{"HTTP/1.1", 200, "OK"}, _, Top}} ->
      io:format(" -> ~p\n", [Top]),
      ok;
    Res ->
      io:format(" -> ~p\n", [Res]),
      Res
  end.

top_post(_S, [Node], Res) ->
  eq(Res, ok).


final_balances([], _) ->
  {undefined, []};
final_balances([Node|_], PubKeys) ->
  TxPool = transaction_pool(Node),
  Balances = [ balance(Node, PubKey) || PubKey <- PubKeys ],
  {Balances, TxPool}.

balance(Node, PubKey) ->
  Host = aest_nodes_mgr:get_service_address(Node, ext_http),
  URL = binary_to_list(iolist_to_binary([Host, "v2/account/balance/", aec_base58c:encode(account_pubkey, PubKey)])),
  io:format("GET ~p ", [URL]),
  case httpc:request(get, {URL, []}, [], []) of
    {ok, {{"HTTP/1.1", 200, "OK"}, _, Body}} ->
      io:format(" -> ~p\n", [Body]),
      jsx:decode(iolist_to_binary(Body));
    Res ->
      io:format(" -> ~p\n", [Res]),
      {request_failed, PubKey}
  end.



weight(_S, start) -> 10;
weight(S, add_account) -> 
  if S#state.running == [] -> 0;
     true -> 20
  end;
weight(_S, stop) -> 1;
weight(_S, _) -> 2.


%% -- Property ---------------------------------------------------------------

gen_ttl() ->
    {delta, choose(3, 10)}.

gen_key_pair() ->
    return(crypto:generate_key(ecdh, crypto:ec_curve(secp256k1))).

account_gen(NatGen) ->
    ?LET(Balance, NatGen,
         begin
           {PubKey, PrivKey} = crypto:generate_key(ecdh, crypto:ec_curve(secp256k1)),
           #account{ pubkey = PubKey, balance = Balance, privkey = PrivKey }
         end).


prop_transactions() ->
  prop_transactions(10000).


prop_transactions(FinalSleep) ->
  ?FORALL({Accounts, Nodes}, {noshrink(non_empty(list(account_gen(1000000)))),
                              systems(2)},
  ?IMPLIES(all_connected(Nodes), 
  ?FORALL(Cmds, commands(?MODULE, #state{nodes = Nodes, accounts = Accounts}),
  begin
    DataDir = filename:absname("data"),
    Genesis = filename:join(DataDir, "accounts.json"),
    JSON = 
      jsx:encode(
        [ { aec_base58c:encode(account_pubkey, PK), B} || #account{ pubkey = PK, balance = B } <- Accounts ]),
    ok = filelib:ensure_dir(Genesis),
    ok = file:write_file(Genesis, JSON),

    aest_nodes_mgr:start([aest_docker], #{data_dir => DataDir,
                                          temp_dir => "/tmp"}),
    aest_nodes_mgr:setup_nodes([ Node#{genesis => Genesis, 
                                       backend => aest_docker} || Node <- Nodes ]),
    {H, S, Res} = run_commands(Cmds),
    timer:sleep(FinalSleep),
    {FinalBalances, TransactionPool} = final_balances(S#state.running, [ A#account.pubkey || A <-S#state.accounts]),
    aest_nodes_mgr:stop(),
    check_command_names(Cmds,
      measure(length, commands_length(Cmds),
      measure(spend_tx, length([ 1 || {_, add_account, 4} <- command_names(Cmds)]),
        pretty_commands(?MODULE, Cmds, {H, S, Res},
                        conjunction([{result, Res == ok},
                                     {transactions, equals([ Tx || Tx <- TransactionPool, is_possible(S, Tx) ], [])},
                                     {balances, true}])))))
  end))).

is_possible(S, Tx) ->
  From = aetx:origin(Tx),
  Type = aetx:tx_type(Tx),
  {From, Type, Tx}.


%% -- helper functions

-define(EPOCH_CONFIG_FILE, "/home/epoch/epoch.yaml").
-define(EPOCH_LOG_FOLDER, "/home/epoch/node/log").


all_connected(Nodes) ->
  Graph = digraph:new(),
  [ digraph:add_vertex(Graph, Name) || #{name := Name} <- Nodes ],
  [ digraph:add_edge(Graph, Name, Peer) || #{name := Name, peers := Peers} <- Nodes, Peer <- Peers ],
  Result = length(digraph_utils:components(Graph)) == 1,
  digraph:delete(Graph),
  Result.


