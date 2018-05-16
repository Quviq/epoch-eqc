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
-record(state,{nodes = [], accounts = [], running = [], names = [], invalid_transactions = []}).

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
  Names = [ list_to_atom(lists:concat([node, Name])) || Name <- lists:seq(1,N) ],
  [ #{name => Name,
      peers => ?LET(Disconnect, sublist(Names), Names -- [Name | Disconnect]),
      source => {pull, oneof(["aeternity/epoch:local"])}
     } || Name <- Names ].

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(S, Cmd) ->
  Cmd == start orelse S#state.running =/= [].

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

%% stop_args(S) ->
%%   [elements(S#state.running)].

stop_pre(S, [Node]) ->
  lists:member(Node, S#state.running).

stop(Node) ->
  aest_nodes_mgr:stop_node(Node, infinity).

stop_next(S, _Value, [Node]) ->
  S#state{running = S#state.running -- [Node]}.

%% --- add_account ---
add_account_args(S) ->
  noshrink(
  [elements(S#state.running), 
   elements(S#state.accounts), account_gen(elements([5, 10, 23, 71, 200, 0])), 
   choose(0,5), <<"quickcheck">>]).

add_account_pre(S, [Node, Sender, _Receiver, _Fee, _Payload]) ->
  lists:member(Sender, S#state.accounts) andalso
    lists:member(Node, S#state.running).

%% Doesn't work if S#state.running is []
%% add_account_adapt(S, [Node, Sender, Receiver, Fee, Payload]) ->
%%   [Sender, Receiver, Fee, hd(S#state.running)].

add_account(Node, Sender, Receiver, Fee, Payload) ->
  {ok, Tx} =
    aec_spend_tx:new(#{ sender    => Sender#account.pubkey,
                        recipient => Receiver#account.pubkey,
                        amount    => Receiver#account.balance,   %% we create it with this much
                        fee       => Fee,
                        payload   => Payload,
                        nonce     => Sender#account.nonce + 1
                        }),
  SignedTx = aetx_sign:sign(Tx, Sender#account.privkey),
  Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(SignedTx)),
  file:write_file("stats.txt", "t", [append]),
  file:write_file("txs.erl", 
                  io_lib:format("{ok, 200, #{}} = aehttp_client:request('PostTx', #{tx => ~p}, "
                                "[{ext_http, maps:get(~p, Nodes)}, "
                                " {ct_log, fun log/2}]),\n",
                                [Transaction, Node]), [append]),
  request(Node, 'PostTx', #{tx => Transaction}).

add_account_next(S, _V, [_Node, Sender = #account{ balance = PB, nonce = PN },
                         Receiver = #account{ balance = NB }, Fee, Payload]) ->
  case is_invalid(Sender, Receiver, Fee, Payload) of
    true ->
      {ok, Tx} =
        aec_spend_tx:new(#{ sender    => Sender#account.pubkey,
                            recipient => Receiver#account.pubkey,
                            amount    => Receiver#account.balance,
                            fee       => Fee,
                            payload   => Payload,
                            nonce     => Sender#account.nonce + 1
                          }),
      S#state{invalid_transactions = S#state.invalid_transactions ++ [ Tx ]};
    false ->
      case PB >= NB + Fee of
        false -> S;  %% not enough balance
        true ->
          Accounts = lists:keyreplace(Sender#account.privkey, #account.privkey, S#state.accounts, 
                                      Sender#account{ balance = PB - NB - Fee, nonce = PN + 1 }),
          S#state{ accounts = Accounts ++ [Receiver] }
      end
  end.

add_account_post(_S, [_Node, _Sender, _Receiver, _Fee, _Payload], Res) ->
  eq(Res, {ok, 200, #{}}).

is_invalid(_Sender, _Receiver, Fee, _Payload) ->
  Fee < aec_governance:minimum_tx_fee().

%% --- Operation: balance ---
%% balance_pre(S) ->
%%   S#state.running =/= [].

balance_args(S) ->
  [ elements(S#state.running), 
    ?LET(Account, oneof(S#state.accounts), Account#account.pubkey) ].

balance_pre(S, [Node, PubKey]) ->
  lists:member(Node, S#state.running) andalso lists:keymember(PubKey, #account.pubkey, S#state.accounts).

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





%% --- Operation: transaction_pool ---
transaction_pool_args(S) ->
  [elements(S#state.running)].

transaction_pool_pre(S, [Node]) ->
  lists:member(Node, S#state.running).

transaction_pool(Node) ->
  case request(Node, 'GetTxs', #{}) of
    {ok, 200, Transactions} ->
      Txs = [ begin
                {transaction, Trans} = aec_base58c:decode(T),
                %% Not sure all transactions in pool must be signed???
                aetx_sign:tx(aetx_sign:deserialize_from_binary(Trans))
              end || #{tx := T} <- Transactions ],
      io:format("\n\nTransactions ~p\nTxs ~p\n\n", [Transactions, Txs]),
      Txs;
    Res ->
      Res
  end.


transaction_pool_post(_S, [_Node], Res) ->
  is_list(Res).


%% --- Operation: name_preclaim ---
%% name_preclaim_pre(S) ->
%%     S#state.running /= [].

%% name_preclaim_args(_S) ->
%%   [elements(S#state.running), elements(S#state.accounts), choose(0,5), utf8()].

name_preclaim_pre(S, [Node, _, _, _]) ->
  lists:member(Node, S#state.running).

name_preclaim(Node, Sender, Fee, Commitment) ->
  {ok, Tx} =
    aens_preclaim_tx:new(#{account    => Sender#account.pubkey,
                           nonce      => Sender#account.nonce + 1,
                           commitment => Commitment,
                           fee        => Fee}),
  SignedTx = aetx_sign:sign(Tx, Sender#account.privkey),
  Transaction = aec_base58c:encode(transaction, aetx_sign:serialize_to_binary(SignedTx)),
  request(Node, 'PostNamePreclaim',  #{tx => Transaction}).

name_preclaim_next(S, _Value, [ _Node, #account{ balance = PB, nonce = PN } = Sender, Fee, Commitment]) ->
  case PB >= Fee of
    false -> S;  %% not enough balance
    true ->
      Accounts = lists:keyreplace(Sender#account.privkey, #account.privkey, S#state.accounts, 
                                  Sender#account{ balance = PB - Fee, nonce = PN + 1 }),
      S#state{ accounts = Accounts, names = S#state.names ++ [{Sender#account.pubkey, Commitment, preclaim}] }
  end.

name_preclaim_post(_S, [_Name], Res) ->
  case Res of 
    {ok, 200, _} -> true;
    {error, socket_closed_remotely} ->
      file:write_file("stats.txt", "C", [append]),
      timer:sleep(1000),
      socket_closed;
    _ -> eq(Res, ok)
  end.

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
  request(Node, 'GetTop', #{}).

top_post(_S, [_Node], Res) ->
  case Res of 
    {ok, 200, _} -> true;
    _ -> eq(Res, ok)
  end.


final_balances([], _) ->
  {undefined, []};
final_balances(Nodes, PubKeys) ->
  TxPools = lists:append([ transaction_pool(Node) || Node <- Nodes ]),
  Balances = [ balance(Node, PubKey) || Node <- Nodes, PubKey <- PubKeys ],
  {lists:usort(Balances), lists:usort(TxPools)}.

tag(_Tag, true) -> true;
tag(Tag, false) -> Tag;
tag(Tag, Other) -> {Tag, Other}. 

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
           #{ public := PubKey, secret := PrivKey} = enacl:sign_keypair(),
           #account{ pubkey = PubKey, balance = Balance, privkey = PrivKey }
         end).


%% UAT keys: https://github.com/aeternity/testnet-keys/tree/master/accounts/UAT_sender_account
prop_transactions() ->
  prop_transactions(10000, [#account{ pubkey = <<206,167,173,228,112,201,249,157,157,78,64,8,128,168,111,
                                                 29,73,187,68,75,98,241,26,158,187,100,187,207,235,115,
                                                 254,243>>,
                                      privkey = <<230,169,29,99,60,119,207,87,113,50,157,51,84,179,188,
                                                  239,27,197,224,50,196,61,112,182,211,90,249,35,206,30,
                                                  183,77,206,167,173,228,112,201,249,157,157,78,64,8,128,
                                                  168,111,29,73,187,68,75,98,241,26,158,187,100,187,207,
                                                  235,115,254,243>>,
                                      balance = 1000000,
                                      nonce = 19}]).


prop_transactions(FinalSleep) ->
  ?FORALL(Accounts, noshrink(non_empty(list(account_gen(1000000)))),
          prop_transactions(FinalSleep, Accounts)).

prop_transactions(FinalSleep, Accounts) ->
  ?SETUP(fun() ->
             
             fun() -> ok end
         end,
         prop_patron(FinalSleep, Accounts)).

prop_patron(FinalSleep, Accounts) ->
  ?FORALL(Nodes, systems(2),
  ?IMPLIES(all_connected(Nodes), 
  ?FORALL(Cmds, more_commands(20, commands(?MODULE, #state{nodes = Nodes, accounts = Accounts})),
  ?SOMETIMES(2,
  begin
    DataDir = filename:absname("data"),
    Genesis = filename:join(DataDir, "accounts.json"),
    JSON = 
      jsx:encode(
        [ { aec_base58c:encode(account_pubkey, PK), B} || #account{ pubkey = PK, balance = B } <- Accounts ]),
    ok = filelib:ensure_dir(Genesis),
    ok = file:write_file(Genesis, JSON),
    file:write_file("stats.txt", "|", [append]),

    aest_nodes_mgr:start([aest_docker], #{data_dir => DataDir,
                                          temp_dir => "/tmp"}),
    aest_nodes_mgr:setup_nodes([ Node#{ genesis => Genesis,
                                        backend => aest_docker
                                      } || Node <- Nodes ]),
    {H, S, Res} = run_commands(Cmds),
    timer:sleep(FinalSleep),
    {FinalBalances, TransactionPool} = final_balances(S#state.running, [ A#account.pubkey || A <-S#state.accounts]),
    eqc:format("Balances ~p\n", [FinalBalances]),
    NonceGapTxs = nonce_gaps(S#state.accounts, TransactionPool),
    eqc:format("Nonces ~p\n", [NonceGapTxs]),

    aest_nodes_mgr:stop(),
    timer:sleep(8000),

    check_command_names(Cmds,
      measure(length, commands_length(Cmds),
      measure(spend_tx, length([ 1 || {_, add_account, _} <- command_names(Cmds)]),
        pretty_commands(?MODULE, Cmds, {H, S, Res},
                        conjunction([{result, Res == ok},
                                     {transactions, equals([ Tx || Tx <- TransactionPool, 
                                                                   is_possible(S#state.accounts, Tx),
                                                                   not in_nonce_gap(NonceGapTxs, Tx)
                                                           ], [])},
                                     {nonce_gap, true}, %% equals(NonceGapTxs, [])
                                     {invalid_transactions, subset(S#state.invalid_transactions, TransactionPool)}])))))
  end)))).


is_possible(Accounts, Tx) ->
  From = aetx:origin(Tx),
  FromBalance = balance_of(From, Accounts),
  Type = aetx:tx_type(Tx),
  Fee = aetx:fee(Tx),
  Amount = 
    case Type of
      <<"spend_tx">> ->
        %% Why is there no amount API ??? Utterly ugly.
        {aetx,spend_tx,aec_spend_tx,
         {spend_tx, _, _, A, _, _, _}} = Tx,
        A
      end,
  Amount + Fee < FromBalance andalso Fee >= aec_governance:minimum_tx_fee().

nonce_gaps(Accounts, Txs) ->
  Unprocessed = 
    lists:foldl(fun(Tx, Map) ->
                    Sender = aetx:origin(Tx),
                    Nonce = aetx:nonce(Tx),
                    maps:put(Sender, lists:sort([Nonce | maps:get(Sender, Map, [])]), Map)
                end, #{}, Txs), 
  maps:fold(fun(Sender, Nonces, Acc) ->
                [{Sender, dropped(nonce_of(Sender, Accounts), lists:reverse(Nonces))}] ++ Acc
            end, [], Unprocessed).

in_nonce_gap(Gaps, Tx) ->
  Sender = aetx:origin(Tx),
  Nonce = aetx:nonce(Tx),
  case lists:keyfind(Sender, 1, Gaps) of
    false ->
      false;
    {_, Nonces} ->
      lists:member(Nonce, Nonces)
  end.

dropped(_Max, []) ->
  [];
dropped(Max, [N | Ns]) when Max > N ->
  [N | Ns];
dropped(Max, [Max | Ns]) ->
  dropped(Max -1, Ns);
dropped(_, _Ns) ->
  [].




%% There are no invalid transactions left in the pool.
subset(Txs, Pool) ->
  ?WHENFAIL(eqc:format("Txs = ~p =/= TransactionPool = ~p\n", [Txs, Pool]),
            (Txs -- Pool) == Txs).

%% -- helper functions

all_connected(Nodes) ->
  Graph = digraph:new(),
  [ digraph:add_vertex(Graph, Name) || #{name := Name} <- Nodes ],
  [ digraph:add_edge(Graph, Name, Peer) || #{name := Name, peers := Peers} <- Nodes, Peer <- Peers ],
  Result = length(digraph_utils:components(Graph)) == 1,
  digraph:delete(Graph),
  Result.


request(Node, Id, Params) ->
  io:format("request ~p\n", [Id]),
  aehttp_client:request(Id, Params, 
                        [{ext_http, aest_nodes_mgr:get_service_address(Node, ext_http)}, 
                         {ct_log, fun(Fmt, Args) -> io:format(Fmt++["\n"], Args) end }]).



