%%% @author Thomas Arts 
%%% @doc Testing state channel fsm at system test level.
%%%
%%%      The idea is that these tests could run on UAT as well.
%%%      For that reason, we cannot assume any specific height or nonces of the root account.
%%%      The Patron is the account that has a lot of tokens and we start by reading 
%%%      that account and creating working accounts from it.
%%%
%%%      Running: rebar3 as system_test, test shell
%%%      cd("eqc/system-test").
%%%
%%%
%%% @end
%%% Created : 17 May 2018 by Thomas Arts 
%%% Updated : 30 Sep 2018 by Thomas Arts

-module(transactions_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

%% -- State and state functions ----------------------------------------------
-record(state,{nodes = [], accounts = [], nonce_delta = 1, 
               running = [], http_ready = [],
               height = 0,
               tx_hashes = [], %% symbolic !
               users = []
              }).

-record(user, {name, balance, nonce}).

-record(account, { pubkey,
                   balance,
                   privkey,
                   nonce = 0}).

-define(DELTA_TTL, 10).  %% times 3? minutes on UAT

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
  ?LET(TTL, choose(0, 20), Height + (200 - TTL)).

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

add_account(Node, From, Nonce, {Name, Balance}, Fee, _, Payload) ->
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

pingpong_adapt(S, [Node, #{from := From, to := To, ttl := TTL} = Tx]) ->
  case {lists:keyfind(From, #user.name, S#state.accounts), 
        lists:keyfind(To, #user.name, S#state.accounts)} of
    {false, _} -> false;
    {_, false} -> false;
    {Account1, Account2} ->
      [Node, Tx#{from_nonce => Account1#user.nonce + 1, to_nonce =>
                   Account2#user.nonce, ttl => ttl(S, TTL)}]
  end.

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
          tx_hashes = {call, ?MODULE, append, [Value , S#state.tx_hashes]}}.

pingpong_post(_S, [_Account1, _Account2], Res) ->
  case Res of
    [ _, _] -> true;
    _ ->
      Res
  end.


append({exception, _}, L) ->
  L;
append(L1, L2) ->
  L1 ++ L2.


%% --- Operation: balance ---
balance_pre(S) ->
  S#state.http_ready =/= [] andalso S#state.accounts =/= [].

balance_args(S) ->
  [ elements(S#state.http_ready), ?LET(A, oneof(S#state.accounts), A#user.name), weighted_default({99, #{}}, 
                                                                                                  {1, #{pubkey => binary()}}) ].

balance_pre(S, [Node, Name, _]) ->
  lists:member(Node, S#state.http_ready) andalso lists:keymember(Name, #user.name, S#state.accounts).

balance(Node, Name, FaultInject) ->
    [{_, #account{pubkey = PubKey}}] = ets:lookup(accounts, Name),
    try
        #{Node := #{PubKey := Balance}} = aest_nodes:wait_for_value({balance, PubKey, 0}, [Node], 2000,
                                                                    [{fault_inject, FaultInject}]),
        Balance
    catch
        _:Reason ->
            case FaultInject =/= #{} andalso Reason == timeout of
                true  -> undefined;
                false -> {'EXIT', Reason, erlang:get_stacktrace()}
            end
    end.


%% --- Operation: transaction_pool ---
transaction_pool_pre(S) ->
  S#state.http_ready =/= [].

transaction_pool_args(S) ->
  [elements(S#state.http_ready)].

transaction_pool_pre(S, [Node]) ->
  lists:member(Node, S#state.http_ready).

transaction_pool(Node) ->
    case catch aest_nodes:get_mempool(Node) of 
        {'EXIT', Reason} ->
            io:format("\n\nTransactions ~p\n\n", [Reason]),
            %% on uat crashes (no internal interface accessible)
            [];
        Transactions ->
            io:format("\n\nTransactions ~p\n\n", [Transactions]),
            %% I might have saved them encoded in memory, need to re-encode if I want to compare
            Txs = [ Tx || #{tx := Tx} <- Transactions ],
            io:format("\n\nTransactions ~p\nTxs ~p\n\n", [Transactions, Txs]),
            Txs
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
  Balances = [ {Account#user.name, balance(Node, Account#user.name, #{}), Account#user.balance} 
               || Node <- Nodes, Account <- Accounts ],
  lists:usort(Balances).

%% Return all transactions that we genearated but are not yet on chain
final_transactions([], _) ->
  [];
final_transactions([Node|_], _Hashes) ->
  transaction_pool(Node).


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

weight(_S, add_account) -> 10;
weight(_S, pingpong) -> 200;
weight(_S, start) -> 1;
weight(_S, balance) -> 0;
weight(_S, transaction_pool) -> 0;
weight(_S, _) -> 1.


%% -- Generators -------------------------------------------------------------
gen_key_pair() ->
    return(crypto:generate_key(ecdh, crypto:ec_curve(secp256k1))).

account_gen(NatGen) ->
    ?LET({[Name], Balance}, {eqc_erlang_program:words(1), NatGen}, {Name, Balance}).

check_ttl(_S, Number) when is_integer(Number) ->
  true;
check_ttl(S, {Height, _}) ->
  Height == S#state.height;
check_ttl(_S, optional) ->
  true.

optional_ttl(Tx) ->
  case maps:get(ttl, Tx) of
    optional -> 
      maps:without([ttl], Tx);
    {Height, DTTL} ->
          Tx#{ttl => Height + DTTL};
     Absolute ->
          Tx#{ttl => Absolute}
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

prop_dev2() ->
   prop_patron(7*60*1000, #account{ pubkey = <<206,167,173,228,112,201,249,157,157,78,64,8,128,168,111,
                                                 29,73,187,68,75,98,241,26,158,187,100,187,207,235,115,
                                                 254,243>>,
                                    privkey = <<230,169,29,99,60,119,207,87,113,50,157,51,84,179,188,
                                                  239,27,197,224,50,196,61,112,182,211,90,249,35,206,30,
                                                  183,77,206,167,173,228,112,201,249,157,157,78,64,8,128,
                                                  168,111,29,73,187,68,75,98,241,26,158,187,100,187,207,
                                                  235,115,254,243>>,
                                    balance = 1000000 %% ensure at least this much in patron account
                                   }, aest_dev2).  %% 31.13.249.78

%% One could run this with an arbitrary generated account 
prop_patron(FinalSleep, Patron, Backend) ->
  eqc:dont_print_counterexample(
  ?LET(Shrinking, parameter(shrinking, false),
  ?FORALL([NodeName|_] = Nodes, systems(1),
  ?FORALL(Cmds, more_commands(20, commands(?MODULE, #state{nodes = Nodes, running = [NodeName]})),
  ?SOMETIMES(if not (Shrinking orelse Backend == aest_uat) -> 1; 
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
                                          , log_fun => fun(Fmt, As) -> io:format(Fmt ++ ["\n"], As) end}
                                          %% , log_fun => fun(Fmt, _As) -> io:format("#") end}
                             ),
    aest_nodes_mgr:setup_nodes(
      aest_nodes:cluster(Nodes, #{ genesis => Genesis,
                                   source => {pull, "aeternity/epoch:local"},
                                   backend => Backend })),
    %% eqc:format("Cmds = ~p\n", [Cmds]),
    start(NodeName),
    http_ready(NodeName),
    PatronNonce = try_get_nonce(NodeName, Patron#account.pubkey),
    eqc:format("Patron nonce ~p\n", [PatronNonce]),
    Table = ets:new(accounts, [named_table]),
    ets:insert(accounts, {patron, Patron#account{nonce = PatronNonce}}),

    {H, S, Res} = run_commands(Cmds, [{patron_nonce, PatronNonce + 1}]),
   
    eqc:format("final state ~p\n", [S]),
    WaitForChain =
          case eqc_symbolic:eval(S#state.tx_hashes) of
              [] -> [];
              TxHashes ->
                  OnNode = aest_nodes:wait_for_value({txs_on_node, TxHashes}, S#state.http_ready, 2000, []),
                  case lists:usort([ Tx || {Tx, At} <- lists:append(maps:values(OnNode)),  At < 0 ]) of
                      [] -> [];
                      MemPool ->
                          (catch aest_nodes:wait_for_value({txs_on_chain, MemPool}, 
                                                           S#state.http_ready, FinalSleep, [{key_blocks, 0}]))
                  end
          end,
    eqc:format("Wait for chain ~p\n", [WaitForChain]),
    %% If this times out, then we have transactions in the mempool, or discareded transactions

    FinalBalances = final_balances(S#state.http_ready, S#state.accounts),
    eqc:format("Balances ~p\n", [FinalBalances]),

    ets:delete(Table),
    aest_nodes_mgr:dump_logs(),

    aest_nodes_mgr:stop(),
    if Backend =/= aest_uat -> timer:sleep(10000);
       true -> ok
    end,

    check_command_names(Cmds,
      measure(length, commands_length(Cmds),
      measure(spend_tx, lists:sum([ case Cmd of
                                        add_account -> 1;
                                        pingpong -> 2;
                                        _ -> 0
                                    end || {_, Cmd, _} <- command_names(Cmds)]),
      aggregate(call_features(H),
        pretty_commands(?MODULE, Cmds, {H, S, Res},
                        conjunction([{result, Res == ok},
                                     {balances, equals([{Name, B, MB} || FinalBalances =/= undefined, {Name, B, MB}<-FinalBalances, B=/=MB], [])},
                                     {transactions, equals(WaitForChain, [])}
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
  io:format("------- ~p ~p\n", [Id, Params]),
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
