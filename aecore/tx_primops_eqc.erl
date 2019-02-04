%%% @author Thomas Arts
%%% @doc
%%%
%%%      Start a second epoch node with old code using something like:
%%%            ./rebar3 as test shell --sname oldepoch@localhost --apps ""
%%%            we need the test profile to assure that the cookie is set to aeternity_cookie
%%%            The test profile has a name and a cookie set in {dist_node, ...}
%%% 
%%%       TODO: 
%%%          - fix channel_withdraw
%%%          - add channel mutual close
%%%          - add oracle names to the state such that we can use names with oracles
%%%          - add names to oracle txs
%%%          - add extend oracle
%%%          - add contract txs (quite a lot of work, I fear)
%%%          - tune distribution (all EXIT differences should show up in features)
%%%          - mock aec_governance values to test for name revoke re-use etc.
%%% @end
%%% Created : 23 Jan 2019 by Thomas Arts

-module(tx_primops_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).
-define(REMOTE_NODE, 'oldepoch@localhost').
-define(Patron, <<1, 1, 0:240>>).
-define(NAMEFRAGS, ["foo", "bar", "baz"]).

-record(account, {key, amount, nonce, names_owned = []}).
-record(preclaim,{name, salt, height, claimer}).
-record(claim,{name, height, update_height, valid_height, revoke_height, claimer}).
-record(query, {sender, id, fee, response_ttl}).
-record(channel, {id, round = 1, amount = 0, reserve = 0}).

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{claims => [], preclaims => []}.

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
    true.

precondition_common(_S, _Call) ->
    true.

postcondition_common(_S, _Call, _Res) ->
    true.

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
init_pre(S) ->
    not maps:is_key(accounts, S).

init_args(_S) ->
    TxEnv = aetx_env:tx_env(0),   %% a hack, we need to create a nice env here, time field has side-effect 
    [TxEnv].

init(_) ->
    Trees = rpc(aec_trees, new_without_backend, [], fun hash_equal/2),
    EmptyAccountTree = rpc(aec_trees, accounts, [Trees]),
    Account = rpc(aec_accounts, new, [?Patron, 1200000]), 
    AccountTree = rpc(aec_accounts_trees, enter, [Account, EmptyAccountTree]),
    InitialTrees = rpc(aec_trees, set_accounts, [Trees, AccountTree], fun hash_equal/2),
    put(trees, InitialTrees),
    InitialTrees, 
    ok.

init_next(S, _Value, [TxEnv]) ->
    S#{tx_env => TxEnv,
       accounts => [#account{key = ?Patron, amount = 1200000, nonce = 1}]}.

%% --- Operation: mine ---
mine_pre(S) ->
    maps:is_key(accounts, S).

mine_args(#{tx_env := TxEnv}) ->
    Height = aetx_env:height(TxEnv),
    [Height].

mine_pre(#{tx_env := TxEnv}, [H]) ->
    aetx_env:height(TxEnv) == H.

mine_adapt(#{tx_env := TxEnv}, [_]) ->
    [aetx_env:height(TxEnv)];
mine_adapt(_, _) ->
    false.

mine(Height) ->
    Trees = get(trees),
    NewTrees = rpc(aec_trees, perform_pre_transformations, [Trees, Height + 1], fun hash_equal/2),
    put(trees, NewTrees),
    NewTrees,
    ok.

mine_next(#{tx_env := TxEnv} = S, _Value, [H]) ->
    Payback = [ Query || Query <- maps:get(queries, S, []), Query#query.response_ttl =< H],
    Accounts = [ case lists:keyfind(Account#account.key, #query.sender, Payback) of
                     false -> Account;
                     Query -> Account#account{amount = Account#account.amount + Query#query.fee}
                 end || Account <- maps:get(accounts, S, [])],
    S#{tx_env => aetx_env:set_height(TxEnv, H + 1),
       accounts => Accounts,
       queries =>  maps:get(queries, S, []) -- Payback
      }.

mine_features(S, [H], _Res) ->
    [mine_response_ttl || [ true || Query <- maps:get(queries, S, []), Query#query.response_ttl =< H ] =/= [] ] ++
        [mine].


%% --- Operation: spend ---
spend_pre(S) ->
    maps:is_key(accounts, S).

spend_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
    ?LET([{SenderTag, Sender}, {ReceiverTag, Receiver}], 
         vector(2, gen_account_pubkey(Accounts)),  %% Add oracle as well! and contract
         ?LET([Amount, Nonce, To], [nat(), gen_nonce(Sender), 
                                    oneof([account, {name, elements(maps:keys(maps:get(named_accounts, S, #{})) ++ [<<"ta.test">>])}])],
              %% important: we should never generate ta.test, it is a definitely wrong name
              [Env, {SenderTag, Sender#account.key}, 
               case To of
                   account -> {ReceiverTag, Receiver#account.key};
                   {name, Name} -> {name, Name}
               end,
               #{sender_id => aec_id:create(account, Sender#account.key),  %% The sender is asserted to never be a name.
                 recipient_id =>  
                     case To of 
                         account ->
                             aec_id:create(account, Receiver#account.key);
                         {name, Name} ->
                             aec_id:create(name, aens_hash:name_hash(Name))
                     end,
                 amount => Amount,
                 fee => choose(1, 10), 
                 nonce => Nonce,
                 payload => utf8()}])),
         Args ++ [spend_valid(S, Args)]).

spend_pre(#{accounts := Accounts} = S, [Env, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, Correct]) ->
    Valid = spend_valid(S, [Env, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx]),
    ReceiverOk = 
        case ReceiverTag of 
            new -> lists:keyfind(Receiver, #account.key, Accounts) == false;
            existing -> lists:keyfind(Receiver, #account.key, Accounts) =/= false;
            name -> maps:is_key(Receiver, maps:get(named_accounts, S, #{}))
        end,
    ReceiverOk andalso Correct == Valid
        andalso correct_height(S, Env).

spend_valid(#{accounts := Accounts, tx_env := TxEnv} = S, [_Env, {_, Sender}, {ReceiverTag, Receiver}, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) 
                andalso SenderAccount#account.amount >= maps:get(amount, Tx) + maps:get(fee, Tx) 
                andalso maps:get(fee, Tx) >= 0  %% it seems fee == 0 does not return error
                andalso
                   case ReceiverTag of
                       new -> true;
                       existing -> lists:keyfind(Receiver, #account.key, Accounts) /= false;   
                       name ->
                           case lists:keyfind(Receiver, #claim.name, maps:get(claims, S, [])) of
                               false -> false;
                               Claim -> 
                                   Claim#claim.revoke_height == undefined
                                       andalso Claim#claim.valid_height >= aetx_env:height(TxEnv)
                                       andalso aec_id:create(name, 
                                                             aens_hash:name_hash(Receiver)) == maps:get(recipient_id, Tx)
                                   %% for shrinking
                           end
                   end
    end.

spend_adapt(#{tx_env := TxEnv} = S, [_, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, _Correct]) ->
    [TxEnv, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, 
     spend_valid(S, [TxEnv, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx])];
spend_adapt(_, _) ->
    false.

    
spend(Env, _Sender, _Receiver, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aec_spend_tx, new, [Tx]),
    {_, SpendTx} = aetx:specialize_type(AeTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aec_spend_tx, check, [SpendTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aec_spend_tx, process, [SpendTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aec_spend_tx, process, [SpendTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.


spend_next(#{accounts := Accounts} = S, _Value, 
           [_Env, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, Correct]) ->
    if Correct ->
            %% Classical mistake if sender and receiver are the same! Update carefully
            SAccount = lists:keyfind(Sender, #account.key, Accounts),
            RAccount = 
                case ReceiverTag of
                    name -> 
                        RealReceiver = maps:get(Receiver, maps:get(named_accounts, S, #{})),
                        case lists:keyfind(RealReceiver, #account.key, Accounts) of
                            false -> #account{key = RealReceiver, amount = 0, nonce = 1};
                            Acc -> Acc
                        end;
                    new -> #account{key = Receiver, amount = 0, nonce = 1};
                    existing ->
                        lists:keyfind(Receiver, #account.key, Accounts)
                end,
            case Sender == RAccount#account.key of
                false ->
                    S#{accounts => 
                           (Accounts -- [RAccount, SAccount]) ++
                           [SAccount#account{amount = SAccount#account.amount - maps:get(amount,Tx) - maps:get(fee, Tx), 
                                             nonce = maps:get(nonce, Tx) + 1},
                            RAccount#account{amount = maps:get(amount,Tx) + RAccount#account.amount}]};  %% add to end of list
                true ->
                    S#{accounts => 
                           (Accounts -- [SAccount]) ++
                           [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx), 
                                             nonce = maps:get(nonce, Tx) + 1}]}
            end;
       not Correct -> 
            S
    end.

spend_post(_S, [_Env, _, _, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.


spend_features(S, [_Env, {_, Sender}, {Tag, Receiver}, Tx, Correct], Res) ->
    [{spend_accounts, length(maps:get(accounts, S))}, 
     {correct,  if Correct -> spend; true -> false end}] ++
        [ spend_to_self || Sender == Receiver andalso Correct] ++
             [ {spend, zero} || maps:get(amount, Tx) == 0 andalso Correct] ++
             [ {spend, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [ {spend_to_name, Receiver} || Tag == name ] ++
        [ {spend, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: register_oracle ---
register_oracle_pre(S) ->
    length(maps:get(accounts, S, [])) > 1.

register_oracle_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET({SenderTag, Sender}, gen_account_pubkey(lists:keydelete(?Patron, #account.key, Accounts)),
              [Env, {SenderTag, Sender#account.key},
                    #{account_id => aec_id:create(account, Sender#account.key), 
                      query_format    => <<"send me any string"/utf8>>,
                      response_format => <<"boolean()"/utf8>>,
                      query_fee       => nat(),
                      fee => choose(1, 10), 
                      nonce => gen_nonce(Sender),
                      oracle_ttl => {delta, 100}}]),
         Args ++ [register_oracle_valid(S, [lists:nth(2, Args), lists:last(Args)])]).

register_oracle_pre(S, [Env, Sender, Tx, Correct]) ->
    Correct == register_oracle_valid(S, [Sender, Tx]) andalso correct_height(S, Env).

register_oracle_valid(S, [{_, Sender}, Tx]) ->
    case lists:keyfind(Sender, #account.key, maps:get(accounts, S, [])) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) andalso
                not lists:keymember(Sender, 1, maps:get(oracles, S, []))
    end.

register_oracle_adapt(#{tx_env := TxEnv} = S, [_, Sender, Tx, _Correct]) ->
    [TxEnv, Sender, Tx, register_oracle_valid(S, [Sender, Tx])];
register_oracle_adapt(_, _) ->
    %% in case we don't even have a TxEnv
    false.

register_oracle(Env, _Sender, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aeo_register_tx, new, [Tx]),
    {oracle_register_tx, OracleTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aeo_register_tx, check, [OracleTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aeo_register_tx, process, [OracleTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aeo_register_tx, process, [OracleTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.
    

register_oracle_next(#{accounts := Accounts} = S, _Value, [_Env, {_, Sender}, Tx, Correct]) ->
    if Correct ->
            SAccount = lists:keyfind(Sender, #account.key, Accounts),
            S#{accounts => 
                   (Accounts -- [SAccount]) ++
                   [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx), 
                                     nonce = maps:get(nonce, Tx) + 1}],
               oracles =>
                   maps:get(oracles, S, []) ++ [{Sender, maps:get(query_fee, Tx)}]};
       not Correct -> 
            S
    end.

register_oracle_post(_S, [_Env, _Sender,_Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.

register_oracle_features(_S, [_Env, {_, _Sender}, Tx, Correct], Res) ->
    [{correct, if Correct -> register_oracle; true -> false end} ] ++
        [ {oracle_query_fee, zero} || maps:get(query_fee, Tx) == 0 andalso Correct] ++
        [{register_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: query_oracle ---
query_oracle_pre(S) ->
     maps:is_key(accounts, S).

query_oracle_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET([{SenderTag, Sender}, {_, Oracle}], 
              vector(2, gen_account_pubkey(Accounts)),
                   [Env, {SenderTag, Sender#account.key}, Oracle#account.key,
                    #{sender_id => aec_id:create(account, Sender#account.key), 
                      oracle_id => aec_id:create(oracle, Oracle#account.key), 
                      query => oneof([<<"{foo: bar}"/utf8>>, <<"any string"/utf8>>, <<>>]),
                      query_fee => nat(),
                      query_ttl => {delta, 3},
                      response_ttl => {delta, 3},
                      fee => choose(1, 10), 
                      nonce => gen_nonce(Sender)
                     }]),
         Args ++ [query_oracle_valid(S, Args)]).

query_oracle_pre(S, [Env, {SenderTag, Sender}, Oracle, Tx, Correct]) ->
    Correct == query_oracle_valid(S, [Env, {SenderTag, Sender}, Oracle, Tx]) andalso correct_height(S, Env).

query_oracle_valid(S, [_Env, {_SenderTag, Sender}, Oracle, Tx]) ->
    case {lists:keyfind(Sender, #account.key, maps:get(accounts, S, [])),
          lists:keyfind(Oracle, 1, maps:get(oracles, S, []))}
          of
        {false, _} -> false;
        {_, false} -> false;
        {SenderAccount, {_, QueryFee}} ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) + maps:get(query_fee, Tx) andalso
                maps:get(query_fee, Tx) >= QueryFee
    end.

query_oracle_adapt(#{tx_env := TxEnv} = S, [_Env, Sender, Oracle, Tx, _Correct]) ->
    [TxEnv, Sender, Oracle, Tx, query_oracle_valid(S, [TxEnv, Sender, Oracle, Tx])];
query_oracle_adapt(_, _) ->
    false.


query_oracle(Env, _Sender, _Oracle, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aeo_query_tx, new, [Tx]),
    {oracle_query_tx, OracleTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aeo_query_tx, check, [OracleTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aeo_query_tx, process, [OracleTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aeo_query_tx, process, [OracleTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

query_oracle_next(#{accounts := Accounts} = S, _Value, [Env, {_, Sender}, Oracle, Tx, Correct]) ->
    if Correct ->
            {delta, Delta} = maps:get(response_ttl, Tx),
            SAccount = lists:keyfind(Sender, #account.key, Accounts),
            S#{accounts => 
                   (Accounts -- [SAccount]) ++
                   [SAccount#account{
                      amount = SAccount#account.amount - maps:get(fee, Tx) - maps:get(query_fee, Tx), 
                      nonce = maps:get(nonce, Tx) + 1}],
              queries => maps:get(queries, S, []) ++
                   [#query{sender = Sender, 
                           id = {Sender, maps:get(nonce, Tx), Oracle}, 
                           response_ttl = Delta + aetx_env:height(Env), 
                           fee = maps:get(query_fee, Tx)}]};
       not Correct -> 
            S
    end.

query_oracle_post(_S, [_Env, _Sender, _Oracle, _Tx, Correct], Res) ->
     case Res of
        {error, _} -> not Correct;
        ok -> Correct;
         _ -> not Correct andalso valid_mismatch(Res)
    end.

query_oracle_features(_S, [_Env, _, _, Tx, Correct], Res) ->
    [{correct, if Correct -> query_oracle; true -> false end} ] ++
             [ {query_query_fee, zero} || maps:get(query_fee, Tx) == 0 andalso Correct] ++
             [ {query_oracle, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [{query_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].

%% --- Operation: response_oracle ---
response_oracle_pre(S) ->
     maps:get(queries, S, []) =/= [].

%% Only responses to existing query tested for the moment, no fault injection
response_oracle_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET({Sender, Nonce, Oracle}, 
               frequency([{99, ?LET(Query, elements(maps:get(queries, S)), Query#query.id)},
                          {1, {?Patron, 2, ?Patron}}]),
              [Env, {Sender, Nonce, Oracle},
               #{oracle_id => aec_id:create(oracle, Oracle), 
                 query_id => aeo_query:id(Sender, Nonce, Oracle),
                 response => <<"yes, you can">>,
                 response_ttl => {delta, 3},
                 fee => choose(1, 10), 
                 nonce => case lists:keyfind(Oracle, #account.key, Accounts) of
                              false -> 1;
                              Account -> Account#account.nonce
                          end
                }]),
         Args ++ [response_oracle_valid(S, Args)]).

response_oracle_pre(S, [Env, QueryId, Tx, Correct]) ->
    Correct == response_oracle_valid(S, [Env, QueryId, Tx]) 
        andalso correct_height(S, Env).

response_oracle_valid(S, [_Env, {_, _, Oracle} = QueryId, Tx]) ->
    case lists:keyfind(Oracle, #account.key, maps:get(accounts, S)) of
        false -> false;
        OracleAccount ->
            Query = lists:keyfind(QueryId, #query.id, maps:get(queries, S, [])),
            OracleAccount#account.nonce == maps:get(nonce, Tx) andalso
                OracleAccount#account.amount >= maps:get(fee, Tx) andalso 
                Query =/= false
    end.

response_oracle_adapt(#{tx_env := TxEnv} = S, [_, QueryId, Tx, _Correct]) ->
    [TxEnv, QueryId, Tx, register_oracle_valid(S, [TxEnv, QueryId, Tx])];
response_oracle_adapt(_, _) ->
    %% in case we don't even have a TxEnv
    false.


response_oracle(Env, _QueryId, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aeo_response_tx, new, [Tx]),
    {oracle_response_tx, OracleTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aeo_response_tx, check, [OracleTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aeo_response_tx, process, [OracleTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aeo_response_tx, process, [OracleTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

response_oracle_next(#{accounts := Accounts} = S, _Value, [_Env, QueryId, Tx, Correct]) ->
    if Correct ->
            {_, _, Oracle} = QueryId,
            OracleAccount = lists:keyfind(Oracle, #account.key, Accounts),
            Query = lists:keyfind(QueryId, #query.id, maps:get(queries, S, [])),
            QueryFee = Query#query.fee,

            S#{accounts => 
                   (Accounts -- [OracleAccount]) ++
                   [OracleAccount#account{
                      amount = OracleAccount#account.amount - maps:get(fee, Tx) + QueryFee, 
                      nonce = maps:get(nonce, Tx) + 1}],
              queries => maps:get(queries, S, []) -- [Query]};
       not Correct -> 
            S
    end.

response_oracle_post(_S, [_Env, _Oracle, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.

response_oracle_features(_S, [_Env, _, _Tx, Correct], Res) ->
    [{correct, if Correct -> response_oracle; true -> false end} ] ++
        [{response_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].

%% --- Operation: channel_create ---
channel_create_pre(S) ->
    length(maps:get(accounts, S, [])) > 1.

channel_create_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET([{_, Initiator}, {_, Responder}],
              vector(2, gen_account_pubkey(Accounts)),
              [Env, Initiator#account.key, Responder#account.key,
                    #{initiator_id => aec_id:create(account, Initiator#account.key),
                      responder_id => aec_id:create(account, Responder#account.key),
                      state_hash => <<1:256>>,
                      initiator_amount => nat(),
                      responder_amount => nat(),
                      push_amount => nat(),
                      lock_period => choose(0,2),
                      channel_reserve => choose(0,10),
                      fee => choose(1, 10), 
                      nonce => gen_nonce(Initiator)}]),
         Args ++ [channel_create_valid(S, Args)]).

channel_create_pre(S, [Env, Initiator, Responder, Tx, Correct]) ->
    Initiator =/= Responder andalso
    Correct == channel_create_valid(S, [Env, Initiator, Responder, Tx]) 
        andalso correct_height(S, Env).

channel_create_valid(S, [_Env, Initiator, Responder, Tx]) ->
   case {lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])),
         lists:keyfind(Responder, #account.key, maps:get(accounts, S, []))} of
        {false, _} -> false;
        {_, false} -> false;
        {IAccount, RAccount} ->
            IAccount#account.nonce == maps:get(nonce, Tx) andalso
               IAccount#account.amount >= maps:get(fee, Tx) + maps:get(initiator_amount, Tx) andalso
               RAccount#account.amount >= maps:get(responder_amount, Tx) andalso
               maps:get(initiator_amount, Tx) >= maps:get(channel_reserve, Tx) andalso
               maps:get(responder_amount, Tx) >= maps:get(channel_reserve, Tx) 
    end.

channel_create_adapt(#{tx_env := TxEnv} = S, [_, Initiator, Responder, Tx, _Correct]) ->
    [TxEnv, Initiator, Responder, Tx, channel_create_valid(S, [TxEnv, Initiator, Responder, Tx])];
channel_create_adapt(_, _) ->
    %% in case we don't even have a TxEnv
    false.


channel_create(Env, _Initiator, _Responder, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aesc_create_tx, new, [Tx]),
    {channel_create_tx, ChannelTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aesc_create_tx, check, [ChannelTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aesc_create_tx, process, [ChannelTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aesc_create_tx, process, [ChannelTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

channel_create_next(#{accounts := Accounts} = S, _Value, [_Env, Initiator, Responder, Tx, Correct]) ->
    if Correct ->
            IAccount = lists:keyfind(Initiator, #account.key, Accounts),
            RAccount = lists:keyfind(Responder, #account.key, Accounts),
            S#{accounts => 
                   (Accounts -- [IAccount, RAccount]) ++
                   [IAccount#account{amount = 
                                         IAccount#account.amount - 
                                         maps:get(fee, Tx) - 
                                         maps:get(initiator_amount, Tx), 
                                     nonce = maps:get(nonce, Tx) + 1},
                   RAccount#account{amount = 
                                        RAccount#account.amount - 
                                        maps:get(responder_amount, Tx)}],
               channels =>
                   maps:get(channels, S, []) ++ [#channel{id = {Initiator, maps:get(nonce, Tx), Responder},
                                                          amount = maps:get(initiator_amount, Tx) +
                                                              maps:get(responder_amount, Tx),
                                                          reserve = maps:get(channel_reserve, Tx)}]};
       not Correct ->
            S
    end.

channel_create_post(_S, [_Env, _Initiator, _Responder, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.


%% --- Operation: channel_deposit ---
channel_deposit_pre(S) ->
    maps:is_key(channels, S).

channel_deposit_args(#{tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET([{Initiator, N, Responder}, Party], 
              [frequency([{99, ?LET(Channel, elements(maps:get(channels, S)), Channel#channel.id)},
                          {1, {?Patron, 2, ?Patron}}]), elements([initiator, responder])],
              [Env, {Initiator, N, Responder}, Party,
                    #{channel_id => aec_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
                      from_id => case Party of
                                     initiator -> aec_id:create(account, Initiator);
                                     responder ->  aec_id:create(account, Responder)
                                 end,
                      amount => nat(),
                      round => nat(),
                      fee => choose(1, 10),
                      state_hash => <<0:256>>,
                      nonce => 
                          case Party of
                              initiator -> gen_nonce(lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])));
                              responder ->  gen_nonce(lists:keyfind(Responder, #account.key, maps:get(accounts, S, [])))
                          end}]),
         Args ++ [channel_deposit_valid(S, Args)]).


channel_deposit_pre(S, [Env, ChannelId, Party, Tx, Correct]) ->
    Correct == channel_deposit_valid(S, [Env, ChannelId, Party, Tx]) 
        andalso correct_height(S, Env).

channel_deposit_valid(S, [_Env, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    case {lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])),
          lists:keyfind(Responder, #account.key, maps:get(accounts, S, []))} of
        {false, _} -> false;
        {_, false} -> false;
        {IAccount, RAccount} ->
            FromAccount = case Party of 
                              initiator -> IAccount;
                              responder -> RAccount
                          end,
            Channel = lists:keyfind(ChannelId, #channel.id, maps:get(channels, S, [])),
            Channel /= false andalso
                FromAccount#account.nonce == maps:get(nonce, Tx) andalso
                FromAccount#account.amount >= maps:get(fee, Tx) + maps:get(amount, Tx) andalso
                maps:get(round, Tx) > Channel#channel.round
    end.

channel_deposit_adapt(#{tx_env := TxEnv} = S, [_, ChannelId, Party, Tx, _Correct]) ->
    [TxEnv, ChannelId, Party, Tx, channel_deposit_valid(S, [TxEnv, ChannelId, Party, Tx])];
channel_deposit_adapt(_, _) ->
    %% in case we don't even have a TxEnv
    false.


channel_deposit(Env, _Channeld, _Party, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aesc_deposit_tx, new, [Tx]),
    {channel_deposit_tx, ChannelTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aesc_deposit_tx, check, [ChannelTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aesc_deposit_tx, process, [ChannelTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aesc_deposit_tx, process, [ChannelTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

channel_deposit_next(#{accounts := Accounts} = S, _Value, [_Env, {Initiator, _, Responder} = ChannelId, Party, Tx, Correct]) ->
    if Correct ->
            case {lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])),
                  lists:keyfind(Responder, #account.key, maps:get(accounts, S, []))} of
                {false, _} -> false;
                {_, false} -> false;
                {IAccount, RAccount} ->
                    FromAccount = case Party of 
                                      initiator -> IAccount;
                                      responder -> RAccount
                                  end,
                    Channels = maps:get(channels, S),
                    Channel = lists:keyfind(ChannelId, #channel.id, Channels),
                    S#{accounts => 
                           (Accounts -- [FromAccount]) ++
                           [FromAccount#account{amount = 
                                                    FromAccount#account.amount - 
                                                    maps:get(fee, Tx) - 
                                                    maps:get(amount, Tx), 
                                                nonce = maps:get(nonce, Tx) + 1}],
                       channels =>
                           (Channels -- [Channel]) ++ [Channel#channel{round = maps:get(round, Tx),
                                                                       amount = Channel#channel.amount + maps:get(amount, Tx)}]}
            end;
       not Correct ->
            S
    end.

channel_deposit_post(_S, [_Env, _ChannelId, _Party, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.

channel_deposit_features(_S, [_Env, _Channeld, _Party, _Tx, Correct], Res) ->
    [{correct, if Correct -> channel_deposit; true -> false end} ] ++
        [{channel_deposit, Res} || is_tuple(Res) andalso element(1, Res) == error].

%% --- Operation: channel_withdraw ---
channel_withdraw_pre(S) ->
    false andalso maps:is_key(channels, S).


%% We do not yet test wirthdraw by third party!
channel_withdraw_args(#{tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET([{Initiator, N, Responder}, Party], 
              [frequency([{99, ?LET(Channel, elements(maps:get(channels, S)), Channel#channel.id)},
                          {1, {?Patron, 2, ?Patron}}]), elements([initiator, responder])],
              [Env, {Initiator, N, Responder}, Party,
                    #{channel_id => aec_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
                      to_id => case Party of
                                     initiator -> aec_id:create(account, Initiator);
                                     responder ->  aec_id:create(account, Responder)
                                 end,
                      amount => nat(),
                      round => nat(),
                      fee => choose(1, 10),
                      state_hash => <<0:256>>,
                      nonce => 
                          case Party of
                              initiator -> gen_nonce(lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])));
                              responder ->  gen_nonce(lists:keyfind(Responder, #account.key, maps:get(accounts, S, [])))
                          end}]),
         Args ++ [channel_withdraw_valid(S, Args)]).


channel_withdraw_pre(S, [Env, ChannelId, Party, Tx, Correct]) ->
    Correct == channel_withdraw_valid(S, [Env, ChannelId, Party, Tx]) 
        andalso correct_height(S, Env).

channel_withdraw_valid(S, [_Env, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    case {lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])),
          lists:keyfind(Responder, #account.key, maps:get(accounts, S, []))} of
        {false, _} -> false;
        {_, false} -> false;
        {IAccount, RAccount} ->
            FromAccount = case Party of 
                              initiator -> IAccount;
                              responder -> RAccount
                          end,
            Channel = lists:keyfind(ChannelId, #channel.id, maps:get(channels, S, [])),
            Channel /= false andalso
                FromAccount#account.nonce == maps:get(nonce, Tx) andalso
                FromAccount#account.amount >= maps:get(fee, Tx) andalso
                maps:get(round, Tx) > Channel#channel.round andalso
                maps:get(amount, Tx) =< Channel#channel.amount
    end.

channel_withdraw_adapt(#{tx_env := TxEnv} = S, [_, ChannelId, Party, Tx, _Correct]) ->
    [TxEnv, ChannelId, Party, Tx, channel_withdraw_valid(S, [TxEnv, ChannelId, Party, Tx])];
channel_withdraw_adapt(_, _) ->
    %% in case we don't even have a TxEnv
    false.


channel_withdraw(Env, _Channeld, _Party, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aesc_withdraw_tx, new, [Tx]),
    {channel_withdraw_tx, ChannelTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aesc_withdraw_tx, check, [ChannelTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aesc_withdraw_tx, process, [ChannelTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aesc_withdraw_tx, process, [ChannelTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

channel_withdraw_next(#{accounts := Accounts} = S, _Value, [_Env, {Initiator, _, Responder} = ChannelId, Party, Tx, Correct]) ->
    if Correct ->
            case {lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])),
                  lists:keyfind(Responder, #account.key, maps:get(accounts, S, []))} of
                {false, _} -> false;
                {_, false} -> false;
                {IAccount, RAccount} ->
                    FromAccount = case Party of 
                                      initiator -> IAccount;
                                      responder -> RAccount
                                  end,
                    Channels = maps:get(channels, S),
                    Channel = lists:keyfind(ChannelId, #channel.id, Channels),
                    S#{accounts => 
                           (Accounts -- [FromAccount]) ++
                           [FromAccount#account{amount = 
                                                    FromAccount#account.amount - 
                                                    maps:get(fee, Tx) + 
                                                    maps:get(amount, Tx), 
                                                nonce = maps:get(nonce, Tx) + 1}],
                       channels =>
                           (Channels -- [Channel]) ++ [Channel#channel{round = maps:get(round, Tx),
                                                                       amount = Channel#channel.amount - maps:get(amount, Tx)}]}
            end;
       not Correct ->
            S
    end.

channel_withdraw_post(_S, [_Env, _ChannelId, _Party, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.

channel_withdraw_features(_S, [_Env, _Channeld, _Party, _Tx, Correct], Res) ->
   [{correct, if Correct -> channel_withdraw; true -> false end} ] ++
    [{channel_withdraw, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: name_preclaim ---

name_preclaim_pre(S) ->
    maps:is_key(accounts, S).

name_preclaim_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args,
	 ?LET([{SenderTag, Sender}, Name, Salt], 
	      [gen_account_pubkey(Accounts), gen_name(), choose(270,280)],
	      [Env, {SenderTag, Sender#account.key}, {Name, Salt},
	       #{account_id => aec_id:create(account, Sender#account.key),
		 fee => choose(1, 10), 
		 commitment_id => 
		     aec_id:create(commitment, 
				   aens_hash:commitment_hash(Name, Salt)),
		 nonce =>gen_nonce(Sender)}]), 
	 Args ++ [name_preclaim_valid(S, Args)]).

name_preclaim_pre(S, [Env, {SenderTag, Sender}, {Name, Salt}, Tx, Correct]) ->
    %% Let us not test the unlikely case that someone provides the same name with the same salt
    [present || #preclaim{name = N, salt = St} <- maps:get(preclaims, S, []), N == Name, St == Salt] == [] 
        andalso name_preclaim_valid(S, [Env, {SenderTag, Sender}, {Name, Salt}, Tx]) == Correct 
        andalso aec_id:create(commitment, aens_hash:commitment_hash(Name, Salt)) == maps:get(commitment_id, Tx)
        andalso correct_height(S, Env).

name_preclaim_valid(#{accounts := Accounts}, 
		    [_Env, {_, Sender}, {_Name, _Salt}, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx)
    end.   

name_preclaim_adapt(#{tx_env := TxEnv} = S, [_Env, {SenderTag, Sender}, {Name, Salt}, Tx, _Correct]) ->
    [TxEnv, {SenderTag, Sender}, {Name, Salt}, Tx, name_preclaim_valid(S, [TxEnv, {SenderTag, Sender}, {Name, Salt}, Tx])];
name_preclaim_adapt(_, _) ->
    false.

name_preclaim(Env, _Sender, {_Name,_Salt}, Tx, _Correct) ->
    Trees = get(trees),
    {ok, NTx} = rpc(aens_preclaim_tx, new, [Tx]),
    {_, NameTx} = aetx:specialize_type(NTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aens_preclaim_tx, check, [NameTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aens_preclaim_tx, process, [NameTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aens_preclaim_tx, process, [NameTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

name_preclaim_next(#{tx_env := TxEnv,
		     accounts := Accounts, 
		     preclaims := Preclaims} = S,
		   _Value, [_Env, {_, Sender}, {Name, Salt}, Tx, Correct]) ->
    if Correct ->
	    SAccount = lists:keyfind(Sender, #account.key, Accounts),
	    S#{accounts => 
		   (Accounts -- [SAccount]) ++
		   [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx), 
				     nonce = maps:get(nonce, Tx) + 1}],
	       preclaims => 
		   Preclaims ++ [#preclaim{name = Name, 
					   salt = Salt,
					   height = aetx_env:height(TxEnv),
                                           claimer = Sender}]};
       not Correct ->
	    S
    end.

name_preclaim_post(_S, [_Env, _Sender, {_Name, _Salt}, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.

name_preclaim_features(#{claims := Claims}, 
		       [_Env, {_, _Sender}, {Name,_Salt}, _Tx, Correct], Res) ->
    [ {correct, if Correct -> name_preclaim; true -> false end} ] ++
    [ {name_preclaim, Res} || is_tuple(Res) andalso element(1, Res) == error] ++
	[{reclaim_name, Res} || lists:keymember(Name, #claim.name, Claims)].
    

%% --- Operation: claim ---
claim_pre(S) ->
    maps:is_key(accounts, S).

%% @doc claim_args - Argument generator
-spec claim_args(S :: eqc_statem:symbolic_state()) -> eqc_gen:gen([term()]).
claim_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args,
	 ?LET([Name, {SenderTag, Sender}], 
	      [gen_name(), gen_account_pubkey(Accounts)],
	      [Env, {SenderTag, Sender#account.key},
	       #{account_id => aec_id:create(account, Sender#account.key),
		 name => Name,
		 name_salt => choose(270,280),
		 fee => choose(1, 10), 
		 nonce => gen_nonce(Sender)}]), 
	 Args ++ [claim_valid(S, Args)]).


claim_pre(S, [Env, {SenderTag, Sender}, Tx, Correct]) ->
    claim_valid(S, [Env, {SenderTag, Sender}, Tx]) == Correct andalso correct_height(S, Env).

claim_valid(#{accounts := Accounts, tx_env := Env} = S, [_Env, {_, Sender}, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) + aec_governance:name_claim_locked_fee() andalso
		case [ PC || #preclaim{name = Name, salt = Salt, claimer = Claimer} = PC <- maps:get(preclaims, S, []), 
                             Name ==  maps:get(name, Tx), 
                             Salt == maps:get(name_salt, Tx),
                             Claimer == Sender ] of
		    [] ->
			false;
		    [Preclaim] ->
                        %% preclaim and claim are in different blocks
                        Preclaim#preclaim.height + aec_governance:name_claim_preclaim_delta() =< aetx_env:height(Env) 
                            andalso
                            aetx_env:height(Env) < Preclaim#preclaim.height + aec_governance:name_preclaim_expiration()
		end
		andalso valid_name(Tx) andalso 
                not already_claimed(S, Tx)

    end.

% names may not have dots in between, only at the end (.test)
valid_name(Tx) ->
    case string:lexemes(maps:get(name,Tx), ".") of
	[_, <<"test">>] -> true;
	_ -> false
    end.

already_claimed(#{claims := Claims}, Tx) ->
    [ present || #claim{name = N} <- Claims, N == maps:get(name,Tx)] =/= [].

claim_adapt(#{tx_env := TxEnv} = S, [_Env, {SenderTag, Sender}, Tx, _Correct]) ->
    [TxEnv, {SenderTag, Sender}, Tx, claim_valid(S, [TxEnv, {SenderTag, Sender}, Tx])];
claim_adapt(_, _) ->
    false.


claim(Env, _Sender, Tx,_Correct) ->
    Trees = get(trees),
    {ok, NTx} = rpc(aens_claim_tx, new, [Tx]),
    {_, NameTx} = aetx:specialize_type(NTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aens_claim_tx, check, [NameTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aens_claim_tx, process, [NameTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aens_claim_tx, process, [NameTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

claim_next(#{tx_env := TxEnv,
             accounts := Accounts, 
	     claims := Claims} = S, 
	   _Value, [_Env, {_, Sender}, Tx, Correct]) ->
    if Correct ->
	    SAccount = lists:keyfind(Sender, #account.key, Accounts),
	    S#{accounts => 
	    	   (Accounts -- [SAccount]) ++
	    	   [SAccount#account{amount = SAccount#account.amount - 
                                         maps:get(fee, Tx) - 
                                         aec_governance:name_claim_locked_fee(), 
	    			     nonce = maps:get(nonce, Tx) + 1}],
	      claims => 
		   Claims ++ [#claim{name = maps:get(name, Tx), 
				     height = aetx_env:height(TxEnv),
                                     valid_height = -1,
                                     claimer = Sender}]};
       not Correct ->
	    S
    end.

claim_post(_S, [_Env, _Sender, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
	_ -> not Correct andalso valid_mismatch(Res)
    end.

claim_features(_S, [_Env, {_, _Sender}, _Tx, Correct], Res) ->
   [{correct, if Correct -> ns_claim; true -> false end} ] ++
        [{ns_claim, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: claim_update ---
ns_update_pre(S) ->
    maps:is_key(accounts, S).

ns_update_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args,
	 ?LET([Name, {SenderTag, Sender}, {Tag, NameAccount}], 
	      [gen_name(S), gen_account_pubkey(Accounts), gen_account_pubkey(Accounts)],
	      [Env, Name, {SenderTag, Sender#account.key}, {Tag, NameAccount#account.key},
	       #{account_id => aec_id:create(account, Sender#account.key),
		 name_id => aec_id:create(name, aens_hash:name_hash(Name)),
		 name_ttl => nat(),
                 client_ttl => nat(),
		 fee => choose(1, 10),
		 nonce => gen_nonce(Sender),
                 pointers =>
                     oneof([[], 
                            [aens_pointer:new(<<"account_pubkey">>, aec_id:create(account, NameAccount#account.key))]
                            ])}]), 
	 Args ++ [ns_update_valid(S, Args)]).

ns_update_pre(S, [Env, Name, Sender, NameAccount, Tx, Correct]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx) 
        andalso ns_update_valid(S, [Env, Name, Sender, NameAccount, Tx]) == Correct 
        andalso correct_height(S, Env).

ns_update_valid(#{accounts := Accounts} = S, [Env, Name, {_, Sender}, _, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) + aec_governance:name_claim_locked_fee() andalso
		case [ PC || #claim{name = N, claimer = Claimer} = PC <- maps:get(claims, S, []), 
                             Name == N, 
                             Claimer == Sender ] of
		    [] ->
			false;
		    [Claim] ->
                        Claim#claim.revoke_height == undefined andalso
                            (Claim#claim.update_height == undefined orelse 
                             aetx_env:height(Env) =< Claim#claim.valid_height)
		end
    end.

ns_update_adapt(#{tx_env := TxEnv} = S, [_Env, Name, {SenderTag, Sender}, NameAccount, Tx, _Correct]) ->
    [TxEnv, Name, {SenderTag, Sender}, NameAccount, Tx, 
     ns_update_valid(S, [TxEnv, Name, {SenderTag, Sender}, NameAccount, Tx])];
ns_update_adapt(_, _) ->
    false.    

ns_update(Env, _Name, _Sender, _NameAccount, Tx, _Correct) ->
    Trees = get(trees),
    {ok, NTx} = rpc(aens_update_tx, new, [Tx]),
    {_, NameTx} = aetx:specialize_type(NTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aens_update_tx, check, [NameTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aens_update_tx, process, [NameTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aens_update_tx, process, [NameTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

ns_update_next(#{accounts := Accounts} = S, _Value, [Env, Name, {_, Sender}, {_, NameAccount}, Tx, Correct]) ->
    if Correct ->
	    SAccount = lists:keyfind(Sender, #account.key, Accounts),
            Claims = maps:get(claims, S, []),
            Claim = lists:keyfind(Name, #claim.name, Claims),
	    S#{accounts => 
	    	   (Accounts -- [SAccount]) ++
	    	   [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx),
	    			     nonce = maps:get(nonce, Tx) + 1, 
                                     names_owned = (SAccount#account.names_owned -- [Name]) ++ [Name]
                                    }],
               named_accounts => 
                   %% bit of a drity hack, but only zero or 1 pointer
                   case maps:get(pointers, Tx) of
                       [] -> maps:remove(Name, maps:get(named_accounts, S, #{}));
                       _ -> maps:merge(maps:get(named_accounts, S, #{}), #{Name => NameAccount})
                   end,
               claims => 
                   (Claims -- [Claim]) ++ 
                   [Claim#claim{update_height = aetx_env:height(Env),
                                valid_height = max(Claim#claim.valid_height,
                                                   aetx_env:height(Env) + maps:get(name_ttl, Tx))}]
              };
       not Correct ->
	    S
    end.

ns_update_post(_S, [_Env, _Name, _Sender, _NameAccount, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
	_ -> not Correct andalso valid_mismatch(Res)
    end.

ns_update_features(_S, [_Env, _Name, _Sender, {Tag, _NameAccount}, _Tx, Correct], Res) ->
    [{correct, if Correct -> ns_update; true -> false end} ] ++
        [{ns_update, Tag} ] ++
        [{ns_update, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: ns_revoke ---
ns_revoke_pre(S) ->
    maps:is_key(accounts, S).

ns_revoke_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args,
	 ?LET([Name, {SenderTag, Sender}], 
	      [gen_name(S), gen_account_pubkey(Accounts)],
	      [Env, {SenderTag, Sender#account.key}, Name,
	       #{account_id => aec_id:create(account, Sender#account.key),
		 name_id => aec_id:create(name, aens_hash:name_hash(Name)),
		 fee => choose(1, 10),
		 nonce => gen_nonce(Sender)
                }]), 
	 Args ++ [ns_revoke_valid(S, Args)]).


ns_revoke_pre(S, [Env, Sender, Name, Tx, Correct]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx) 
        andalso ns_revoke_valid(S, [Env, Sender, Name, Tx]) == Correct 
        andalso correct_height(S, Env).

ns_revoke_valid(#{accounts := Accounts} = S, [_Env, {_SenderTag, Sender}, Name, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) andalso
		case [ PC || #claim{name = N, claimer = Claimer} = PC <- maps:get(claims, S, []), 
                             Name == N, 
                             Claimer == Sender ] of
		    [] ->
			false;
		    [_Claim] ->
                        true 
		end
    end.

ns_revoke_adapt(#{tx_env := TxEnv} = S, [_Env, {SenderTag, Sender}, Name, Tx, _Correct]) ->
    [TxEnv, {SenderTag, Sender}, Name, Tx, 
     ns_revoke_valid(S, [TxEnv, {SenderTag, Sender}, Name, Tx])];
ns_revoke_adapt(_, _) ->
    false.    

ns_revoke(Env, _Sender, _Name, Tx, _Correct) ->
    Trees = get(trees),
    {ok, NTx} = rpc(aens_revoke_tx, new, [Tx]),
    {_, NameTx} = aetx:specialize_type(NTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aens_revoke_tx, check, [NameTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aens_revoke_tx, process, [NameTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aens_revoke_tx, process, [NameTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

ns_revoke_next(#{accounts := Accounts} = S, _Value, [Env, {_SenderTag, Sender}, Name, Tx, Correct]) ->
    if Correct ->
	    SAccount = lists:keyfind(Sender, #account.key, Accounts),
            Claims = maps:get(claims, S, []),
            Claim = lists:keyfind(Name, #claim.name, Claims),
	    S#{accounts => 
	    	   (Accounts -- [SAccount]) ++
	    	   [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx),
	    			     nonce = maps:get(nonce, Tx) + 1, 
                                     names_owned = (SAccount#account.names_owned -- [Name])
                                    }],
               named_accounts => 
                   maps:remove(Name, maps:get(named_accounts, S, #{})),
               claims => 
                   (Claims -- [ Claim || Claim#claim.revoke_height == undefined ]) ++ 
                   [ Claim#claim{valid_height = -1,
                                revoke_height = aec_governance:name_protection_period() + aetx_env:height(Env)}
                     || Claim#claim.revoke_height == undefined ]
              };
       not Correct ->
	    S
    end.

ns_revoke_post(_S, [_Env, _Sender, _Name, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
	_ -> not Correct andalso valid_mismatch(Res)
    end.

ns_revoke_features(_S, [_Env, _Sender, _Name, _Tx, Correct], Res) ->
    [{correct, if Correct -> ns_revoke; true -> false end} ] ++
        [{ns_revoke, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: ns_transfer ---
ns_transfer_pre(S) ->
    maps:is_key(accounts, S).

ns_transfer_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args,
    ?LET([{SenderTag, Sender}, {ReceiverTag, Receiver}], 
         vector(2, gen_account_pubkey(Accounts)),
         ?LET([Name, To], [gen_name(S), 
                           oneof([account, {name, elements(maps:keys(maps:get(named_accounts, S, #{})) ++ 
                                                               [<<"ta.test">>])}])],
              [Env, {SenderTag, Sender#account.key},
               case To of
                   account -> {ReceiverTag, Receiver#account.key};
                   {name, ToName} -> {name, ToName}
               end, Name,
               #{account_id => aec_id:create(account, Sender#account.key),  %% The sender is asserted to never be a name.
                 recipient_id =>  
                     case To of 
                         account ->
                             aec_id:create(account, Receiver#account.key);
                         {name, ToName} ->
                             aec_id:create(name, aens_hash:name_hash(ToName))
                     end,
                 name_id => aec_id:create(name, aens_hash:name_hash(Name)),
		 fee => choose(1, 10),
		 nonce => gen_nonce(Sender)
                }])), 
	 Args ++ [ns_transfer_valid(S, Args)]).


ns_transfer_pre(S, [Env, Sender, Receiver,  Name, Tx, Correct]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx) 
        andalso ns_transfer_valid(S, [Env, Sender, Receiver, Name, Tx]) == Correct 
        andalso correct_height(S, Env).

ns_transfer_valid(#{accounts := Accounts} = S, [Env, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Name, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) andalso
                case lists:keyfind(Name, #claim.name, maps:get(claims, S, [])) of
                    false -> false;
                    Claim -> 
                        Claim#claim.claimer == Sender
                            andalso Claim#claim.revoke_height == undefined
                end andalso
                case ReceiverTag of
                       new -> true;
                       existing -> lists:keyfind(Receiver, #account.key, Accounts) /= false;   
                       name -> 
                           case lists:keyfind(Receiver, #claim.name, maps:get(claims, S, [])) of
                               false -> false;
                               RClaim -> 
                                   RClaim#claim.revoke_height == undefined
                                       %% andalso RClaim#claim.valid_height >= aetx_env:height(Env)
                                       andalso aec_id:create(name, 
                                                             aens_hash:name_hash(Receiver)) == maps:get(recipient_id, Tx)
                                   %% for shrinking
                           end
                end
    end.

ns_transfer_adapt(#{tx_env := TxEnv} = S, [_Env, Sender, Receiver, Name, Tx, _Correct]) ->
    [TxEnv, Sender, Receiver, Name, Tx, 
     ns_transfer_valid(S, [TxEnv, Sender, Receiver, Name, Tx])];
ns_transfer_adapt(_, _) ->
    false.    

ns_transfer(Env, _Sender, _Receiver, _Name, Tx, _Correct) ->
    Trees = get(trees),
    {ok, NTx} = rpc(aens_transfer_tx, new, [Tx]),
    {_, NameTx} = aetx:specialize_type(NTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aens_transfer_tx, check, [NameTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aens_transfer_tx, process, [NameTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aens_transfer_tx, process, [NameTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

%% Assumption the recipient does not need to exist, it is created when we provided
%% it with a name
ns_transfer_next(#{accounts := Accounts} = S, _Value, 
                 [_Env, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Name, Tx, Correct]) ->
    ReceiverKey = 
         case ReceiverTag of
             name -> 
                 maps:get(Receiver, maps:get(named_accounts, S, #{}), Sender);
                 %% a hack, but if the Receievr name does not point to an account, then 
                 %% we only need to increment the nonce and reduce amount of the sender
             _ -> Receiver
         end,
    if Correct ->
	    SAccount = lists:keyfind(Sender, #account.key, Accounts),
            RAccount = 
                case ReceiverTag of
                    name -> 
                       case lists:keyfind(ReceiverKey, #account.key, Accounts) of
                           false -> #account{key = ReceiverKey, amount = 0, nonce = 1};
                           Acc -> Acc
                       end;
                    new -> #account{key = Receiver, amount = 0, nonce = 1};
                    existing ->
                        lists:keyfind(Receiver, #account.key, Accounts)
                end,
            case Sender == ReceiverKey of
                true -> 
                    S#{accounts =>
                           (Accounts -- [SAccount]) ++
                           [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx),
                                             nonce = maps:get(nonce, Tx) + 1
                                            }]};
                false ->
                    S#{accounts =>
                           (Accounts -- [SAccount, RAccount]) ++
                               [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx),
                                                 nonce = maps:get(nonce, Tx) + 1, 
                                                 names_owned = SAccount#account.names_owned -- [Name]
                                                },
                                RAccount#account{names_owned = 
                                                     (RAccount#account.names_owned -- [Name]) ++ [Name]}],
                       named_accounts => 
                           %% Should this point to the name (and if that name changes go to new account)
                           %% or the resolved key???
                           maps:put(Name, Receiver, maps:get(named_accounts, S, #{}))
                      }
            end;
       not Correct ->
	    S
    end.

ns_transfer_post(_S, [_Env, _Sender, _Receiver, _Name, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
	_ -> not Correct andalso valid_mismatch(Res)
    end.

ns_transfer_features(_S, [_Env, _Sender, _Receiver, _Name, _Tx, Correct], Res) ->
    [{correct, if Correct -> ns_transfer; true -> false end} ] ++
        [{ns_transfer, Res} || is_tuple(Res) andalso element(1, Res) == error].




%% ---------------



%% -- Property ---------------------------------------------------------------
prop_tx_primops() ->
    eqc:dont_print_counterexample(
    in_parallel(
    ?FORALL(Cmds, commands(?MODULE),
    begin
        pong = net_adm:ping(?REMOTE_NODE),

        {H, S, Res} = run_commands(Cmds),
        Height = 
            case maps:get(tx_env, S, undefined) of
                undefined -> 0;
                TxEnv -> aetx_env:height(TxEnv)
            end,
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            features(call_features(H),
            aggregate(call_features(H),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok))))))
    end))).

bugs() -> bugs(10).

bugs(N) -> bugs(N, []).

bugs(Time, Bugs) ->
    more_bugs(eqc:testing_time(Time, prop_tx_primops()), 20, Bugs).



%% --- local helpers ------

correct_height(#{tx_env := TxEnv}, Env) ->
    aetx_env:height(TxEnv) == aetx_env:height(Env).

strict_equal(X, Y) ->
     case X == Y of 
         true -> X; 
         false -> exit({different, X, Y}) 
     end.

hash_equal(X, Y) ->
     case {X, Y} of 
         {{ok, L}, {ok, R}} -> 
             case aec_trees:hash(L) == aec_trees:hash(R) of
                 true -> X;
                 false -> exit({hash_differs, X, Y})
             end;
         {E, E} -> E;
         _ -> exit({different, X, Y}) 
     end.
 
rpc(Module, Fun, Args) ->
    rpc(Module, Fun, Args, fun(X,Y) -> strict_equal(X, Y) end).

rpc(Module, Fun, Args, InterpretResult) ->
    Local = rpc:call(node(), Module, Fun, Args, 1000),
    Remote = rpc:call(?REMOTE_NODE, Module, Fun, Args, 1000),
    eq_rpc(Local, Remote, InterpretResult).

eq_rpc(Local, Remote, InterpretResult) ->
    case {Local, Remote} of
        {{badrpc, {'EXIT', {E1, ST}}},{badrpc, {'EXIT', {E2, _}}}} when E1 == E2 ->
            {'EXIT', {E1, ST}};
        _ ->
            InterpretResult(Local, Remote)
    end.


valid_mismatch({'EXIT',{different, {error, account_nonce_too_low},
                        {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_nonce_too_high},
                         {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_nonce_too_high},
                         {error, multiple_namespaces}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_nonce_too_low},
                         {error, multiple_namespaces}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_not_found},
			 {error, multiple_namespaces}}}) -> true;
valid_mismatch({'EXIT', {different, {error, insufficient_funds},
			 {error, multiple_namespaces}}}) -> true;
valid_mismatch({'EXIT', {different, {error, name_does_not_exist},
                         {error, name_not_found}}}) ->  true;
valid_mismatch({'EXIT', {different, {error, name_does_not_exist},
                         {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, pointer_id_not_found},
                         {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, name_revoked}, 
                         {error, insufficient_funds}}}) -> true;
valid_mismatch(_) -> false.

%% -- Generators -------------------------------------------------------------


gen_account_pubkey(Accounts) ->
    oneof([?LAZY({existing, elements(Accounts)}), 
           ?LAZY({new, #account{key = noshrink(binary(32)), amount = 0, nonce = 0 }})]).

unique_name(List) ->
    ?LET([W], 
         noshrink(?SUCHTHAT([Word], 
                            eqc_erlang_program:words(1), not lists:member(Word, List))), 
         W).

gen_nonce(false) ->
    choose(0,2);  %% account is not present
gen_nonce(Account) when is_record(Account, account) ->
    %% 0 is always wrong, 1 is often too low and 100 is often too high
    frequency([{1, 0}, {1, 1}, {97, Account#account.nonce}, {1, 100}]).

gen_name() ->
    ?LET(NFs, frequency([{1, non_empty(list(elements(?NAMEFRAGS)))}, 
    			 {90, [elements(?NAMEFRAGS)]}]),
    return(iolist_to_binary(lists:join(".", NFs ++ ["test"])))).

gen_name(S) ->
    frequency([{90, elements(maps:keys(maps:get(names, S, #{})) ++ [<<"ta.test">>])},
               {1, gen_name()}]).


