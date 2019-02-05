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
    #{claims => [], preclaims => [], oracles => []}.

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
    true.

precondition_common(_S, _Call) ->
    true.

postcondition_common(S, {call, ?MODULE, Fun, Args}, Res) ->
    Correct = valid_common(Fun, S, Args),
    case Res of
        {error, _} when Correct -> eq(Res, ok);
        {error, _}              -> true;
        ok when Correct         -> true;
        ok                      -> eq(ok, {error, '_'});
        _                       -> not Correct andalso valid_mismatch(Res)
    end.

valid_common(init, _, _)                -> true;
valid_common(mine, _, _)                -> true;
valid_common(spend, S, Args)            -> spend_valid(S, Args);
valid_common(register_oracle, S, Args)  -> register_oracle_valid(S, Args);
valid_common(query_oracle, S, Args)     -> query_oracle_valid(S, Args);
valid_common(response_oracle, S, Args)  -> response_oracle_valid(S, Args);
valid_common(channel_create, S, Args)   -> channel_create_valid(S, Args);
valid_common(channel_deposit, S, Args)  -> channel_deposit_valid(S, Args);
valid_common(channel_withdraw, S, Args) -> channel_withdraw_valid(S, Args);
valid_common(name_preclaim, S, Args)    -> name_preclaim_valid(S, Args);
valid_common(claim, S, Args)            -> claim_valid(S, Args);
valid_common(ns_update, S, Args)        -> ns_update_valid(S, Args);
valid_common(ns_revoke, S, Args)        -> ns_revoke_valid(S, Args);
valid_common(ns_transfer, S, Args)      -> ns_transfer_valid(S, Args).

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
init_pre(S) ->
    not maps:is_key(accounts, S).

init_args(_S) ->
    [0].

init(_Height) ->
    Trees = rpc(aec_trees, new_without_backend, [], fun hash_equal/2),
    EmptyAccountTree = rpc(aec_trees, accounts, [Trees]),
    Account = rpc(aec_accounts, new, [?Patron, 1200000]),
    AccountTree = rpc(aec_accounts_trees, enter, [Account, EmptyAccountTree]),
    InitialTrees = rpc(aec_trees, set_accounts, [Trees, AccountTree], fun hash_equal/2),
    put(trees, InitialTrees),
    InitialTrees,
    ok.

init_next(S, _Value, [Height]) ->
    S#{height => Height,
       accounts => [#account{key = ?Patron, amount = 1200000, nonce = 1}]}.

%% --- Operation: mine ---
mine_pre(S) ->
    maps:is_key(accounts, S).

mine_args(#{height := Height}) ->
    [Height].

mine_pre(#{height := Height}, [H]) ->
    Height == H.

mine_adapt(#{height := Height}, [_]) ->
    [Height];
mine_adapt(_, _) ->
    false.

mine(Height) ->
    Trees = get(trees),
    NewTrees = rpc(aec_trees, perform_pre_transformations, [Trees, Height + 1], fun hash_equal/2),
    put(trees, NewTrees),
    NewTrees,
    ok.

mine_next(#{height := Height} = S, _Value, [_H]) ->
    Payback = [ Query || Query <- maps:get(queries, S, []), Query#query.response_ttl =< Height],
    Accounts = [ case lists:keyfind(Account#account.key, #query.sender, Payback) of
                     false -> Account;
                     Query -> Account#account{amount = Account#account.amount + Query#query.fee}
                 end || Account <- maps:get(accounts, S, [])],
    S#{height => Height + 1,
       accounts => Accounts,
       queries =>  maps:get(queries, S, []) -- Payback
      }.

mine_features(S, [H], _Res) ->
    [mine_response_ttl || [ true || Query <- maps:get(queries, S, []), Query#query.response_ttl =< H ] =/= [] ] ++
        [mine].


%% --- Operation: spend ---
spend_pre(S) ->
    maps:is_key(accounts, S).

spend_args(#{accounts := Accounts, height := Height} = S) ->
    ?LET([{SenderTag, Sender}, {ReceiverTag, Receiver}],
         vector(2, gen_account_pubkey(Accounts)),  %% Add oracle as well! and contract
         ?LET([Amount, Nonce, To], [nat(), gen_nonce(Sender),
                                    oneof([account, {name, elements(maps:keys(maps:get(named_accounts, S, #{})) ++ [<<"ta.test">>])}])],
              %% important: we should never generate ta.test, it is a definitely wrong name
              [Height, {SenderTag, Sender#account.key},
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
                 fee => gen_fee(),
                 nonce => Nonce,
                 payload => utf8()}])).

spend_pre(#{accounts := Accounts} = S, [Height, _Sender, {ReceiverTag, Receiver}, _Tx]) ->
    ReceiverOk =
        case ReceiverTag of
            new -> lists:keyfind(Receiver, #account.key, Accounts) == false;
            existing -> lists:keyfind(Receiver, #account.key, Accounts) =/= false;
            name -> maps:is_key(Receiver, maps:get(named_accounts, S, #{}))
        end,
    ReceiverOk andalso correct_height(S, Height).

spend_valid(S, [Height, {_, Sender}, {ReceiverTag, Receiver}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(amount, Tx) + maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso case ReceiverTag of
               new      -> true;
               existing -> is_account(S, Receiver);
               name     -> is_valid_name(S, Receiver, Height)
                           andalso correct_name_id(Receiver, maps:get(recipient_id, Tx))
            end.

spend_adapt(#{height := Height}, [_, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx]) ->
    [Height, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx];
spend_adapt(_, _) ->
    false.

spend(Height, _Sender, _Receiver, Tx) ->
    apply_transaction(Height, aec_spend_tx, Tx).


spend_next(#{accounts := Accounts} = S, _Value,
           [_Height, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Tx] = Args) ->
    Correct = spend_valid(S, Args),
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

spend_features(S, [_Height, {_, Sender}, {Tag, Receiver}, Tx] = Args, Res) ->
    Correct = spend_valid(S, Args),
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

register_oracle_args(#{accounts := Accounts, height := Height}) ->
     ?LET({SenderTag, Sender}, gen_account_pubkey(lists:keydelete(?Patron, #account.key, Accounts)),
          [Height, {SenderTag, Sender#account.key},
                #{account_id => aec_id:create(account, Sender#account.key),
                  query_format    => <<"send me any string"/utf8>>,
                  response_format => <<"boolean()"/utf8>>,
                  query_fee       => nat(),
                  fee => gen_fee(),
                  nonce => gen_nonce(Sender),
                  oracle_ttl => {delta, 100}}]).

register_oracle_pre(S, [Height, _Sender, _Tx]) ->
    correct_height(S, Height).

register_oracle_valid(S, [_, {_, Sender}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso not is_oracle(S, Sender).

register_oracle_adapt(#{height := Height}, [_, Sender, Tx]) ->
    [Height, Sender, Tx];
register_oracle_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

register_oracle(Height, _Sender, Tx) ->
    apply_transaction(Height, aeo_register_tx, Tx).


register_oracle_next(#{accounts := Accounts} = S, _Value, [_Height, {_, Sender}, Tx] = Args) ->
    Correct = register_oracle_valid(S, Args),
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

register_oracle_features(S, [_Height, {_, _Sender}, Tx] = Args, Res) ->
    Correct = register_oracle_valid(S, Args),
    [{correct, if Correct -> register_oracle; true -> false end} ] ++
        [ {oracle_query_fee, zero} || maps:get(query_fee, Tx) == 0 andalso Correct] ++
        [{register_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: query_oracle ---
query_oracle_pre(S) ->
     maps:is_key(accounts, S).

query_oracle_args(#{accounts := Accounts, height := Height}) ->
     ?LET([{SenderTag, Sender}, {_, Oracle}],
          vector(2, gen_account_pubkey(Accounts)),
               [Height, {SenderTag, Sender#account.key}, Oracle#account.key,
                #{sender_id => aec_id:create(account, Sender#account.key),
                  oracle_id => aec_id:create(oracle, Oracle#account.key),
                  query => oneof([<<"{foo: bar}"/utf8>>, <<"any string"/utf8>>, <<>>]),
                  query_fee => nat(),
                  query_ttl => {delta, 3},
                  response_ttl => {delta, 3},
                  fee => gen_fee(),
                  nonce => gen_nonce(Sender)
                 }]).

query_oracle_pre(S, [Height, _Sender, _Oracle, _Tx]) ->
    correct_height(S, Height).

query_oracle_valid(S, [_Height, {_SenderTag, Sender}, Oracle, Tx]) ->
    is_account(S, Sender)
    andalso is_oracle(S, Oracle)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + maps:get(query_fee, Tx))
    andalso valid_fee(Tx)
    andalso oracle_query_fee(S, Oracle) =< maps:get(query_fee, Tx).

query_oracle_adapt(#{height := Height}, [_Height, Sender, Oracle, Tx]) ->
    [Height, Sender, Oracle, Tx];
query_oracle_adapt(_, _) ->
    false.


query_oracle(Height, _Sender, _Oracle, Tx) ->
    apply_transaction(Height, aeo_query_tx, Tx).

query_oracle_next(#{accounts := Accounts} = S, _Value, [Height, {_, Sender}, Oracle, Tx] = Args) ->
    Correct = query_oracle_valid(S, Args),
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
                           response_ttl = Delta + Height,
                           fee = maps:get(query_fee, Tx)}]};
       not Correct ->
            S
    end.

query_oracle_features(S, [_Height, _, _, Tx] = Args, Res) ->
    Correct = query_oracle_valid(S, Args),
    [{correct, if Correct -> query_oracle; true -> false end} ] ++
             [ {query_query_fee, zero} || maps:get(query_fee, Tx) == 0 andalso Correct] ++
             [ {query_oracle, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [{query_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].

%% --- Operation: response_oracle ---
response_oracle_pre(S) ->
     maps:get(queries, S, []) =/= [].

%% Only responses to existing query tested for the moment, no fault injection
response_oracle_args(#{accounts := Accounts, height := Height} = S) ->
     ?LET({Sender, Nonce, Oracle},
           frequency([{99, ?LET(Query, elements(maps:get(queries, S)), Query#query.id)},
                      {1, {?Patron, 2, ?Patron}}]),
          [Height, {Sender, Nonce, Oracle},
           #{oracle_id => aec_id:create(oracle, Oracle),
             query_id => aeo_query:id(Sender, Nonce, Oracle),
             response => <<"yes, you can">>,
             response_ttl => {delta, 3},
             fee => gen_fee(),
             nonce => case lists:keyfind(Oracle, #account.key, Accounts) of
                          false -> 1;
                          Account -> Account#account.nonce
                      end
            }]).

response_oracle_pre(S, [Height, _QueryId, _Tx]) ->
    correct_height(S, Height).

response_oracle_valid(S, [_Height, {_, _, Oracle} = QueryId, Tx]) ->
    is_account(S, Oracle)
    andalso is_oracle(S, Oracle)
    andalso correct_nonce(S, Oracle, Tx)
    andalso check_balance(S, Oracle,  maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso is_query(S, QueryId).

response_oracle_adapt(#{height := Height}, [_, QueryId, Tx]) ->
    [Height, QueryId, Tx];
response_oracle_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


response_oracle(Height, _QueryId, Tx) ->
    apply_transaction(Height, aeo_response_tx, Tx).

response_oracle_next(#{accounts := Accounts} = S, _Value, [_Height, QueryId, Tx] = Args) ->
    Correct = response_oracle_valid(S, Args),
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

response_oracle_features(S, [_Height, _, _Tx] = Args, Res) ->
    Correct = response_oracle_valid(S, Args),
    [{correct, if Correct -> response_oracle; true -> false end} ] ++
        [{response_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].

%% --- Operation: channel_create ---
channel_create_pre(S) ->
    length(maps:get(accounts, S, [])) > 1.

channel_create_args(#{accounts := Accounts, height := Height}) ->
     ?LET([{_, Initiator}, {_, Responder}],
          vector(2, gen_account_pubkey(Accounts)),
          [Height, Initiator#account.key, Responder#account.key,
                #{initiator_id => aec_id:create(account, Initiator#account.key),
                  responder_id => aec_id:create(account, Responder#account.key),
                  state_hash => <<1:256>>,
                  initiator_amount => nat(),
                  responder_amount => nat(),
                  push_amount => nat(),
                  lock_period => choose(0,2),
                  channel_reserve => choose(0,10),
                  fee => gen_fee(),
                  nonce => gen_nonce(Initiator)}]).

channel_create_pre(S, [Height, Initiator, Responder, _Tx]) ->
    Initiator =/= Responder andalso
    correct_height(S, Height).

channel_create_valid(S, [_Height, Initiator, Responder, Tx]) ->
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso correct_nonce(S, Initiator, Tx)
    andalso check_balance(S, Initiator, maps:get(fee, Tx) + maps:get(initiator_amount, Tx))
    andalso check_balance(S, Responder, maps:get(responder_amount, Tx))
    andalso valid_fee(Tx)
    andalso maps:get(initiator_amount, Tx) >= maps:get(channel_reserve, Tx)
    andalso maps:get(responder_amount, Tx) >= maps:get(channel_reserve, Tx).

channel_create_adapt(#{height := Height}, [_, Initiator, Responder, Tx]) ->
    [Height, Initiator, Responder, Tx];
channel_create_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


channel_create(Height, _Initiator, _Responder, Tx) ->
    apply_transaction(Height, aesc_create_tx, Tx).

channel_create_next(#{accounts := Accounts} = S, _Value, [_Height, Initiator, Responder, Tx] = Args) ->
    Correct = channel_create_valid(S, Args),
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

%% --- Operation: channel_deposit ---
channel_deposit_pre(S) ->
    maps:is_key(channels, S).

channel_deposit_args(#{height := Height} = S) ->
     ?LET([{Initiator, N, Responder}, Party],
          [frequency([{99, ?LET(Channel, elements(maps:get(channels, S)), Channel#channel.id)},
                      {1, {?Patron, 2, ?Patron}}]), elements([initiator, responder])],
          [Height, {Initiator, N, Responder}, Party,
                #{channel_id => aec_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
                  from_id => case Party of
                                 initiator -> aec_id:create(account, Initiator);
                                 responder ->  aec_id:create(account, Responder)
                             end,
                  amount => nat(),
                  round => nat(),
                  fee => gen_fee(),
                  state_hash => <<0:256>>,
                  nonce =>
                      case Party of
                          initiator -> gen_nonce(lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])));
                          responder ->  gen_nonce(lists:keyfind(Responder, #account.key, maps:get(accounts, S, [])))
                      end}]).

channel_deposit_pre(S, [Height, _ChannelId, _Party, _Tx]) ->
    correct_height(S, Height).

channel_deposit_valid(S, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso check_balance(S, From, maps:get(fee, Tx) + maps:get(amount, Tx))
    andalso valid_fee(Tx)
    andalso correct_round(S, ChannelId, Tx).

channel_deposit_adapt(#{height := Height}, [_, ChannelId, Party, Tx]) ->
    [Height, ChannelId, Party, Tx];
channel_deposit_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


channel_deposit(Height, _Channeld, _Party, Tx) ->
    apply_transaction(Height, aesc_deposit_tx, Tx).

channel_deposit_next(#{accounts := Accounts} = S, _Value, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx] = Args) ->
    Correct = channel_deposit_valid(S, Args),
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

channel_deposit_features(S, [_Height, _Channeld, _Party, _Tx] = Args, Res) ->
    Correct = channel_deposit_valid(S, Args),
    [{correct, if Correct -> channel_deposit; true -> false end} ] ++
        [{channel_deposit, Res} || is_tuple(Res) andalso element(1, Res) == error].

%% --- Operation: channel_withdraw ---
channel_withdraw_pre(S) ->
    false andalso maps:is_key(channels, S).


%% We do not yet test wirthdraw by third party!
channel_withdraw_args(#{height := Height} = S) ->
     ?LET([{Initiator, N, Responder}, Party],
          [frequency([{99, ?LET(Channel, elements(maps:get(channels, S)), Channel#channel.id)},
                      {1, {?Patron, 2, ?Patron}}]), elements([initiator, responder])],
          [Height, {Initiator, N, Responder}, Party,
                #{channel_id => aec_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
                  to_id => case Party of
                                 initiator -> aec_id:create(account, Initiator);
                                 responder ->  aec_id:create(account, Responder)
                             end,
                  amount => nat(),
                  round => nat(),
                  fee => gen_fee(),
                  state_hash => <<0:256>>,
                  nonce =>
                      case Party of
                          initiator -> gen_nonce(lists:keyfind(Initiator, #account.key, maps:get(accounts, S, [])));
                          responder ->  gen_nonce(lists:keyfind(Responder, #account.key, maps:get(accounts, S, [])))
                      end}]).

channel_withdraw_pre(S, [Height, _ChannelId, _Party, _Tx]) ->
    correct_height(S, Height).

channel_withdraw_valid(S, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso check_balance(S, From, maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso correct_round(S, ChannelId, Tx)
    andalso (channel(S, ChannelId))#channel.amount >= maps:get(amount, Tx).

channel_withdraw_adapt(#{height := Height} = S, [_, ChannelId, Party, Tx]) ->
    [Height, ChannelId, Party, Tx, channel_withdraw_valid(S, [Height, ChannelId, Party, Tx])];
channel_withdraw_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


channel_withdraw(Height, _Channeld, _Party, Tx) ->
    apply_transaction(Height, aesc_withdraw_tx, Tx).

channel_withdraw_next(#{accounts := Accounts} = S, _Value, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx] = Args) ->
    Correct = channel_withdraw_valid(S, Args),
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

channel_withdraw_features(S, [_Height, _Channeld, _Party, _Tx] = Args, Res) ->
    Correct = channel_withdraw_valid(S, Args),
    [{correct, if Correct -> channel_withdraw; true -> false end} ] ++
    [{channel_withdraw, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: name_preclaim ---

name_preclaim_pre(S) ->
    maps:is_key(accounts, S).

name_preclaim_args(#{accounts := Accounts, height := Height}) ->
     ?LET([{SenderTag, Sender}, Name, Salt],
          [gen_account_pubkey(Accounts), gen_name(), choose(270,280)],
          [Height, {SenderTag, Sender#account.key}, {Name, Salt},
           #{account_id => aec_id:create(account, Sender#account.key),
             fee => gen_fee(),
             commitment_id =>
                 aec_id:create(commitment,
                               aens_hash:commitment_hash(Name, Salt)),
             nonce =>gen_nonce(Sender)}]).

name_preclaim_pre(S, [Height, _Sender, {Name, Salt}, Tx]) ->
    %% Let us not test the unlikely case that someone provides the same name with the same salt
    [present || #preclaim{name = N, salt = St} <- maps:get(preclaims, S, []), N == Name, St == Salt] == []
        andalso aec_id:create(commitment, aens_hash:commitment_hash(Name, Salt)) == maps:get(commitment_id, Tx)
        andalso correct_height(S, Height).

name_preclaim_valid(S, [_Height, {_, Sender}, {_Name, _Salt}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso valid_fee(Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx)).

name_preclaim_adapt(#{height := Height}, [_Height, {SenderTag, Sender}, {Name, Salt}, Tx]) ->
    [Height, {SenderTag, Sender}, {Name, Salt}, Tx];
name_preclaim_adapt(_, _) ->
    false.

name_preclaim(Height, _Sender, {_Name,_Salt}, Tx) ->
    apply_transaction(Height, aens_preclaim_tx, Tx).

name_preclaim_next(#{height := Height,
                     accounts := Accounts,
                     preclaims := Preclaims} = S,
                   _Value, [_Height, {_, Sender}, {Name, Salt}, Tx] = Args) ->
    Correct = name_preclaim_valid(S, Args),
    if Correct ->
            SAccount = lists:keyfind(Sender, #account.key, Accounts),
            S#{accounts =>
                   (Accounts -- [SAccount]) ++
                   [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx),
                                     nonce = maps:get(nonce, Tx) + 1}],
               preclaims =>
                   Preclaims ++ [#preclaim{name = Name,
                                           salt = Salt,
                                           height = Height,
                                           claimer = Sender}]};
       not Correct ->
            S
    end.

name_preclaim_features(#{claims := Claims} = S,
                       [_Height, {_, _Sender}, {Name,_Salt}, _Tx] = Args, Res) ->
    Correct = name_preclaim_valid(S, Args),
    [ {correct, if Correct -> name_preclaim; true -> false end} ] ++
    [ {name_preclaim, Res} || is_tuple(Res) andalso element(1, Res) == error] ++
        [{reclaim_name, Res} || lists:keymember(Name, #claim.name, Claims)].


%% --- Operation: claim ---
claim_pre(S) ->
    maps:is_key(accounts, S).

%% @doc claim_args - Argument generator
-spec claim_args(S :: eqc_statem:symbolic_state()) -> eqc_gen:gen([term()]).
claim_args(#{accounts := Accounts, height := Height}) ->
     ?LET([Name, {SenderTag, Sender}],
          [gen_name(), gen_account_pubkey(Accounts)],
          [Height, {SenderTag, Sender#account.key},
           #{account_id => aec_id:create(account, Sender#account.key),
             name => Name,
             name_salt => choose(270,280),
             fee => gen_fee(),
             nonce => gen_nonce(Sender)}]).


claim_pre(S, [Height, _Sender, _Tx]) ->
    correct_height(S, Height).

claim_valid(S, [Height, {_, Sender}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + aec_governance:name_claim_locked_fee())
    andalso valid_fee(Tx)
    andalso is_valid_preclaim(S, Tx, Sender, Height).

is_valid_preclaim(S = #{preclaims := Ps}, Tx = #{name := Name, name_salt := Salt}, Claimer, Height) ->
    case [ PC || PC = #preclaim{name = N, salt = Sa, claimer = C} <- Ps,
                 Name == N, Salt == Sa, Claimer == C ] of
        [] -> false;
        [#preclaim{ height = H }] ->
            H + aec_governance:name_claim_preclaim_delta() =< Height
            andalso Height < H +  aec_governance:name_preclaim_expiration()
            andalso valid_name(Tx)
            andalso not is_claimed(S, Name)
    end.

% names may not have dots in between, only at the end (.test)
valid_name(Tx) ->
    case string:lexemes(maps:get(name,Tx), ".") of
        [_, <<"test">>] -> true;
        _ -> false
    end.

claim_adapt(#{height := Height}, [_Height, {SenderTag, Sender}, Tx]) ->
    [Height, {SenderTag, Sender}, Tx];
claim_adapt(_, _) ->
    false.


claim(Height, _Sender, Tx) ->
    apply_transaction(Height, aens_claim_tx, Tx).

claim_next(#{height := Height,
             accounts := Accounts,
             claims := Claims} = S,
           _Value, [_Height, {_, Sender}, Tx] = Args) ->
    Correct = claim_valid(S, Args),
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
                                     height = Height,
                                     valid_height = -1,
                                     claimer = Sender}]};
       not Correct ->
            S
    end.

claim_features(S, [_Height, {_, _Sender}, _Tx] = Args, Res) ->
    Correct = claim_valid(S, Args),
    [{correct, if Correct -> ns_claim; true -> false end} ] ++
        [{ns_claim, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: claim_update ---
ns_update_pre(S) ->
    maps:is_key(accounts, S).

ns_update_args(#{accounts := Accounts, height := Height} = S) ->
     ?LET([Name, {SenderTag, Sender}, {Tag, NameAccount}],
          [gen_name(S), gen_account_pubkey(Accounts), gen_account_pubkey(Accounts)],
          [Height, Name, {SenderTag, Sender#account.key}, {Tag, NameAccount#account.key},
           #{account_id => aec_id:create(account, Sender#account.key),
             name_id => aec_id:create(name, aens_hash:name_hash(Name)),
             name_ttl => nat(),
             client_ttl => nat(),
             fee => gen_fee(),
             nonce => gen_nonce(Sender),
             pointers =>
                 oneof([[],
                        [aens_pointer:new(<<"account_pubkey">>, aec_id:create(account, NameAccount#account.key))]
                        ])}]).

ns_update_pre(S, [Height, Name, _Sender, _NameAccount, Tx]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height).

ns_update_valid(S, [Height, Name, {_, Sender}, _, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + aec_governance:name_claim_locked_fee())
    andalso valid_fee(Tx)
    andalso owns_name(S, Sender, Name)
    andalso is_valid_name(S, Name, Height).

ns_update_adapt(#{height := Height}, [_Height, Name, {SenderTag, Sender}, NameAccount, Tx]) ->
    [Height, Name, {SenderTag, Sender}, NameAccount, Tx];
ns_update_adapt(_, _) ->
    false.

ns_update(Height, _Name, _Sender, _NameAccount, Tx) ->
    apply_transaction(Height, aens_update_tx, Tx).

ns_update_next(#{accounts := Accounts} = S, _Value, [Height, Name, {_, Sender}, {_, NameAccount}, Tx] = Args) ->
    Correct = ns_update_valid(S, Args),
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
                   [Claim#claim{update_height = Height,
                                valid_height = max(Claim#claim.valid_height,
                                                   Height + maps:get(name_ttl, Tx))}]
              };
       not Correct ->
            S
    end.

ns_update_features(S, [_Height, _Name, _Sender, {Tag, _NameAccount}, _Tx] = Args, Res) ->
    Correct = ns_update_valid(S, Args),
    [{correct, if Correct -> ns_update; true -> false end} ] ++
        [{ns_update, Tag} ] ++
        [{ns_update, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: ns_revoke ---
ns_revoke_pre(S) ->
    maps:is_key(accounts, S).

ns_revoke_args(#{accounts := Accounts, height := Height} = S) ->
     ?LET([Name, {SenderTag, Sender}],
          [gen_name(S), gen_account_pubkey(Accounts)],
          [Height, {SenderTag, Sender#account.key}, Name,
           #{account_id => aec_id:create(account, Sender#account.key),
             name_id => aec_id:create(name, aens_hash:name_hash(Name)),
             fee => gen_fee(),
             nonce => gen_nonce(Sender)
            }]).

ns_revoke_pre(S, [Height, _Sender, Name, Tx]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height).

ns_revoke_valid(S, [_Height, {_SenderTag, Sender}, Name, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso owns_name(S, Sender, Name).

ns_revoke_adapt(#{height := Height}, [_Height, {SenderTag, Sender}, Name, Tx]) ->
    [Height, {SenderTag, Sender}, Name, Tx];
ns_revoke_adapt(_, _) ->
    false.

ns_revoke(Height, _Sender, _Name, Tx) ->
    apply_transaction(Height, aens_revoke_tx, Tx).

ns_revoke_next(#{accounts := Accounts} = S, _Value, [Height, {_SenderTag, Sender}, Name, Tx] = Args) ->
    Correct = ns_revoke_valid(S, Args),
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
                                revoke_height = aec_governance:name_protection_period() + Height}
                     || Claim#claim.revoke_height == undefined ]
              };
       not Correct ->
            S
    end.

ns_revoke_features(S, [_Height, _Sender, _Name, _Tx] = Args, Res) ->
    Correct = ns_revoke_valid(S, Args),
    [{correct, if Correct -> ns_revoke; true -> false end} ] ++
        [{ns_revoke, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: ns_transfer ---
ns_transfer_pre(S) ->
    maps:is_key(accounts, S).

ns_transfer_args(#{accounts := Accounts, height := Height} = S) ->
    ?LET([{SenderTag, Sender}, {ReceiverTag, Receiver}],
         vector(2, gen_account_pubkey(Accounts)),
         ?LET([Name, To], [gen_name(S),
                           oneof([account, {name, elements(maps:keys(maps:get(named_accounts, S, #{})) ++
                                                               [<<"ta.test">>])}])],
              [Height, {SenderTag, Sender#account.key},
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
                 fee => gen_fee(),
                 nonce => gen_nonce(Sender)
                }])).

ns_transfer_pre(S, [Height, _Sender, _Receiver, Name, Tx]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height).

ns_transfer_valid(S, [Height, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Name, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso owns_name(S, Sender, Name)
    andalso case ReceiverTag of
               new      -> true;
               existing -> is_account(S, Receiver);
               name     -> is_valid_name(S, Receiver, Height)
            end.

ns_transfer_adapt(#{height := Height}, [_Height, Sender, Receiver, Name, Tx]) ->
    [Height, Sender, Receiver, Name, Tx];
ns_transfer_adapt(_, _) ->
    false.

ns_transfer(Height, _Sender, _Receiver, _Name, Tx) ->
    apply_transaction(Height, aens_transfer_tx, Tx).

%% Assumption the recipient does not need to exist, it is created when we provided
%% it with a name
ns_transfer_next(#{accounts := Accounts} = S, _Value,
                 [_Height, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Name, Tx] = Args) ->
    Correct = ns_transfer_valid(S, Args),
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

ns_transfer_features(S, [_Height, _Sender, _Receiver, _Name, _Tx] = Args, Res) ->
    Correct = ns_transfer_valid(S, Args),
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
        Height = maps:get(height, S, 0),
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
is_valid_name(#{claims := Names}, Name, Height) ->
    case lists:keyfind(Name, #claim.name, Names) of
        false -> false;
        Claim -> Claim#claim.revoke_height == undefined
                 andalso Claim#claim.valid_height >= Height
    end.

owns_name(#{claims := Names}, Who, Name) ->
    case lists:keyfind(Name, #claim.name, Names) of
        false -> false;
        Claim -> Claim#claim.claimer == Who
                 andalso Claim#claim.revoke_height == undefined
    end.

correct_name_id(Name, NameId) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == NameId.

is_account(#{accounts := Accounts}, Key) ->
    lists:keymember(Key, #account.key, Accounts).

is_oracle(#{oracles := Oracles}, Oracle) ->
    lists:keymember(Oracle, 1, Oracles).

oracle_query_fee(#{oracles := Oracles}, Oracle) ->
    {_, QFee} = lists:keyfind(Oracle, 1, Oracles),
    QFee.

is_query(#{queries := Qs}, Q) ->
    lists:keymember(Q, #query.id, Qs).

valid_fee(#{ fee := Fee }) ->
    Fee >= 20000.   %% not precise, but we don't generate fees in the shady range

correct_nonce(S, Key, #{nonce := Nonce}) ->
    (account(S, Key))#account.nonce == Nonce.

check_balance(S, Key, Amount) ->
     (account(S, Key))#account.amount >= Amount.

account(#{accounts := Accounts}, Key) ->
    lists:keyfind(Key, #account.key, Accounts).

is_channel(S, CId) ->
    channel(S, CId) /= false.

channel(#{channels := Cs}, CId) ->
    lists:keyfind(CId, #channel.id, Cs).

correct_round(S, CId, #{round := Round}) ->
    (channel(S, CId))#channel.round < Round.

is_claimed(#{claims := Cs}, Name) ->
    lists:keymember(Name, #claim.name, Cs).


correct_height(#{height := Height0}, Height1) ->
    Height0 == Height1.

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

eq_rpc(Local, Remote) ->
    eq_rpc(Local, Remote, fun hash_equal/2).

eq_rpc(Local, Remote, InterpretResult) ->
    case {Local, Remote} of
        {{badrpc, {'EXIT', {E1, ST}}},{badrpc, {'EXIT', {E2, _}}}} when E1 == E2 ->
            {'EXIT', {E1, ST}};
        _ ->
            InterpretResult(Local, Remote)
    end.

apply_transaction(Height, TxMod, TxArgs) ->
    Env   = aetx_env:tx_env(Height),
    Trees = get(trees),
    {ok, Tx} = rpc(TxMod, new, [TxArgs]),

    Remote = case rpc:call(?REMOTE_NODE, aetx, check, [Tx, Trees, Env], 1000) of
                {ok, RemoteTrees} -> rpc:call(node(), aetx, process, [Tx, RemoteTrees, Env], 1000);
                RemoteErr         -> RemoteErr
            end,
    Local = rpc:call(node(), aetx, process, [Tx, Trees, Env], 1000),

    case eq_rpc(Local, Remote) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
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

gen_fee() ->
    weighted_default({9, choose(20000, 50000)},
                     {1, choose(0, 15000)}).    %% too low

