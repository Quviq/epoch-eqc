%%% @author Thomas Arts
%%% @doc
%%%
%%%       TODO:
%%%          - better shrinking for channel Ids (they contain the nonce...) - use good/bad tagging?
%%%          - add oracle names to the state such that we can use names with oracles
%%%          - add names to oracle txs
%%%          - add contract txs (quite a lot of work, I fear)
%%%          - tune distribution (all EXIT differences should show up in features)
%%%          - mock aec_governance values to test for name revoke re-use etc.
%%% @end
%%% Created : 23 Jan 2019 by Thomas Arts

-module(txs_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).
-define(Patron, <<1, 1, 0:240>>).
-define(PatronAmount, 120000000).
-define(NAMEFRAGS, ["foo", "bar", "baz"]).

-record(account, {key, amount, nonce, names_owned = []}).
-record(preclaim,{name, salt, height, claimer}).
-record(claim,{name, height, update_height, valid_height, revoke_height, claimer}).
-record(query, {sender, id, fee, response_ttl}).
-record(channel, {id, round = 1, amount = 0, reserve = 0}).

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{claims => [], preclaims => [], oracles => [], fees => []}.

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
        ok                      -> eq(ok, {error, '_'})
    end.

valid_common(init, _, _)                    -> true;
valid_common(mine, _, _)                    -> true;
valid_common(multi_mine, _, _)              -> true;
valid_common(spend, S, Args)                -> spend_valid(S, Args);
valid_common(register_oracle, S, Args)      -> register_oracle_valid(S, Args);
valid_common(extend_oracle, S, Args)        -> extend_oracle_valid(S, Args);
valid_common(query_oracle, S, Args)         -> query_oracle_valid(S, Args);
valid_common(response_oracle, S, Args)      -> response_oracle_valid(S, Args);
valid_common(channel_create, S, Args)       -> channel_create_valid(S, Args);
valid_common(channel_deposit, S, Args)      -> channel_deposit_valid(S, Args);
valid_common(channel_withdraw, S, Args)     -> channel_withdraw_valid(S, Args);
valid_common(channel_close_mutual, S, Args) -> channel_close_mutual_valid(S, Args);
valid_common(ns_preclaim, S, Args)          -> ns_preclaim_valid(S, Args);
valid_common(ns_claim, S, Args)             -> ns_claim_valid(S, Args);
valid_common(ns_update, S, Args)            -> ns_update_valid(S, Args);
valid_common(ns_revoke, S, Args)            -> ns_revoke_valid(S, Args);
valid_common(ns_transfer, S, Args)          -> ns_transfer_valid(S, Args).

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
init_pre(S) ->
    not maps:is_key(accounts, S).

init_args(_S) ->
    [0].

init(_Height) ->
    Trees         = aec_trees:new_without_backend(),
    AccountTrees  = aec_trees:accounts(Trees),
    PatronAccount = aec_accounts:new(?Patron, ?PatronAmount),
    AccountTrees1 = aec_accounts_trees:enter(PatronAccount, AccountTrees),
    Trees1        = aec_trees:set_accounts(Trees, AccountTrees1),
    put(trees, Trees1),
    ok.

init_next(S, _Value, [Height]) ->
    S#{height   => Height,
       accounts => [#account{key = ?Patron, amount = ?PatronAmount, nonce = 1}]}.

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
    Trees  = get(trees),
    Trees1 = aec_trees:perform_pre_transformations(Trees, Height + 1),
    put(trees, Trees1),
    ok.

%% In this model we do not pay beneficiaries (that's on a higher level)
%% Thus no update needed when we reach aec_governance:beneficiary_reward_delay()
mine_next(#{height := Height, accounts := Accounts} = S, _Value, [_H]) ->
    ExpiredQs = expired_queries(S, Height),
    Accounts1 = lists:foldl(
        fun(Q, As) -> case lists:keyfind(Q#query.sender, #account.key, As) of
                        false -> As;
                        A     -> lists:keyreplace(A#account.key, #account.key, As,
                                                  A#account{ amount = A#account.amount + Q#query.fee })
                      end
        end, Accounts, ExpiredQs),
    S#{height   => Height + 1,
       accounts => Accounts1,
       queries  => maps:get(queries, S, []) -- ExpiredQs
      }.

mine_features(S, [H], _Res) ->
    [mine_response_ttl || expired_queries(S, H) =/= [] ] ++
    [mine].

expired_queries(S, Height) ->
    [ Q || Q <- maps:get(queries, S, []), Q#query.response_ttl =< Height ].

%% --- Operation: multi_mine ---
multi_mine_pre(S) ->
    maps:is_key(accounts, S).

multi_mine_args(#{height := Height}) ->
    [Height, elements([10, 100, 1000, 10000])].

multi_mine_pre(#{height := Height}, [H, _]) ->
    Height == H.

multi_mine_adapt(#{height := Height}, [_, Blocks]) ->
    [Height, Blocks];
multi_mine_adapt(_, _) ->
    false.

multi_mine(Height, Blocks) ->
    Trees  = get(trees),
    Trees1 = lists:foldl(
        fun(H, T) -> aec_trees:perform_pre_transformations(T, H + 1) end,
        Trees, lists:seq(Height, Height + Blocks - 1)),

    put(trees, Trees1),
    ok.

multi_mine_next(#{height := Height, accounts := Accounts} = S, _Value, [_H, Blocks]) ->
    ExpiredQs = expired_queries(S, Height + Blocks - 1),
    Accounts1 = lists:foldl(
        fun(Q, As) -> case lists:keyfind(Q#query.sender, #account.key, As) of
                        false -> As;
                        A     -> lists:keyreplace(A#account.key, #account.key, As,
                                                  A#account{ amount = A#account.amount + Q#query.fee })
                      end
        end, Accounts, ExpiredQs),
    S#{height   => Height + Blocks,
       accounts => Accounts1,
       queries  => maps:get(queries, S, []) -- ExpiredQs
      }.

multi_mine_features(_S, [_, _], _Res) ->
    [multi_mine].


%% --- Operation: spend ---
spend_pre(S) ->
    maps:is_key(accounts, S).

spend_args(#{accounts := Accounts, height := Height} = S) ->
    ?LET({{SenderTag, Sender}, {ReceiverTag, Receiver}},
         {gen_account(1, 49, Accounts), gen_account(2, 1, Accounts)},
         ?LET([Amount, Nonce, To], [gen_spend_amount(Sender), gen_nonce(Sender),
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

spend_pre(#{accounts := Accounts} = S, [Height, {_, Sender}, {RTag, Receiver}, Tx]) ->
    ReceiverOk =
        case RTag of
            new      -> lists:keyfind(Receiver, #account.key, Accounts) == false;
            existing -> lists:keyfind(Receiver, #account.key, Accounts) =/= false;
            name     -> maps:is_key(Receiver, maps:get(named_accounts, S, #{}))
        end,
    ReceiverOk andalso correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

spend_valid(S, [Height, {_, Sender}, {ReceiverTag, Receiver}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(amount, Tx) + maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso case ReceiverTag of
               new      -> true;
               existing -> is_account(S, Receiver);
               name     -> is_valid_name_account(S, Receiver, Height)
                           andalso correct_name_id(Receiver, maps:get(recipient_id, Tx))
            end.

spend_adapt(#{height := Height} = S, [_, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx]) ->
    [Height, {SenderTag, Sender}, {ReceiverTag, Receiver}, adapt_nonce(S, Sender, Tx)];
spend_adapt(_, _) ->
    false.

spend(Height, _Sender, _Receiver, Tx) ->
    apply_transaction(Height, aec_spend_tx, Tx).


spend_next(S, _Value, [_Height, {_SenderTag, Sender}, Receiver, Tx] = Args) ->
    case spend_valid(S, Args) of
        false -> S;
        true  ->
            #{ amount := Amount, fee := Fee } = Tx,
            RKey = resolve_account(S, Receiver),
            reserve_fee(Fee,
            bump_and_charge(Sender, Amount + Fee,
                credit(RKey, Amount, S)))
    end.

spend_features(S, [_Height, {_, _Sender}, {_Tag, _Receiver}, _Tx] = Args, Res) ->
    Correct = spend_valid(S, Args),
    [%{spend, {accounts, length(maps:get(accounts, S))}},
     {correct,  if Correct -> spend; true -> false end}] ++
        %% [ {spend, to_self} || Sender == Receiver andalso Correct] ++
        %% [ {spend, zero} || maps:get(amount, Tx) == 0 andalso Correct] ++
        %% [ {spend, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        %% [ {spend, to_name} || Tag == name ] ++
        %% [ {spend, Res} || is_tuple(Res) andalso element(1, Res) == error].
        [{spend, Res}].


%% --- Operation: register_oracle ---
register_oracle_pre(S) ->
    length(maps:get(accounts, S, [])) > 1.

register_oracle_args(S = #{height := Height}) ->
     ?LET({SenderTag, Sender}, gen_new_oracle_account(S),
          [Height, {SenderTag, Sender#account.key},
                #{account_id => aec_id:create(account, Sender#account.key),
                  query_format    => <<"send me any string"/utf8>>,
                  response_format => <<"boolean()"/utf8>>,
                  query_fee       => gen_query_fee(),
                  fee => gen_fee(),
                  nonce => gen_nonce(Sender),
                  oracle_ttl => {delta, 100},
                  abi_version => 0}]).

register_oracle_pre(S, [Height, {_, Sender}, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

register_oracle_valid(S, [_, {_, Sender}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso not is_oracle(S, Sender).

register_oracle_adapt(#{height := Height} = S, [_, {STag, Sender}, Tx]) ->
    [Height, {STag, Sender}, adapt_nonce(S, Sender, Tx)];
register_oracle_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

register_oracle(Height, _Sender, Tx) ->
    apply_transaction(Height, aeo_register_tx, Tx).


register_oracle_next(S, _Value, [_Height, {_, Sender}, Tx] = Args) ->
    case register_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, query_fee := QFee } = Tx,
            Oracle = {Sender, QFee},
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                add(oracles, Oracle, S)))
    end.

register_oracle_features(S, [_Height, {_, _Sender}, _Tx] = Args, Res) ->
    Correct = register_oracle_valid(S, Args),
    [{correct, if Correct -> register_oracle; true -> false end},
     {register_oracle, Res}].

%% --- Operation: extend_oracle ---
extend_oracle_pre(S) ->
    maps:is_key(accounts, S) andalso maps:get(oracles, S, []) /= [].

extend_oracle_args(S = #{height := Height}) ->
    ?LET({{_, Oracle}, DeltaTTL},
         {gen_oracle_account(S), gen_ttl()},
         [Height, Oracle#account.key,
          #{oracle_id  => aec_id:create(oracle, Oracle#account.key),
            nonce      => gen_nonce(Oracle),
            oracle_ttl => {delta, DeltaTTL},
            fee        => gen_fee()
           }]).

extend_oracle_pre(S, [Height, Oracle, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Oracle, Tx).

extend_oracle_valid(S, [_Height, Oracle, Tx]) ->
    is_account(S, Oracle)
    andalso is_oracle(S, Oracle)
    andalso correct_nonce(S, Oracle, Tx)
    andalso check_balance(S, Oracle, maps:get(fee, Tx))
    andalso valid_fee(Tx).

extend_oracle_adapt(#{height := Height} = S, [_Height, Oracle, Tx]) ->
    [Height, Oracle, adapt_nonce(S, Oracle, Tx)];
extend_oracle_adapt(_, _) ->
    false.

extend_oracle(Height, _Oracle, Tx) ->
    apply_transaction(Height, aeo_extend_tx, Tx).

extend_oracle_next(S, _Value, [_Height, Oracle, Tx] = Args) ->
    case extend_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ oracle_ttl := {delta, _Delta}, fee := Fee} = Tx,
            reserve_fee(Fee,
            bump_and_charge(Oracle, Fee, S))
    end.

extend_oracle_features(S, [_Height, _, _Tx] = Args, Res) ->
    Correct = extend_oracle_valid(S, Args),
    [{correct, if Correct -> extend_oracle; true -> false end},
     {extend_oracle, Res}].

%% --- Operation: query_oracle ---
query_oracle_pre(S) ->
     maps:is_key(accounts, S).

query_oracle_args(S = #{accounts := Accounts, height := Height}) ->
     ?LET({{SenderTag, Sender}, {_, Oracle}},
          {gen_account(1, 49, Accounts), gen_oracle_account(S)},
          begin
              QFee = case oracle(S, Oracle#account.key) of
                       false -> 100;
                       {_, QFee0} -> QFee0
                     end,
              [Height, {SenderTag, Sender#account.key}, Oracle#account.key,
               #{sender_id => aec_id:create(account, Sender#account.key),
                 oracle_id => aec_id:create(oracle, Oracle#account.key),
                 query => oneof([<<"{foo: bar}"/utf8>>, <<"any string"/utf8>>, <<>>]),
                 query_fee => gen_query_fee(QFee),
                 query_ttl => {delta, 3},
                 response_ttl => {delta, 3},
                 fee => gen_fee(),
                 nonce => gen_nonce(Sender)
                }]
          end).

query_oracle_pre(S, [Height, {_, Sender}, _Oracle, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

query_oracle_valid(S, [_Height, {_SenderTag, Sender}, Oracle, Tx]) ->
    is_account(S, Sender)
    andalso is_oracle(S, Oracle)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + maps:get(query_fee, Tx))
    andalso valid_fee(Tx)
    andalso oracle_query_fee(S, Oracle) =< maps:get(query_fee, Tx).

query_oracle_adapt(#{height := Height} = S, [_Height, {STag, Sender}, Oracle, Tx]) ->
    [Height, {STag, Sender}, Oracle, adapt_nonce(S, Sender, Tx)];
query_oracle_adapt(_, _) ->
    false.


query_oracle(Height, _Sender, _Oracle, Tx) ->
    apply_transaction(Height, aeo_query_tx, Tx).

query_oracle_next(S, _Value, [Height, {_, Sender}, Oracle, Tx] = Args) ->
    case query_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ response_ttl := {delta, Delta}, fee := Fee, query_fee := QFee } = Tx,
            Query = #query{sender       = Sender,
                           id           = {Sender, maps:get(nonce, untag_nonce(Tx)), Oracle},
                           response_ttl = Delta + Height,
                           fee          = maps:get(query_fee, Tx)},
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee + QFee,
                add(queries, Query, S)))
    end.

query_oracle_features(S, [_Height, _, _, _Tx] = Args, Res) ->
    Correct = query_oracle_valid(S, Args),
    [{correct, if Correct -> query_oracle; true -> false end},
     {query_oracle, Res}].

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
                          false -> {bad, 1};
                          Account -> {good, Account#account.nonce}
                      end
            }]).

response_oracle_pre(S, [Height, {_, _, Q}, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Q, Tx).

response_oracle_valid(S, [_Height, {_, _, Oracle} = QueryId, Tx]) ->
    is_account(S, Oracle)
    andalso is_oracle(S, Oracle)
    andalso correct_nonce(S, Oracle, Tx)
    andalso check_balance(S, Oracle,  maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso is_query(S, QueryId).

response_oracle_adapt(#{height := Height} = S, [_, QueryId = {_, _, Q}, Tx]) ->
    [Height, QueryId, adapt_nonce(S, Q, Tx)];
response_oracle_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


response_oracle(Height, _QueryId, Tx) ->
    apply_transaction(Height, aeo_response_tx, Tx).

response_oracle_next(S, _Value, [_Height, QueryId, Tx] = Args) ->
    case response_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee } = Tx,
            {_, _, Oracle} = QueryId,
            #query{ fee = QueryFee } = get_query(S, QueryId),
            reserve_fee(Fee,
            bump_and_charge(Oracle, Fee - QueryFee,
                remove_query(QueryId, S)))
    end.

response_oracle_features(S, [_Height, _, _Tx] = Args, Res) ->
    Correct = response_oracle_valid(S, Args),
    [{correct, if Correct -> response_oracle; true -> false end},
     {response_oracle, Res}].

%% --- Operation: channel_create ---
channel_create_pre(S) ->
    length(maps:get(accounts, S, [])) > 1.

channel_create_args(#{accounts := Accounts, height := Height}) ->
     ?LET([{_, Initiator}, {_, Responder}],
          vector(2, gen_account(1, 49, Accounts)),
     ?LET({IAmount, RAmount, ChannelReserve}, gen_create_channel_amounts(),
          [Height, Initiator#account.key, Responder#account.key,
                #{initiator_id => aec_id:create(account, Initiator#account.key),
                  responder_id => aec_id:create(account, Responder#account.key),
                  state_hash => <<1:256>>,
                  initiator_amount => IAmount,
                  responder_amount => RAmount,
                  lock_period => choose(0,2),
                  channel_reserve => ChannelReserve,
                  fee => gen_fee(),
                  nonce => gen_nonce(Initiator)}])).

channel_create_pre(S, [Height, Initiator, Responder, Tx]) ->
    Initiator =/= Responder
    andalso correct_height(S, Height) andalso valid_nonce(S, Initiator, Tx).

channel_create_valid(S, [_Height, Initiator, Responder, Tx]) ->
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso correct_nonce(S, Initiator, Tx)
    andalso check_balance(S, Initiator, maps:get(fee, Tx) + maps:get(initiator_amount, Tx))
    andalso check_balance(S, Responder, maps:get(responder_amount, Tx))
    andalso valid_fee(Tx)
    andalso maps:get(initiator_amount, Tx) >= maps:get(channel_reserve, Tx)
    andalso maps:get(responder_amount, Tx) >= maps:get(channel_reserve, Tx).

channel_create_adapt(#{height := Height} = S, [_, Initiator, Responder, Tx]) ->
    [Height, Initiator, Responder, adapt_nonce(S, Initiator, Tx)];
channel_create_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


channel_create(Height, _Initiator, _Responder, Tx) ->
    apply_transaction(Height, aesc_create_tx, Tx).

channel_create_next(S, _Value, [_Height, Initiator, Responder, Tx] = Args) ->
    case channel_create_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee              := Fee,
               nonce            := {_, Nonce},
               initiator_amount := IAmount,
               responder_amount := RAmount,
               channel_reserve  := Reserve } = Tx,
            Channel = #channel{ id = {Initiator, Nonce, Responder},
                                amount = IAmount + RAmount,
                                reserve = Reserve },
            reserve_fee(Fee,
            bump_and_charge(Initiator, Fee + IAmount,
                charge(Responder, RAmount,
                add(channels, Channel, S))))
    end.

channel_create_features(S, [_Height, _, _, _Tx] = Args, Res) ->
    Correct = channel_create_valid(S, Args),
    [{correct, if Correct -> channel_create; true -> false end},
     {channel_create, Res}].

%% --- Operation: channel_deposit ---
channel_deposit_pre(S) ->
    maps:is_key(channels, S).


channel_deposit_args(#{height := Height} = S) ->
     ?LET({CId = {Initiator, N, Responder}, Party},
          {gen_state_channel_id(S), gen_party()},
     begin
          From = case Party of initiator -> Initiator; responder -> Responder end,
          [Height, {Initiator, N, Responder}, Party,
                #{channel_id => aec_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
                  from_id => aec_id:create(account, From),
                  amount => gen_channel_amount(),
                  round => gen_channel_round(S, CId),
                  fee => gen_fee(),
                  state_hash => <<0:256>>,
                  nonce => gen_nonce(account(S, From))
                 }]
     end).

channel_deposit_pre(S, [Height, {I, _, R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    correct_height(S, Height) andalso valid_nonce(S, From, Tx).

channel_deposit_valid(S, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso check_balance(S, From, maps:get(fee, Tx) + maps:get(amount, Tx))
    andalso valid_fee(Tx)
    andalso correct_round(S, ChannelId, Tx).

channel_deposit_adapt(#{height := Height} = S, [_, ChannelId = {I, _, R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    [Height, ChannelId, Party, adapt_nonce(S, From, Tx)];
channel_deposit_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


channel_deposit(Height, _Channeld, _Party, Tx) ->
    apply_transaction(Height, aesc_deposit_tx, Tx).

channel_deposit_next(S, _Value, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx] = Args) ->
    case channel_deposit_valid(S, Args) of
        false -> S;
        true  ->
            From = case Party of
                     initiator -> Initiator;
                     responder -> Responder
                   end,
            #{ fee    := Fee,
               amount := Amount,
               round  := Round } = Tx,
            reserve_fee(Fee,
            bump_and_charge(From, Fee + Amount,
                credit_channel(ChannelId, Round, Amount, S)))
    end.

channel_deposit_features(S, [_Height, _Channeld, _Party, _Tx] = Args, Res) ->
    Correct = channel_deposit_valid(S, Args),
    [{correct, if Correct -> channel_deposit; true -> false end},
     {channel_deposit, Res}].

%% --- Operation: channel_withdraw ---
channel_withdraw_pre(S) ->
    maps:is_key(channels, S).

%% We do not yet test wirthdraw by third party!
channel_withdraw_args(#{height := Height} = S) ->
    ?LET({CId = {Initiator, N, Responder}, Party},
         {gen_state_channel_id(S), gen_party()},
    begin
         From = case Party of initiator -> Initiator; responder -> Responder end,
         [Height, {Initiator, N, Responder}, Party,
               #{channel_id => aec_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
                 to_id => aec_id:create(account, From),
                 amount => gen_channel_amount(),
                 round => gen_channel_round(S, CId),
                 fee => gen_fee(),
                 state_hash => <<0:256>>,
                 nonce => gen_nonce(account(S, From))
                }]
    end).

channel_withdraw_pre(S, [Height, {I, _, R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    correct_height(S, Height) andalso valid_nonce(S, From, Tx).

channel_withdraw_valid(S, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso check_balance(S, From, maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso correct_round(S, ChannelId, Tx)
    andalso (channel(S, ChannelId))#channel.amount >= maps:get(amount, Tx)
    andalso (channel(S, ChannelId))#channel.amount - maps:get(amount, Tx) >= (channel(S, ChannelId))#channel.reserve*2.

channel_withdraw_adapt(#{height := Height} = S, [_, ChannelId = {I, _ ,R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    [Height, ChannelId, Party, adapt_nonce(S, From, Tx)];
channel_withdraw_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

channel_withdraw(Height, _Channeld, _Party, Tx) ->
    apply_transaction(Height, aesc_withdraw_tx, Tx).

channel_withdraw_next(S, _Value, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx] = Args) ->
    case channel_withdraw_valid(S, Args) of
        false -> S;
        true  ->
            From = case Party of
                     initiator -> Initiator;
                     responder -> Responder
                   end,
            #{ fee    := Fee,
               amount := Amount,
               round  := Round } = Tx,
            reserve_fee(Fee,
            bump_and_charge(From, Fee - Amount,
                credit_channel(ChannelId, Round, -Amount, S)))
    end.

channel_withdraw_features(S, [_Height, _Channeld, _Party, _Tx] = Args, Res) ->
    Correct = channel_withdraw_valid(S, Args),
    [{correct, if Correct -> channel_withdraw; true -> false end},
     {channel_withdraw, Res}].

%% --- Operation: channel_close_mutual ---
channel_close_mutual_pre(S) ->
    maps:is_key(channels, S).

channel_close_mutual_args(#{height := Height} = S) ->
    ?LET({CId = {Initiator, N, Responder}, Party},
         {gen_state_channel_id(S), gen_party()},
    ?LET({IFinal, RFinal, Fee}, gen_close_channel_amounts(S, CId),
    begin
         From = case Party of initiator -> Initiator; responder -> Responder end,
         [Height, {Initiator, N, Responder}, Party,
               #{channel_id => aec_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
                 from_id => aec_id:create(account, From),
                 initiator_amount_final => IFinal,
                 responder_amount_final => RFinal,
                 %% round => gen_channel_round(S, CId),
                 fee => Fee,
                 nonce => gen_nonce(account(S, From))
                }]
    end)).

channel_close_mutual_pre(S, [Height, {I, _, R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    correct_height(S, Height) andalso valid_nonce(S, From, Tx).

channel_close_mutual_valid(S, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso valid_fee(Tx)
    andalso (channel(S, ChannelId))#channel.amount >=
                maps:get(initiator_amount_final, Tx) + maps:get(responder_amount_final, Tx) + maps:get(fee, Tx).

channel_close_mutual_adapt(#{height := Height} = S, [_, ChannelId = {I, _ ,R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    [Height, ChannelId, Party, adapt_nonce(S, From, Tx)];
channel_close_mutual_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

channel_close_mutual(Height, _Channeld, _Party, Tx) ->
    apply_transaction(Height, aesc_close_mutual_tx, Tx).

channel_close_mutual_next(S, _Value, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx] = Args) ->
    case channel_close_mutual_valid(S, Args) of
        false -> S;
        true  ->
            #{ initiator_amount_final := IFinal,
               responder_amount_final := RFinal,
               fee := Fee} = Tx,
            {{From, AF}, {To, AT}} =
                case Party of
                    initiator -> {{Initiator, IFinal}, {Responder, RFinal}};
                    responder -> {{Responder, RFinal}, {Initiator, IFinal}}
                end,
            reserve_fee(Fee,
            bump_and_charge(From, -AF,
                charge(To, -AT, delete_channel(ChannelId, S))))
    end.

channel_close_mutual_features(S, [_Height, _Channeld, _Party, _Tx] = Args, Res) ->
    Correct = channel_close_mutual_valid(S, Args),
    [{correct, if Correct -> channel_close_mutual; true -> false end},
     {channel_close_mutual, Res}].


%% --- Operation: ns_preclaim ---

ns_preclaim_pre(S) ->
    maps:is_key(accounts, S).

ns_preclaim_args(#{accounts := Accounts, height := Height}) ->
     ?LET([{SenderTag, Sender}, Name, Salt],
          [gen_account(1, 49, Accounts), gen_name(), gen_salt()],
          [Height, {SenderTag, Sender#account.key}, {Name, Salt},
           #{account_id => aec_id:create(account, Sender#account.key),
             fee => gen_fee(),
             commitment_id =>
                 aec_id:create(commitment,
                               aens_hash:commitment_hash(Name, Salt)),
             nonce =>gen_nonce(Sender)}]).

ns_preclaim_pre(S, [Height, {_, Sender}, {Name, Salt}, Tx]) ->
    %% Let us not test the unlikely case that someone provides the same name with the same salt
    [present || #preclaim{name = N, salt = St} <- maps:get(preclaims, S, []), N == Name, St == Salt] == []
        andalso aec_id:create(commitment, aens_hash:commitment_hash(Name, Salt)) == maps:get(commitment_id, Tx)
        andalso correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

ns_preclaim_valid(S, [_Height, {_, Sender}, {_Name, _Salt}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso valid_fee(Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx)).

ns_preclaim_adapt(#{height := Height} = S, [_Height, {SenderTag, Sender}, {Name, Salt}, Tx]) ->
    [Height, {SenderTag, Sender}, {Name, Salt}, adapt_nonce(S, Sender, Tx)];
ns_preclaim_adapt(_, _) ->
    false.

ns_preclaim(Height, _Sender, {_Name,_Salt}, Tx) ->
    apply_transaction(Height, aens_preclaim_tx, Tx).

ns_preclaim_next(#{height := Height} = S, _, [_Height, {_, Sender}, {Name, Salt}, Tx] = Args) ->
    case ns_preclaim_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee } = Tx,
            Preclaim = #preclaim{name    = Name,
                                 salt    = Salt,
                                 height  = Height,
                                 claimer = Sender},
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                add(preclaims, Preclaim, S)))
    end.

ns_preclaim_features(S, [_Height, {_, _Sender}, {_Name,_Salt}, _Tx] = Args, Res) ->
    Correct = ns_preclaim_valid(S, Args),
    [{correct, if Correct -> ns_preclaim; true -> false end},
     {ns_preclaim, Res} ].


%% --- Operation: claim ---
ns_claim_pre(S) ->
    maps:is_key(accounts, S) andalso maps:get(preclaims, S, []) /= [].

%% @doc ns_claim_args - Argument generator
-spec ns_claim_args(S :: eqc_statem:symbolic_state()) -> eqc_gen:gen([term()]).
ns_claim_args(S = #{height := Height}) ->
     ?LET({Name, Salt, {SenderTag, Sender}}, gen_preclaim(S),
          [Height, {SenderTag, Sender#account.key},
           #{account_id => aec_id:create(account, Sender#account.key),
             name => Name,
             name_salt => Salt,
             fee => gen_fee(),
             nonce => gen_nonce(Sender)}]).


ns_claim_pre(S, [Height, {_STag, Sender}, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

ns_claim_valid(S, [Height, {_, Sender}, Tx]) ->
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

ns_claim_adapt(#{height := Height} = S, [_Height, {SenderTag, Sender}, Tx]) ->
    [Height, {SenderTag, Sender}, adapt_nonce(S, Sender, Tx)];
ns_claim_adapt(_, _) ->
    false.

ns_claim(Height, _Sender, Tx) ->
    apply_transaction(Height, aens_claim_tx, Tx).

ns_claim_next(#{height := Height} = S, _, [_Height, {_, Sender}, Tx] = Args) ->
    case ns_claim_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, name := Name } = Tx,
            Claim = #claim{ name         = Name,
                            height       = Height,
                            valid_height = Height + aec_governance:name_claim_max_expiration(),
                            claimer      = Sender },
            remove_preclaim(Tx,
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee + aec_governance:name_claim_locked_fee(),
                add(claims, Claim, S))))
    end.

ns_claim_features(S, [_Height, {_, _Sender}, _Tx] = Args, Res) ->
    Correct = ns_claim_valid(S, Args),
    [{correct, if Correct -> ns_claim; true -> false end},
     {ns_claim, Res}].

%% --- Operation: claim_update ---
ns_update_pre(S) ->
    maps:is_key(accounts, S).

ns_update_args(#{accounts := Accounts, height := Height} = S) ->
     ?LET({{Name, {SenderTag, Sender}}, {Tag, NameAccount}},
          {gen_name_claim(S), gen_account(1, 5, Accounts)},
          [Height, Name, {SenderTag, Sender#account.key}, {Tag, NameAccount#account.key},
           #{account_id => aec_id:create(account, Sender#account.key),
             name_id => aec_id:create(name, aens_hash:name_hash(Name)),
             name_ttl => nat(),
             client_ttl => nat(),
             fee => gen_fee(),
             nonce => gen_nonce(Sender),
             pointers =>
                 gen_pointers(aec_id:create(account, NameAccount#account.key))
            }]).

gen_pointers(Id) ->
    weighted_default(
        {3, [aens_pointer:new(<<"account_pubkey">>, Id)]},
        {1, []}).

ns_update_pre(S, [Height, Name, {_, Sender}, _NameAccount, Tx]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

ns_update_valid(S, [Height, Name, {_, Sender}, _, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + aec_governance:name_claim_locked_fee())
    andalso valid_fee(Tx)
    andalso owns_name(S, Sender, Name)
    andalso is_valid_name(S, Name, Height).

ns_update_adapt(#{height := Height} = S, [_Height, Name, {SenderTag, Sender}, NameAccount, Tx]) ->
    [Height, Name, {SenderTag, Sender}, NameAccount, adapt_nonce(S, Sender, Tx)];
ns_update_adapt(_, _) ->
    false.

ns_update(Height, _Name, _Sender, _NameAccount, Tx) ->
    apply_transaction(Height, aens_update_tx, Tx).

ns_update_next(S, _, [Height, Name, {_, Sender}, {_, NameAccount}, Tx] = Args) ->
    case ns_update_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, pointers := Pointers, name_ttl := TTL } = Tx,
            S1 = case Pointers of
                    [] -> remove_named_account(Name, S);
                    _  -> add_named_account(Name, NameAccount, S)
                 end,
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                update_claim_height(Name, Height, TTL, S1)))
    end.

ns_update_features(S, [_Height, _Name, _Sender, {_Tag, _NameAccount}, _Tx] = Args, Res) ->
    Correct = ns_update_valid(S, Args),
    [{correct, if Correct -> ns_update; true -> false end},
     {ns_update, Res}].

%% --- Operation: ns_revoke ---
ns_revoke_pre(S) ->
    maps:is_key(accounts, S).

ns_revoke_args(#{height := Height} = S) ->
     ?LET({Name, {SenderTag, Sender}}, gen_name_claim(S),
          [Height, {SenderTag, Sender#account.key}, Name,
           #{account_id => aec_id:create(account, Sender#account.key),
             name_id => aec_id:create(name, aens_hash:name_hash(Name)),
             fee => gen_fee(),
             nonce => gen_nonce(Sender)
            }]).

ns_revoke_pre(S, [Height, {_, Sender}, Name, Tx]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

ns_revoke_valid(S, [Height, {_SenderTag, Sender}, Name, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso owns_name(S, Sender, Name)
    andalso is_valid_name(S, Name, Height).

ns_revoke_adapt(#{height := Height} = S, [_Height, {SenderTag, Sender}, Name, Tx]) ->
    [Height, {SenderTag, Sender}, Name, adapt_nonce(S, Sender, Tx)];
ns_revoke_adapt(_, _) ->
    false.

ns_revoke(Height, _Sender, _Name, Tx) ->
    apply_transaction(Height, aens_revoke_tx, Tx).

ns_revoke_next(S, _Value, [Height, {_SenderTag, Sender}, Name, Tx] = Args) ->
    case ns_revoke_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee } = Tx,
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                remove_named_account(Name,
                revoke_claim(Name, Height, S))))
    end.

ns_revoke_features(S, [_Height, _Sender, _Name, _Tx] = Args, Res) ->
    Correct = ns_revoke_valid(S, Args),
    [{correct, if Correct -> ns_revoke; true -> false end},
     {ns_revoke, Res}].


%% --- Operation: ns_transfer ---
ns_transfer_pre(S) ->
    maps:is_key(accounts, S).

ns_transfer_args(#{accounts := Accounts, height := Height} = S) ->
    ?LET({{Name, {SenderTag, Sender}}, {ReceiverTag, Receiver}},
         {gen_name_claim(S), gen_account(1, 49, Accounts)},
         ?LET(To, oneof([account, {name, elements(maps:keys(maps:get(named_accounts, S, #{})) ++ [<<"ta.test">>])}]),
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

ns_transfer_pre(S, [Height, {STag, Sender}, Receiver, Name, Tx]) ->
    aec_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height)
        andalso valid_nonce(S, Sender, Tx)
        andalso valid_account(S, STag, Sender) andalso valid_account(S, Receiver).

ns_transfer_valid(S, [Height, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Name, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Tx)
    andalso owns_name(S, Sender, Name)
    andalso is_valid_name(S, Name, Height)
    andalso case ReceiverTag of
               new      -> true;
               existing -> is_account(S, Receiver);
               name     -> is_valid_name_account(S, Receiver, Height)
            end.

ns_transfer_adapt(#{height := Height} = S, [_Height, {STag, Sender}, Receiver, Name, Tx]) ->
    [Height, {STag, Sender}, Receiver, Name, adapt_nonce(S, Sender, Tx)];
ns_transfer_adapt(_, _) ->
    false.

ns_transfer(Height, _Sender, _Receiver, _Name, Tx) ->
    apply_transaction(Height, aens_transfer_tx, Tx).

%% Assumption the recipient does not need to exist, it is created when we provided
%% it with a name
ns_transfer_next(S, _, [_Height, {_SenderTag, Sender}, Receiver, Name, Tx] = Args) ->
    case ns_transfer_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee } = Tx,
            ReceiverKey = resolve_account(S, Receiver),
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                transfer_name(ReceiverKey, Name,
                credit(ReceiverKey, 0, S))))   %% to create it if it doesn't exist
    end.

ns_transfer_features(S, [_Height, _Sender, _Receiver, _Name, _Tx] = Args, Res) ->
    Correct = ns_transfer_valid(S, Args),
    [{correct, if Correct -> ns_transfer; true -> false end},
     {ns_transfer, Res}].




%% ---------------



%% -- Property ---------------------------------------------------------------
weight(_S, spend) -> 10;
weight(S, mine)  ->
    case maps:get(preclaims, S, []) of
        [] -> 1;
        _  -> 20 end;
weight(_S, multi_mine) -> 3;
weight(_S, init)  -> 1;
weight(S, register_oracle) ->
    case non_oracle_accounts(S) of
        [] -> 1;
        _  -> 10 end;
weight(S, extend_oracle) ->
    case maps:get(oracles, S, []) of
        [] -> 0;
        _  -> 5 end;
weight(S, query_oracle)  ->
    case maps:get(oracles, S, []) of
        [] -> 1;
        _  -> 10 end;
weight(S, response_oracle)  ->
    case maps:get(queries, S, []) of
        [] -> 1;
        _  -> 10 end;
weight(S, ns_preclaim) ->
    case maps:get(preclaims, S, []) of
        [] -> 10;
        _  -> 3 end;
weight(S, ns_claim)    ->
    case good_preclaims(S) of
        [] -> 1;
        _  -> 10 end;
weight(S, ns_update) ->
    case maps:get(claims, S, []) of
        [] -> 1;
        _  -> 9 end;
weight(S, ns_revoke) ->
    case maps:get(claims, S, []) of
        [] -> 1;
        _  -> 3 end;
weight(S, ns_transfer) ->
    case maps:get(claims, S, []) of
        [] -> 1;
        _  -> 5 end;
weight(_S, channel_create) -> 5;
weight(S, channel_deposit) ->
    case maps:get(channels, S, []) of
        [] -> 0;
        _  -> 10 end;
weight(S, channel_withdraw) ->
    case maps:get(channels, S, []) of
        [] -> 0;
        _  -> 10 end;
weight(S, channel_close_mutual) ->
    case maps:get(channels, S, []) of
        [] -> 0;
        _  -> 4 end;
weight(_S, _) -> 0.

prop_txs() ->
    eqc:dont_print_counterexample(
    in_parallel(
    ?FORALL(Cmds, commands(?MODULE),
    begin
        put(trees, undefined),
        {H, S, Res} = run_commands(Cmds),
        Height = maps:get(height, S, 0),
        TreesTotal = 
            case get(trees) of
                undefined -> #{};
                Trees -> aec_trees:sum_total_coin(Trees)
            end,
        Total = lists:sum(maps:values(TreesTotal)),
        FeeTotal =  lists:sum([ Fee || {Fee, _} <- maps:get(fees, S, [])]),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            features(call_features(H),
            aggregate_feats([atoms, correct | all_command_names()], call_features(H),
                ?WHENFAIL(eqc:format("Total = ~p~nFeeTotal = ~p~n", [TreesTotal, FeeTotal]),
                          pretty_commands(?MODULE, Cmds, {H, S, Res},
                                          Res == ok andalso 
                                          (Total == 0 orelse Total == ?PatronAmount - FeeTotal))))))))
    end))).

aggregate_feats([], [], Prop) -> Prop;
aggregate_feats([atoms | Kinds], Features, Prop) ->
    {Atoms, Rest} = lists:partition(fun is_atom/1, Features),
    aggregate(with_title(atoms), Atoms, aggregate_feats(Kinds, Rest, Prop));
aggregate_feats([Tag | Kinds], Features, Prop) ->
    {Tuples, Rest} = lists:partition(fun(X) -> is_tuple(X) andalso element(1, X) == Tag end, Features),
    aggregate(with_title(Tag), [ Arg || {_, Arg} <- Tuples ], aggregate_feats(Kinds, Rest, Prop)).

%% -- State update and query functions ---------------------------------------

lookup_name(S, Name) ->
    maps:get(Name, maps:get(named_accounts, S, #{})).

get_account(S, {name, Name}) ->
    lookup_name(S, Name);
get_account(_, {new, Acc}) ->
    #account{ key = Acc, amount = 0, nonce = 1 };
get_account(#{ accounts := Accounts }, {existing, Acc}) ->
    lists:keyfind(Acc, #account.key, Accounts).

resolve_account(S, {name, Name})    -> lookup_name(S, Name);
resolve_account(_, {new, Key})      -> Key;
resolve_account(_, {existing, Key}) -> Key.

on_account(Key, Fun, S = #{accounts := Accounts}) ->
    Upd = fun(Acc = #account{ key = Key1 }) when Key1 == Key -> Fun(Acc);
             (Acc) -> Acc end,
    S#{ accounts => lists:map(Upd, Accounts) }.

credit(Key, Amount, S = #{ accounts := Accounts }) ->
    case is_account(S, Key) of
        true ->
            on_account(Key, fun(Acc) -> Acc#account{ amount = Acc#account.amount + Amount } end, S);
        false ->
            S#{ accounts => Accounts ++ [#account{ key = Key, amount = Amount, nonce = 1 }] }
    end.

charge(Key, Amount, S) -> credit(Key, -Amount, S).

bump_nonce(Key, S) ->
    on_account(Key, fun(Acc) -> Acc#account{ nonce = Acc#account.nonce + 1 } end, S).

reserve_fee(Fee, S = #{fees := Fees, height := H}) ->
    S#{fees => Fees ++ [{Fee, H}]}.

bump_and_charge(Key, Fee, S) ->
    bump_nonce(Key, charge(Key, Fee, S)).

add(Tag, X, S) ->
    S#{ Tag => maps:get(Tag, S, []) ++ [X] }.

remove(Tag, X, I, S) ->
    S#{ Tag := lists:keydelete(X, I, maps:get(Tag, S)) }.

remove_query(Id, S) ->
    remove(queries, Id, #query.id, S).

remove_preclaim(#{name := Na, name_salt := Sa}, S = #{preclaims := Ps}) ->
    S#{preclaims := [ P || P = #preclaim{name = Na0, salt = Sa0} <- Ps,
                           Na0 /= Na orelse Sa0 /= Sa ]}.

get(S, Tag, Key, I) ->
    lists:keyfind(Key, I, maps:get(Tag, S)).

get_query(S, Id) ->
    get(S, queries, Id, #query.id).

on_channel(Id, Fun, S = #{ channels := Channels }) ->
    Upd = fun(C = #channel{ id = I }) when I == Id -> Fun(C);
             (C) -> C end,
    S#{ channels => lists:map(Upd, Channels) }.

credit_channel(Id, Round, Amount, S) ->
    on_channel(Id, fun(C) -> C#channel{ amount = C#channel.amount + Amount,
                                        round = Round }
                   end, S).
delete_channel(CId, S = #{ channels := Channels }) ->
    S#{ channels := lists:keydelete(CId, #channel.id, Channels) }.

transfer_name(NewOwner, Name, S) ->
    on_claim(Name, fun(C) -> C#claim{ claimer = NewOwner } end, S).

on_claim(Name, Fun, S = #{ claims := Claims }) ->
    Upd = fun(C = #claim{ name = N }) when Name == N -> Fun(C);
             (C) -> C end,
    S#{ claims := lists:map(Upd, Claims) }.

update_claim_height(Name, Height, TTL, S) ->
    on_claim(Name, fun(C) -> C#claim{ update_height = Height,
                                      %% valid_height  = max(C#claim.valid_height, Height + TTL) }
                                      valid_height  = Height + TTL }
                   end, S).

revoke_claim(Name, Height, S) ->
    on_claim(Name, fun(C) when C#claim.revoke_height == undefined ->
                        C#claim{ valid_height = -1,
                                 revoke_height = aec_governance:name_protection_period() + Height };
                      (C) -> C end, S).

remove_named_account(Name, S) ->
    S#{ named_accounts => maps:remove(Name, maps:get(named_accounts, S, #{})) }.

add_named_account(Name, Acc, S) ->
    S#{ named_accounts => maps:merge(maps:get(named_accounts, S, #{}), #{ Name => Acc }) }.

%% --- local helpers ------

is_valid_name(#{claims := Names}, Name, Height) ->
    case lists:keyfind(Name, #claim.name, Names) of
        false -> false;
        Claim -> Claim#claim.revoke_height == undefined
                 andalso Claim#claim.valid_height >= Height
    end.

is_valid_name_account(#{claims := Names} = S, Name, Height) ->
    case lists:keyfind(Name, #claim.name, Names) of
        false -> false;
        Claim -> Claim#claim.revoke_height == undefined
                 andalso Claim#claim.valid_height >= Height
                 andalso maps:is_key(Name, maps:get(named_accounts, S, #{}))
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


valid_account(S, Tag, Key) -> valid_account(S, {Tag, Key}).
valid_account(_S, {name, _}) -> true;
valid_account(S, {Tag, Key}) ->
    IsA = is_account(S, Key),
    (IsA andalso Tag == existing) orelse (not IsA andalso Tag == new).

is_oracle(#{oracles := Oracles}, Oracle) ->
    lists:keymember(Oracle, 1, Oracles).

oracle(#{oracles := Oracles}, Oracle) ->
    lists:keyfind(Oracle, 1, Oracles).

oracle_query_fee(#{oracles := Oracles}, Oracle) ->
    {_, QFee} = lists:keyfind(Oracle, 1, Oracles),
    QFee.

is_query(#{queries := Qs}, Q) ->
    lists:keymember(Q, #query.id, Qs).

valid_fee(#{ fee := Fee }) ->
    Fee >= 20000.   %% not precise, but we don't generate fees in the shady range

correct_nonce(S, Key, #{nonce := {_Tag, Nonce}}) ->
    (account(S, Key))#account.nonce == Nonce.

valid_nonce(S, Key, #{nonce := {good, N}}) ->
    case account(S, Key) of
        #account{nonce = N} -> true;
        _                   -> false
    end;
valid_nonce(_S, _Key, #{nonce := {bad, _N}}) ->
    true. %% Bad nonces are always valid to test

adapt_nonce(S, A, Tx = #{nonce := {good, _}}) ->
    %% io:format("Adaptnonce ~p ~p\n", [maps:get(nonce, Tx),account(S, A)]),
    case account(S, A) of
        #account{nonce = N} -> Tx#{nonce := {good, N}};
        _                   -> Tx
    end;
adapt_nonce(_S, _A, Tx) ->
    Tx. %% Don't fix bad nonces...


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

non_oracle_accounts(#{accounts := As, oracles := Os}) ->
    [ A || A = #account{ key = K } <- As, not lists:keymember(K, 1, Os) ].

good_preclaims(#{ preclaims := Ps, height := H}) ->
    [ P || P = #preclaim{ height = H0 } <- Ps, H0 < H ].

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


apply_transaction(Height, TxMod, TxArgs0) ->
    Env      = aetx_env:tx_env(Height),
    Trees    = get(trees),
    TxArgs   = untag_nonce(TxArgs0),
    {ok, Tx} = apply(TxMod, new, [TxArgs]),

    case aetx:process(Tx, Trees, Env) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other ->
            Other
    end.

untag_nonce(M = #{nonce := {_Tag, N}}) -> M#{nonce := N};
untag_nonce(M)                         -> M.

%% -- Generators -------------------------------------------------------------


gen_account(_, _, []) -> {new, gen_account()};
gen_account(New, Exist, Accounts) ->
    weighted_default({Exist, {existing, elements(Accounts)}},
                     {New,   {new, gen_account()}}).

gen_account() ->  #account{key = noshrink(binary(32)), amount = 0, nonce = 0 }.

gen_oracle_account(#{accounts := As, oracles := []}) ->
    gen_account(1, 1, As);
gen_oracle_account(#{accounts := As, oracles := Os}) ->
    weighted_default(
        {39, ?LET({O, _}, elements(Os), {existing, lists:keyfind(O, #account.key, As)})},
        {1,  gen_account(9, 1, As)}).


gen_new_oracle_account(S = #{accounts := As}) ->
    case non_oracle_accounts(S) of
        [] -> gen_account(1, 1, As); %% We can't get a good one, fail evenly
        GoodAs ->
            weighted_default({29, {existing, elements(GoodAs)}},
                             {1,  gen_account(1, 9, As)})
    end.

gen_account_pubkey(Accounts) ->
    oneof([?LAZY({existing, elements(Accounts)}),
           ?LAZY({new, gen_account()})]).

gen_preclaim(#{preclaims := [], accounts := As}) ->
    {gen_name(), gen_salt(), gen_account(1, 1, As)};
gen_preclaim(#{preclaims := Ps, accounts := As}) ->
    weighted_default(
        {39, ?LET(#preclaim{name = N, salt = S, claimer = C}, elements(Ps),
                  begin
                    A = {existing, lists:keyfind(C, #account.key, As)},
                    frequency([{1, {N, S+1, A}}, {1, {gen_name(), S, A}}, {37, {N, S, A}}])
                  end)},
        {1, {gen_name(), gen_salt(), gen_account(1, 1, As)}}).

gen_name_claim(#{claims := [], accounts := As}) ->
    {gen_name(), gen_account(1, 1, As)};
gen_name_claim(#{claims := Cs, accounts := As}) ->
    weighted_default(
        {39, ?LET(#claim{name = N, claimer = C}, elements(Cs),
                  begin
                    A = {existing, lists:keyfind(C, #account.key, As)},
                    frequency([{1, {gen_name(), A}}, {1, {N, gen_account(0, 1, As)}}, {38, {N, A}}])
                  end)},
        {1, {gen_name(), gen_account(1, 1, As)}}).


unique_name(List) ->
    ?LET([W],
         noshrink(?SUCHTHAT([Word],
                            eqc_erlang_program:words(1), not lists:member(Word, List))),
         W).

gen_nonce(false) ->
    {bad, 1};  %% account is not present
gen_nonce(#account{nonce = N}) ->
    weighted_default({49, {good, N}}, {1, ?LET(X, elements([N-5, N-1, N+1, N+5]), {bad, abs(X)})}).

gen_spend_amount(#account{ amount = X }) when X == 0 ->
    choose(0, 10000000);
gen_spend_amount(#account{ amount = X }) ->
    weighted_default({49, round(X / 5)}, {1, choose(0, 10000000)}).

gen_name() ->
    ?LET(NFs, frequency([{1, non_empty(list(elements(?NAMEFRAGS)))},
                         {90, [elements(?NAMEFRAGS)]}]),
    return(iolist_to_binary(lists:join(".", NFs ++ ["test"])))).

gen_name(S) ->
    frequency([{90, elements(maps:keys(maps:get(names, S, #{})) ++ [<<"ta.test">>])},
               {1, gen_name()}]).

gen_state_channel_id(#{channels := [], accounts := As}) ->
    ?LET([{_, A1}, {_, A2}], vector(2, gen_account(0, 1, As)),
         {A1#account.key, choose(1, 5), A2#account.key});
gen_state_channel_id(#{channels := Cs} = S) ->
    weighted_default(
        {39, ?LET(C, elements(Cs), C#channel.id)},
        {1,  gen_state_channel_id(S#{channels := []})}).

gen_party() ->
    elements([initiator, responder]).

gen_channel_round(#{channels := Cs}, CId) ->
    case lists:keyfind(CId, #channel.id, Cs) of
        false -> choose(0, 5);
        #channel{round = R} ->
            weighted_default({29, R+1}, {1, ?LET(R_, elements([R-3, R-1, R, R+3]), abs(R_))})
    end.

gen_fee() ->
    weighted_default({29, choose(20000, 30000)},
                     {1,  choose(0, 15000)}).    %% too low

gen_query_fee() ->
    choose(10, 1000).

gen_query_fee(QF) ->
    weighted_default({29, QF}, {1, elements([QF - 10, QF - 1, QF + 1, QF + 10, QF + 100])}).

gen_salt() -> choose(270, 280).

gen_channel_amount() ->
    choose(20000, 200000).

gen_create_channel_amounts() ->
    ?LET({I, R}, {gen_channel_amount(), gen_channel_amount()},
            weighted_default({29, {I, R, min(I, R) - 2000}}, {1, {I, R, gen_channel_amount()}})).

gen_close_channel_amounts(#{channels := Cs}, CId) ->
    case lists:keyfind(CId, #channel.id, Cs) of
        false -> {gen_channel_amount(), gen_channel_amount(), gen_fee()};
        #channel{amount = A} ->
            weighted_default(
                {5, ?LET({Fee, Factor1, Factor2}, {gen_fee(), choose(0, 50), choose(0, 50)},
                     begin
                        I = ((A - Fee) * Factor1) div 100,
                        R = ((A - Fee) * Factor2) div 100,
                        {I, R, Fee}
                     end)},
                {1, ?LET({Fee, Factor1, Factor2}, {gen_fee(), choose(0, 100), choose(0, 100)},
                     begin
                        I = ((A - Fee) * Factor1) div 100,
                        R = ((A - Fee) * Factor2) div 100,
                        {I, R, Fee}
                     end)})
    end.


gen_ttl() ->
    choose(5, 50).
