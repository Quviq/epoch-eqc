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
-define(PatronAmount, 100000000000001).  %% read from file
-define(NAMEFRAGS, ["foo", "bar", "baz"]).

-record(account, {key, amount, nonce, names_owned = []}).
-record(preclaim,{name, salt, height, claimer, protocol}).
-record(claim,{name, height, expires_by, protected_height,  claimer, protocol}).
-record(query, {sender, id, fee, response_ttl, query_ttl}).
-record(oracle, {id, qfee, oracle_ttl}).
-record(channel, {id, round = 1, amount = 0, reserve = 0, trees, closed = false, lock_period}).
-record(contract, {name, id, amount, deposit, vm, abi, compiler_version, protocol, src, functions}).

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{claims => [], preclaims => [], oracles => [], fees => [], contracts => [], gaccounts => [], keys => #{}}.

initial_state(Contracts) ->
    maps:put(compiled_contracts, Contracts, initial_state()).

patron() ->
    #{ public := Pubkey, secret := Privkey } =
                     #{public =>
                           <<227,81,22,143,182,219,118,194,214,164,169,153,6,190,90,
                             72,72,11,74,195,160,239,10,12,98,144,86,254,51,110,216,
                             22>>,
                       secret =>
                           <<156,127,9,241,107,48,249,188,92,91,80,218,172,41,140,
                             147,102,228,17,21,148,192,27,47,228,212,93,153,220,174,
                             52,19,227,81,22,143,182,219,118,194,214,164,169,153,6,
                             190,90,72,72,11,74,195,160,239,10,12,98,144,86,254,51,
                             110,216,22>>},
    {Pubkey, Privkey, ?PatronAmount}.

minimum_gas_price(H) ->
    aec_governance:minimum_gas_price(H).

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
    true.

precondition_common(_S, _Call) ->
    true.

postcondition_common(_S, {call, ?MODULE, newkey, _Args}, _Res) ->
    true;
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
valid_common(channel_close_solo, S, Args)   -> channel_close_solo_valid(S, Args);
valid_common(channel_settle, S, Args)       -> channel_settle_valid(S, Args);
valid_common(ns_preclaim, S, Args)          -> ns_preclaim_valid(S, Args);
valid_common(ns_claim, S, Args)             -> ns_claim_valid(S, Args);
valid_common(ns_update, S, Args)            -> ns_update_valid(S, Args);
valid_common(ns_revoke, S, Args)            -> ns_revoke_valid(S, Args);
valid_common(ns_transfer, S, Args)          -> ns_transfer_valid(S, Args);
valid_common(contract_create, S, Args)      -> contract_create_valid(S, Args);
valid_common(contract_call, S, Args)        -> contract_call_valid(S, Args).



%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
init_pre(S) ->
    not maps:is_key(accounts, S).

init_args(_S) ->
    [0].

init(_Height) ->
    put(trees, initial_trees()),
    ok.

initial_trees() ->
    {PA, _Secret, PAmount} = patron(),
    trees_with_accounts([{account, PA, PAmount}]).

init_next(S, _Value, [Height]) ->
    {PA, Secret, PAmount} = patron(),
    S#{height   => Height,
       accounts => [#account{key = PA, amount = PAmount, nonce = 1}],
       keys => maps:put(PA, Secret, maps:get(keys, S))}.

%% --- Operation: init ---
newkey_args(_S) ->
    #{ public := Pubkey, secret := Privkey } = enacl:sign_keypair(),
    [Pubkey, Privkey].

newkey(PubKey, _) ->
    PubKey.

newkey_next(S, Value, [_Pubkey, Privkey]) ->
    S#{keys => maps:put(Value, Privkey, maps:get(keys, S))}.

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
mine_next(S, Value, [H]) ->
    multi_mine_next(S, Value, [H, 1]).

mine_features(S, [H], Res) ->
    multi_mine_features(S, [H, 1], Res).

expired_queries(S, Height) ->
    [ Q || Q <- maps:get(queries, S, []), Q#query.response_ttl =< Height ].

expired_claims(S, Height) ->
    [ C || C <- maps:get(claims, S, []),
           C#claim.expires_by + aec_governance:name_protection_period() =< Height ].

expired_solo_close(S, Height) ->
    [ C || C <- maps:get(channels, S, []),
           is_valid_unlock_solo(S#{height => Height}, C)].

%% --- Operation: multi_mine ---
multi_mine_pre(S) ->
    maps:is_key(accounts, S).

multi_mine_args(#{height := Height}) ->
    [Height, elements([10, 100, 1000, 10000, 25000])].

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
    ExpiredClaims = expired_claims(S, Height + Blocks - 1),
    ExpiredNames = [ C#claim.name || C <- ExpiredClaims ],
    Accounts1 = lists:foldl(
        fun(Q, As) -> case lists:keyfind(Q#query.sender, #account.key, As) of
                        false -> As;
                        A     -> lists:keyreplace(A#account.key, #account.key, As,
                                                  A#account{ amount = A#account.amount + Q#query.fee })
                      end
        end, Accounts, ExpiredQs),
    S#{height   => Height + Blocks,
       accounts => Accounts1,
       queries  => maps:get(queries, S, []) -- ExpiredQs,
       claims => maps:get(claims, S, []) -- ExpiredClaims,
       named_accounts =>
           maps:without(ExpiredNames, maps:get(named_accounts, S, #{}))
      }.

multi_mine_features(S, [H, B], _Res) ->
    [{mine, solo_close_unlocked} || expired_solo_close(S, H+B) =/= [] ] ++
    [{mine, response_ttl} || expired_queries(S, H+B) =/= [] ] ++
    [multi_mine].


%% --- Operation: spend ---
spend_pre(S) ->
    maps:is_key(accounts, S).


%% here we should add spending to oracle and contract
%% aeser_id:specialize_type(Recv),
%% names are always accounts, hard coded in tx_processor
spend_args(#{height := Height} = S) ->
    ?LET([{SenderTag, Sender}, To], [gen_account(1, 49, S),
                                     frequency([{10, {account,  gen_account(2, 1, S)}},
                                                {2, {oracle, gen_oracle_account(S)}},
                                                {1, {contract, gen_contract_id(1, 100, maps:get(contracts, S))}},
                                                {2, {name, elements(maps:keys(maps:get(named_accounts, S, #{})) ++ [<<"ta.test">>])}}])],
         [Height, {SenderTag, Sender#account.key},
          case To of
              {account, {ReceiverTag, Receiver}} -> {ReceiverTag, Receiver#account.key};
              {oracle, {ReceiverTag, Receiver}} -> {ReceiverTag, Receiver#account.key};
              {contract, {_, Contract}} -> {contract, Contract#contract.id};
              {name, Name} -> {name, Name}
          end,
          #{sender_id => aeser_id:create(account, Sender#account.key),  %% The sender is asserted to never be a name.
            recipient_id =>
                case To of
                    {account, {_, Receiver}} ->
                        aeser_id:create(account, Receiver#account.key);
                    {oracle, {_, Receiver}} ->
                        aeser_id:create(oracle, Receiver#account.key);
                    {contract, {_, Contract}} ->
                        aeser_id:create(contract, Contract#contract.id);
                    {name, Name} ->
                        aeser_id:create(name, aens_hash:name_hash(Name))
                end,
            amount => gen_spend_amount(Sender),
            fee => gen_fee(Height),
            nonce => gen_nonce(Sender),
            payload => utf8()}]).

spend_pre(#{accounts := Accounts} = S, [Height, {_, Sender}, {RTag, Receiver}, Tx]) ->
    ReceiverOk =
        case RTag of
            new      -> lists:keyfind(Receiver, #account.key, Accounts) == false;
            existing -> lists:keyfind(Receiver, #account.key, Accounts) =/= false;
            contract ->
                %% only allow valid contracts, otherwise it's just a new account without secret key to sign
                lists:keyfind(Receiver, #contract.id, maps:get(contracts, S, [])) =/= false;
            name     -> maps:is_key(Receiver, maps:get(named_accounts, S, #{}))
        end,
    ReceiverOk andalso correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

spend_valid(S, [Height, {_, Sender}, {ReceiverTag, Receiver}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(amount, Tx) + maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso case ReceiverTag of
               new      -> true;
               existing -> is_account(S, Receiver);
               contract -> true;
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
            case resolve_account(S, Receiver) of
                false -> S;
                {contract, ContractId} ->
                     reserve_fee(Fee,
                                bump_and_charge(Sender, Amount + Fee,
                                                credit_amount(ContractId, Amount, S)));
                RKey ->
                    reserve_fee(Fee,
                                bump_and_charge(Sender, Amount + Fee,
                                                credit(RKey, Amount, S)))
            end
    end.

spend_features(S, [_Height, {_, Sender}, {Tag, Receiver}, Tx] = Args, Res) ->
    Correct = spend_valid(S, Args),
    [{correct,  if Correct -> spend; true -> false end}] ++
        [ {spend, to_self, Tag} || Sender == Receiver andalso Correct] ++
        [ {spend, element(2, maps:get(recipient_id, Tx))} ||  Correct] ++
        [ {spend, name} || Correct andalso Tag == name] ++
        [{spend, Res}].


%% --- Operation: register_oracle ---
register_oracle_pre(S) ->
    length(maps:get(accounts, S, [])) > 1.

register_oracle_args(S = #{height := Height}) ->
     ?LET({SenderTag, Sender}, gen_new_oracle_account(S),
          [Height, {SenderTag, Sender#account.key},
                #{account_id => aeser_id:create(account, Sender#account.key),
                  query_format    => <<"send me any string"/utf8>>,
                  response_format => <<"boolean()"/utf8>>,
                  query_fee       => gen_query_fee(),
                  fee => gen_fee(Height),
                  nonce => gen_nonce(Sender),
                  oracle_ttl => {delta, frequency([{9, 1001}, {1, elements([0, 1, 2])}])},
                  abi_version => 0}]).

register_oracle_pre(S, [Height, {_, Sender}, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

register_oracle_valid(S, [Height, {_, Sender}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso (not is_oracle(S, Sender) orelse oracle_ttl(S, Sender) < Height).

register_oracle_adapt(#{height := Height} = S, [_, {STag, Sender}, Tx]) ->
    [Height, {STag, Sender}, adapt_nonce(S, Sender, Tx)];
register_oracle_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

register_oracle(Height, _Sender, Tx) ->
    apply_transaction(Height, aeo_register_tx, Tx).


register_oracle_next(S, _Value, [Height, {_, Sender}, Tx] = Args) ->
    case register_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, query_fee := QFee, oracle_ttl := {delta, D} } = Tx,
            Oracle = #oracle{id = Sender, qfee = QFee,
	    	     	     oracle_ttl = D + Height},
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                add(oracles, Oracle,
                remove(oracles, Sender, #oracle.id, S))))
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
          #{oracle_id  => aeser_id:create(oracle, Oracle#account.key),
            nonce      => gen_nonce(Oracle),
            oracle_ttl => {delta, DeltaTTL},
            fee        => gen_fee(Height)
           }]).

extend_oracle_pre(S, [Height, Oracle, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Oracle, Tx).

extend_oracle_valid(S, [Height, Oracle, Tx]) ->
    is_account(S, Oracle)
    andalso is_oracle(S, Oracle)
    andalso correct_nonce(S, Oracle, Tx)
    andalso check_balance(S, Oracle, maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso oracle_ttl(S, Oracle) >= Height.

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
            #{ oracle_ttl := {delta, Delta}, fee := Fee} = Tx,
            reserve_fee(Fee,
            bump_and_charge(Oracle, Fee,
            oracle_ext(Oracle, Delta, S)))
    end.

extend_oracle_features(S, [_Height, _, _Tx] = Args, Res) ->
    Correct = extend_oracle_valid(S, Args),
    [{correct, if Correct -> extend_oracle; true -> false end},
     {extend_oracle, Res}].

%% --- Operation: query_oracle ---
query_oracle_pre(S) ->
     maps:is_key(accounts, S).

query_oracle_args(#{height := Height} = S) ->
     ?LET({{SenderTag, Sender}, {_, Oracle}},
          {gen_account(1, 49, S), gen_oracle_account(S)},
          begin
              QueryFee =
                  case oracle(S, Oracle#account.key) of
                      false -> 100;
                      #oracle{qfee = QFee} -> QFee
                  end,
              [Height, {SenderTag, Sender#account.key}, Oracle#account.key,
               #{sender_id => aeser_id:create(account, Sender#account.key),
                 oracle_id => aeser_id:create(oracle, Oracle#account.key),
                 query => oneof([<<"{foo: bar}"/utf8>>, <<"any string"/utf8>>, <<>>]),
                 query_fee => gen_query_fee(QueryFee),
                 query_ttl => {delta, choose(1,5)},
                 response_ttl => {delta, choose(1,5)},
                 fee => gen_fee(Height),
                 nonce => gen_nonce(Sender)
                }]
          end).

query_oracle_pre(S, [Height, {_, Sender}, _Oracle, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

query_oracle_valid(S, [Height, {_SenderTag, Sender}, Oracle, Tx]) ->
    {delta, ResponseTTL} = maps:get(response_ttl, Tx),
    {delta, QueryTTL} = maps:get(query_ttl, Tx),
    is_account(S, Sender)
    andalso is_oracle(S, Oracle)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + maps:get(query_fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso oracle_query_fee(S, Oracle) =< maps:get(query_fee, Tx)
    andalso oracle_ttl(S, Oracle) >= Height + ResponseTTL + QueryTTL.

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
            #{ response_ttl := ResponseTTL,
               query_ttl := {delta, Delta},
               fee := Fee, query_fee := QFee } = Tx,
            Query = #query{sender       = Sender,
                           id           = {Sender, maps:get(nonce, untag_nonce(Tx)), Oracle},
                           query_ttl    = Height + Delta,
                           response_ttl = ResponseTTL,
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

response_oracle_args(#{accounts := Accounts, height := Height} = S) ->
     ?LET({Sender, Nonce, Oracle} = QueryId,
           frequency([{9, ?LET(Query, elements(maps:get(queries, S)), Query#query.id)},
                      {1, {gen_map_key(maps:get(keys, S)), 2, gen_map_key(maps:get(keys, S))}}]),
          [Height, {Sender, Nonce, Oracle},
           #{oracle_id => aeser_id:create(oracle, Oracle),
             response => weighted_default({9, <<"yes, you can">>}, {1, utf8()}),
             response_ttl => gen_query_response_ttl(S, QueryId),
             fee => gen_fee(Height),
             nonce => case lists:keyfind(Oracle, #account.key, Accounts) of
                          false -> {bad, 1};
                          Account -> {good, Account#account.nonce}
                      end
            }]).

response_oracle_pre(S, [Height, {_, _, Q}, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Q, Tx).

response_oracle_valid(S, [Height, {_, _, Oracle} = QueryId, Tx]) ->
    is_account(S, Oracle)
    andalso is_oracle(S, Oracle)
    andalso correct_nonce(S, Oracle, Tx)
    andalso check_balance(S, Oracle,  maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso is_query(S, QueryId)
    andalso query_query_ttl(S, QueryId) >= Height
    andalso query_response_ttl(S, QueryId) == maps:get(response_ttl, Tx).

response_oracle_adapt(#{height := Height} = S, [_, {Sender, _, Oracle}, Tx]) ->
    QIds = [ Q#query.id || Q <- maps:get(queries, S, []),
                           element(1, Q#query.id) == Sender,
                           element(3, Q#query.id) == Oracle],
    case QIds of
        [] -> false;
        _ ->
            [Height, elements(QIds), adapt_nonce(S, Oracle, Tx)]
    end;
response_oracle_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


response_oracle(Height, QueryId, Tx) ->
    NewTx = response_oracle_tx(QueryId, Tx),
    apply_transaction(Height, aeo_response_tx, NewTx).

response_oracle_tx({Sender, Nonce, Oracle}, Tx) ->
    Tx#{query_id => aeo_query:id(Sender, Nonce, Oracle)}.

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
    maps:get(height, S, 0) >= 1 andalso
    length(maps:get(accounts, S, [])) > 1.

channel_create_args(#{height := Height} = S) ->
     ?LET([{_, Initiator}, {_, Responder}],
          vector(2, gen_account(1, 49, S)),
     ?LET({IAmount, RAmount, ChannelReserve}, gen_create_channel_amounts(Height),
          [Height, Initiator#account.key, Responder#account.key,
                #{initiator_id => aeser_id:create(account, Initiator#account.key),
                  responder_id => aeser_id:create(account, Responder#account.key),
                  state_hash => gen_state_hash([{account, Initiator, IAmount}, {account, Responder, RAmount}]),
                  initiator_amount => IAmount,
                  responder_amount => RAmount,
                  lock_period => choose(0,3),
                  channel_reserve => ChannelReserve,
                  fee => gen_fee(Height),
                  nonce => gen_nonce(Initiator)}])).

channel_create_pre(S, [Height, Initiator, Responder, Tx]) ->
    Initiator =/= Responder
    andalso correct_height(S, Height) andalso valid_nonce(S, Initiator, Tx).

channel_create_valid(S, [Height, Initiator, Responder, Tx]) ->
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso correct_nonce(S, Initiator, Tx)
    andalso check_balance(S, Initiator, maps:get(fee, Tx) + maps:get(initiator_amount, Tx))
    andalso check_balance(S, Responder, maps:get(responder_amount, Tx))
    andalso valid_fee(Height, Tx)
    andalso maps:get(initiator_amount, Tx) >= maps:get(channel_reserve, Tx)
    andalso maps:get(responder_amount, Tx) >= maps:get(channel_reserve, Tx).

channel_create_adapt(#{height := Height} = S, [_, Initiator, Responder, #{state_hash := {Tag, Accounts}} = Tx]) ->
    NewAccounts =
        case Tag of
            valid ->
                [{account, Initiator, maps:get(initiator_amount, Tx)},
                 {account, Responder, maps:get(responder_amount, Tx)}];
            invalid ->
                %% invalid stays invalid
                Accounts
        end,
    [Height, Initiator, Responder, adapt_nonce(S, Initiator, Tx#{state_hash => {Tag, NewAccounts}})];
channel_create_adapt(_, _) ->
    %% in case we don't even have a Height
    false.


channel_create(Height, _Initiator, _Responder, Tx) ->
    NewTx = channel_create_tx(Tx),
    apply_transaction(Height, aesc_create_tx, NewTx).

channel_create_tx(#{state_hash := {_, Accounts}} = Tx) ->
    Tx#{state_hash => aec_trees:hash(trees_with_accounts(Accounts))}.

channel_create_next(S, _Value, [_Height, Initiator, Responder, Tx] = Args) ->
    case channel_create_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee              := Fee,
               nonce            := {_, Nonce},
               initiator_amount := IAmount,
               responder_amount := RAmount,
               channel_reserve  := Reserve,
               lock_period      := LockPeriod,
               state_hash       := ChannelTrees } = Tx,
            Channel = #channel{ id = {Initiator, Nonce, Responder},
                                amount = IAmount + RAmount,
                                reserve = Reserve,
                                lock_period = LockPeriod,
                                trees = ChannelTrees},
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
          From = case Party of initiator -> Initiator; responder -> Responder end,  %% Add someone else as From as well!
          [Height, {Initiator, N, Responder}, Party,
                #{from_id => aeser_id:create(account, From),
                  amount => gen_channel_amount(Height),
                  round => gen_channel_round(S, CId),
                  fee => gen_fee(Height),
                  state_hash => case channel(S, CId) of
                                    false ->
                                        {invalid, []};
                                    Channel ->
                                        %% Here we can change the state!
                                        Channel#channel.trees
                                end,
                  nonce => gen_nonce(account(S, From))
                 }]
     end).

channel_deposit_pre(S, [Height, {I, _, R} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    correct_height(S, Height) andalso valid_nonce(S, From, Tx) andalso
        case maps:get(state_hash, Tx) of
            {valid, _} = Ts ->
                case channel(S, ChannelId) of
                    #channel{trees = Trees} -> Trees == Ts;
                    _ -> true %% invalid channel id filtered later
                end;
            _ -> true
        end.

channel_deposit_valid(S, [Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso check_balance(S, From, maps:get(fee, Tx) + maps:get(amount, Tx))
    andalso valid_fee(Height, Tx)
    andalso correct_round(S, ChannelId, Tx).

channel_deposit_adapt(#{height := Height} = S, [_, {I, _, R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    Channels = [ C || C <- maps:get(channels, S, []),
                             element(1, C#channel.id) == I,
                             element(3, C#channel.id) == R],
    case Channels of
        [] -> false;
        _ ->
            ?LET(Channel, elements(Channels),
                 [Height, Channel#channel.id, Party, adapt_state_hash(Channel, From, maps:get(amount, Tx), adapt_nonce(S, From, Tx))])
    end;
channel_deposit_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

channel_deposit(Height, ChannelId, Party, Tx) ->
    NewTx = channel_deposit_tx(ChannelId, Party, Tx),
    apply_transaction(Height, aesc_deposit_tx, NewTx).

channel_deposit_tx({Initiator, N, Responder}, _Party, #{state_hash := {_, Accounts}} = Tx) ->
    Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
       state_hash => aec_trees:hash(trees_with_accounts(Accounts))}.

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

%% We do not yet test withdraw by third party!
channel_withdraw_args(#{height := Height} = S) ->
    ?LET({CId = {Initiator, N, Responder}, Party, Amount},
         {gen_state_channel_id(S), gen_party(), gen_channel_amount(Height)},
    begin
         From = case Party of initiator -> Initiator; responder -> Responder end,
         [Height, {Initiator, N, Responder}, Party,
               #{to_id => aeser_id:create(account, From),
                 amount => Amount,
                 round => gen_channel_round(S, CId),
                 fee => gen_fee(Height),
                 state_hash =>case channel(S, CId) of
                                    false ->
                                        {invalid, []};
                                    Channel ->
                                        %% Here we can change the state!
                                        case Channel#channel.trees of
                                            {valid, Accounts} ->
                                                weighted_default(
                                                  {9, {valid, gen_state_hash_account_keys(adapt_account(Accounts, From, -Amount))}},
                                                  {if Amount == 0 -> 0; true -> 1 end, {invalid, Accounts}});
                                            Invalid ->
                                                Invalid
                                        end
                                end,
                 nonce => gen_nonce(account(S, From))
                }]
    end).

channel_withdraw_pre(S, [Height, {I, _, R} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    correct_height(S, Height) andalso valid_nonce(S, From, Tx) andalso
        case maps:get(state_hash, Tx) of
            {valid, _} = Ts -> (channel(S, ChannelId))#channel.trees == Ts;
            _ -> true
        end.

channel_withdraw_valid(S, [Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso check_balance(S, From, maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso correct_round(S, ChannelId, Tx)
    andalso (channel(S, ChannelId))#channel.amount >= maps:get(amount, Tx)
    andalso (channel(S, ChannelId))#channel.amount - maps:get(amount, Tx) >= (channel(S, ChannelId))#channel.reserve*2.

channel_withdraw_adapt(#{height := Height} = S, [_, {I, _ ,R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    Channels = [ C || C <- maps:get(channels, S, []),
                             element(1, C#channel.id) == I,
                             element(3, C#channel.id) == R],
    case Channels of
        [] -> false;
        _ ->
            ?LET(Channel, elements(Channels),
                 [Height, Channel#channel.id, Party, adapt_state_hash(Channel, From, -maps:get(amount, Tx), adapt_nonce(S, From, Tx))])
    end;
channel_withdraw_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

channel_withdraw(Height, ChannelId, Party, Tx) ->
    NewTx = channel_withdraw_tx(ChannelId, Party, Tx),
    apply_transaction(Height, aesc_withdraw_tx, NewTx).

channel_withdraw_tx({Initiator, N, Responder}, _Party, #{state_hash := {_, Accounts}} =Tx) ->
    Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
       state_hash => aec_trees:hash(trees_with_accounts(Accounts))}.


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
         {gen_state_channel_id(S, fun(C) -> C#channel.closed == false end), gen_party()},
    ?LET({IFinal, RFinal, Fee}, gen_close_channel_amounts(S, CId),
    begin
         From = case Party of initiator -> Initiator; responder -> Responder end,
         [Height, {Initiator, N, Responder}, Party,
               #{from_id => aeser_id:create(account, From),
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

channel_close_mutual_valid(S, [Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, Initiator)
    andalso is_account(S, Responder)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso valid_fee(Height, Tx)
    andalso maps:get(initiator_amount_final, Tx) >= 0
    andalso maps:get(responder_amount_final, Tx) >= 0
    andalso (channel(S, ChannelId))#channel.closed == false
    andalso (channel(S, ChannelId))#channel.amount >=
                maps:get(initiator_amount_final, Tx) + maps:get(responder_amount_final, Tx) + maps:get(fee, Tx).

channel_close_mutual_adapt(#{height := Height} = S, [_, _ChannelId = {I, _ ,R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    CIds = [ C#channel.id || C <- maps:get(channels, S, []), element(1, C#channel.id) == I,
                             element(3, C#channel.id) == R],
    case CIds of
        [] -> false;
        _ ->
            [Height, elements(CIds), Party, adapt_nonce(S, From, Tx)]
    end;
channel_close_mutual_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

channel_close_mutual(Height, Channeld, Party, Tx) ->
    NewTx = channel_close_mutual_tx(Channeld, Party, Tx),
    apply_transaction(Height, aesc_close_mutual_tx, NewTx).

channel_close_mutual_tx({Initiator, N, Responder}, _Party, Tx) ->
    Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder))}.



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
                credit(To, AT, close_channel(ChannelId, mutual, S))))
    end.

channel_close_mutual_features(S, [_Height, _Channeld, _Party, _Tx] = Args, Res) ->
    Correct = channel_close_mutual_valid(S, Args),
    [{correct, if Correct -> channel_close_mutual; true -> false end},
     {channel_close_mutual, Res}].


%% --- Operation: channel_close_solo ---
channel_close_solo_pre(S) ->
    maps:is_key(channels, S).

channel_close_solo_args(#{height := Height} = S) ->
    ?LET({CId = {Initiator, _, Responder}, Party},
         {gen_state_channel_id(S, fun(C) -> C#channel.closed == false end), gen_party()},
         begin
             From = case Party of initiator -> Initiator; responder -> Responder end,
             Poi = case channel(S, CId) of
                       false -> {invalid, []};
                       Channel ->
                           case Channel#channel.trees of
                               {valid, Accounts} ->
                                   frequency(
                                     [{90, {valid, Accounts}},
                                      {10, {invalid,
                                            ?LET({account, Acc, Amount}, elements(Accounts),
                                                 (Accounts -- [{account, Acc, Amount}]) ++
                                                     [ {account, Acc, ?SUCHTHAT(I, nat(), I =/= Amount)} ])}}]);
                               Invalid ->
                                   Invalid
                           end
                   end,
             [Height, CId, Party,
              #{from_id => aeser_id:create(account, From),
                payload => <<>>,
                poi => Poi,
                fee => gen_fee_above(Height, 24999),  %% POI takes bytes! 23120 is normal cost
                nonce => gen_nonce(account(S, From))
               }]
         end).

channel_close_solo_pre(S, [Height, {I, _, R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    correct_height(S, Height) andalso valid_nonce(S, From, Tx).

channel_close_solo_valid(S, [Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, From)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso valid_solo_close_fee(Height, Tx)
    andalso (channel(S, ChannelId))#channel.closed == false
    andalso is_valid_poi(S, ChannelId, maps:get(poi, Tx))
    andalso check_balance(S, From, maps:get(fee, Tx)).

is_valid_poi(_S, _ChannelId, {invalid, _}) ->
    false;
is_valid_poi(S, {I, _, R} = ChannelId, {valid, Accounts}) ->
    (channel(S,ChannelId))#channel.amount >= lists:sum([ A || {account, Key, A} <- Accounts, lists:member(Key, [I, R])]).

channel_close_solo_adapt(#{height := Height} = S, [_, {I, _ ,R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    Channels = [ C || C <- maps:get(channels, S, []), element(1, C#channel.id) == I,
                  element(3, C#channel.id) == R],
    case Channels of
        [] -> false;
        _ ->
            ?LET(Channel, elements(Channels),
                 [Height, Channel#channel.id, Party, adapt_poi(Channel, adapt_nonce(S, From, Tx))])
    end;
channel_close_solo_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

channel_close_solo(Height, Channeld, Party, Tx) ->
    NewTx = channel_close_solo_tx(Channeld, Party, Tx),
    apply_transaction(Height, aesc_close_solo_tx, NewTx).

channel_close_solo_tx({Initiator, N, Responder}, _Party, #{poi := {_, Accounts}} = Tx) ->
    Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder)),
        poi =>
            begin
                ChannelTrees = trees_with_accounts(Accounts),
                lists:foldl(fun({account, Acc, _}, Poi) ->
                                    {ok, NewPoi} = aec_trees:add_poi(accounts, Acc, ChannelTrees, Poi),
                                    NewPoi
                            end, aec_trees:new_poi(ChannelTrees), Accounts)
            end}.

channel_close_solo_next(S, _Value, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx] = Args) ->
    case channel_close_solo_valid(S, Args) of
        false -> S;
        true  ->
            From = case Party of initiator -> Initiator; responder -> Responder end,
            #{fee := Fee} = Tx,
            reserve_fee(Fee,
            bump_and_charge(From, Fee, close_channel(ChannelId, solo, S)))
    end.

channel_close_solo_features(S, [_Height, _Channeld, _Party, _Tx] = Args, Res) ->
    Correct = channel_close_solo_valid(S, Args),
    [{correct, if Correct -> channel_close_solo; true -> false end},
     {channel_close_solo, Res}].


%% --- Operation: channel_settle ---
channel_settle_pre(S) ->
    maps:get(channels, S, []) /= [].

channel_settle_args(#{height := Height} = S) ->
    ?LET({CId = {Initiator, _, Responder}, Party},
         {gen_state_channel_id(S, fun(C) ->
                                          case C#channel.closed of {solo, _} -> true; _ -> false end
                                  end), gen_party()},
         begin
             From = case Party of initiator -> Initiator; responder -> Responder end,
             [IAmount, RAmount] =
                 case channel(S, CId) of
                     false -> [nat(), nat()];
                     Channel ->
                         case Channel#channel.trees of
                             {valid, Accounts} ->
                                 {account, _, InA} = lists:keyfind(Initiator, 2, Accounts),
                                 {account, _, ReA} = lists:keyfind(Responder, 2, Accounts),
                                 [ frequency([{30, InA}, {1, InA - 10}, {1, InA + 10}]),
                                   frequency([{30, ReA}, {1, ReA - 10}, {1, ReA + 10}])];
                             _ ->
                                 %% this is also invalid (unless in very unlikely case)
                                 [Channel#channel.amount, Channel#channel.reserve]
                         end
                 end,
             [Height, CId, Party,
              #{from_id => aeser_id:create(account, From),
                initiator_amount_final => IAmount,
                responder_amount_final => RAmount,
                fee => gen_fee(Height),
                nonce => gen_nonce(account(S, From))
               }]
         end).

channel_settle_pre(S, [Height, {I, _, R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    correct_height(S, Height) andalso valid_nonce(S, From, Tx).

channel_settle_valid(S, [Height, {Initiator, _, Responder} = ChannelId, Party, Tx]) ->
    From = case Party of initiator -> Initiator; responder -> Responder end,
    is_account(S, From)
    andalso is_channel(S, ChannelId)
    andalso correct_nonce(S, From, Tx)
    andalso valid_fee(Height, Tx)
    andalso is_valid_unlock_solo(S, channel(S, ChannelId))
    andalso is_valid_split(channel(S, ChannelId), Tx)
    andalso check_balance(S, From, maps:get(fee, Tx)).


is_valid_split(#channel{ id = {I, _, R}, amount = Amount,
                         trees = {valid, Accounts}},
               #{initiator_amount_final := IAmount,
                 responder_amount_final := RAmount}) ->
    {account, _, InA} = lists:keyfind(I, 2, Accounts),
    {account, _, ReA} = lists:keyfind(R, 2, Accounts),
    InA == IAmount andalso ReA == RAmount andalso ReA + InA =< Amount;
is_valid_split(_, _Tx) ->
    false.


is_valid_unlock_solo(S, C) ->
    case C#channel.closed of
        {solo, H} -> H + C#channel.lock_period =< maps:get(height, S);
        _ -> false
    end.

channel_settle_adapt(#{height := Height} = S, [_, {I, _ ,R}, Party, Tx]) ->
    From = case Party of initiator -> I; responder -> R end,
    Channels = [ C || C <- maps:get(channels, S, []), element(1, C#channel.id) == I,
                  element(3, C#channel.id) == R],
    case Channels of
        [] -> false;
        _ ->
            ?LET(Channel, elements(Channels),
                 [Height, Channel#channel.id, Party, adapt_nonce(S, From, Tx)])
    end;
channel_settle_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

channel_settle(Height, Channeld, Party, Tx) ->
    NewTx = channel_settle_tx(Channeld, Party, Tx),
    apply_transaction(Height, aesc_settle_tx, NewTx).

channel_settle_tx({Initiator, N, Responder}, _Party, Tx) ->
    Tx#{channel_id =>
            aeser_id:create(channel, aesc_channels:pubkey(Initiator, N, Responder))}.

channel_settle_next(S, _Value, [_Height, {Initiator, _, Responder} = ChannelId, Party, Tx] = Args) ->
    case channel_settle_valid(S, Args) of
        false -> S;
        true  ->
            From = case Party of initiator -> Initiator; responder -> Responder end,
            #{fee := Fee,  initiator_amount_final := IAmount, responder_amount_final := RAmount} = Tx,
            Locked = (channel(S, ChannelId))#channel.amount - (IAmount + RAmount),
            reserve_fee(Fee,
            credit(Initiator, IAmount,
            credit(Responder, RAmount,
                   close_channel(ChannelId, {settle, Locked},
                                 bump_and_charge(From, -Fee, S)))))
    end.

channel_settle_features(S, [_Height, _Channeld, _Party, _Tx] = Args, Res) ->
    Correct = channel_settle_valid(S, Args),
    [{correct, if Correct -> channel_settle; true -> false end},
     {channel_settle, Res}].


%% --- Operation: ns_preclaim ---

ns_preclaim_pre(S) ->
    maps:is_key(accounts, S).

ns_preclaim_args(#{height := Height} = S) ->
     ?LET([{SenderTag, Sender}, Name, Salt],
          [gen_account(1, 49, S), gen_name(), gen_salt()],
          [Height, {SenderTag, Sender#account.key}, {Name, Salt},
           #{account_id => aeser_id:create(account, Sender#account.key),
             fee => gen_fee(Height),
             commitment_id =>
                 aeser_id:create(commitment,
                               aens_hash:commitment_hash(Name, Salt)),
             nonce => gen_nonce(Sender)}]).

ns_preclaim_pre(S, [Height, {_, Sender}, {Name, Salt}, Tx]) ->
    %% Let us not test the unlikely case that someone provides the same name with the same salt
    [present || #preclaim{name = N, salt = St} <- maps:get(preclaims, S, []), N == Name, St == Salt] == []
        andalso aeser_id:create(commitment, aens_hash:commitment_hash(Name, Salt)) == maps:get(commitment_id, Tx)
        andalso correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

ns_preclaim_valid(S, [Height, {_, Sender}, {_Name, _Salt}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso valid_fee(Height, Tx)
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
                                 claimer = Sender,
				 protocol = aec_hard_forks:protocol_effective_at_height(Height)},
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
ns_claim_args(S = #{height := Height}) ->
     ?LET({Name, Salt, {SenderTag, Sender}}, gen_preclaim(S),
          [Height, {SenderTag, Sender#account.key},
           #{account_id => aeser_id:create(account, Sender#account.key),
             name => Name,
             name_salt => Salt,
             fee => gen_fee(Height),
             nonce => gen_nonce(Sender)}]).


ns_claim_pre(S, [Height, {_STag, Sender}, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

ns_claim_valid(S, [Height, {_, Sender}, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + aec_governance:name_claim_locked_fee())
    andalso valid_fee(Height, Tx)
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
                            expires_by   = Height + aec_governance:name_claim_max_expiration() + 1,
                            claimer      = Sender,
			    protocol = aec_hard_forks:protocol_effective_at_height(Height) },
            remove_preclaim(Tx,
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee + aec_governance:name_claim_locked_fee(),
                add(claims, Claim, S))))
    end.

ns_claim_features(S, [Height, {_, _Sender}, Tx] = Args, Res) ->
    Correct = ns_claim_valid(S, Args),
    [{correct, if Correct -> ns_claim; true -> false end},
     {ns_claim, Res}] ++
  	[ {protocol, ns_claim,
 	   aec_hard_forks:protocol_effective_at_height(Height) -
	       get_preclaim_protocol(Tx,S)} ||
 	    Correct ].

%% --- Operation: claim_update ---
ns_update_pre(S) ->
    maps:is_key(accounts, S).

ns_update_args(#{height := Height} = S) ->
     ?LET({{Name, {SenderTag, Sender}}, Pointers},
          {gen_name_claim(S), gen_pointers(S)},
          [Height, Name, {SenderTag, Sender#account.key}, Pointers,
           #{account_id => aeser_id:create(account, Sender#account.key),
             name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
             name_ttl => frequency([{10, nat()}, {1, 36000}, {10, 25000}, {1, choose(30000, 60000)}]),
             client_ttl => nat(),
             fee => gen_fee(Height),
             nonce => gen_nonce(Sender),
             pointers =>
                 [ case Kind of
                       account -> aens_pointer:new(<<"account_pubkey">>, aeser_id:create(account, Key));
                       oracle -> aens_pointer:new(<<"oracle">>, aeser_id:create(oracle, Key));
                       fake -> aens_pointer:new(<<"fake">>, aeser_id:create(account, Key))
                               %% We need create. Otherwise crashes for unknown types, because specialize type in aeser_id is used.
                               %% This means that such a transaction cannot be created (which makes sense if serialization of it is undefined
                   end || {Kind, Key} <- Pointers ]
            }]).

gen_pointers(S) ->
    ?LET(Pointers, [?LET({Kind, {_, NameAccount}},
                         oneof([{account, gen_account(1, 5, S)}, {oracle, gen_oracle_account(S)}]),
                         {Kind, NameAccount#account.key}), {fake, binary(32)}, {fake, binary(32)}],
        sublist(Pointers)).

ns_update_pre(S, [Height, Name, {_, Sender}, _Pointers, Tx]) ->
    aeser_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

ns_update_valid(S, [Height, Name, {_, Sender}, _Pointers, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + aec_governance:name_claim_locked_fee())
    andalso valid_fee(Height, Tx)
    andalso maps:get(name_ttl, Tx) =< aec_governance:name_claim_max_expiration()
    andalso owns_name(S, Sender, Name)
    andalso is_valid_name(S, Name, Height).

ns_update_adapt(#{height := Height} = S, [_Height, Name, {SenderTag, Sender}, Pointers, Tx]) ->
    [Height, Name, {SenderTag, Sender}, Pointers, adapt_nonce(S, Sender, Tx)];
ns_update_adapt(_, _) ->
    false.

ns_update(Height, _Name, _Sender, _Pointers, Tx) ->
    apply_transaction(Height, aens_update_tx, Tx).

ns_update_next(S, _, [Height, Name, {_, Sender}, Pointers, Tx] = Args) ->
    case ns_update_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, name_ttl := TTL } = Tx,
            S1 = case Pointers of
                    [] -> remove_named_account(Name, S);
                    _  -> add_named_account(Name, Pointers, S)
                 end,
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                update_claim_height(Name, Height, TTL, S1)))
    end.

ns_update_features(S, [_Height, _Name, _Sender, Pointers, _Tx] = Args, Res) ->
    Correct = ns_update_valid(S, Args),
    [{correct, if Correct -> ns_update; true -> false end},
     {ns_update, Res}] ++
        [{ns_update, [ Kind || {Kind, _} <- Pointers]}].

%% --- Operation: ns_revoke ---
ns_revoke_pre(S) ->
    maps:is_key(accounts, S).

ns_revoke_args(#{height := Height} = S) ->
     ?LET({Name, {SenderTag, Sender}}, gen_name_claim(S),
          [Height, {SenderTag, Sender#account.key}, Name,
           #{account_id => aeser_id:create(account, Sender#account.key),
             name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
             fee => gen_fee(Height),
             nonce => gen_nonce(Sender)
            }]).

ns_revoke_pre(S, [Height, {_, Sender}, Name, Tx]) ->
    aeser_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

ns_revoke_valid(S, [Height, {_SenderTag, Sender}, Name, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
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

ns_revoke_features(S, [Height, {_SenderTag, Sender}, Name, _Tx] = Args, Res) ->
    Correct = ns_revoke_valid(S, Args),
    [{correct, if Correct -> ns_revoke; true -> false end},
     {ns_revoke, Res}] ++
  	[ {protocol, ns_revoke,
 	   aec_hard_forks:protocol_effective_at_height(Height) -
	       get_claim_protocol({Name, Sender}, S)} ||
 	    Correct
	].


%% --- Operation: ns_transfer ---
ns_transfer_pre(S) ->
    maps:is_key(accounts, S).

ns_transfer_args(#{height := Height} = S) ->
    ?LET({{Name, {SenderTag, Sender}}, {ReceiverTag, Receiver}},
         {gen_name_claim(S), gen_account(1, 49, S)},
         ?LET(To, oneof([account, {name, elements(maps:keys(maps:get(named_accounts, S, #{})) ++ [<<"ta.test">>])}]),
              [Height, {SenderTag, Sender#account.key},
               case To of
                   account -> {ReceiverTag, Receiver#account.key};
                   {name, ToName} -> {name, ToName}
               end, Name,
               #{account_id => aeser_id:create(account, Sender#account.key),  %% The sender is asserted to never be a name.
                 recipient_id =>
                     case To of
                         account ->
                             aeser_id:create(account, Receiver#account.key);
                         {name, ToName} ->
                             aeser_id:create(name, aens_hash:name_hash(ToName))
                     end,
                 name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
                 fee => gen_fee(Height),
                 nonce => gen_nonce(Sender)
                }])).

ns_transfer_pre(S, [Height, {STag, Sender}, Receiver, Name, Tx]) ->
    aeser_id:create(name, aens_hash:name_hash(Name)) == maps:get(name_id, Tx)
        andalso correct_height(S, Height)
        andalso valid_nonce(S, Sender, Tx)
        andalso valid_account(S, STag, Sender) andalso valid_account(S, Receiver).

ns_transfer_valid(S, [Height, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Name, Tx]) ->
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
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

%% --- Operation: create_contract ---
contract_create_pre(S) ->
    %% for testing against old version, put hard-fork height to large number and use:
    %% #{<<"2">> := Fork} = application:get_env(aecore, hard_forks),
    %%  maps:get(height, S) < Fork andalso
    maps:is_key(accounts, S) andalso maps:get(height, S) > 0.


contract_create_args(#{height := Height} = S) ->
     ?LET({SenderTag, Sender}, gen_account(1, 100, S),
          ?LET(Name, gen_contract(),
               begin
                   #{gasfun := GasFun, basefee := Fixed} = contract(Name),
                   [Height, {SenderTag, Sender#account.key}, Name,
                    frequency([{10, 1}, {30, 2}]),
                    #{owner_id => aeser_id:create(account, Sender#account.key),
                      vm_version  => frequency([{1, elements([0,5])}, {max(10, Height), aevm_sophia_1},
                                                {2, vm_solidity}, {50, aevm_sophia_2}]),
                      abi_version => weighted_default({49, 1}, {1, elements([0,3])}),
                      fee => gen_fee_above(Height, Fixed),
                      gas_price => frequency([{1,0}, {10, 1}, {89, minimum_gas_price(Height)}]),
                      gas => frequency([{7, GasFun(Height)}, {1, GasFun(Height) - 1}, {1, GasFun(Height) + 100}, {1, 10}]),
                      nonce => gen_nonce(Sender),
                      deposit => nat(),
                      amount => gen_spend_amount(Sender)
                     }]
               end)).

contract_create_pre(S, [Height, {_, Sender}, _, _, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Sender, Tx).

contract_create_valid(S, [Height, {_, Sender}, Name, CompilerVersion, Tx]) ->
    #{gasfun := GasFun, basefee := Fixed} = contract(Name),
    Protocol = aec_hard_forks:protocol_effective_at_height(Height),
    is_account(S, Sender)
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + GasFun(Height) * maps:get(gas_price, Tx) +
                              maps:get(amount, Tx) + maps:get(deposit, Tx))
    andalso valid_contract_fee(Height, Fixed, Tx)
    andalso if Protocol == 1 ->
                    lists:member({maps:get(vm_version, Tx), maps:get(abi_version, Tx)},
                                 [{aevm_sophia_1, 1}]);  %% second compiler could create VM1 code ?
               Protocol == 2 ->
                    lists:member({maps:get(vm_version, Tx), maps:get(abi_version, Tx)},
                                 [{aevm_sophia_2, 1}]);
               Protocol == 3 ->
                    lists:member({maps:get(vm_version, Tx), maps:get(abi_version, Tx)},
                                 [{aevm_sophia_3, 1}, {aevm_sophia_2, 1}])
            end
    andalso lists:member(CompilerVersion,
                             [ 1 || Protocol >= 1] ++
                             [ 2 || Protocol >= 2]).

contract_create_adapt(#{height := Height} = S, [_, {STag, Sender}, Contract, CompilerVersion, Tx]) ->
    [Height, {STag, Sender}, Contract, CompilerVersion, adapt_nonce(S, Sender, Tx)];
contract_create_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

contract_create(Height, {_, _Sender}, Name, CompilerVersion, Tx) ->
    NewTx = contract_create_tx(Name, CompilerVersion, Tx),
    apply_transaction(Height, aect_create_tx, NewTx).

contract_create_tx(Name, CompilerVersion, Tx) ->
    #{src := Contract, args := Args} = CompiledContract = contract(Name),
    {ok, CallData} = aect_sophia:encode_call_data(Contract, <<"init">>, Args),
    Code = maps:get({code, CompilerVersion}, CompiledContract),
    NTx = maps:update_with(vm_version, fun(aevm_sophia_1) -> 1;
                                          (vm_solidity) -> 2;
                                          (aevm_sophia_2) -> 3;
                                          (aevm_sophia_3) -> 4;
                                          (N) when is_integer(N), N >= 0 -> N
                                       end, Tx),
    NTx#{code => Code, call_data => CallData}.

%% Since the nonce is part of the contract ID, shrinking a contract create could possibly work, but then it will
%% no longer be called by a contract call, since the create ID has changed!
contract_create_next(S, _Value, [Height, {_, Sender}, Name,
                                 CompilerVersion, Tx] = Args) ->
    case contract_create_valid(S, Args) of
        false -> S;
        true  ->
            #{gasfun := GasFun, src := Source, functions := Funs} = contract(Name),
            #{ fee := Fee, gas_price := GasPrice, amount := Amount,
               deposit := Deposit, gas := Gas, vm_version := Vm, abi_version := Abi} = Tx,
            case Gas >= GasFun(Height) of
                true ->
                    ContractId = {call, aect_contracts, compute_contract_pubkey, [Sender, maps:get(nonce, untag_nonce(Tx))]},
                    reserve_fee(Fee + GasFun(Height) * GasPrice,
                                bump_and_charge(Sender,
                                                Fee + GasFun(Height) * GasPrice + Amount + Deposit,
                                                add(contracts,
                                                    #contract{name = Name,
                                                              id = ContractId,
                                                              amount = Amount,
                                                              deposit = Deposit,
                                                              vm = Vm,
                                                              abi = Abi,
                                                              compiler_version = CompilerVersion,
                                                              src = Source,
                                                              functions = Funs,
                                                              protocol = aec_hard_forks:protocol_effective_at_height(Height)}, S)));
                false ->
                    %% out of gas
                    reserve_fee(Fee + Gas * GasPrice,
                                bump_and_charge(Sender,
                                                Fee + Gas * GasPrice,
                                                S))
            end
    end.

contract_create_features(S, [Height, {_, _Sender}, Name, CompilerVersion, Tx] = Args, Res) ->
    #{gasfun := GasFun} = contract(Name),
    Correct = contract_create_valid(S, Args) andalso maps:get(gas, Tx) >= GasFun(Height),
    [{correct, if Correct -> contract_create; true -> false end},
     {contract_create, Res},
     {contract_create, compiler, CompilerVersion}].

%% --- Operation: call_contract ---
contract_call_pre(S) ->
    maps:is_key(accounts, S) andalso maps:get(contracts, S) /= [].

%% Given https://github.com/aeternity/protocol/blame/44b459970144fb030df55e32b166a9d62a79b523/contracts/contract_vms.md#L23
%% I would expect vm_version to be present either in ct_version form or as separate key
%% But not so in aect_call_tx
%% Most likely determined by the contract's VM version!
contract_call_args(#{height := Height, contracts := Contracts} = S) ->
     ?LET([{SenderTag, Sender}, {ContractTag, Contract}],
          [gen_account(1, 100, S), gen_contract_id(1, 100, Contracts)],
          ?LET({Func, As, UseGas, _},
               case ContractTag of
                   invalid -> {<<"main">>, [], 1, <<>>};
                   _ -> oneof(Contract#contract.functions)
               end,
               [Height, {SenderTag, Sender#account.key}, {ContractTag, Contract},
                #{caller_id => aeser_id:create(account, Sender#account.key),   %% could also be a contract!
                  contract_id =>
                      case ContractTag of
                          {name, Name} -> aeser_id:create(name, aens_hash:name_hash(Name));
                          _ -> aeser_id:create(contract, Contract#contract.id)   %% handles symbolic calls!
                      end,
                  abi_version => weighted_default({49, Contract#contract.abi}, {1, elements([0,3])}),
                  fee => gen_fee_above(Height, call_base_fee(As)),
                  gas_price => frequency([{1,0}, {10, 1}, {89, minimum_gas_price(Height)}]),
                  gas => frequency([{7, UseGas},
                                    %% {1, UseGas-1},
                                    {1, 2*UseGas}, {1, 1}]),
                  nonce => gen_nonce(Sender),
                  amount => nat(),
                  call_data => {Func, As, UseGas}
                 }])).

call_base_fee(As) ->
    aec_governance:tx_base_gas(contract_call_tx) + 5000 + 32 * length(As).

contract_call_pre(S, [Height, {_, Sender}, {ContractTag, Contract}, Tx]) ->
    correct_height(S, Height) andalso valid_nonce(S, Sender, Tx) andalso
        (ContractTag == invalid  orelse lists:member(Contract#contract.id, [ C#contract.id || C <- maps:get(contracts, S) ])).

contract_call_valid(S, [Height, {_, Sender}, {ContractTag, _Contract}, Tx]) ->
    #{call_data := {_, As, _}} = Tx,
    is_account(S, Sender)
    andalso ContractTag == valid
    andalso correct_nonce(S, Sender, Tx)
    andalso check_balance(S, Sender, maps:get(fee, Tx) + maps:get(gas, Tx) * maps:get(gas_price, Tx))
    andalso valid_contract_fee(Height, call_base_fee(As), Tx)
    andalso maps:get(abi_version, Tx) == 1.

contract_call_adapt(#{height := Height} = S, [_, {STag, Sender}, Contract, Tx]) ->
    [Height, {STag, Sender}, Contract, adapt_nonce(S, Sender, Tx)];
contract_call_adapt(_, _) ->
    %% in case we don't even have a Height
    false.

contract_call(Height, _, Contract, Tx) ->
    NewTx = contract_call_tx(Contract, Tx),
    apply_transaction(Height, aect_call_tx, NewTx).

contract_call_tx({invalid, _Contract}, Tx) ->
    Tx#{call_data => <<"Blubber">>};
contract_call_tx({valid, Contract}, #{call_data := {Func, As, _}} = Tx) ->
    ContractSrc = Contract#contract.src,
    BinaryAs = [ to_binary(A) || A <- As],
    {ok, CallData} = aect_sophia:encode_call_data(ContractSrc, Func, BinaryAs),
    Tx#{call_data => CallData}.

to_binary(B) when is_binary(B) ->
    B;
to_binary(I) when is_integer(I) ->
    integer_to_binary(I);
to_binary(Other) ->
    error({cannot_convert, Other}).


contract_call_next(S, _Value, [_Height, {_, Sender}, _Contract, Tx] = Args) ->
    case contract_call_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, gas_price := GasPrice, amount := Amount,
               gas := Gas, call_data := {_Func, _As, UseGas}} = Tx,
            case Gas >= UseGas of
                true ->
                    %% ContractId = compute_contract_pubkey(Sender, maps:get(nonce, untag_nonce(Tx))),
                    reserve_fee(Fee + UseGas * GasPrice,
                                bump_and_charge(Sender,
                                                Fee + UseGas * GasPrice + Amount,
                                                S));
                false ->
                    %% out of gas
                    reserve_fee(Fee + Gas * GasPrice,
                                bump_and_charge(Sender,
                                                Fee + Gas * GasPrice,
                                                S))
            end
    end.

contract_call_features(S, [Height, {_, _Sender}, {_ContractTag, Contract}, Tx] = Args, Res) ->
    Correct = contract_call_valid(S, Args),
    #{gas := Gas, call_data := {Func, _As, UseGas}} = Tx,
    [{correct, if Correct -> contract_call; true -> false end}] ++
     [{contract_call_fun, Contract#contract.name} || Correct andalso Gas >= UseGas ] ++
     [{contract_call, Res}] ++
        [ {protocol, contract_call, Func, aec_hard_forks:protocol_effective_at_height(Height) - Contract#contract.protocol} ||
            Correct andalso Gas >= UseGas ].




%% -- Property ---------------------------------------------------------------
weight(_S, spend) -> 10;
weight(S, newkey) -> max(1, 5 - maps:size(maps:get(keys, S)));
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
        Channels  -> 3 * (length([ 1 || #channel{closed = false} <- Channels]) + 1)
    end;
weight(S, channel_withdraw) ->
    case maps:get(channels, S, []) of
        [] -> 0;
        Channels  -> 3 * (length([ 1 || #channel{closed = false} <- Channels]) + 1)
    end;
weight(S, channel_close_mutual) ->
    case maps:get(channels, S, []) of
        [] -> 0;
        Channels  -> 3 * (length([ 1 || #channel{closed = false} <- Channels]) + 1)
    end;
weight(S, channel_close_solo) ->
    case  [ C || #channel{closed = false} = C <-maps:get(channels, S, []) ] of
        [] -> 0;
        Channels  -> 5 * length(Channels)
    end;
weight(S, channel_settle) ->
    case [ H + P || #channel{closed = {solo, H}, lock_period = P} <- maps:get(channels, S, []) ] of
        [] -> 0;
        Hs -> 5 * (length([ He || He <- Hs, maps:get(height, S, 0) >= He ]) + 1)
    end;
weight(_S, contract_create) ->
    10;
weight(S, contract_call) ->
    case maps:get(contracts, S, []) of
        [] -> 0;
        _  -> 10 end;
weight(_S, _) -> 0.


compile_contracts() ->
    %% read and compile contracts once (and use them in parallel
    catch ets:delete(contracts),
    ets:new(contracts, [{read_concurrency, true}, named_table]),
    [ ets:insert(contracts, {maps:get(name, C), C}) || C <- contracts() ].


prop_txs() ->
    prop_txs(3).

prop_txs(Fork) ->
    application:load(aesophia),  %% Since we do in_parallel, we may have a race in line 86 of aesophia_compiler
    propsetup(Fork,
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
        FeeTotal = lists:sum([ Fee || {Fee, _} <- maps:get(fees, S, [])]),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            features(call_features(H),
            aggregate_feats([atoms, correct, protocol, contract_call_fun | all_command_names()], call_features(H),
                ?WHENFAIL(eqc:format("Total = ~p~nFeeTotal = ~p~n", [TreesTotal, FeeTotal]),
                          pretty_commands(?MODULE, Cmds, {H, S, Res},
                              conjunction([{result, Res == ok},
                                           {total, Total == 0 orelse equals(Total, ?PatronAmount - FeeTotal)}]))))))))
    end)))).

aggregate_feats([], [], Prop) -> Prop;
aggregate_feats([atoms | Kinds], Features, Prop) ->
    {Atoms, Rest} = lists:partition(fun is_atom/1, Features),
    aggregate(with_title(atoms), Atoms, aggregate_feats(Kinds, Rest, Prop));
aggregate_feats([Tag | Kinds], Features, Prop) ->
    {Tuples, Rest} = lists:partition(fun(X) -> is_tuple(X) andalso element(1, X) == Tag end, Features),
    aggregate(with_title(Tag), [ case tl(tuple_to_list(Tuple)) of
                                     [A] -> A;
                                     L -> list_to_tuple(L)
                                 end || Tuple <- Tuples ], aggregate_feats(Kinds, Rest, Prop)).

%% -- State update and query functions ---------------------------------------

lookup_name(S, Name) ->
    case lists:keyfind(account, 1, maps:get(Name, maps:get(named_accounts, S, #{}))) of
        {_, Key} -> Key;
        false -> false
    end.

resolve_account(S, {name, Name}) -> lookup_name(S, Name);
resolve_account(_, {contract, Key}) -> {contract, Key};
resolve_account(_, {_, Key})     -> Key.

account_key(#account{key = Key}) ->
    Key.

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

update_contract_id(OldId, NewId, S) ->
    Fun = fun(C) -> C#contract{id = NewId} end,
    on_contract(OldId, Fun, S).

credit_amount(Id, Credit, S) ->
    Fun = fun(C) -> C#contract{amount = C#contract.amount + Credit} end,
    on_contract(Id, Fun, S).

on_contract(Id, Fun, S = #{contracts := Contracts}) ->
    Upd = fun(C = #contract{ id = I }) when I == Id -> Fun(C);
             (C) -> C end,
    S#{ contracts => lists:map(Upd, Contracts) }.

oracle_ext(Id, Delta, S) ->
    Fun = fun(O) -> O#oracle{oracle_ttl = O#oracle.oracle_ttl + Delta} end,
    on_oracle(Id, Fun, S).
remove(Tag, X, I, S) ->
    S#{ Tag := lists:keydelete(X, I, maps:get(Tag, S)) }.

update_oracle_id(OldId, NewId, S) ->
    on_oracle(OldId, fun(O) -> O#oracle{id = NewId} end, S).

on_oracle(Id, Fun, S = #{ oracles := Oracles }) ->
    Upd = fun(C = #oracle{id = I}) when I == Id -> Fun(C);
             (C) -> C end,
    S#{ oracles => lists:map(Upd, Oracles) }.

remove_query(Id, S) ->
    remove(queries, Id, #query.id, S).

remove_preclaim(#{name := Na, name_salt := Sa}, S = #{preclaims := Ps}) ->
    S#{preclaims := [ P || P = #preclaim{name = Na0, salt = Sa0} <- Ps,
                           Na0 /= Na orelse Sa0 /= Sa ]}.

get_preclaim_protocol(#{name := Na, name_salt := Sa}, #{preclaims := Ps}) ->
    hd([P#preclaim.protocol || P = #preclaim{name = Na0, salt = Sa0} <- Ps,
	   Na0 == Na andalso Sa0 == Sa]).

get_claim_protocol({Na, Sender}, #{claims := Cs}) ->
    hd([C#claim.protocol || C = #claim{name = Na0, claimer = Sa0} <- Cs,
	   Na0 == Na andalso Sa0 == Sender]).

get(S, Tag, Key, I) ->
    lists:keyfind(Key, I, maps:get(Tag, S)).

get_query(S, Id) ->
    get(S, queries, Id, #query.id).

update_query_id(OldId, NewId, S) ->
    on_query(OldId, fun(Q) -> Q#query{ id = NewId } end, S).

on_query(Id, Fun, S = #{ queries := Queries }) ->
    Upd = fun(C = #query{ id = I }) when I == Id -> Fun(C);
             (C) -> C end,
    S#{ queries => lists:map(Upd, Queries) }.

on_channel(Id, Fun, S) ->
    Channels = maps:get(channels, S, []),
    Upd = fun(C = #channel{ id = I }) when I == Id -> Fun(C);
             (C) -> C end,
    S#{ channels => lists:map(Upd, Channels) }.

update_channel_id(OldId, NewId, S) ->
    Fun = fun(C) -> C#channel{id = NewId} end,
    on_channel(OldId, Fun, S).

credit_channel(Id, Round, Amount, S) ->
    on_channel(Id, fun(C) -> C#channel{ amount = C#channel.amount + Amount,
                                        round = Round }
                   end, S).

close_channel(CId, mutual, S) ->
    on_channel(CId, fun(C) -> C#channel{closed = mutual} end, S);
close_channel(CId, solo, S) ->
    on_channel(CId, fun(C) ->
                            C#channel{ closed = {solo, maps:get(height, S)}}
                    end, S);
close_channel(CId, {settle, Locked}, S) ->
    on_channel(CId, fun(C) -> C#channel{amount = Locked, closed = settle} end, S).


transfer_name(NewOwner, Name, S) ->
    on_claim(Name, fun(C) -> C#claim{ claimer = NewOwner } end, S).

on_claim(Name, Fun, S = #{ claims := Claims }) ->
    Upd = fun(C = #claim{ name = N }) when Name == N -> Fun(C);
             (C) -> C end,
    S#{ claims := lists:map(Upd, Claims) }.

update_claim_height(Name, Height, TTL, S) ->
    on_claim(Name, fun(C) -> C#claim{ expires_by = Height + TTL}
                   end, S).

revoke_claim(Name, Height, S) ->
    on_claim(Name, fun(C) ->
                        C#claim{ expires_by = Height - 1}
                           %% trick, after a revoke, the name cannot be used any more on that height or heigher
                    end, S).

remove_named_account(Name, S) ->
    S#{ named_accounts => maps:remove(Name, maps:get(named_accounts, S, #{})) }.

add_named_account(Name, Acc, S) ->
    S#{ named_accounts => maps:merge(maps:get(named_accounts, S, #{}), #{ Name => Acc }) }.

%% --- local helpers ------

is_valid_name(#{claims := Names}, Name, Height) ->
    case lists:keyfind(Name, #claim.name, Names) of
        false -> false;
        Claim -> Height =< Claim#claim.expires_by
    end.

is_valid_name_account(#{claims := Names} = S, Name, Height) ->
    case lists:keyfind(Name, #claim.name, Names) of
        false -> false;
        Claim ->
            Height =< Claim#claim.expires_by andalso
                case maps:get(Name, maps:get(named_accounts, S, #{}), undefined) of
                    undefined -> false;
                    Pointers -> lists:keyfind(account, 1, Pointers) /= false
                end
    end.

owns_name(#{claims := Names, height := Height}, Who, Name) ->
    case lists:keyfind(Name, #claim.name, Names) of
        false -> false;
        Claim -> Claim#claim.claimer == Who
                 andalso Claim#claim.expires_by >= Height
    end.

correct_name_id(Name, NameId) ->
    aeser_id:create(name, aens_hash:name_hash(Name)) == NameId.

is_account(#{accounts := Accounts}, Key) ->
    lists:keymember(Key, #account.key, Accounts).

valid_account(S, Tag, Key) -> valid_account(S, {Tag, Key}).
valid_account(_S, {name, _}) -> true;
valid_account(S, {Tag, Key}) ->
    IsA = is_account(S, Key),
    (IsA andalso Tag == existing) orelse (not IsA andalso Tag == new).

is_oracle(#{oracles := Oracles}, OracleId) ->
    lists:keymember(OracleId, #oracle.id, Oracles).

oracle(#{oracles := Oracles}, OracleId) ->
    lists:keyfind(OracleId, #oracle.id, Oracles).

oracle_query_fee(S, OracleId) ->
    Oracle = oracle(S, OracleId),
    Oracle#oracle.qfee.

oracle_ttl(S, OracleId) ->
    Oracle = oracle(S, OracleId),
    Oracle#oracle.oracle_ttl.

query_response_ttl(#{queries := Queries}, QueryId) ->
    Query = lists:keyfind(QueryId, #query.id, Queries),
    Query#query.response_ttl.

query_query_ttl(#{queries := Queries}, QueryId) ->
    Query = lists:keyfind(QueryId, #query.id, Queries),
    Query#query.query_ttl.

is_query(#{queries := Qs}, Q) ->
    lists:keymember(Q, #query.id, Qs).

valid_contract_fee(H, Fixed, #{ fee := Fee, gas_price := GasPrice }) ->
    GasPrice >= minimum_gas_price(H)
        andalso Fee >= Fixed * minimum_gas_price(H).

valid_solo_close_fee(H, #{ fee := Fee }) ->
    Fee >= (20000 + 3000) * minimum_gas_price(H).

valid_fee(H, #{ fee := Fee }) ->
    Fee >= 20000 * minimum_gas_price(H).   %% not precise, but we don't generate fees in the shady range

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

adapt_poi(Channel, Tx) ->
    case maps:get(poi, Tx) of
        {valid, _} ->
            Tx#{poi => Channel#channel.trees};
        _Invalid ->
            Tx
    end.


adapt_state_hash(Channel, _From, _Amount, Tx) ->
    case maps:get(state_hash, Tx) of
        {valid, _} ->
            Tx#{state_hash => Channel#channel.trees};
        _Invalid ->
            Tx
    end.

adapt_account(Accounts, From, Amount) ->
    [ {account, Key,
       case Key == From of
           true -> max(0, Amt + Amount);   %% Amount can ne negative, but result always >= 0
           false -> Amt
       end} || {account, Key, Amt} <- Accounts].


check_balance(S, Key, Amount) ->
     (account(S, Key))#account.amount >= Amount.

account(#{accounts := Accounts}, Key) ->
    lists:keyfind(Key, #account.key, Accounts).

is_channel(S, CId) ->
    channel(S, CId) /= false.

channel(#{channels := Cs}, CId) ->
    lists:keyfind(CId, #channel.id, Cs).

correct_round(S, CId, #{round := Round}) ->
    (channel(S, CId))#channel.closed == false andalso
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


apply_transaction(Height, TxMod, TxArgs) ->
    Env      = aetx_env:tx_env(Height),
    Trees    = get(trees),
    Tx       = create_aetx(TxMod, TxArgs),

    case aetx:process(Tx, Trees, Env) of
        {ok, NewTrees, _NewEnv} ->
            put(trees, NewTrees),
            ok;
        Other ->
            Other
    end.

create_aetx(TxMod, TxArgs) ->
    {ok, AeTx} = apply(TxMod, new, [untag_nonce(TxArgs)]),
    AeTx.

untag_nonce(M = #{nonce := {_Tag, N}}) -> M#{nonce := N};
untag_nonce(M)                         -> M.

trees_with_accounts(Accounts) ->
    trees_with_accounts(Accounts, aec_trees:new_without_backend()).

trees_with_accounts([], Trees) ->
    Trees;
trees_with_accounts([{account, Acc, Amount}|Rest], Trees) ->
    Account = aec_accounts:new(Acc, Amount),
    AccountTrees = aec_accounts_trees:enter(Account, aec_trees:accounts(Trees)),
    trees_with_accounts(Rest, aec_trees:set_accounts(Trees, AccountTrees)).


%% -- Generators -------------------------------------------------------------


gen_account(New, Exist, #{accounts := Accounts, keys := Keys}) ->
    case [ Key || Key <- maps:keys(Keys), not lists:keymember(Key, #account.key, Accounts) ] of
        [] ->
            {existing, elements(Accounts)};
        NewKeys ->
            weighted_default(
              {Exist, {existing, elements(Accounts)}},
              {New,   {new, #account{key = oneof(NewKeys),  %% do not shrink (cannot become un-new either)
                                     amount = 0, nonce = 0 }}})
    end.

gen_oracle_account(#{oracles := []} = S) ->
    gen_account(1, 1, S);
gen_oracle_account(#{accounts := As, oracles := Os} = S) ->
    weighted_default(
        {39, ?LET(#oracle{id = Id}, elements(Os), {existing, lists:keyfind(Id, #account.key, As)})},
        {1,  gen_account(9, 1, S)}).


gen_new_oracle_account(S) ->
    case non_oracle_accounts(S) of
        [] -> gen_account(1, 1, S); %% We can't get a good one, fail evenly
        GoodAs ->
            weighted_default({29, {existing, elements(GoodAs)}},
                             {1,  gen_account(1, 9, S)})
    end.

gen_preclaim(#{preclaims := []} = S) ->
    {gen_name(), gen_salt(), gen_account(1, 1, S)};
gen_preclaim(#{preclaims := Ps, accounts := As} = S) ->
    weighted_default(
        {39, ?LET(#preclaim{name = N, salt = Salt, claimer = C}, elements(Ps),
                  begin
                    A = {existing, lists:keyfind(C, #account.key, As)},
                    frequency([{1, {N, Salt+1, A}}, {1, {gen_name(), Salt, A}}, {37, {N, Salt, A}}])
                  end)},
        {1, {gen_name(), gen_salt(), gen_account(1, 1, S)}}).

gen_name_claim(#{claims := []} = S) ->
    {gen_name(), gen_account(1, 1, S)};
gen_name_claim(#{claims := Cs, accounts := As} = S) ->
    weighted_default(
        {39, ?LET(#claim{name = N, claimer = C}, elements(Cs),
                  begin
                    A = {existing, lists:keyfind(C, #account.key, As)},
                    frequency([{1, {gen_name(), A}}, {1, {N, gen_account(0, 1, S)}}, {38, {N, A}}])
                  end)},
        {1, {gen_name(), gen_account(1, 1, S)}}).


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

gen_state_channel_id(S) ->
    gen_state_channel_id(S, fun(_) -> true end).

gen_state_channel_id(#{channels := []} = S, _) ->
    ?LET([{_, A1}, {_, A2}], vector(2, gen_account(0, 1, S)),
         {A1#account.key, choose(1, 5), A2#account.key});
gen_state_channel_id(#{channels := Cs} = S, Filter) ->
    Channels = [ Channel || Channel <- Cs, Filter(Channel)],
    frequency([{if Channels /= [] -> 44; true -> 0 end,
                ?LAZY(?LET(C, elements(Channels), C#channel.id))},
               {5,  ?LET(C, elements(Cs), C#channel.id)},
               {1,  gen_state_channel_id(S#{channels := []}, Filter)}]).

gen_party() ->
    elements([initiator, responder]).

gen_channel_round(#{channels := Cs}, CId) ->
    case lists:keyfind(CId, #channel.id, Cs) of
        false -> choose(0, 5);
        #channel{round = R} ->
            weighted_default({29, R+1}, {1, ?LET(R_, elements([R-3, R-1, R, R+3]), abs(R_))})
    end.

gen_state_hash(Accounts) ->
    gen_state_hash_account_keys([ {account, A#account.key, Amount} || {account, A, Amount} <- Accounts ]).

gen_state_hash_account_keys(List) ->
    frequency([{1, {invalid, []}},
               {1, {invalid, [elements(List) || length(List) > 1 ]}},
               {40, {valid, List}}]).


gen_fee(H) ->
    frequency([{29, ?LET(F, choose(20000, 30000), F * minimum_gas_price(H))},
                {1,  ?LET(F, choose(0, 15000), F)},   %%  too low (and very low for hard fork)
                {1,  ?LET(F, choose(0, 15000), F * minimum_gas_price(H))}]).    %% too low

gen_fee_above(H, Amount) ->
    frequency([{29, ?LET(F, choose(Amount, Amount + 10000), F * minimum_gas_price(H))},
                {1,  ?LET(F, choose(0, Amount - 5000), F)},   %%  too low (and very low for hard fork)
                {1,  ?LET(F, choose(0, Amount - 5000), F * minimum_gas_price(H))}]).    %% too low


gen_query_fee() ->
    choose(10, 1000).

gen_query_fee(QF) ->
    weighted_default({29, QF}, {1, elements([QF - 10, QF - 1, QF + 1, QF + 10, QF + 100])}).

gen_query_response_ttl(S, QueryId) ->
    case lists:keyfind(QueryId, #query.id, maps:get(queries, S, [])) of
        false ->
            {delta, nat()};
        Query ->
            frequency([{9, Query#query.response_ttl}, {1, {delta, nat()}}])
    end.

gen_salt() -> choose(270, 280).

gen_channel_amount(H) ->
    ?LET(F, choose(20000, 200000), F * minimum_gas_price(H)).

gen_create_channel_amounts(H) ->
    ?LET({I, R}, {gen_channel_amount(H), gen_channel_amount(H)},
            weighted_default({29, {I, R, min(I, R) - 2000}}, {1, {I, R, gen_channel_amount(H)}})).

gen_close_channel_amounts(#{channels := Cs, height := Height}, CId) ->
    ?LET(Fee, gen_fee(Height),
    case lists:keyfind(CId, #channel.id, Cs) of
        false -> {gen_channel_amount(Height), gen_channel_amount(Height), Fee};
        #channel{amount = A} ->
            weighted_default(
                {5, ?LET({Factor1, Factor2}, {choose(0, 50), choose(0, 50)},
                     begin
                        I = ((A - Fee) * Factor1) div 100,
                        R = ((A - Fee) * Factor2) div 100,
                        {abs(I), abs(R), Fee}
                     end)},
                {1, ?LET({Factor1, Factor2}, {choose(0, 100), choose(0, 100)},
                     begin
                        I = ((A - Fee) * Factor1) div 100,
                        R = ((A - Fee) * Factor2) div 100,
                        {abs(I), abs(R), Fee}
                     end)})
    end).

gen_ttl() ->
    choose(5, 50).

%% Generate a contract
gen_contract() ->
    elements(["identity", "authorize_nonce"]).

contract(Name) ->
    [{_, Map}] = ets:lookup(contracts, Name),
    Map.

%% Add srcs dynamically for the compilers available
contracts() ->
    Static =
        [#{name => "identity",
           args => [],
           gasfun => fun(_) -> 193 end,
           basefee => 75000 + 24000,
           functions => [{<<"main">>, [nat()], 192, <<>>}]
          },
         #{name => "authorize_nonce",
           args => [],
           gasfun => fun(_) -> 275 end,
           basefee => 75000 + 30000,
           auth_fun => <<"nonce_correct">>,
           functions => [{<<"nonce_correct">>, [nat()], 314, <<175,167,108,196,77,122,134,90,197,152,206,179,38,153,
                                                               232,187,88,41,45,167,79,246,181,13,185,101,189,45,109,
                                                               228,184,223>> }]
          }
        ],
    [ begin
          File = filename:join("contracts", maps:get(name, C)),
          {ok, ContractSrc} = aect_test_utils:read_contract(File),
          CompiledCode =
              [ begin
                    {ok, Code} = aect_test_utils:compile_contract(CompilerVersion, File),
                    {{code, CompilerVersion}, Code}
                end || CompilerVersion <- [1, 2] ],
          maps:merge(C#{src => ContractSrc}, maps:from_list(CompiledCode))
      end || C <- Static ].

gen_contract_id(_, _, []) ->
    {invalid, fake_contract_id()};
gen_contract_id(Invalid, Valid, Contracts) ->
    weighted_default({Valid,
                      ?LET(Contract, elements(Contracts),
                           {valid, Contract})
                     },
                     {Invalid, {invalid, fake_contract_id()}}).

gen_map_key(Map) ->
    elements(maps:keys(Map)).

fake_contract_id() ->
    ?LET(Pubkey, noshrink(binary(32)),
         #contract{id = aect_contracts:compute_contract_pubkey(Pubkey, 12),
                   abi = nat(),
                   vm = nat()
                  }).

propsetup(Fork, Prop) ->
    ?SETUP(
    fun() ->
            _ = application:load(aecore),
            compile_contracts(),
            HardForksTeardown = setup_hard_forks(#{<<"1">> => 0, <<"2">> => Fork, <<"3">> => 2*Fork}),
            DataDirTeardown = setup_data_dir(),
            fun() ->
                    DataDirTeardown(),
                    HardForksTeardown()
            end
    end, Prop).

setup_data_dir() ->
    %% make sure we can run in eqc/aecore_eqc
    {ok, Dir} = file:get_cwd(),
    %% Not asserting that configuration parameter is undefined so to ease experimenting in Erlang shell.
    case lists:reverse(filename:split(Dir)) of
        [_, "eqc" | _] ->
            application:set_env(setup, data_dir, "../../data");
        _ ->
            application:set_env(setup, data_dir, "data")
    end,
    fun() ->
            ok = application:unset_env(setup, data_dir)
    end.

setup_hard_forks(X) ->
    %% Not asserting that configuration parameter is undefined so to ease experimenting in Erlang shell.
    ok = application:set_env(aecore, hard_forks, X),
    fun() ->
            ok = application:unset_env(aecore, hard_forks)
    end.
