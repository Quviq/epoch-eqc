%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Thomas Arts
%%% @doc  Modeling oracle transactions
%%%
%%% @end
%%% Created : 23 May 2019 by Thomas Arts

-module(txs_oracles_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-record(query, {sender, symb_id, id, fee, response_ttl, query_ttl, response_due, expired = false}).
-record(oracle, {id, qfee, oracle_ttl}).

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{oracles => []}.


%% -- Common pre-/post-conditions --------------------------------------------

common_postcond(Correct, Res) ->
    case Res of
        {error, _} when Correct -> eq(Res, ok);
        {error, _}              -> true;
        ok when Correct         -> true;
        ok                      -> eq(ok, {error, '_'})
    end.


%% -- Operations -------------------------------------------------------------



%% --- Operation: multi_mine ---
%%
%% The multi mine part that is oracle dependent
%%
%% This will generate warnings:
%%    Warning: multi_mine_next unused (no multi_mine_command or multi_mine_args defined).
%%    Warning: multi_mine_features unused (no multi_mine_command or multi_mine_args defined).
%% Make sure that in the feature we can switch that off.
mine_next(#{height := Height} = S, _Value, [Blocks]) ->
    ExpiredQs = expired_queries(S, Height + Blocks),

%% alreeady Height +1 due to update in core model!!!!
    %% io:format("H: ~p ~p -> Expired ~p\n", [ Height, Blocks, ExpiredQs]),
    lists:foldl(
      fun(Q, NS) ->
              expire_query(Q#query.symb_id,
                 txs_spend_eqc:credit(Q#query.sender, Q#query.fee, NS))
      end, S, ExpiredQs).

mine_features(#{height := Height} = S, [Blocks], _Res) ->
    [{mine, response_ttl} || expired_queries(S, Height + Blocks) =/= [] ].



%% --- Operation: register_oracle ---
register_oracle_pre(S) ->
    maps:is_key(accounts, S).

register_oracle_args(S = #{height := Height}) ->
     ?LET(Sender, gen_non_oracle_account(1, 49, S),
          [Sender,
                #{account_id => aeser_id:create(account, Sender),
                  query_format    => <<"send me any string"/utf8>>,
                  response_format => <<"boolean()"/utf8>>,
                  query_fee       => gen_query_fee(),
                  fee => gen_fee(Height),
                  nonce => gen_nonce(),
                  oracle_ttl => frequency([{9, {delta, 1001}}, {1, {delta, elements([0, 1, 2])}},
                                           {1, {block, choose(0,1000)}}]),
                  abi_version => 0}]).

register_oracle_valid(S = #{height := Height}, [Sender, Tx]) ->
    is_account(S, Sender)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso maps:get(nonce, Tx) == good
    andalso valid_fee(Height, Tx)
    andalso valid_ttl(Height, maps:get(oracle_ttl, Tx))
    andalso (not is_oracle(S, Sender) orelse oracle_ttl(S, Sender) < Height).
    %% Very nice shrinking example if removing 'oracle_ttl(S, Sender) < Height'

register_oracle_tx(S, [Sender, Tx]) ->
    aeo_register_tx:new(update_nonce(S, Sender, Tx)).

register_oracle_next(S = #{height := Height}, _Value, [Sender, Tx] = Args) ->
    case register_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, query_fee := QFee, oracle_ttl := OracleTTL } = Tx,
            Oracle = #oracle{id = Sender, qfee = QFee,
	    	     	     oracle_ttl = delta(Height, OracleTTL)},
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                add(oracles, Oracle,
                remove(oracles, Sender, #oracle.id, S))))
    end.

register_oracle_post(S, Args, Res) ->
    common_postcond(register_oracle_valid(S, Args), Res).


register_oracle_features(S, [_Sender, Tx] = Args, Res) ->
    Correct = register_oracle_valid(S, Args),
    [{correct, if Correct -> register_oracle; true -> false end},
     {register_oracle, Res}] ++
        [ {register_oracle, {ttl, element(1, maps:get(oracle_ttl, Tx))}} || Correct ].

%% --- Operation: extend_oracle ---
extend_oracle_pre(S) ->
    maps:is_key(accounts, S).

extend_oracle_args(S = #{height := Height}) ->
    ?LET({OracleId, DeltaTTL},
         {gen_oracle_account(1, 49, S), gen_ttl()},  %% TTL always relative
         [OracleId,
          #{oracle_id  => aeser_id:create(oracle, OracleId),
            nonce      => gen_nonce(),
            oracle_ttl => {delta, DeltaTTL},
            fee        => gen_fee(Height)
           }]).


extend_oracle_valid(S = #{height := Height}, [Oracle, Tx]) ->
    is_account(S, Oracle)
    andalso is_oracle(S, Oracle)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Oracle, maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso oracle_ttl(S, Oracle) >= Height.

extend_oracle_tx(S, [Sender, Tx]) ->
    aeo_extend_tx:new(update_nonce(S, Sender, Tx)).

extend_oracle_next(S, _Value, [Oracle, Tx] = Args) ->
    case extend_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ oracle_ttl := {delta, Delta}, fee := Fee} = Tx,
            reserve_fee(Fee,
            bump_and_charge(Oracle, Fee,
            oracle_ext(Oracle, Delta, S)))
    end.

extend_oracle_post(S, Args, Res) ->
    common_postcond(extend_oracle_valid(S, Args), Res).

extend_oracle_features(S, Args, Res) ->
    Correct = extend_oracle_valid(S, Args),
    [{correct, if Correct -> extend_oracle; true -> false end},
     {extend_oracle, Res}].

%% --- Operation: query_oracle ---
query_oracle_pre(S) ->
     maps:is_key(accounts, S).

query_oracle_args(#{height := Height} = S) ->
     ?LET({Sender, Oracle},
          {txs_spend_eqc:gen_account_key(1, 49, S), gen_oracle_account(1, 49, S)},
          begin
              QueryFee =
                  case oracle(S, Oracle) of
                      false -> 100;
                      #oracle{qfee = QFee} -> QFee
                  end,
              [Sender, Oracle, length(maps:get(queries, S, [])) + 1,
               #{sender_id => aeser_id:create(account, Sender),
                 oracle_id => aeser_id:create(oracle, Oracle),
                 query => oneof([<<"{foo: bar}"/utf8>>, <<"any string"/utf8>>, <<>>]),
                 query_fee => gen_query_fee(QueryFee),
                 query_ttl => weighted_default({10, {delta, choose(1,5)}}, {1, {block, choose(0,1000)}}),
                 response_ttl =>  {delta, choose(1,5)},  %% Always relavtive (function clause if not
                 fee => gen_fee(Height),
                 nonce => gen_nonce()
                }]
          end).


query_oracle_valid(S = #{height := Height}, [Sender, Oracle, _SymId, Tx]) ->
    RelativeQueryTTL = delta(Height, maps:get(query_ttl, Tx)) - Height,
    RelativeResponseTTL = delta(Height, maps:get(response_ttl, Tx)) - Height,
    is_account(S, Sender)
    andalso is_oracle(S, Oracle)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Sender, maps:get(fee, Tx) + maps:get(query_fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso valid_ttl(Height, maps:get(query_ttl, Tx))
    andalso valid_ttl(Height, maps:get(response_ttl, Tx))
    andalso oracle_query_fee(S, Oracle) =< maps:get(query_fee, Tx)
    andalso oracle_ttl(S, Oracle) >=            %% orcale must as least as long as the query
        Height + RelativeQueryTTL + RelativeResponseTTL.

query_oracle_tx(S, [Sender, _Oracle,  _SymId, Tx]) ->
    aeo_query_tx:new(update_nonce(S, Sender, Tx)).

query_oracle_next(S = #{height := Height}, _Value, [Sender, Oracle, SymId, Tx] = Args) ->
    case query_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ response_ttl := ResponseTTL,  %% can be a delta
               query_ttl := QueryTTL,
               fee := Fee, query_fee := QFee } = Tx,
            Nonce = txs_spend_eqc:account_nonce(txs_spend_eqc:account(S, Sender)),
            Query = #query{sender       = Sender,
                           id           = {Sender, Nonce, Oracle},
                           symb_id      = SymId,
                           query_ttl    = delta(Height, QueryTTL),
                           response_ttl = ResponseTTL,
                           response_due = delta(Height, QueryTTL),
                           fee          = maps:get(query_fee, Tx)},
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee + QFee,
                add(queries, Query, S)))
    end.

query_oracle_post(S, Args, Res) ->
    common_postcond(query_oracle_valid(S, Args), Res).

query_oracle_features(S, [_Sender, _Oracle, _SymId, Tx] = Args, Res) ->
    Correct = query_oracle_valid(S, Args),
    [{correct, if Correct -> query_oracle; true -> false end},
     {query_oracle, Res}] ++
        [ {query_oracle, {ttl, element(1, maps:get(query_ttl, Tx))}} || Correct ].

%% --- Operation: response_oracle ---
response_oracle_pre(S) ->
     maps:is_key(queries, S).

response_oracle_args(#{height := Height} = S) ->
     ?LET(QueryId, choose(1, length(maps:get(queries, S, [])) + 1),
          [QueryId, resolve_query_id(S, QueryId, {elements(maps:keys(maps:get(keys, S))), nat(), elements(maps:keys(maps:get(keys, S)))}),
           #{
             response => weighted_default({9, <<"yes, you can">>}, {1, utf8()}),
             response_ttl => gen_query_response_ttl(S, QueryId),
             fee => gen_fee(Height),
             nonce => gen_nonce()
            }]).

%% It could happen that the fake id actually is an exisiting id during shrinking.
%% Take away that possibility using a precondition
response_oracle_pre(#{queries := Queries}, [QueryId, FakeId, _Tx]) ->
    case lists:keyfind(FakeId, #query.id, Queries) of
        false -> true;   %% fine Fake is really fake
        Query -> Query#query.symb_id == QueryId
    end.

response_oracle_valid(S = #{height := Height}, [QueryId, FakeId, Tx]) ->
    {_, _, Oracle} = resolve_query_id(S, QueryId, FakeId),
    is_account(S, Oracle)
    andalso is_oracle(S, Oracle)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Oracle,  maps:get(fee, Tx))
    andalso valid_fee(Height, Tx)
    andalso is_query(S, QueryId)
    andalso query_query_ttl(S, QueryId) >= Height
    andalso query_response_ttl(S, QueryId) == maps:get(response_ttl, Tx)
    andalso not is_expired_query(S, QueryId).

response_oracle_tx(S, [QueryId, FakeId, Tx]) ->
    {Sender, Nonce, Oracle} = resolve_query_id(S, QueryId, FakeId),
    NewTx = update_nonce(S, Oracle, Tx#{oracle_id => aeser_id:create(oracle, Oracle),
                                        query_id => aeo_query:id(Sender, Nonce, Oracle)}),
    aeo_response_tx:new(NewTx).

response_oracle_next(S, _Value, [QueryId, _FakeId, Tx] = Args) ->
    case response_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee } = Tx,
            #query{id = {_, _, Oracle}, fee = QueryFee} =
                lists:keyfind(QueryId, #query.symb_id, maps:get(queries, S)),
            reserve_fee(Fee,
            bump_and_charge(Oracle, Fee - QueryFee, %% S ))
                expire_query(QueryId, S)))
    end.

response_oracle_post(S, Args, Res) ->
    common_postcond(response_oracle_valid(S, Args), Res).


response_oracle_features(S, [QueryId, _, _Tx] = Args, Res) ->
    Correct = response_oracle_valid(S, Args),
    [{correct, if Correct -> response_oracle; true -> false end},
     {response_oracle, Res}] ++
        [response_expired_query || is_expired_query(S, QueryId)].




%% -- weight ---------------------------------------------------------------
weight(S, register_oracle) ->
    %% Makes most sense if there are accounts that can be turned into an oracle
    (10 * free_accounts(S)) + 1;
weight(S, extend_oracle) ->
    case maps:get(oracles, S, []) of
        [] -> 1;
        _  -> 5 end;
weight(S, query_oracle)  ->
    case maps:get(oracles, S, []) of
        [] -> 1;
        Os  -> min(length(Os), 10) end;
weight(S, response_oracle)  ->
    case maps:get(queries, S, []) of
        [] -> 1;
        Qs ->
            min(length([Q || Q <- Qs, not Q#query.expired]), 10) end;
weight(_S, _) -> 0.

free_accounts(S) ->
    length(maps:get(accounts, S)) - length(maps:get(oracles, S)).

%% -- Transactions modifiers

update_nonce(S, Sender, Tx) ->
    txs_spend_eqc:update_nonce(S, Sender,Tx).


%% -- State update and query functions ---------------------------------------

expired_queries(S, Height) ->
    [ Q || Q <- maps:get(queries, S, []),
           not Q#query.expired andalso Q#query.response_due < Height ].


oracle_ext(Id, Delta, S) ->
    Fun = fun(O) -> O#oracle{oracle_ttl = O#oracle.oracle_ttl + Delta} end,
    on_oracle(Id, Fun, S).

update_oracle_id(OldId, NewId, S) ->
    on_oracle(OldId, fun(O) -> O#oracle{id = NewId} end, S).

on_oracle(Id, Fun, S = #{ oracles := Oracles }) ->
    Upd = fun(C = #oracle{id = I}) when I == Id -> Fun(C);
             (C) -> C end,
    S#{ oracles => lists:map(Upd, Oracles) }.

expire_query(Id, S) ->
    on_query(Id, fun(Q) -> Q#query{expired = true} end, S).

remove_query(Id, S) ->
    remove(queries, Id, #query.id, S).

get_query(S, Id) ->
    lists:keyfind(Id, #query.id, maps:get(queries, S, [])).

on_query(Id, Fun, S = #{ queries := Queries }) ->
    Upd = fun(C = #query{ symb_id = I }) when I == Id -> Fun(C);
             (C) -> C end,
    S#{ queries => lists:map(Upd, Queries) }.

add(Tag, X, S) ->
    S#{ Tag => maps:get(Tag, S, []) ++ [X] }.

remove(Tag, X, I, S) ->
    S#{ Tag := lists:keydelete(X, I, maps:get(Tag, S)) }.


%% --- local helpers ------


is_account(S, Key) ->
    txs_spend_eqc:is_account(S, Key).

reserve_fee(Fee, S) ->
    txs_spend_eqc:reserve_fee(Fee, S).

bump_and_charge(Key, Fee, S) ->
    txs_spend_eqc:bump_and_charge(Key, Fee, S).

check_balance(S, Sender, Amount) ->
    txs_spend_eqc:check_balance(S, Sender, Amount).

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

delta(H, {delta, N}) ->
    max(0, H + N);
delta(_H, {block, N}) when is_integer(N) ->
    N.

query_response_ttl(#{queries := Queries}, QueryId) ->
    Query = lists:keyfind(QueryId, #query.symb_id, Queries),
    Query#query.response_ttl.

query_query_ttl(#{queries := Queries}, QueryId) ->
    Query = lists:keyfind(QueryId, #query.symb_id, Queries),
    Query#query.query_ttl.

resolve_query_id(S, QueryId, FakeId) ->
    %% io:format("S = ~p and Id = ~p\n", [S, QueryId]),
    case lists:keyfind(QueryId, #query.symb_id, maps:get(queries, S, [])) of
        false -> FakeId;
        Query -> Query#query.id
    end.


is_query(#{queries := Qs}, Q) ->
    lists:keymember(Q, #query.symb_id, Qs).

is_expired_query(S, QueryId) ->
    case lists:keyfind(QueryId, #query.symb_id, maps:get(queries, S, [])) of
        false -> false;
        Query -> Query#query.expired
    end.

valid_fee(H, #{ fee := Fee }) ->
    Fee >= 20000 * minimum_gas_price(H).   %% not precise, but we don't generate fees in the shady range

valid_ttl(Height, {block, H}) ->
    H > Height;
valid_ttl(_, {delta, _}) ->
    true.  %% Always in the future


%% -- Generators -------------------------------------------------------------
minimum_gas_price(H) ->
    aec_governance:minimum_gas_price(H).

gen_nonce() ->
    weighted_default({49, good}, {1, {bad, elements([-1, 1, -5, 5, 10000])}}).

gen_oracle_account(_New, _Existing, #{oracles := []} = S) ->
    txs_spend_eqc:gen_account_key(1, 1, S);
gen_oracle_account(New, Existing, #{oracles := Os} = S) ->
    weighted_default(
        {Existing, elements([ Id || #oracle{id = Id} <- Os])},
        {New,  txs_spend_eqc:gen_account_key(1, 49, S)}).

gen_non_oracle_account(New, Existing, #{oracles := Os} = S) ->
    %% remove Oracles from accounts before searching
    Keys =  txs_spend_eqc:account_keys(S) -- [ O#oracle.id || O <- Os],
    oneof(Keys ++ [txs_spend_eqc:gen_account_key(New, Existing, S)]).

gen_fee(H) ->
    frequency([{29, ?LET(F, choose(20000, 30000), F * minimum_gas_price(H))},
                {1,  ?LET(F, choose(0, 15000), F)},   %%  too low (and very low for hard fork)
                {1,  ?LET(F, choose(0, 15000), F * minimum_gas_price(H))}]).    %% too low

gen_query_fee() ->
    choose(10, 1000).

gen_query_fee(QF) ->
    weighted_default({29, QF}, {1, elements([QF - 10, QF - 1, QF + 1, QF + 10, QF + 100])}).

%% QueryId is just an index, or a made up id and then any delta fine
gen_query_response_ttl(S, QueryId) ->
    case lists:keyfind(QueryId, #query.symb_id, maps:get(queries, S, [])) of
        false ->
            {delta, nat()};
        Query ->
            frequency([{49, Query#query.response_ttl}, {1, {delta, nat()}}])
    end.


gen_ttl() ->
    choose(1, 50).
