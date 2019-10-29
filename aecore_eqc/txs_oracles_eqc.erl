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
-include("txs_eqc.hrl").


%% -- State and state functions ----------------------------------------------
initial_state(S) ->
    S#{oracles => #{}, queries => #{}}.

%% -- Operations -------------------------------------------------------------

%% --- Operation: multi_mine ---
%%
%% The multi mine part that is oracle dependent
%%
%% This will generate warnings:
%%    Warning: multi_mine_next unused (no multi_mine_command or multi_mine_args defined).
%%    Warning: multi_mine_features unused (no multi_mine_command or multi_mine_args defined).
mine_next(#{height := Height} = S, _Value, [Blocks]) ->
    ExpiredQs = expired_queries(S, Height + Blocks),
    lists:foldl(
      fun({QId, Q}, NS) ->
          update_query(QId, Q#query{ expired = true },
                       credit(?ACCOUNT(Q#query.sender), Q#query.fee, NS))
      end, S, ExpiredQs).

mine_features(#{height := Height} = S, [Blocks], _Res) ->
    [{mine, response_ttl} || expired_queries(S, Height + Blocks) =/= [] ].

%% --- Operation: register_oracle ---
register_oracle_pre(S) ->
    maps:is_key(accounts, S).

register_oracle_args(S = #{protocol := Protocol}) ->
     ?LET(Account, gen_non_oracle_account(1, 49, S),
          [Account,
           #{query_format    => <<"send me any string"/utf8>>,
             response_format => <<"boolean()"/utf8>>,
             query_fee       => gen_query_fee(),
             fee             => gen_fee(Protocol),
             nonce           => gen_nonce(),
             oracle_ttl      => frequency([{9, {delta, 1001}},
                                           {1, {delta, elements([0, 1, 2])}},
                                           {1, {block, choose(0, 1000)}}]),
             abi_version     => 0}]).

register_oracle_valid(S = #{height := Height}, [Account, Tx]) ->
    is_account(S, Account)
    andalso check_balance(S, Account, maps:get(fee, Tx))
    andalso maps:get(nonce, Tx) == good
    andalso valid_fee(S, Tx)
    andalso valid_ttl(Height, maps:get(oracle_ttl, Tx))
    andalso (not is_oracle(S, Account) orelse oracle_ttl(S, mk_oracle_id(Account)) < Height).
    %% Very nice shrinking example if removing 'oracle_ttl(S, Account) < Height'

register_oracle_tx(S, [Account, Tx]) ->
    AccountId = aeser_id:create(account, get_account_key(S, Account)),
    aeo_register_tx:new(update_nonce(S, Account, Tx#{ account_id => AccountId })).

register_oracle_next(S = #{height := Height}, _Value, [Account, Tx] = Args) ->
    case register_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee, query_fee := QFee, oracle_ttl := OracleTTL } = Tx,
            OracleId = mk_oracle_id(Account),
            ?ACCOUNT(AccountId) = Account,
            Oracle = #oracle{account = AccountId, qfee = QFee,
                             oracle_ttl = delta(Height, OracleTTL)},
            reserve_fee(Fee,
              bump_and_charge(Account, Fee, update_oracle(OracleId, Oracle, S)))
    end.

register_oracle_post(S, Args, Res) ->
    common_postcond(register_oracle_valid(S, Args), Res).

register_oracle_features(S, [_Account, _Tx] = Args, Res) ->
    Correct = register_oracle_valid(S, Args),
    [{correct, if Correct -> register_oracle; true -> false end},
     {register_oracle, Res}].
        %% [ {register_oracle, {ttl, element(1, maps:get(oracle_ttl, Tx))}} || Correct ].

%% --- Operation: extend_oracle ---
extend_oracle_pre(S) ->
    maps:is_key(accounts, S).

extend_oracle_args(S = #{protocol := Protocol}) ->
    ?LET({OracleId, DeltaTTL},
         {gen_oracle_id(1, 49, S), gen_ttl()},  %% TTL always relative
         [resolve_oracle(S, OracleId),
          #{nonce      => gen_nonce(),
            oracle_ttl => {delta, DeltaTTL},
            fee        => gen_fee(Protocol)
           }]).

extend_oracle_valid(S = #{height := Height}, [Oracle, Tx]) ->
    Account = get_oracle_account(S, Oracle),
    is_oracle(S, Oracle)
    andalso is_account(S, Account)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Account, maps:get(fee, Tx))
    andalso valid_fee(S, Tx)
    andalso oracle_ttl(S, Oracle) >= Height.

extend_oracle_tx(S, [Oracle, Tx]) ->
    OracleId = create_oracle_id(S, Oracle),
    aeo_extend_tx:new(update_nonce_(S, Oracle, Tx#{ oracle_id => OracleId })).

extend_oracle_next(S, _Value, [OracleId, Tx] = Args) ->
    case extend_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ oracle_ttl := {delta, Delta}, fee := Fee} = Tx,
            O = #oracle{ oracle_ttl = OTTL, account = Account } = get_oracle(S, OracleId),
            reserve_fee(Fee,
              bump_and_charge(?ACCOUNT(Account), Fee,
                update_oracle(OracleId, O#oracle{ oracle_ttl = OTTL + Delta }, S)))
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

query_oracle_args(#{protocol := Protocol} = S) ->
     ?LET({Sender, Oracle0},
          {gen_account(1, 49, S), gen_oracle_id(1, 49, S)},
          begin
              Oracle = resolve_oracle(S, Oracle0),
              QueryFee = case get_oracle(S, Oracle) of
                             false -> 100;
                             #oracle{qfee = QFee} -> QFee
                         end,
              [Sender, Oracle, next_id(query),
               #{query        => oneof([<<"{foo: bar}"/utf8>>, <<"any string"/utf8>>, <<>>]),
                 query_fee    => gen_query_fee(QueryFee),
                 query_ttl    => weighted_default({10, {delta, choose(1, 5)}}, {1, {block, choose(0, 1000)}}),
                 response_ttl => {delta, choose(1, 5)},  %% Always relative
                 fee          => gen_fee(Protocol),
                 nonce        => gen_nonce()
                }]
          end).


query_oracle_valid(S = #{height := Height}, [Sender, Oracle, _QId, Tx]) ->
    RelQueryTTL    = delta(Height, maps:get(query_ttl, Tx)) - Height,
    RelResponseTTL = delta(Height, maps:get(response_ttl, Tx)) - Height,
    is_oracle(S, Oracle)
    andalso is_account(S, Sender)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Sender, maps:get(fee, Tx) + maps:get(query_fee, Tx))
    andalso valid_fee(S, Tx)
    andalso valid_ttl(Height, maps:get(query_ttl, Tx))
    andalso valid_ttl(Height, maps:get(response_ttl, Tx))
    andalso oracle_query_fee(S, Oracle) =< maps:get(query_fee, Tx)
    andalso oracle_ttl(S, Oracle) >= Height + RelQueryTTL + RelResponseTTL. %% oracle TTL must as least as long as the query

query_oracle_tx(S, [Sender, Oracle,  _QId, Tx]) ->
    Tx1 = update_nonce(S, Sender, Tx),
    SenderId = aeser_id:create(account, get_account_key(S, Sender)),
    OracleId = create_oracle_id(S, Oracle),
    aeo_query_tx:new(Tx1#{ sender_id => SenderId, oracle_id => OracleId }).

create_oracle_id(S, O = ?ORACLE(_)) -> aeser_id:create(oracle, get_oracle_key(S, O));
create_oracle_id(S, A)              -> aeser_id:create(oracle, get_account_key(S, A)).


query_oracle_next(S = #{height := Height}, _Value, [Sender, Oracle, QId, Tx] = Args) ->
    case query_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ response_ttl := ResponseTTL,  %% can be a delta
               query_ttl := QueryTTL,
               fee := Fee, query_fee := QFee } = Tx,
            QueryId  = calc_query_id(S, Sender, Oracle),
            %% SenderPK = get_account_key(S, Sender),
            %% Nonce    = get_account_nonce(S, Sender),
            %% OraclePK = get_oracle_key(S, Oracle),
            %% QueryId  = aeo_query:id(SenderPK, Nonce, OraclePK),
            ?ORACLE(OId)  = Oracle,
            ?ACCOUNT(SId) = Sender,
            Query = #query{sender       = SId,
                           oracle       = OId,
                           id           = QueryId,
                           query_ttl    = delta(Height, QueryTTL),
                           response_ttl = ResponseTTL,
                           response_due = delta(Height, QueryTTL),
                           fee          = maps:get(query_fee, Tx)},
            reserve_fee(Fee,
              bump_and_charge(Sender, Fee + QFee, update_query(QId, Query, S1)))
    end.

calc_query_id(S, Sender, Oracle) ->
    OraclePK = get_oracle_key(S, Oracle),
    case get_account(S, Sender) of
        #account{ ga = #ga{ contract = CId }, key = Key } ->
            #contract{ abi = ABI } = txs_contracts_eqc:get_contract(S, CId),
            GAPK                   = get_pubkey(S, Key),
            {ok, AuthData}         = txs_ga_eqc:make_auth_data(S, Sender, ABI, good),
            GANonce                = aega_meta_tx:auth_id(GAPK, AuthData),
            aeo_query:ga_id(GANonce, OraclePK);
        #account{ key = Key, nonce = Nonce } ->
            SenderPK = get_pubkey(S, Key),
            aeo_query:id(SenderPK, Nonce, OraclePK)
    end.

query_oracle_post(S, Args, Res) ->
    common_postcond(query_oracle_valid(S, Args), Res).

query_oracle_features(S, [_Sender, _Oracle, _SymId, _Tx] = Args, Res) ->
    Correct = query_oracle_valid(S, Args),
    [{correct, if Correct -> query_oracle; true -> false end},
     {query_oracle, Res}].
     %%   [ {query_oracle, {ttl, element(1, maps:get(query_ttl, Tx))}} || Correct ].

%% --- Operation: response_oracle ---
response_oracle_pre(S) ->
     maps:is_key(queries, S).

response_oracle_args(#{protocol := Protocol} = S) ->
     ?LET(QueryId, gen_query_id(1, 49, S),
          [QueryId, % resolve_query_id(S, QueryId, {elements(maps:keys(maps:get(keys, S))), nat(), elements(maps:keys(maps:get(keys, S)))}),
           #{
             response => weighted_default({9, <<"yes, you can">>}, {1, utf8()}),
             response_ttl => gen_query_response_ttl(S, QueryId),
             fee => gen_fee(Protocol),
             nonce => gen_nonce()
            }]).

response_oracle_valid(S = #{height := Height}, [QueryId, Tx]) ->
    Oracle  = get_query_oracle(S, QueryId),
    Account = get_oracle_account(S, Oracle),
    is_query(S, QueryId)
    andalso is_oracle(S, Oracle)
    andalso is_account(S, Account)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Account,  maps:get(fee, Tx))
    andalso valid_fee(S, Tx)
    andalso query_query_ttl(S, QueryId) >= Height
    andalso query_response_ttl(S, QueryId) == maps:get(response_ttl, Tx)
    andalso not is_expired_query(S, QueryId).

response_oracle_tx(S, [?QUERY(_) = QId, Tx]) ->
    Oracle  = get_query_oracle(S, QId),
    Account = get_oracle_account(S, Oracle),
    QueryId = get_query_key(S, QId),
    response_oracle_tx_(S, Tx, Account, get_oracle_key(S, Oracle), QueryId);
response_oracle_tx(S, [#query{ id = QId, oracle = Oracle }, Tx]) ->
    response_oracle_tx_(S, Tx, no_account, Oracle, QId).

response_oracle_tx_(S, Tx, Account, OracleKey, QueryId) ->
    Tx1      = update_nonce(S, Account, Tx),
    OracleId = aeser_id:create(oracle, OracleKey),
    NewTx = Tx1#{oracle_id => OracleId, query_id => QueryId},
    aeo_response_tx:new(NewTx).

response_oracle_next(S, _Value, [QueryId, Tx] = Args) ->
    case response_oracle_valid(S, Args) of
        false -> S;
        true  ->
            #{ fee := Fee } = Tx,
            Q = #query{ fee = QFee, oracle = O } = get_query(S, QueryId),
            reserve_fee(Fee,
              bump_and_charge(get_oracle_account(S, O), Fee - QFee,
                              update_query(QueryId, Q#query{ expired = true }, S)))
    end.

response_oracle_post(S, Args, Res) ->
    common_postcond(response_oracle_valid(S, Args), Res).

response_oracle_features(S, [_QueryId, _Tx] = Args, Res) ->
    Correct = response_oracle_valid(S, Args),
    [{correct, if Correct -> response_oracle; true -> false end},
     {response_oracle, Res}].
        %% [response_expired_query || is_expired_query(S, QueryId)].


%% -- weight ---------------------------------------------------------------
weight(S, register_oracle) ->
    case active_oracles(S) of
      [] -> 30;
      _  -> min(1, 10 * free_accounts(S)) end;
weight(S, extend_oracle) ->
    case maps:size(maps:get(oracles, S, #{})) of
        0  -> 1;
        _N -> 3 end;
weight(S, query_oracle)  ->
    case active_oracles(S) of
        [] -> 1;
        _  -> min(3, (5 - length(open_queries(S))) * 5) end;
weight(S, response_oracle)  ->
    max(1, 20 * length(open_queries(S)));
weight(_S, _) -> 0.

free_accounts(S) ->
  maps:size(maps:get(accounts, S)) - maps:size(maps:get(oracles, S)).

open_queries(S) ->
  [ Q || Q <- maps:values(maps:get(queries, S)), not Q#query.expired ].

active_oracles(S = #{ height := H }) ->
  [ O || O <- maps:values(maps:get(oracles, S)), O#oracle.oracle_ttl >= H ].

%% -- State update and query functions ---------------------------------------

expired_queries(S, Height) ->
    [ X || X = {_, Q} <- maps:to_list(maps:get(queries, S, [])),
           not Q#query.expired andalso Q#query.response_due < Height ].

update_oracle(?ORACLE(OId), O, S) -> update_oracle(OId, O, S);
update_oracle(OId, O, S = #{ oracles := Os }) ->
    S#{ oracles := Os#{ OId => O } }.

update_query(?QUERY(QId), Q, S) -> update_query(QId, Q, S);
update_query(QId, Q, S = #{ queries := Qs }) ->
    S#{ queries := Qs#{ QId => Q } }.

%% --- local helpers ------
is_oracle(#{oracles := Os}, ?ACCOUNT(A)) ->
  lists:keymember(A, #oracle.account, maps:values(Os));
is_oracle(S, ?ORACLE(O)) ->
  is_oracle(S, O);
is_oracle(#{oracles := Os}, O) ->
  maps:is_key(O, Os).

get_oracle(S, ?ORACLE(O)) ->
  get_oracle(S, O);
get_oracle(S, O) ->
  maps:get(O, maps:get(oracles, S), false).

get_oracle_key(S, O) ->
  get_account_key(S, get_oracle_account(S, O)).

get_oracle_account(S, OId) ->
  case get_oracle(S, OId) of
    false -> OId;
    O     -> ?ACCOUNT(O#oracle.account)
  end.

oracle_ttl(S, OId) ->
  case get_oracle(S, OId) of
    false -> 0;
    O     -> O#oracle.oracle_ttl
  end.

oracle_query_fee(S, OId) ->
  case get_oracle(S, OId) of
    false -> 0;
    O     -> O#oracle.qfee
  end.

is_query(S, ?QUERY(Q)) ->
  is_query(S, Q);
is_query(#{queries := Qs}, Q) ->
  maps:is_key(Q, Qs).

get_query(S, ?QUERY(Q)) ->
  get_query(S, Q);
get_query(S, Q) ->
  maps:get(Q, maps:get(queries, S), false).

get_query_key(_S, #query{ id = Id }) ->
  Id;
get_query_key(S, Q) ->
  #query{ id = Id } = get_query(S, Q),
  Id.

get_query_oracle(_S, #query{ oracle = O }) ->
  O;
get_query_oracle(S, Q) ->
  #query{ oracle = O } = get_query(S, Q),
  ?ORACLE(O).

query_response_ttl(S, Q) ->
  #query{ response_ttl = RTTL } = get_query(S, Q),
  RTTL.

query_query_ttl(S, Q) ->
  #query{ query_ttl = QTTL } = get_query(S, Q),
  QTTL.

is_expired_query(S, Q) ->
  #query{ expired = E } = get_query(S, Q),
  E.

delta(H, {delta, N}) ->
    max(0, H + N);
delta(_H, {block, N}) when is_integer(N) ->
    N.

valid_ttl(Height, {block, H}) ->
    H > Height;
valid_ttl(_, {delta, _}) ->
    true.  %% Always in the future

mk_oracle_id(?ACCOUNT(A)) ->
  StrId = lists:last(string:lexemes(atom_to_list(A), "_")),
  list_to_atom("oracle_" ++ StrId).

resolve_oracle(_S, O = ?ORACLE(_)) -> O;
resolve_oracle(S, ?ACCOUNT(A)) ->
  case [ O || {O, #oracle{ account = A1 }} <- maps:to_list(maps:get(oracles, S)),
              A == A1 ] of
    [O] -> ?ORACLE(O);
    _   -> ?ACCOUNT(A)
  end;
resolve_oracle(_S, A) ->
  A.

update_nonce_(S, O = ?ORACLE(_), Tx) ->
  update_nonce(S, get_oracle_account(S, O), Tx);
update_nonce_(S, A, Tx) ->
  update_nonce(S, A, Tx).

%% -- Generators -------------------------------------------------------------
gen_oracle_id(New, Existing, S) ->
    case maps:keys(maps:get(oracles, S, #{})) of
        [] -> gen_account(1, 5, S);
        Os -> weighted_default({Existing, ?LET(O, gen_oracle_id(S, Os), ?ORACLE(O))},
                               {New,      gen_account(1, 5, S)})
    end.

gen_oracle_id(S = #{ with_ga := true }, Os) ->
  gen_elem(Os, [ O || O <- Os, is_ga(S, ?ORACLE(O)) ]);
gen_oracle_id(S, Os) ->
  gen_elem(Os, [ O || O <- Os, not is_ga(S, ?ORACLE(O)) ]).

gen_elem(Os, [])  -> elements(Os);
gen_elem(Os0, Os) -> weighted_default({29, elements(Os)}, {1, elements(Os0)}).

gen_query_id(New, Existing, S) ->
    case maps:to_list(maps:get(queries, S, #{})) of
        [] -> no_query();
        Qs ->
            WeightedQs = [ weight_query(Q) || Q <- Qs ],
            weighted_default({Existing, ?LET(Q, gen_query_id(S, WeightedQs), ?QUERY(Q))},
                             {New,      no_query()})
    end.

gen_query_id(S = #{ with_ga := true }, Qs) ->
  gen_freq(Qs, [ {N, Q} || {N, Q} <- Qs, is_ga(S, ?QUERY(Q)) ]);
gen_query_id(S, Qs) ->
  gen_freq(Qs, [ {N, Q} || {N, Q} <- Qs, not is_ga(S, ?QUERY(Q)) ]).

gen_freq(Os, [])  -> frequency(Os);
gen_freq(Os0, Os) -> weighted_default({29, frequency(Os)}, {1, frequency(Os0)}).


weight_query({Q, #query{ expired = true }})  -> {1, Q};
weight_query({Q, #query{ expired = false }}) -> {20, Q}.

no_query() -> #query{ id = noshrink(binary(32)), oracle = noshrink(binary(32)) }.

gen_non_oracle_account(New, Existing, S = #{ with_ga := true }) ->
    gen_account(New, Existing, S, fun(A) -> not is_oracle(S, A) andalso is_ga(S, ?ACCOUNT(A)) end);
gen_non_oracle_account(New, Existing, S) ->
    gen_account(New, Existing, S, fun(A) -> not is_oracle(S, A) andalso not is_ga(S, ?ACCOUNT(A)) end).

gen_query_fee() ->
    choose(10, 1000).

gen_query_fee(QF) ->
    weighted_default({29, QF}, {1, elements([QF - 10, QF - 1, QF + 1, QF + 10, QF + 100])}).

%% QueryId is just an index, or a made up id and then any delta fine
gen_query_response_ttl(S, QueryId) ->
    case get_query(S, QueryId) of
        false ->
            {delta, nat()};
        Query ->
            frequency([{49, Query#query.response_ttl}, {1, {delta, nat()}}])
    end.

gen_ttl() ->
    choose(1, 50).
