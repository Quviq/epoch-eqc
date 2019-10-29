%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Hans Svensson
%%% @doc Generalized accounts

-module(txs_channels_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-include("txs_eqc.hrl").

%% -- State and state functions ----------------------------------------------
initial_state(S) -> S#{ channels => #{} }.


%% --- Operation: sc_create ---
sc_create_pre(S) ->
  maps:size(maps:get(accounts, S)) > 1.

sc_create_args(S = #{ protocol := P }) ->
  ?LET(Initiator, gen_account(1, 49, S),
  ?LET(Responder, gen_account(1, 49, maps:remove(ga, S#{paying_for => Initiator})), %% Avoid I == R
  ?LET({IAmt, RAmt, ChResv}, gen_sc_create_amounts(),
       [Initiator, Responder, next_id(channel),
        #{ state_hash => noshrink(binary(32)),
           initiator_amount => IAmt,
           responder_amount => RAmt,
           channel_reserve  => ChResv,
           lock_period      => gen_lock_period(),
           fee              => gen_fee(P),
           nonce            => gen_nonce()
         }]))).

sc_create_pre(_S, _Args) ->
  true.

sc_create_valid(S, [Init, Resp, _, Tx]) ->
  is_account(S, Init)
  andalso is_account(S, Resp)
  andalso Init /= Resp
  andalso maps:get(nonce, Tx) == good
  andalso valid_fee(S, Tx)
  andalso check_balance(S, Init, maps:get(initiator_amount, Tx), maps:get(fee, Tx))
  andalso check_balance(S, Resp, maps:get(responder_amount, Tx), 0)
  andalso maps:get(initiator_amount, Tx) >= maps:get(channel_reserve, Tx)
  andalso maps:get(responder_amount, Tx) >= maps:get(channel_reserve, Tx).

sc_create_tx(S, [Init, Resp, _, Tx]) ->
  InitId = aeser_id:create(account, get_account_key(S, Init)),
  RespId = aeser_id:create(account, get_account_key(S, Resp)),
  Tx1 = update_nonce(S, Init, Tx#{initiator_id => InitId, responder_id => RespId}),
  aesc_create_tx:new(Tx1).

sc_create_next(S, _Value, Args = [Init, Resp, ChId, Tx]) ->
  case sc_create_valid(S, Args) of
    false -> S;
    true  ->
      ChPK = calc_channel_pubkey(S, Init, Resp),

      ?ACCOUNT(InitId) = Init,
      ?ACCOUNT(RespId) = Resp,
      Ch = #channel{ initiator = InitId, responder = RespId,
                     id = ChPK,
                     amount  = maps:get(initiator_amount, Tx)
                                + maps:get(responder_amount, Tx),
                     ch_resv = maps:get(channel_reserve, Tx),
                     lockp   = maps:get(lock_period, Tx) },
      S1 = update_channel(ChId, Ch, S),
      reserve_fee(maps:get(fee, Tx),
        bump_and_charge(Init, maps:get(initiator_amount, Tx), maps:get(fee, Tx),
          charge(Resp, maps:get(responder_amount, Tx), S1)))
  end.

calc_channel_pubkey(S, Init, Resp) ->
  InitPK = get_account_key(S, Init),
  RespPK = get_account_key(S, Resp),
  InitNonce =
    case get_account(S, Init) of
      #account{ ga = #ga{ contract = CId } } ->
        #contract{ abi = ABI } = txs_contracts_eqc:get_contract(S, CId),
        %% We have already bumped the nonce when we get here :-) So, {bad, -1} is good!
        {ok, AuthData}         = txs_ga_eqc:make_auth_data(S, Init, ABI, {bad, -1}),
        aega_meta_tx:auth_id(InitPK, AuthData);
      #account{ nonce = InitNonce0 } ->
        InitNonce0
    end,
  aesc_channels:pubkey(InitPK, InitNonce, RespPK).

sc_create_post(S, Args, Res) ->
  common_postcond(sc_create_valid(S, Args), Res).

sc_create_features(S, Args, Res) ->
  Correct = sc_create_valid(S, Args),
  [{correct, if Correct -> sc_create; true -> false end}] ++
  [{sc_create, Res}].

%% --- Operation: sc_deposit ---

sc_deposit_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_deposit_args(S) ->
  ?LET({Actor, Channel}, gen_channel_id(1, 19, S),
  begin
    NotActor = get_not_actor(S, Channel, Actor),
    [Actor, NotActor, Channel,
     #{ amount => gen_amount(),
        fee    => gen_fee(S),
        nonce  => gen_nonce(),
        round  => gen_round(S, Channel)
      }]
  end).

sc_deposit_valid(_S, [{neither, _}, _, _Channel, _Tx]) -> false;
sc_deposit_valid(_S, [_, _, fake_channel_id, _Tx]) -> false;
sc_deposit_valid(S, [Actor, NotActor, Channel, Tx]) ->
  is_account(S, Actor)
  andalso is_account(S, NotActor)
  andalso is_channel_party(S, Actor, Channel)
  %% andalso is_channel_party(S, NotActor, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_fee(S, Tx)
  andalso check_balance(S, Actor, maps:get(amount, Tx), maps:get(fee, Tx))
  andalso is_valid_round(S, Channel, maps:get(round, Tx)).

sc_deposit_tx(S, [Actor, _NotActor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  Tx1 = update_nonce(S, Actor, Tx#{from_id => ActorId, channel_id => ChannelId, state_hash => <<0:256>>}),
  aesc_deposit_tx:new(Tx1).

sc_deposit_next(S, _Value, Args = [Actor, _NotActor, Channel, Tx]) ->
  case sc_deposit_valid(S, Args) of
    false -> S;
    true ->
      C = get_channel(S, Channel),
      C1 = C#channel{ round = maps:get(round, Tx),
                      amount = C#channel.amount + maps:get(amount, Tx) },
      S1 = update_channel(Channel, C1, S),
      reserve_fee(maps:get(fee, Tx),
        bump_and_charge(Actor, maps:get(amount, Tx), maps:get(fee, Tx), S1))
  end.

sc_deposit_post(S, Args, Res) ->
  common_postcond(sc_deposit_valid(S, Args), Res).

sc_deposit_features(S, Args, Res) ->
  Correct = sc_deposit_valid(S, Args),
  [{correct, if Correct -> sc_deposit; true -> false end}] ++
  [{sc_deposit, Res}].

%% --- Operation: sc_withdraw ---

sc_withdraw_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_withdraw_args(S) ->
  ?LET({Actor, Channel}, gen_channel_id(1, 39, S),
  begin
    NotActor = get_not_actor(S, Channel, Actor),
    [Actor, NotActor, Channel,
     #{ amount => gen_withdraw_amount(S, Channel),
        fee    => gen_fee(S),
        nonce  => gen_nonce(),
        round  => gen_round(S, Channel)
      }]
  end).

sc_withdraw_valid(_S, [{neither, _}, _, _Channel, _Tx]) -> false;
sc_withdraw_valid(_S, [_, _, fake_channel_id, _Tx]) -> false;
sc_withdraw_valid(S, [Actor, NotActor, Channel, Tx]) ->
  is_account(S, Actor)
  andalso is_account(S, NotActor)
  andalso is_channel_party(S, Actor, Channel)
  %% andalso is_channel_party(S, NotActor, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_fee(S, Tx)
  andalso check_balance(S, Actor, maps:get(fee, Tx))
  andalso is_valid_withdraw(S, Channel, maps:get(amount, Tx))
  andalso is_valid_round(S, Channel, maps:get(round, Tx)).

sc_withdraw_tx(S, [Actor, _NotActor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  Tx1 = update_nonce(S, Actor, Tx#{to_id => ActorId, channel_id => ChannelId, state_hash => <<0:256>>}),
  aesc_withdraw_tx:new(Tx1).

sc_withdraw_next(S, _Value, Args = [Actor, _NotActor, Channel, Tx]) ->
  case sc_withdraw_valid(S, Args) of
    false -> S;
    true ->
      C = get_channel(S, Channel),
      C1 = C#channel{ round = maps:get(round, Tx),
                      amount = C#channel.amount - maps:get(amount, Tx) },
      S1 = update_channel(Channel, C1, S),
      reserve_fee(maps:get(fee, Tx),
        bump_and_charge(Actor, -maps:get(amount, Tx), maps:get(fee, Tx), S1))
  end.

sc_withdraw_post(S, Args, Res) ->
  common_postcond(sc_withdraw_valid(S, Args), Res).

sc_withdraw_features(S, Args, Res) ->
  Correct = sc_withdraw_valid(S, Args),
  [{correct, if Correct -> sc_withdraw; true -> false end}] ++
  [{sc_withdraw, Res}].

weight(S, sc_create) ->
  NAccounts = maps:size(maps:get(accounts, S)),
  case good_accounts(S) of
    [] -> 0;
    Xs -> case maps:is_key(ga, S) of
            true   when NAccounts > 1  -> 8;
            false  when length(Xs) > 1 -> 10;
            _ -> 0 end
    end;
weight(S, Fun) when Fun == sc_deposit; Fun == sc_withdraw ->
  case good_channels(S, classify_channels(S)) of
    [] -> 0;
    _  -> 10 end;
weight(_S, _) -> 0.

%% -- Generators -------------------------------------------------------------

classify_channels(S) ->
  [ classify_channel(S, ChId) || ChId <- maps:keys(maps:get(channels, S, #{})) ].

classify_channel(S, ChId) ->
  #channel{ initiator = Init, responder = Resp } = get_channel(S, ChId),
  {ChId, {Init, is_ga(S, ?ACCOUNT(Init))}, {Resp, is_ga(S, ?ACCOUNT(Resp))}}.

good_channels(#{ ga := _ }, Cs) ->
  [ C || C = {_, {_, I}, {_, R}} <- Cs, I orelse R ];
good_channels(_S, Cs) ->
  [ C || C = {_, {_, I}, {_, R}} <- Cs, not I andalso not R ].

gen_channel_id(Invalid, Valid, S) ->
  gen_channel_id(Invalid, Valid, S, classify_channels(S)).

gen_channel_id(_, _, S, []) -> {gen_account(0, 1, S), fake_channel_id};
gen_channel_id(Invalid, Valid, S, Cs) ->
  case good_channels(S, Cs) of
    []  -> {gen_account(0, 1, S), fake_channel_id};
    Cs1 ->
      weighted_default(
        {Valid, ?LET({C, {I, IGA}, {R, RGA}}, elements(Cs1),
                     {?LET(A, gen_channel_actor(maps:is_key(ga, S), {I, IGA}, {R, RGA}), ?ACCOUNT(A)), ?CHANNEL(C)})},
        {Invalid, frequency([{1, ?LET({C, _, _}, elements(Cs1), {gen_account(0, 1, S), ?CHANNEL(C)})},
                             {1, ?LET({C, {I, _}, _}, elements(Cs), {?ACCOUNT(I), ?CHANNEL(C)})},
                             {1, ?LET({_, {I, _}, _}, elements(Cs), {?ACCOUNT(I), fake_channel_id})},
                             {1, ?LET({C, _, _}, elements(Cs1), {{neither, noshrink(binary(32))}, ?CHANNEL(C)})}])})
  end.

gen_channel_actor(true, {I, IGA}, {R, RGA})  -> elements([I || IGA] ++ [R || RGA]);
gen_channel_actor(false, {I, IGA}, {R, RGA}) -> elements([I || not IGA] ++ [R || not RGA]).

gen_round(S, ChannelId) ->
  case get_channel(S, ChannelId) of
    false -> choose(1, 10);
    #channel{ round = Rnd } ->
      weighted_default({49, ?LET(Delta, choose(1, 10), Rnd + Delta)},
                       {1,  ?LET(Delta, choose(0, 5), max(0, Rnd - Delta))})
  end.

gen_sc_create_amounts() ->
  ?LET({I, R}, {gen_amount(), gen_amount()},
       frequency([{39, {I, R, min(I, R) div 5}},
                  {10, {I, R, 0}},
                  {1,  oneof([{I, R, min(I, R) + 1}, {0, R, 1}, {I, 0, 1}])}])).

gen_amount() -> choose(0, 1000000).

gen_withdraw_amount(S, Channel) ->
  case get_channel(S, Channel) of
    #channel{ amount = A, ch_resv = R } ->
      weighted_default({39, (A - 2 * R) div 5},
                       {1,  ?LET(Delta, choose(1, 1000), A - 2 * R + Delta)});
    _ ->
      gen_amount()
  end.

gen_lock_period() -> choose(0, 5).

%% --- local helpers ------

get_channel(S, ?CHANNEL(C)) -> get_channel(S, C);
get_channel(#{ channels := Cs }, C) ->
  maps:get(C, Cs, false).

get_channel_id(_S, fake_channel_id) -> <<12345678:256>>;
get_channel_id(S, CId) ->
  C = get_channel(S, CId), C#channel.id.

is_channel(S, CId) ->
  false /= get_channel(S, CId).

is_channel_party(S, ?ACCOUNT(ActorId), CId) ->
  case get_channel(S, CId) of
    #channel{ initiator = ActorId } -> true;
    #channel{ responder = ActorId } -> true;
    _ -> false
  end;
is_channel_party(_, _, _) ->
  false.

get_not_actor(S, ChId, ?ACCOUNT(ActorId)) ->
  case get_channel(S, ChId) of
    C = #channel{ initiator = ActorId } -> ?ACCOUNT(C#channel.responder);
    C = #channel{ responder = ActorId } -> ?ACCOUNT(C#channel.initiator);
    _ -> not_an_account
  end;
get_not_actor(_, _, _) -> not_an_account.

get_actor_key(_S, {neither, Key}) -> Key;
get_actor_key(S, A)               -> get_account_key(S, A).

update_channel(?CHANNEL(ChId), Ch, S) ->
  update_channel(ChId, Ch, S);
update_channel(ChId, Ch, S = #{ channels := Chs }) ->
  S#{ channels := Chs#{ ChId => Ch } }.

is_valid_round(S, ChId, Rnd) ->
  case get_channel(S, ChId) of
    #channel{ round = Rnd1 } when Rnd1 < Rnd -> true;
    _ -> false
  end.

is_valid_withdraw(S, ChId, Amt) ->
  case get_channel(S, ChId) of
    #channel{ amount = A, ch_resv = R } when A - 2 * R >= Amt -> true;
    _ -> false
  end.

