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
  ?LET({IAmt, RAmt, ChResv}, gen_sc_create_amounts(S, Initiator, Responder),
       [Initiator, Responder, next_id(channel),
        #{ initiator_amount => IAmt,
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
  StateHash = calc_state_hash(S, init_cs(Init, Resp, Tx)),
  Tx1 = Tx#{initiator_id => InitId, responder_id => RespId, state_hash => StateHash},
  aesc_create_tx:new(update_nonce(S, Init, Tx1)).

sc_create_next(S, _Value, Args = [Init, Resp, ChId, Tx]) ->
  case sc_create_valid(S, Args) of
    false -> S;
    true  ->
      ChPK = calc_channel_pubkey(S, Init, Resp),

      ?ACCOUNT(InitId) = Init,
      ?ACCOUNT(RespId) = Resp,
      Ch = #channel{ id = ChPK, init = InitId, resp = RespId,
                     i_auth = get_auth(S, Init), r_auth = get_auth(S, Resp),
                     ch_rsv = maps:get(channel_reserve, Tx),
                     lock_p = maps:get(lock_period, Tx),
                     state  = init_cs(Init, Resp, Tx)},
      S1 = update_channel(ChId, Ch, S),
      reserve_fee(maps:get(fee, Tx),
        bump_and_charge(Init, maps:get(initiator_amount, Tx), maps:get(fee, Tx),
          charge(Resp, maps:get(responder_amount, Tx), 0, S1)))
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
  ?LET({Actor, Channel}, gen_active_channel_id(1, 39, S),
  begin
    NotActor = get_not_actor(S, Channel, Actor),
    [Actor, NotActor, Channel,
     #{ amount => gen_amount(S, Actor),
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
  andalso is_channel_active(S, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_fee(S, Tx)
  andalso check_balance(S, Actor, maps:get(amount, Tx), maps:get(fee, Tx))
  andalso is_valid_round(S, Channel, maps:get(round, Tx)).

sc_deposit_tx(S, [Actor, _NotActor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  StateHash = calc_state_hash(S, deposit_cs(S, Channel, Actor, Tx)),
  Tx1 = Tx#{from_id => ActorId, channel_id => ChannelId, state_hash => StateHash},
  aesc_deposit_tx:new(update_nonce(S, Actor, Tx1)).

sc_deposit_next(S, _Value, Args = [Actor, _NotActor, Channel, Tx]) ->
  case sc_deposit_valid(S, Args) of
    false -> S;
    true ->
      C = get_channel(S, Channel),
      C1 = C#channel{ rnd      = maps:get(round, Tx),
                      solo_rnd = 0,
                      state    = deposit_cs(S, Channel, Actor, Tx) },
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
  ?LET({Actor, Channel}, gen_active_channel_id(1, 39, S),
  begin
    NotActor = get_not_actor(S, Channel, Actor),
    [Actor, NotActor, Channel,
     #{ amount => gen_withdraw_amount(S, Channel),
        fee    => gen_fee(S),
        nonce  => gen_nonce(),
        round  => gen_round(S, Channel)
      }]
  end).

sc_withdraw_pre(S, [?ACCOUNT(Actor), _, ChId, #{ amount := Amt }]) ->
  case get_channel(S, ChId) of
    #channel{ init = Actor, ch_rsv = R, state = #cs{ i_am = IA } } ->
      Amt =< IA - R;
    #channel{ resp = Actor, ch_rsv = R, state = #cs{ r_am = RA } } ->
      Amt =< RA - R;
    _ -> true
  end;
sc_withdraw_pre(_, _) ->
  true.

sc_withdraw_valid(_S, [{neither, _}, _, _Channel, _Tx]) -> false;
sc_withdraw_valid(_S, [_, _, fake_channel_id, _Tx]) -> false;
sc_withdraw_valid(S, [Actor, NotActor, Channel, Tx]) ->
  is_account(S, Actor)
  andalso is_account(S, NotActor)
  andalso is_channel_party(S, Actor, Channel)
  andalso is_channel_active(S, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_fee(S, Tx)
  andalso check_balance(S, Actor, maps:get(fee, Tx))
  andalso is_valid_withdraw(S, Channel, maps:get(amount, Tx))
  andalso is_valid_round(S, Channel, maps:get(round, Tx)).

sc_withdraw_tx(S, [Actor, _NotActor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  StateHash = calc_state_hash(S, withdraw_cs(S, Channel, Actor, Tx)),
  Tx1 = Tx#{to_id => ActorId, channel_id => ChannelId, state_hash => StateHash},
  aesc_withdraw_tx:new(update_nonce(S, Actor, Tx1)).

sc_withdraw_next(S, _Value, Args = [Actor, _NotActor, Channel, Tx]) ->
  case sc_withdraw_valid(S, Args) of
    false -> S;
    true ->
      C = get_channel(S, Channel),
      C1 = C#channel{ rnd      = maps:get(round, Tx),
                      solo_rnd = 0,
                      state    = withdraw_cs(S, Channel, Actor, Tx) },
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

%% --- Operation: sc_close_mutual ---

sc_close_mutual_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_close_mutual_args(S) ->
  ?LET({Actor, Channel}, gen_channel_id(1, 39, S),
  begin
    NotActor = get_not_actor(S, Channel, Actor),
    ?LET(Fee, gen_fee(S),
    ?LET({IAmt, RAmt}, gen_close_mutual_amounts(S, Channel, Fee),
         [Actor, NotActor, Channel,
          #{ initiator_amount_final => IAmt,
             responder_amount_final => RAmt,
             fee                    => Fee,
             nonce                  => gen_nonce()
           }]))
  end).

sc_close_mutual_valid(_S, [{neither, _}, _, _Channel, _Tx]) -> false;
sc_close_mutual_valid(_S, [_, _, fake_channel_id, _Tx]) -> false;
sc_close_mutual_valid(S, [Actor, NotActor, Channel, Tx]) ->
  is_account(S, Actor)
  andalso is_account(S, NotActor)
  andalso is_channel_party(S, Actor, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_fee(S, Tx)
  andalso check_balance(S, Actor, maps:get(fee, Tx))
  andalso is_valid_close_mutual(S, Channel, Tx).

sc_close_mutual_tx(S, [Actor, _NotActor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  Tx1 = Tx#{from_id => ActorId, channel_id => ChannelId},
  aesc_close_mutual_tx:new(update_nonce(S, Actor, Tx1)).

sc_close_mutual_next(S, _Value, Args = [Actor, _NotActor, Channel, Tx]) ->
  case sc_close_mutual_valid(S, Args) of
    false -> S;
    true ->
      C  = get_channel(S, Channel),
      S1 = delete_channel(Channel, S),
      reserve_fee(maps:get(fee, Tx),
        bump_nonce(Actor,
          credit(?ACCOUNT(C#channel.init), maps:get(initiator_amount_final, Tx),
            credit(?ACCOUNT(C#channel.resp), maps:get(responder_amount_final, Tx), S1))))
  end.

sc_close_mutual_post(S, Args, Res) ->
  common_postcond(sc_close_mutual_valid(S, Args), Res).

sc_close_mutual_features(S, Args, Res) ->
  Correct = sc_close_mutual_valid(S, Args),
  [{correct, if Correct -> sc_close_mutual; true -> false end}] ++
  [{sc_close_mutual, Res}].

%% --- Operation: sc_snapshot_solo ---

sc_snapshot_solo_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_snapshot_solo_args(S) ->
  ?LET({Actor, Channel}, gen_active_channel_id(1, 39, S),
       [Actor, Channel, #{ fee   => gen_big_fee(S),
                           round => gen_round(S, Channel),
                           nonce => gen_nonce() }]).

sc_snapshot_solo_valid(_S, [{neither, _}, _Channel, _Tx]) -> false;
sc_snapshot_solo_valid(_S, [_, fake_channel_id, _Tx]) -> false;
sc_snapshot_solo_valid(S, [Actor, Channel, Tx]) ->
  is_account(S, Actor)
  andalso is_channel_party(S, Actor, Channel)
  andalso is_channel_active(S, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_sc_fee(S, Tx)
  andalso check_balance(S, Actor, maps:get(fee, Tx))
  andalso is_valid_round(S, Channel, maps:get(round, Tx)).

sc_snapshot_solo_tx(S, [Actor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  Payload   = calc_payload(S, Channel, maps:get(round, Tx)),
  Tx1 = Tx#{from_id => ActorId, channel_id => ChannelId, payload => Payload},
  aesc_snapshot_solo_tx:new(update_nonce(S, Actor, Tx1)).

sc_snapshot_solo_next(S, _Value, Args = [Actor, Channel, Tx]) ->
  case sc_snapshot_solo_valid(S, Args) of
    false -> S;
    true ->
      C   = #channel{ state = CS } = get_channel(S, Channel),
      Rnd = maps:get(round, Tx),
      C1  = C#channel{ rnd = Rnd, solo_rnd = 0, state = CS#cs{ rnd = Rnd } },
      S1  = update_channel(Channel, C1, S),
      reserve_fee(maps:get(fee, Tx),
        bump_and_charge(Actor, maps:get(fee, Tx), S1))
  end.

sc_snapshot_solo_post(S, Args, Res) ->
  common_postcond(sc_snapshot_solo_valid(S, Args), Res).

sc_snapshot_solo_features(S, Args, Res) ->
  Correct = sc_snapshot_solo_valid(S, Args),
  [{correct, if Correct -> sc_snapshot_solo; true -> false end}] ++
  [{sc_snapshot_solo, Res}].

%% --- Operation: sc_close_solo ---

sc_close_solo_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_close_solo_args(S) ->
  ?LET({Actor, Channel}, gen_active_channel_id(1, 39, S),
  ?LET({PayLoad, Round}, {gen_payload(S, Channel), gen_round(S, Channel)},
       [Actor, Channel, #{ fee     => gen_big_fee(S),
                           payload => if PayLoad == on_chain -> PayLoad; true -> {PayLoad, Round} end,
                           nonce   => gen_nonce() }])).

sc_close_solo_fee(on_chain) -> 25000;
sc_close_solo_fee(payload)  -> 30000.

sc_close_solo_valid(_S, [{neither, _}, _Channel, _Tx]) -> false;
sc_close_solo_valid(_S, [_, fake_channel_id, _Tx]) -> false;
sc_close_solo_valid(S, [Actor, Channel, Tx = #{ payload := PayLoad }]) ->
  is_account(S, Actor)
  andalso is_channel_party(S, Actor, Channel)
  andalso is_channel_active(S, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_sc_fee(S, Tx)
  andalso check_balance(S, Actor, maps:get(fee, Tx))
  andalso is_valid_payload(S, Channel, PayLoad)
  andalso (case PayLoad of on_chain -> true;
                           {_, Rnd} -> is_valid_round(S, Channel, Rnd) end).

sc_close_solo_tx(S, [Actor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  Payload   = case maps:get(payload, Tx) of
                on_chain -> <<>>;
                {_, Rnd} -> calc_payload(S, Channel, Rnd)
              end,
  POI       = calc_poi(S, Channel),
  Tx1 = Tx#{from_id => ActorId, channel_id => ChannelId,
            payload => Payload, poi => POI},
  aesc_close_solo_tx:new(update_nonce(S, Actor, Tx1)).

sc_close_solo_next(S, _Value, Args = [Actor, Channel, Tx]) ->
  case sc_close_solo_valid(S, Args) of
    false -> S;
    true ->
      C  = #channel{ state = CS } = get_channel(S, Channel),
      C1 = case maps:get(payload, Tx) of
             on_chain -> C;
             {_, Rnd} -> C#channel{ solo_rnd = 0, rnd = Rnd, state = CS#cs{ rnd = Rnd } }
           end,
      Lock = {maps:get(height, S) + C#channel.lock_p, CS#cs.i_am, CS#cs.r_am},
      %% C2 = C1#channel{ solo_rnd = C1#channel.rnd, locked = Lock },
      C2 = C1#channel{ locked = Lock },
      S1 = update_channel(Channel, C2, S),
      reserve_fee(maps:get(fee, Tx),
        bump_and_charge(Actor, maps:get(fee, Tx), S1))
  end.

sc_close_solo_post(S, Args, Res) ->
  common_postcond(sc_close_solo_valid(S, Args), Res).

sc_close_solo_features(S, Args, Res) ->
  Correct = sc_close_solo_valid(S, Args),
  [{correct, if Correct -> sc_close_solo; true -> false end}] ++
  [{sc_close_solo, Res}].

%% --- Operation: sc_settle ---

sc_settle_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_settle_args(S) ->
  ?LET({Actor, Channel}, gen_closed_channel_id(1, 39, S),
  ?LET(Fee, gen_fee(S),
  ?LET({IAmt, RAmt}, gen_settle_amounts(S, Channel),
       [Actor, Channel,
        #{ initiator_amount_final => IAmt,
           responder_amount_final => RAmt,
           fee                    => Fee,
           nonce                  => gen_nonce()
         }]))).

sc_settle_valid(_S, [{neither, _}, _Channel, _Tx]) -> false;
sc_settle_valid(_S, [_, fake_channel_id, _Tx]) -> false;
sc_settle_valid(S, [Actor, Channel, Tx]) ->
  is_account(S, Actor)
  andalso is_channel_party(S, Actor, Channel)
  andalso is_channel_closed(S, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_fee(S, Tx)
  andalso check_balance(S, Actor, maps:get(fee, Tx))
  andalso is_valid_settle(S, Channel, Tx).

sc_settle_tx(S, [Actor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  Tx1 = Tx#{from_id => ActorId, channel_id => ChannelId},
  aesc_settle_tx:new(update_nonce(S, Actor, Tx1)).

sc_settle_next(S, _Value, Args = [Actor, Channel, Tx]) ->
  case sc_settle_valid(S, Args) of
    false -> S;
    true ->
      C  = get_channel(S, Channel),
      S1 = delete_channel(Channel, S),
      reserve_fee(maps:get(fee, Tx),
        bump_and_charge(Actor, maps:get(fee, Tx),
          credit(?ACCOUNT(C#channel.init), maps:get(initiator_amount_final, Tx),
            credit(?ACCOUNT(C#channel.resp), maps:get(responder_amount_final, Tx), S1))))
  end.

sc_settle_post(S, Args, Res) ->
  common_postcond(sc_settle_valid(S, Args), Res).

sc_settle_features(S, Args, Res) ->
  Correct = sc_settle_valid(S, Args),
  [{correct, if Correct -> sc_settle; true -> false end}] ++
  [{sc_settle, Res}].

%% --- Operation: sc_force_progress ---

sc_force_progress_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_force_progress_args(S) ->
  ?LET({Actor, Channel}, gen_active_channel_id(1, 39, S),
  ?LET(Payload, gen_fp_payload(S, Channel),
       [Actor, Channel, #{ fee     => gen_big_fee(S, 1000000),
                           payload => Payload,
                           round   => gen_round(S, Channel, Payload),
                           nonce   => gen_nonce() }])).

sc_force_progress_valid(_S, [{neither, _}, _Channel, _Tx]) -> false;
sc_force_progress_valid(_S, [_, fake_channel_id, _Tx]) -> false;
sc_force_progress_valid(S, [Actor, Channel, Tx = #{ payload := Payload }]) ->
  is_account(S, Actor)
  andalso is_channel_party(S, Actor, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_sc_fee(S, Tx)
  andalso is_valid_fp_payload(S, Channel, maps:get(payload, Tx))
  andalso is_valid_round(S, Channel, Payload, maps:get(round, Tx), fp)
  andalso check_balance(S, Actor, maps:get(fee, Tx)).

sc_force_progress_tx(S, [Actor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  {S1, Payload, Trees, Round} =
    case maps:get(payload, Tx) of
      on_chain ->
        {_, Ts} = calc_payload_and_trees(S, Channel, 1),
        {S, <<>>, Ts, maps:get(round, Tx)};
      payload  ->
        Rnd = maps:get(round, Tx),
        Sx  = create_cs(S, Channel, Rnd),
        {Pl, Ts} = calc_payload_and_trees(Sx, Channel, Rnd),
        {Sx, Pl, Ts, Rnd + 1}
    end,

  S2 = call_cs(S1, Channel, Actor, Round),
  StateHash = calc_state_hash(S2, Channel),
  Update    = calc_update(S2, Channel),

  Tx1 = Tx#{from_id => ActorId, channel_id => ChannelId, payload => Payload,
            round => Round, %% The round "after" the force_progress
            update => Update, state_hash => StateHash, offchain_trees => Trees},
  aesc_force_progress_tx:new(update_nonce(S, Actor, Tx1)).

sc_force_progress_next(S, _Value, Args = [Actor, Channel, Tx]) ->
  case sc_force_progress_valid(S, Args) of
    false -> S;
    true ->
      Rnd0 = maps:get(round, Tx),
      {S1, Rnd} =
        case maps:get(payload, Tx) of
          on_chain -> {S, Rnd0};
          payload  -> {create_cs(S, Channel, Rnd0), Rnd0 + 1} end,

      S2 = call_cs(S1, Channel, Actor, Rnd),
      Update = calc_update(S2, Channel),

      %% TODO: cleanup
      ABI = aesc_offchain_update:extract_abi_version(Update),
      {_, GasPrice, _} = aesc_offchain_update:extract_amounts(Update),

      GasUsed = case ABI of
                  ?ABI_AEVM_1 -> 10000;
                  ?ABI_FATE_1 -> 156
                end,

      C = #channel{ state = CS } = get_channel(S2, Channel),
      Lock = case C#channel.locked of
               false -> false;
               _ ->  {maps:get(height, S) + C#channel.lock_p, CS#cs.i_am, CS#cs.r_am}
             end,
      C1 = case C#channel.solo_rnd of
             0 -> C#channel{ solo_rnd = Rnd, rnd = Rnd, locked = Lock };
             _ -> C#channel{ rnd = Rnd, locked = Lock }
           end,
      %% C1 = case maps:get(payload, Tx) of
      %%          on_chain -> C#channel{ solo_rnd = Rnd, locked = Lock };
      %%          %% BUG
      %%          payload  -> C#channel{ solo_rnd = Rnd, rnd = Rnd - 1, locked = Lock }
      %%          %% payload  -> C#channel{ solo_rnd = Rnd, locked = Lock }
      %%      end,
      S3 = update_channel(Channel, C1, S2),
      reserve_fee(maps:get(fee, Tx) + GasUsed * GasPrice,
        bump_and_charge(Actor, maps:get(fee, Tx) + GasUsed * GasPrice, S3))
  end.

sc_force_progress_post(S, Args, Res) ->
  common_postcond(sc_force_progress_valid(S, Args), Res).

sc_force_progress_features(S, Args, Res) ->
  Correct = sc_force_progress_valid(S, Args),
  [{correct, if Correct -> sc_force_progress; true -> false end}] ++
  [{sc_force_progress, Res}].

%% --- Operation: sc_slash ---

sc_slash_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_slash_args(S) ->
  ?LET({Actor, Channel}, gen_locked_channel_id(1, 39, S),
       [Actor, Channel, #{ fee   => gen_big_fee(S),
                           round => gen_round(S, Channel),
                           nonce => gen_nonce() }]).

sc_slash_valid(_S, [{neither, _}, _Channel, _Tx]) -> false;
sc_slash_valid(_S, [_, fake_channel_id, _Tx]) -> false;
sc_slash_valid(S, [Actor, Channel, Tx]) ->
  is_account(S, Actor)
  andalso is_channel_party(S, Actor, Channel)
  andalso is_channel_locked(S, Channel)
  andalso maps:get(nonce, Tx) == good
  andalso valid_sc_fee(S, Tx)
  andalso is_valid_round(S, Channel, maps:get(round, Tx))
  andalso check_balance(S, Actor, maps:get(fee, Tx)).

sc_slash_tx(S, [Actor, Channel, Tx]) ->
  ActorId   = aeser_id:create(account, get_actor_key(S, Actor)),
  ChannelId = aeser_id:create(channel, get_channel_id(S, Channel)),
  Payload   = calc_payload(S, Channel, maps:get(round, Tx)),
  POI       = calc_poi(S, Channel),
  Tx1 = Tx#{from_id => ActorId, channel_id => ChannelId,
            payload => Payload, poi => POI},
  aesc_slash_tx:new(update_nonce(S, Actor, Tx1)).

sc_slash_next(S, _Value, Args = [Actor, Channel, Tx]) ->
  case sc_slash_valid(S, Args) of
    false -> S;
    true ->
      C  = #channel{ state = CS } = get_channel(S, Channel),
      C1 = C#channel{ rnd   = maps:get(round, Tx),
                      state = CS#cs{ rnd = maps:get(round, Tx) } },

      Lock = {maps:get(height, S) + C1#channel.lock_p, CS#cs.i_am, CS#cs.r_am},
      %% C2 = C1#channel{ solo_rnd = C1#channel.rnd, locked = Lock },
      C2 = C1#channel{ solo_rnd = 0, locked = Lock },
      %% C2 =  C1#channel{ locked = Lock },
      S1 = update_channel(Channel, C2, S),
      reserve_fee(maps:get(fee, Tx),
        bump_and_charge(Actor, maps:get(fee, Tx), S1))
  end.

sc_slash_post(S, Args, Res) ->
  common_postcond(sc_slash_valid(S, Args), Res).

sc_slash_features(S, Args, Res) ->
  Correct = sc_slash_valid(S, Args),
  [{correct, if Correct -> sc_slash; true -> false end}] ++
  [{sc_slash, Res}].

%% --- Operation: sc_offchain ---

sc_offchain_pre(S) ->
  maps:size(maps:get(channels, S)) > 0.

sc_offchain_args(S) ->
  ?LET(Channel, gen_channel_id(S),
  ?LET(Op, gen_offchain_op(S, Channel), [Channel, Op])).

sc_offchain_valid(S, [Channel, _]) ->
  is_channel(S, Channel).

sc_offchain_tx(_S, _Args) ->
  {ok, no_tx}.

sc_offchain_next(S, _Value, [Channel, Cmd]) ->
  case get_channel(S, Channel) of
    C = #channel{ state = CS = #cs{ i_am = IA, r_am = RA, rnd = Rnd } } ->
      case Cmd of
        {trf, From, _To, Amt} ->
          CS1 = CS#cs{ cmds = CS#cs.cmds ++ [{Rnd + 1, Cmd}], rnd = Rnd + 1 },
          CS2 = if C#channel.init == From -> CS1#cs{ i_am = IA - Amt, r_am = RA + Amt };
                   C#channel.resp == From -> CS1#cs{ i_am = IA + Amt, r_am = RA - Amt }
                end,
          update_channel(Channel, C#channel{ state = CS2 }, S);
        no_op ->
          S
      end;
    _ ->
      S
  end.

sc_offchain_post(_S, _Args, _Res) ->
  true.

sc_offchain_features(S, Args, Res) ->
  Correct = sc_offchain_valid(S, Args),
  [{correct, if Correct -> sc_offchain; true -> false end}] ++
  [{sc_offchain, Res}].

%% -- Weight -----------------------------------------------------------------

weight(S, sc_create) ->
  NAccounts = maps:size(maps:get(accounts, S)),
  case good_accounts(S) of
    [] -> 0;
    Xs -> case maps:is_key(ga, S) of
            true   when NAccounts > 1  -> 8;
            false  when length(Xs) > 1 -> 10;
            _ -> 0 end
    end;
weight(S, Fun) when Fun == sc_deposit; Fun == sc_withdraw;
                    Fun == sc_snapshot_solo ->
  case good_active_channels(S) of
    [] -> 0;
    _  -> 10 end;
weight(S, Fun) when Fun == sc_close_solo; Fun == sc_close_mutual; Fun == sc_force_progress ->
  case good_channels(S) of
    [] -> 0;
    _  -> 4 end;
weight(S, sc_slash) ->
  case good_locked_channels(S) of
    [] -> 0;
    _  -> 10 end;
weight(S, sc_settle) ->
  case good_closed_channels(S) of
    [] -> 0;
    _  -> 10 end;
weight(S, sc_offchain) ->
  case maps:size(maps:get(channels, S)) > 0
       andalso not maps:is_key(ga, S) andalso not maps:is_key(paying_for, S) of
    true  -> 8;
    false -> 0 end;
weight(_S, _) -> 0.

%% -- Generators -------------------------------------------------------------

classify_channels(S) ->
  [ classify_channel(S, ChId) || ChId <- maps:keys(maps:get(channels, S, #{})) ].

classify_channel(S, ChId) ->
  #channel{ init = Init, resp = Resp, locked = L } = get_channel(S, ChId),
  {ChId, {Init, is_ga(S, ?ACCOUNT(Init))}, {Resp, is_ga(S, ?ACCOUNT(Resp))}, L}.

good_channels(#{ ga := _ }, Cs) ->
  [ C || C = {_, {_, I}, {_, R}, _} <- Cs, I orelse R ];
good_channels(_S, Cs) ->
  [ C || C = {_, {_, I}, {_, R}, _} <- Cs, not I andalso not R ].

good_channels(S) -> good_channels(S, classify_channels(S)).

good_active_channels(S) ->
  [ C || C = {_, _, _, false} <- good_channels(S) ].

good_locked_channels(S) ->
  [ C || C = {_, _, _, {_, _, _}} <- good_channels(S) ].

good_closed_channels(S) ->
  [ C || C = {_, _, _, {L, _, _}} <- good_channels(S), L =< maps:get(height, S) ].

gen_channel_id(S) ->
  elements(maps:keys(maps:get(channels, S))).

gen_channel_id(Invalid, Valid, S) ->
  gen_channel_id(Invalid, Valid, S, good_channels(S)).

gen_closed_channel_id(Invalid, Valid, S) ->
  gen_channel_id(Invalid, Valid, S, good_closed_channels(S)).

gen_locked_channel_id(Invalid, Valid, S) ->
  gen_channel_id(Invalid, Valid, S, good_locked_channels(S)).

gen_active_channel_id(Invalid, Valid, S) ->
  gen_channel_id(Invalid, Valid, S, good_active_channels(S)).

gen_channel_id(_, _, S, []) ->
  case maps:keys(maps:get(channels, S)) of
    [] -> {gen_account(0, 1, S), fake_channel_id};
    Cs -> frequency([{3, ?LET(C, elements(Cs), {gen_account(0, 1, S), ?CHANNEL(C)})},
                     {1, {gen_account(0, 1, S), fake_channel_id}}])
  end;
gen_channel_id(Invalid, Valid, S, Cs) ->
  weighted_default(
    {Valid, ?LET({C, {I, IGA}, {R, RGA}, _}, elements(Cs),
                 {?LET(A, gen_channel_actor(maps:is_key(ga, S), {I, IGA}, {R, RGA}), ?ACCOUNT(A)), ?CHANNEL(C)})},
    {Invalid, frequency([{1, ?LET({C, _, _, _}, elements(Cs), {gen_account(0, 1, S), ?CHANNEL(C)})},
                         {1, ?LET({C, _, _, _}, elements(Cs), {{neither, noshrink(binary(32))}, ?CHANNEL(C)})}])}).

gen_channel_actor(true, {I, IGA}, {R, RGA})  -> elements([I || IGA] ++ [R || RGA]);
gen_channel_actor(false, {I, IGA}, {R, RGA}) -> elements([I || not IGA] ++ [R || not RGA]).

gen_round(S, ChId, on_chain) -> gen_round_(S, ChId, 1);
gen_round(S, ChId, payload)  -> gen_round_(S, ChId, 10).

gen_round(S, ChId) -> gen_round_(S, ChId, 10).

gen_round_(S, ChId, MaxDelta) ->
  case get_channel(S, ChId) of
    false ->
      choose(1, 10);
    #channel{ state = #cs{ rnd = OffChainRnd }, rnd = OnChainRnd, solo_rnd = SoloRnd } ->
      Rnd = lists:max([OffChainRnd, OnChainRnd, SoloRnd]),
      frequency([{39, Rnd + 1},
                 {10, ?LET(Delta, choose(1, MaxDelta), OnChainRnd + Delta) },
                 {1,  ?LET(Delta, choose(0, 5), max(0, OnChainRnd - Delta))}])
  end.

gen_sc_create_amounts(S, Init, Resp) ->
  ?LET({I, R}, {gen_amount(S, Init), gen_amount(S, Resp)},
       frequency([{49, {I, R, rnd(min(I, R) div 5)}},
                  {40, {I, R, 0}},
                  {1,  oneof([{I, R, min(I, R) + 1}, {0, R, 1}, {I, 0, 1}])}])).

gen_amount(S, A) ->
  case get_account(S, A) of
    #account{ amount = A } when A > 1000 ->
      ?LET(X, choose(10, 20), rnd(A div X));
    _ ->
      gen_amount()
  end.

gen_amount() -> choose(0, 100000000000).

rnd(X) when X < 1000000000000 -> X;
rnd(X) -> (X div 1000000000000) * 1000000000000.

gen_withdraw_amount(S, Channel) ->
  case get_channel(S, Channel) of
    #channel{ ch_rsv = R, state = #cs{ i_am = IA, r_am = RA, c_am = CA } } ->
      frequency([{44, min((IA - R) div 5, (RA - R) div 5)},
                 {5,  min((IA - R), (RA - R))},
                 {1,  ?LET(Delta, choose(1, 1000), (IA + RA + CA) - 2 * R + Delta)}]);
    _ ->
      gen_amount()
  end.

gen_close_mutual_amounts(S, Channel, Fee) ->
  case get_channel(S, Channel) of
    #channel{ state = #cs{ i_am = IA, r_am = RA, c_am = CA } } when IA + RA + CA >= Fee ->
      ToDistribute = (IA + RA + CA) - Fee,
      ?LET(Pct, choose(0, 100),
      ?LET(DivFactor, frequency([{39, 100}, {10, choose(100, 1000)}, {1, choose(1, 99)}]),
           {(ToDistribute * Pct) div DivFactor, (ToDistribute * (100 - Pct)) div 100}));
    _ ->
      {gen_amount(), gen_amount()}
  end.

gen_settle_amounts(S, Channel) ->
  case get_channel(S, Channel) of
    #channel{ locked = {_, IA, RA} } ->
      weighted_default({49, {IA, RA}}, {1, {IA + 5, max(0, RA - 5)}});
    _ -> {gen_amount(), gen_amount()}
  end.

gen_lock_period() -> choose(0, 5).

gen_offchain_op(S, ChId) ->
  case get_channel(S, ChId) of
    #channel{ state = CS, init = I, resp = R, ch_rsv = CR } ->
      #cs{ i_am = IA, r_am = RA } = CS,
      frequency([{1, ?LET({From, To, A}, elements([{I, R, IA - CR}, {R, I, RA - CR}]),
                          {trf, From, To, rnd(A div 5)})}]);
    _ ->
      no_op
  end.

gen_fp_payload(S, ChId) ->
  case get_channel(S, ChId) of
    #channel{ state = #cs{ c_am = CA, rnd = R}, rnd = R } when CA > 0 ->
      weighted_default({3, on_chain}, {1, payload});
    _ ->
      payload
  end.

gen_payload(S, ChId) ->
  case get_channel(S, ChId) of
    #channel{ state = #cs{ rnd = R }, rnd = R } ->
      elements([payload, on_chain]);
    _ ->
      payload
  end.

gen_big_fee(S) -> gen_big_fee(S, 40000).

gen_big_fee(#{ protocol := P }, Min) ->
  weighted_default({49, ?LET(Delta, choose(0, 5000), (Min + Delta) * minimum_gas_price(P))},
                   {1 , ?LET(Delta, choose(0, 2000), (17000 - Delta) * minimum_gas_price(P))}).

%% --- local helpers ------
valid_sc_fee(#{protocol := P}, #{ fee := Fee }) ->
  Fee > (17000 * minimum_gas_price(P)).

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
    #channel{ init = ActorId } -> true;
    #channel{ resp = ActorId } -> true;
    _ -> false
  end;
is_channel_party(_, _, _) ->
  false.

is_channel_locked(S, ChId) ->
  case get_channel(S, ChId) of
    #channel{ locked = {_, _, _} } -> true;
    _                              -> false
  end.

is_channel_active(S, ChId) ->
  case get_channel(S, ChId) of
    #channel{ locked = false } -> true;
    _                          -> false
  end.

is_channel_closed(S, ChId) ->
  case get_channel(S, ChId) of
    #channel{ locked = {L, _, _} } -> L =< maps:get(height, S);
    _                              -> false
  end.

get_not_actor(S, ChId, ?ACCOUNT(ActorId)) ->
  case get_channel(S, ChId) of
    C = #channel{ init = ActorId } -> ?ACCOUNT(C#channel.resp);
    C = #channel{ resp = ActorId } -> ?ACCOUNT(C#channel.init);
    _ -> not_an_account
  end;
get_not_actor(_, _, _) -> not_an_account.

get_actor_key(_S, {neither, Key}) -> Key;
get_actor_key(S, A)               -> get_account_key(S, A).

update_channel(?CHANNEL(ChId), Ch, S) ->
  update_channel(ChId, Ch, S);
update_channel(ChId, Ch, S = #{ channels := Chs }) ->
  S#{ channels := Chs#{ ChId => Ch } }.

delete_channel(?CHANNEL(ChId), S) ->
  delete_channel(ChId, S);
delete_channel(ChId, S = #{ channels := Chs }) ->
  S#{ channels := maps:remove(ChId, Chs) }.

is_valid_round(S, ChId, Payload, Rnd, fp) ->
  case get_channel(S, ChId) of
    #channel{ rnd = Rnd1, solo_rnd = Rnd2 } ->
      if Payload == on_chain -> Rnd == max(Rnd1, Rnd2) + 1;
         true                -> Rnd > max(Rnd1, Rnd2)
      end;
    _ -> false
  end.

is_valid_round(S, ChId, on_chain, Rnd) ->
  case get_channel(S, ChId) of
    #channel{ rnd = Rnd1, solo_rnd = Rnd2 } -> Rnd == max(Rnd1, Rnd2) + 1;
    _ -> false
  end;
is_valid_round(S, ChId, payload, Rnd) ->
  is_valid_round(S, ChId, Rnd).

is_valid_round(S, ChId, Rnd) ->
  case get_channel(S, ChId) of
    #channel{ rnd = Rnd1, solo_rnd = SRnd } -> Rnd > Rnd1 orelse (SRnd > 0 andalso Rnd >= SRnd);
    _ -> false
  end.

is_valid_withdraw(S, ChId, Amt) ->
  case get_channel(S, ChId) of
    #channel{ ch_rsv = R, state = #cs{ i_am = IA, r_am = RA, c_am = CA } }
      when (IA + RA + CA) - 2 * R >= Amt -> true;
    _ -> false
  end.

is_valid_close_mutual(S, ChId, #{initiator_amount_final := IAf,
                                 responder_amount_final := RAf,
                                 fee := Fee}) ->
  case get_channel(S, ChId) of
    #channel{ state = #cs{ i_am = IA, r_am = RA, c_am = CA } }
        when (IA + RA + CA - Fee) >= IAf + RAf -> true;
    _ -> false
  end.

is_valid_settle(S, ChId, #{initiator_amount_final := IA,
                           responder_amount_final := RA }) ->
  case get_channel(S, ChId) of
    #channel{ locked = {_, IA, RA} } -> true;
    _ -> false
  end.

is_valid_payload(S, Channel, on_chain) ->
  case get_channel(S, Channel) of
    #channel{ state = #cs{ rnd = R1 }, rnd = R2, solo_rnd = SR } -> R1 == R2 orelse R1 == SR;
    _ -> false
  end;
is_valid_payload(_, _, _) -> true.

is_valid_fp_payload(_S, _ChId, payload) -> true;
is_valid_fp_payload(S, ChId, on_chain) ->
  case get_channel(S, ChId) of
    #channel{ state = #cs{ c_am = CA, rnd = R}, rnd = R } when CA > 0 -> true;
    _ -> false
  end.


init_cs(?ACCOUNT(I), ?ACCOUNT(R),
        #{ initiator_amount := IA, responder_amount := RA }) ->
  #cs{ i_am = IA, r_am = RA, rnd = 1, cmds = [{1, {create, I, IA, R, RA}}] };
init_cs(_, _, _) -> #cs{ i_am = 0, r_am = 0, cmds = [] }.

credit_cs(CS = #cs{ i_am = A0 }, i, A1) -> CS#cs{ i_am = A0 + A1 };
credit_cs(CS = #cs{ r_am = A0 }, r, A1) -> CS#cs{ r_am = A0 + A1 };
credit_cs(CS = #cs{ c_am = A0 }, c, A1) -> CS#cs{ c_am = A0 + A1 }.

deposit_cs(S, ChId, ?ACCOUNT(A), #{ amount := Amt, round := Rnd }) ->
  dep_wtd_cs(S, ChId, A, {dep, A, Amt}, Amt, Rnd);
deposit_cs(_, _, _, _) -> #cs{ }.

withdraw_cs(S, ChId, ?ACCOUNT(A), #{ amount := Amt, round := Rnd }) ->
  dep_wtd_cs(S, ChId, A, {wtd, A, Amt}, -Amt, Rnd);
withdraw_cs(_, _, _, _) -> #cs{ }.

dep_wtd_cs(S, ChId, A, Cmd, Amt, Rnd) ->
  case get_channel(S, ChId) of
    C = #channel{ state = CS = #cs{ cmds = Cmds } } ->
      CS1 = CS#cs{ rnd = Rnd, cmds = Cmds ++ [{Rnd, Cmd}] },
      if A == C#channel.init -> credit_cs(CS1, i, Amt);
         A == C#channel.resp -> credit_cs(CS1, r, Amt);
         true                -> CS#cs{ rnd = Rnd }
      end;
    _ -> #cs{ }
  end.

create_cs(S, ChId, Rnd) ->
  case get_channel(S, ChId) of
    C = #channel{ state = CS, init = Init, resp = Resp, ch_rsv = Rsv } ->
      case [x || {_, {contract, _}} <- CS#cs.cmds ] of
        [_] ->
          CS1 = CS#cs{ rnd = Rnd },
          update_channel(ChId, C#channel{ state = CS1 }, S);
        [] ->
          #cs{ i_am = IA, r_am = RA, cmds = Cmds } = CS,
          IA2 = (IA - Rsv) div 2,
          RA2 = (RA - Rsv) div 2,
          ABI = case maps:get(protocol, S) >= ?LIMA_PROTOCOL_VSN of
                  true -> ?ABI_FATE_1; false -> ?ABI_AEVM_1 end,
          CS1 = CS#cs{ i_am = IA - IA2, r_am = RA - RA2,
                       c_am = IA2 + RA2, cabi = ABI,
                       rnd  = Rnd, cmds = Cmds ++ [{Rnd, {wtd, Init, IA2}},
                                                   {Rnd, {wtd, Resp, RA2}},
                                                   {Rnd, {contract, IA2 + RA2}}] },
          update_channel(ChId, C#channel{ state = CS1 }, S)
      end;
    _ ->
      S
  end.

call_cs(S, ChId, ?ACCOUNT(A), Rnd) ->
  case get_channel(S, ChId) of
    C = #channel{ state = CS } ->
      case [x || {_, {contract, _}} <- CS#cs.cmds ] of
        [_] ->
          #cs{ c_am = CA, cmds = Cmds, cabi = ABI } = CS,
          CS1 = CS#cs{ c_am = CA - CA div 2, rnd = Rnd,
                       cmds = Cmds ++ [{Rnd, {ccall, A, Rnd, ABI}}] },
          CS2 = if A == C#channel.init -> credit_cs(CS1, i, CA div 2);
                   A == C#channel.resp -> credit_cs(CS1, r, CA div 2);
                   true                -> CS
                end,
          update_channel(ChId, C#channel{ state = CS2 }, S);
        _ ->
          S
      end;
    _ ->
      S
  end;
call_cs(S, _, _, _) -> S.

calc_state_hash(S, ?CHANNEL(_) = ChId) ->
  #channel{ state = CS } = get_channel(S, ChId),
  calc_state_hash(S, CS);
calc_state_hash(S, #cs{ cmds = Cmds }) ->
  Trees = calc_state_trees(S, Cmds),
  aec_trees:hash(Trees);
calc_state_hash(_, _) -> <<0:256>>.

calc_state_trees(S, Cmds) ->
  calc_state_trees(S, Cmds, aec_trees:new_without_backend()).

calc_state_trees(_S, [], Trees) -> Trees;
calc_state_trees(S, [{R, {wtd, A, Amt}} | Cmds], Trees) ->
  calc_state_trees(S, [{R, {dep, A, -Amt}} | Cmds], Trees);
calc_state_trees(S, [{R, {trf, A, B, Amt}} | Cmds], Trees) ->
  calc_state_trees(S, [{R, {wtd, A, Amt}}, {R, {dep, B, Amt}} | Cmds], Trees);
calc_state_trees(S, [{_, {dep, A, Amt}} | Cmds], Trees) ->
  ATrees0  = aec_trees:accounts(Trees),
  A0       = aec_accounts_trees:get(get_account_key(S, ?ACCOUNT(A)), ATrees0),
  {ok, A1} = earn(A0, Amt),
  ATrees1  = aec_accounts_trees:enter(A1, ATrees0),
  calc_state_trees(S, Cmds, aec_trees:set_accounts(Trees, ATrees1));

calc_state_trees(S, [{_, {contract, Amt}} | Cmds], Trees) ->
  AC = aec_accounts:new(<<1:256>>, Amt),
  ATrees = aec_accounts_trees:enter(AC, aec_trees:accounts(Trees)),
  Trees1 = aec_trees:set_accounts(Trees, ATrees),

  OwnerId  = aeser_id:create(account, <<1:256>>),
  {VmVersion, ABIVersion, Code} =
    case maps:get(protocol, S) of
      Vsn when Vsn >= ?LIMA_PROTOCOL_VSN -> {5, 3, maps:get({code, 5}, txs_contracts_eqc:contract(offchain))}
    end,
  {ok, CallData} = calc_calldata(ABIVersion, init),
  CreateOp = aesc_offchain_update:op_new_contract(OwnerId, VmVersion, ABIVersion, Code, Amt, CallData),
  Env      = aetx_env:tx_env(maps:get(height, S), maps:get(protocol, S)),
  NoTrees  = aec_trees:new_without_backend(),
  Trees2   = aesc_offchain_update:apply_on_trees(CreateOp, Trees1, NoTrees, Env, 1, 0),
  calc_state_trees(S, Cmds, Trees2);

calc_state_trees(S = #{ protocol := P }, [{_, {ccall, A, Round, ABI}} | Cmds], Trees) ->
  CallOp   = calc_call_op(S, A, ABI),
  Env      = aetx_env:tx_env(maps:get(height, S), P),
  NoTrees  = aec_trees:new_without_backend(),
  PTrees   = aect_call_state_tree:prune_without_backend(Trees),
  Trees1   = aesc_offchain_update:apply_on_trees(CallOp, PTrees, NoTrees, Env, max(1, Round), 0),
  calc_state_trees(S, Cmds, Trees1);

calc_state_trees(S, [{_, {create, I, IA, R, RA}} | Cmds], Trees) ->
  AI     = aec_accounts:new(get_account_key(S, ?ACCOUNT(I)), IA),
  AR     = aec_accounts:new(get_account_key(S, ?ACCOUNT(R)), RA),
  ATrees = aec_accounts_trees:enter(AI,
             aec_accounts_trees:enter(AR, aec_trees:accounts(Trees))),
  calc_state_trees(S, Cmds, aec_trees:set_accounts(Trees, ATrees)).

calc_call_op(S = #{ protocol := P }, A, ABI) ->
  CallerId = aeser_id:create(account, get_account_key(S, ?ACCOUNT(A))),
  ContractPK = aect_contracts:compute_contract_pubkey(<<1:256>>, 1),
  ContractId = aeser_id:create(contract, ContractPK),
  {ok, CallData} = calc_calldata(ABI, transfer),
  aesc_offchain_update:op_call_contract(CallerId, ContractId, ABI, 0,
                                        CallData, [], minimum_gas_price(P), 10000).

calc_update(S, ChId) ->
  case get_channel(S, ChId) of
    #channel{ state = CS } ->
      case lists:last(CS#cs.cmds) of
        {_, {ccall, A, _R, ABI}} -> calc_call_op(S, A, ABI);
        _                        -> aesc_offchain_update:op_meta(<<>>)
      end;
    _ -> aesc_offchain_update:op_meta(<<>>)
  end.

calc_payload(S, ChId, Round) ->
  {Payload, _Trees} = calc_payload_and_trees(S, ChId, Round),
  Payload.

calc_payload_and_trees(S, ChId, Round) ->
  case get_channel(S, ChId) of
    #channel{ state = CS, init = Init, resp = Resp, i_auth = IA, r_auth = RA } ->
      Trees = calc_state_trees(S, CS#cs.cmds),
      StateHash = aec_trees:hash(Trees),

      ChannelId = aeser_id:create(channel, get_channel_id(S, ChId)),
      {ok, Tx}  = aesc_offchain_tx:new(#{ state_hash => StateHash,
                                          channel_id => ChannelId,
                                          round      => Round}),
      STx = sign(S, [{Init, IA}, {Resp, RA}], Tx),
      {aetx_sign:serialize_to_binary(STx), Trees};
    _ ->
      {<<>>, aec_trees:new_without_backend()}
  end.

calc_poi(S, ChId) ->
  case get_channel(S, ChId) of
    #channel{ state = CS, init = Init, resp = Resp } ->
      Trees = calc_state_trees(S, CS#cs.cmds),
      poi([{account, get_account_key(S, ?ACCOUNT(Init))},
           {account, get_account_key(S, ?ACCOUNT(Resp))}], Trees);
    _ ->
      aec_trees:new_poi(aec_trees:new_without_backend())
  end.

poi(What, Trees) ->
    add_poi(What, Trees, aec_trees:new_poi(Trees)).

add_poi([], _, PoI) -> PoI;
add_poi([{account, PK} | What], Trees, PoI) ->
    {ok, PoI1} = aec_trees:add_poi(accounts, PK, Trees, PoI),
    add_poi(What, Trees, PoI1).

earn(Acc, Amount) ->
  case aec_accounts:balance(Acc) + Amount >= 0 of
    true  -> aec_accounts:earn(Acc, Amount);
    false -> {ok, Acc} %% Negative balance is not allowed :-)
  end.

sign(S, Signers, Tx) ->
  {GAs, Keys} = get_sign(S, Signers, [], []),
  ga_wrap(S, GAs, aec_test_utils:sign_tx(Tx, [get_privkey(S, K) || K <- Keys ])).

ga_wrap(_S, [], STx) -> STx;
ga_wrap(S, [{GA, N} | GAs], STx) ->
  #account{ ga = #ga{ contract = Ct }, key = Key } = get_account(S, ?ACCOUNT(GA)),
  #contract{ abi = ABI } = txs_contracts_eqc:get_contract(S, ?CONTRACT(Ct)),
  {ok, AuthData} = txs_ga_eqc:encode_calldata(ABI, N),

  GAId = aeser_id:create(account, get_pubkey(S, ?KEY(Key))),
  Tx   = #{ ga_id => GAId, auth_data => AuthData, tx => STx,
            abi_version => txs_contracts_eqc:abi_to_int(ABI),
            gas => 5000, fee => 1, gas_price => 1000000 },
  {ok, GAMetaTx} = aega_meta_tx:new(Tx),
  ga_wrap(S, GAs, aetx_sign:new(GAMetaTx, [])).

get_sign(_S, [], GAs, PKs) -> {GAs, PKs};
get_sign(S, [{_A, Auth} | As], GAs, PKs) when is_atom(Auth) ->
  get_sign(S, As, GAs, [Auth | PKs]);
get_sign(S, [{A, Auth} | As], GAs, PKs) when is_integer(Auth) ->
  get_sign(S, As, [{A, Auth} | GAs], PKs).

get_privkey(S, Key) ->
  #key{private = PrivKey} = maps:get(Key, maps:get(keys, S)),
  PrivKey.

get_auth(S, A) ->
  #account{ ga = GA, nonce = N, key = K } = get_account(S, A),
  case GA of
    false -> K;
    #ga{} -> N
  end.

-define(STUB, "contract X =\n  entrypoint transfer : () => int\n").

calc_calldata(ABI, init) ->
  txs_contracts_eqc:encode_calldata(ABI, ?STUB, "init", []);
calc_calldata(ABI, transfer) ->
  txs_contracts_eqc:encode_calldata(ABI, ?STUB, "transfer", []).

