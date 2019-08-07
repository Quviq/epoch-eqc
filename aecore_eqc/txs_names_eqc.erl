%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Thomas Arts
%%% @doc  Modeling name system transactions
%%%
%%% @end
%%% Created : 23 May 2019 by Thomas Arts
%%% Modified: June 2019 by Clara Benac Earle

-module(txs_names_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-define(NAMEFRAGS, ["foo", "bar", "baz"]).

-record(preclaim,{name, salt, height, claimer, protocol, expires_by}).
-record(claim,{name, height, expires_by, protected_height, claimer, protocol}).


%% -- State and state functions ----------------------------------------------
initial_state() ->
  #{preclaims => [],
    claims => [],
    protected_names => [],
    named_accounts => #{}   %% Name can only be resolved if the Pointers contain "account_pubkey"
   }.


%% -- Common pre-/post-conditions --------------------------------------------

common_postcond(Correct, Res) ->
  case Res of
    {error, _} when Correct -> eq(Res, ok);
    {error, _}              -> true;
    ok when Correct         -> true;
    ok                      -> eq(ok, {error, '_'})
  end.


%% -- Operations -------------------------------------------------------------

mine_next(#{height := Height} = S, _Value, [Blocks]) ->
  ExpiredPreclaims = expired_preclaims(S, Height + Blocks),
  ExpiredClaims = expired_claims(S, Height + Blocks),
  ExpiredNames = [ {C#claim.name, C#claim.expires_by + aec_governance:name_protection_period()} || C <- ExpiredClaims ],
  ExpiredProtected = expired_protection(S, Height + Blocks),
  S#{preclaims => maps:get(preclaims, S, []) -- ExpiredPreclaims,
     claims => maps:get(claims, S, []) -- ExpiredClaims,
     protected_names =>  (maps:get(protected_names, S) -- ExpiredProtected ) ++
       [ {N, H} || {N, H} <- ExpiredNames, H >= Height + Blocks ],
     named_accounts => maps:without([ N || {N,_} <- ExpiredNames], maps:get(named_accounts, S, #{}))
    }.

mine_features(#{height := Height} = S, [Blocks], _Res) ->
  [{mine, expired_preclaims} || expired_preclaims(S, Height + Blocks) =/= [] ] ++
    [{mine, expired_claims} || expired_claims(S, Height + Blocks) =/= [] ] ++
    [{mine, expired_name_protection} || expired_protection(S, Height + Blocks) =/= [] ].




%% --- Operation: ns_preclaim ---
ns_preclaim_pre(S) ->
  maps:is_key(accounts, S).

ns_preclaim_args(S = #{height := Height}) ->
  ?LET([Sender, Name, Salt],
       [gen_account(1, 49, S), gen_name(), gen_salt()],
       [Sender, {Name, Salt},
        #{account_id => aeser_id:create(account, Sender),
          fee => gen_fee(Height),
          commitment_id =>
            aeser_id:create(commitment,
                            aens_hash:commitment_hash(Name, Salt)),
          nonce => gen_nonce()}]).

ns_preclaim_valid(S = #{height := Height}, [Sender, {Name, Salt}, Tx]) ->
  is_account(S, Sender)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso maps:get(nonce, Tx) == good
    andalso valid_fee(Height, Tx)
    andalso new_name_and_salt(maps:get(preclaims, S, []), Name, Salt).

ns_preclaim_tx(S, [Sender, {_Name, _Salt}, Tx]) ->
  aens_preclaim_tx:new(update_nonce(S, Sender, Tx)).

ns_preclaim_next(S = #{height := Height}, _Value, [Sender, {Name, Salt}, Tx] = Args) ->
  case ns_preclaim_valid(S, Args) of
    false -> S;
    true  ->
      #{ fee := Fee } = Tx,
      Preclaim = #preclaim{name    = Name,
                           salt    = Salt,
                           height  = Height,
                           expires_by = Height + aec_governance:name_preclaim_expiration(),
                           claimer = Sender,
                           protocol = aec_hard_forks:protocol_effective_at_height(Height)},
      reserve_fee(Fee,
                  bump_and_charge(Sender, Fee,
                                  add(preclaims, Preclaim, S)))
  end.

ns_preclaim_post(S, Args, Res) ->
  common_postcond(ns_preclaim_valid(S, Args), Res).


ns_preclaim_features(S, [_Sender, {_Name, _Salt}, _Tx] = Args, Res) ->
  Correct = ns_preclaim_valid(S, Args),
  [{correct, if Correct -> ns_preclaim; true -> false end},
   {ns_preclaim, Res} ].

%% --- Operation: ns_claim ---
ns_claim_pre(S) ->
  maps:is_key(accounts, S) andalso maps:get(preclaims, S, []) /= [].

ns_claim_args(S = #{height := Height}) ->
  ?LET({Name, Salt, Sender}, gen_claim(S),
       [Sender,
        #{account_id => aeser_id:create(account, Sender),
          name => Name,
          name_salt => Salt,
          fee => gen_fee(Height),
          nonce => gen_nonce()}]).

ns_claim_valid(S = #{height := Height}, [Sender, #{name := Name} = Tx]) ->
  is_account(S, Sender)
    andalso check_balance(S, Sender, maps:get(fee, Tx))
    andalso maps:get(nonce, Tx) == good
    andalso valid_fee(Height, Tx)
    andalso is_valid_preclaim(S, Tx, Sender)
    andalso not is_claimed(S, Name)
    andalso not is_protected(S, Name).

is_valid_preclaim(#{preclaims := Ps, height := Height}, Tx = #{name := Name, name_salt := Salt}, Claimer) ->
  case [ PC || PC = #preclaim{name = N, salt = Sa, claimer = C} <- Ps,
               Name == N, Salt == Sa, Claimer == C ] of
    [] -> false;
    [#preclaim{ height = H }] ->
      H + aec_governance:name_claim_preclaim_delta() =< Height
        andalso Height < H +  aec_governance:name_preclaim_expiration()  %% this is always the case in this model
        andalso valid_name(Tx)
  end.

%% names may not have dots in between, only at the end (.test)
valid_name(Tx) ->
  case string:lexemes(maps:get(name,Tx), ".") of
    [_, <<"test">>] -> true;
    _ -> false
  end.

ns_claim_tx(S, [Sender, Tx]) ->
  aens_claim_tx:new(update_nonce(S, Sender, Tx)).

ns_claim_next(S = #{height := Height}, _Value, [Sender, Tx] = Args) ->
  case ns_claim_valid(S, Args) of
    false -> S;
    true  ->
      #{ fee := Fee, name := Name } = Tx,
      Claim = #claim{name    = Name,
                     height  = Height,
                     expires_by = Height + aec_governance:name_claim_max_expiration(),
                     claimer = Sender,
                     protocol = aec_hard_forks:protocol_effective_at_height(Height)},
      remove_preclaim(Tx,
                      reserve_fee(Fee,
                                  bump_and_charge(Sender, Fee,
                                                  add(claims, Claim, S))))
  end.

ns_claim_post(S, Args, Res) ->
  common_postcond(ns_claim_valid(S, Args), Res).


ns_claim_features(S =  #{height := Height}, [_Sender, Tx] = Args, Res) ->
  Correct = ns_claim_valid(S, Args),
  [{correct, if Correct -> ns_claim; true -> false end},
   {ns_claim, Res}] ++
    [ {ns_claim, {protocol,
       aec_hard_forks:protocol_effective_at_height(Height) -
         get_preclaim_protocol(Tx,S)}} || Correct ].

%% --- Operation: ns_update ---

ns_update_pre(S) ->
  maps:is_key(accounts, S).

ns_update_args(S = #{height := Height}) ->
  ?LET({{Name, Sender}, Pointers},
       {gen_claimed_name(S), gen_pointers(S)},
       [Name, Sender, Pointers,
        #{account_id => aeser_id:create(account, Sender),
          name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
          name_ttl => frequency([{10, nat()}, {1, 36000}, {10, 25000}, {1, choose(30000, 60000)}]),
          client_ttl => nat(),
          fee => gen_fee(Height),
          nonce => gen_nonce(),
          pointers =>
            [ case Kind of
                account -> aens_pointer:new(<<"account_pubkey">>, aeser_id:create(account, Key));  %% only then named account
                oracle -> aens_pointer:new(<<"oracle">>, aeser_id:create(oracle, Key));
                fake -> aens_pointer:new(<<"fake">>, aeser_id:create(account, Key))
                        %% We need create. Otherwise crashes for unknown types, because specialize type in aeser_id is used.
                        %% This means that such a transaction cannot be created (which makes sense if serialization of it is undefined
              end || {Kind, Key} <- Pointers ]
         }]).

ns_update_valid(#{height := Height} = S, [Name, Sender, _Pointers, Tx]) ->
  is_account(S, Sender)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Sender, maps:get(fee, Tx) + aec_governance:name_claim_locked_fee())
    andalso valid_fee(Height, Tx)
    andalso maps:get(name_ttl, Tx) =< aec_governance:name_claim_max_expiration()
    andalso owns_name(S, Sender, Name)
    andalso is_valid_name(S, Name, Height).

ns_update_tx(S, [_Name, Sender, _Pointers, Tx]) ->
  aens_update_tx:new(update_nonce(S, Sender, Tx)).
ns_update_next(#{height := Height} = S, _, [Name, Sender, Pointers, Tx] = Args) ->
  case ns_update_valid(S, Args) of
    false -> S;
    true  ->
      #{ fee := Fee, name_ttl := TTL } = Tx,
      S1 = case lists:keyfind(account, 1, Pointers) of
             false -> remove_named_account(Name, S);
             {_, Key}  -> add_named_account(Name, Key, S)
           end,
      reserve_fee(Fee,
                  bump_and_charge(Sender, Fee,
                                  update_claim_height(Name, Height, TTL, S1)))
  end.

ns_update_features(S, [_Name, _Sender, Pointers, _Tx] = Args, Res) ->
  Correct = ns_update_valid(S, Args),
  [{correct, if Correct -> ns_update; true -> false end},
   {ns_update, Res}] ++
    [{ns_update, [ Kind || {Kind, _} <- Pointers]}].


%% --- Operation: ns_revoke ---


%% -- weight ---------------------------------------------------------------

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
    _ -> 5 end;

weight(_S, _) -> 0.

%% -- Transactions modifiers

update_nonce(S, Sender, Tx) ->
  txs_spend_eqc:update_nonce(S, Sender,Tx).


%% -- State update and query functions ---------------------------------------
expired_preclaims(S, Height) ->
  [ P || P <- maps:get(preclaims, S, []), P#preclaim.expires_by < Height].

expired_claims(S, Height) ->
  [ C || C <- maps:get(claims, S, []),
         C#claim.expires_by < Height ].

expired_protection(S, Height) ->
  [ {N, H} || {N, H} <- maps:get(protected_names, S), H < Height ].

good_preclaims(#{ preclaims := Ps, height := H}) ->
  [ P || P = #preclaim{ height = H0 } <- Ps, H0 < H ].

add(Tag, X, S) ->
  S#{ Tag => maps:get(Tag, S, []) ++ [X] }.

remove(Tag, X, I, S) ->
  S#{ Tag := lists:keydelete(X, I, maps:get(Tag, S)) }.

remove_named_account(Name, S) ->
  S#{ named_accounts => maps:remove(Name, maps:get(named_accounts, S, #{})) }.

add_named_account(Name, Acc, S) ->
  S#{ named_accounts => maps:merge(maps:get(named_accounts, S, #{}), #{ Name => Acc }) }.




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



%% --- local helpers ------


is_account(S, Key) ->
  txs_spend_eqc:is_account(S, Key).

reserve_fee(Fee, S) ->
  txs_spend_eqc:reserve_fee(Fee, S).

bump_and_charge(Key, Fee, S) ->
  txs_spend_eqc:bump_and_charge(Key, Fee, S).

check_balance(S, Sender, Amount) ->
  txs_spend_eqc:check_balance(S, Sender, Amount).

new_name_and_salt(Ps, Name, Salt) ->
  [ P || P = #preclaim{name = Na, salt = Sa} <- Ps,
         Na == Name andalso Sa == Salt ] == [].

valid_fee(H, #{ fee := Fee }) ->
  Fee >= 20000 * minimum_gas_price(H).   %% not precise, but we don't generate fees in the shady range

is_claimed(#{claims := Cs}, Name) ->
  lists:keymember(Name, #claim.name, Cs).

remove_preclaim(#{name := Na, name_salt := Sa}, S = #{preclaims := Ps}) ->
  S#{preclaims := [ P || P = #preclaim{name = Na0, salt = Sa0} <- Ps,
                         Na0 /= Na orelse Sa0 /= Sa ]}.

get_preclaim_protocol(#{name := Na, name_salt := Sa}, #{preclaims := Ps}) ->
  hd([P#preclaim.protocol || P = #preclaim{name = Na0, salt = Sa0} <- Ps,
                             Na0 == Na andalso Sa0 == Sa]).

get_claim_protocol({Na, Sender}, #{claims := Cs}) ->
  hd([C#claim.protocol || C = #claim{name = Na0, claimer = Sa0} <- Cs,
                          Na0 == Na andalso Sa0 == Sender]).

owns_name(#{claims := Names, height := Height}, Who, Name) ->
  case lists:keyfind(Name, #claim.name, Names) of
    false -> false;
    Claim -> Claim#claim.claimer == Who
               andalso Claim#claim.expires_by >= Height
  end.

is_valid_name(#{claims := Names}, Name, Height) ->
  case lists:keyfind(Name, #claim.name, Names) of
    false -> false;
    Claim -> Height =< Claim#claim.expires_by
  end.

is_protected(S, Name) ->
  proplists:get_value(Name, maps:get(protected_names, S)) =/= undefined.


  %% -- Generators -------------------------------------------------------------
  minimum_gas_price(H) ->
                          aec_governance:minimum_gas_price(H).


gen_name() ->
  ?LET(NFs, frequency([{1, non_empty(list(elements(?NAMEFRAGS)))},
                       {90, [elements(?NAMEFRAGS)]}]),
       return(iolist_to_binary(lists:join(".", NFs ++ ["test"])))).

gen_salt() -> choose(270, 280).

gen_nonce() ->
  weighted_default({49, good}, {1, {bad, elements([-1, 1, -5, 5, 10000])}}).

gen_account(New, Existing, S) ->
  txs_spend_eqc:gen_account_key(New, Existing, S).

gen_fee(H) ->
  frequency([{29, ?LET(F, choose(20000, 30000), F * minimum_gas_price(H))},
             {1,  ?LET(F, choose(0, 15000), F)},   %%  too low (and very low for hard fork)
             {1,  ?LET(F, choose(0, 15000), F * minimum_gas_price(H))}]).    %% too low

gen_claim(#{preclaims := []} = S) ->
  {gen_name(), gen_salt(), gen_account(1, 1, S)};
gen_claim(#{preclaims := Ps} = S) ->
  weighted_default(
    {39, ?LET(#preclaim{name = N, salt = Salt, claimer = C}, elements(Ps),
              begin
                frequency([{1, {N, gen_salt(), C}}, {1, {gen_name(), Salt, C}}, {50, {N, Salt, C}}])
              end)},
    {1, {gen_name(), gen_salt(), gen_account(1, 1, S)}}).

gen_claimed_name(#{claims := []} = S) ->
  {gen_name(), gen_account(1, 1, S)};
gen_claimed_name(#{claims := Cs} = S) ->
  weighted_default(
    {39, ?LET(#claim{name = N, claimer = C}, elements(Cs),
              begin
                frequency([{1, {gen_name(), C}}, {1, {N, gen_account(0, 1, S)}}, {38, {N, C}}])
              end)},
    {1, {gen_name(), gen_account(1, 1, S)}}).

gen_pointers(S) ->
  ?LET(Pointers, [?LET({Kind, AccountKey},
                       oneof([
                              {account, gen_account(1, 5, S)},
                              {oracle, txs_oracles_eqc:gen_oracle_account(1, 5, S)}
                             ]),
                       {Kind, AccountKey}), {fake, binary(32)}, {fake, binary(32)}],
       sublist(Pointers)).
