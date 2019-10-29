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

-include("txs_eqc.hrl").

-define(NAMEFRAGS, ["aaa", "bbbbbbb", "ccccccccccc",
                    "ddddddddddddddd", "eeeeeeeeeeeeeeeee", "ffffffffffffffff"
                   ]).

%% -- State and state functions ----------------------------------------------
initial_state(S) ->
  S#{preclaims => [],
     claims => [],
     auctions => [],
     protected_names => [],
     named_accounts => #{}   %% Name can only be resolved if the Pointers contain "account_pubkey"
   }.

%% -- Operations -------------------------------------------------------------

mine_next(#{height := Height} = S, _Value, [Blocks]) ->
  %% This isn't entirely faithful - if we preclaim, claim, preclaim
  %% the exact same {name, salt} the preclaim will expire early...
  ExpiredPreclaims = expired_preclaims(S, Height + Blocks),
  ExpiredClaims = expired_claims(S, Height + Blocks),
  %% Revoke does set `expires_by` in the past... Fix that here.
  ProtectPeriod = fun(C) ->
                      FixRevoked = if C#claim.expires_by == Height - 1 -> 1; true -> 0 end,
                      C#claim.expires_by + aec_governance:name_protection_period() + FixRevoked
                  end,
  ExpiredNames = [ {C#claim.name, ProtectPeriod(C)} || C <- ExpiredClaims ],
  ExpiredProtected = expired_protection(S, Height + Blocks),
  ExpiredAuctions = expired_auctions(S, Height + Blocks),
  S#{preclaims => maps:get(preclaims, S, []) -- ExpiredPreclaims,
     claims => (maps:get(claims, S, []) -- ExpiredClaims) ++ [ auction_to_claim(A) || A <- ExpiredAuctions],
     auctions => maps:get(auctions, S, []) -- ExpiredAuctions,
     protected_names =>  (maps:get(protected_names, S) -- ExpiredProtected ) ++
       [ {N, H} || {N, H} <- ExpiredNames, H >= Height + Blocks ],
     named_accounts => maps:without([ N || {N,_} <- ExpiredNames], maps:get(named_accounts, S, #{}))
    }.

mine_features(#{height := Height} = S, [Blocks], _Res) ->
  [{mine, expired_preclaims} || expired_preclaims(S, Height + Blocks) =/= [] ] ++
    [{mine, expired_claims} || expired_claims(S, Height + Blocks) =/= [] ] ++
    [{mine, expired_auctions} || expired_auctions(S, Height + Blocks) =/= [] ] ++
    [{mine, expired_name_protection} || expired_protection(S, Height + Blocks) =/= [] ].


%% Note that this does not put them in protected_names !!!
auction_to_claim(#auction{name = Name, expires_by = Height, claimer = Claimer}) ->
  #claim{name = Name,
         height = Height,
         expires_by = Height + aec_governance:name_claim_max_expiration(),
         claimer = Claimer,
         protocol = aec_hard_forks:protocol_effective_at_height(Height)}.


%% --- Operation: ns_preclaim ---
ns_preclaim_pre(S) ->
  maps:is_key(accounts, S).

%% We cannot reject invalid names here, because we only get the hash of it.
ns_preclaim_args(S = #{protocol := P}) ->
  ?LET([Account, Name, Salt],
       [gen_account(1, 49, S), gen_name(P), gen_salt()],
       [Account, {Name, Salt},
        #{fee => gen_fee(P),
          nonce => gen_nonce()}]).

ns_preclaim_valid(S, [Account, {Name, Salt}, Tx]) ->
  valid([{account, is_account(S, Account)},
         {balance, check_balance(S, Account, maps:get(fee, Tx))},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {new_name_and_salt, new_name_and_salt(maps:get(preclaims, S, []), Name, Salt)}
        ]).

ns_preclaim_tx(S, [Account, {Name, Salt}, Tx]) ->
  Tx1       = update_nonce(S, Account, Tx),
  AccountId = aeser_id:create(account, get_account_key(S, Account)),
  CommitId  = aeser_id:create(commitment, aens_hash:commitment_hash(Name, Salt)),
  aens_preclaim_tx:new(Tx1#{ account_id => AccountId, commitment_id => CommitId }).

ns_preclaim_next(S = #{height := Height}, _Value, [Account, {Name, Salt}, Tx] = Args) ->
  case ns_preclaim_valid(S, Args) of
    true  ->
      #{ fee := Fee } = Tx,
      Preclaim = #preclaim{name    = Name,
                           salt    = Salt,
                           height  = Height,
                           expires_by = Height + aec_governance:name_preclaim_expiration(),
                           claimer = Account,
                           protocol = aec_hard_forks:protocol_effective_at_height(Height)},
      reserve_fee(Fee,
                  bump_and_charge(Account, Fee,
                                  add(preclaims, Preclaim, S)));
    _ -> S
  end.

ns_preclaim_post(S, Args, Res) ->
  common_postcond(ns_preclaim_valid(S, Args), Res).

ns_preclaim_features(S, [_Account, {_Name, _Salt}, _Tx] = Args, Res) ->
  Correct = ns_preclaim_valid(S, Args),
  [{correct, case Correct of true -> ns_preclaim; _ -> false end},
   {ns_preclaim, Res} ].

%% --- Operation: ns_claim ---
ns_claim_pre(S) ->
  maps:is_key(accounts, S) andalso maps:get(auctions, S) ++ maps:get(preclaims, S, []) /= [].

ns_claim_args(S = #{protocol := Protocol}) ->
  ?LET({Name, Salt, Account}, gen_claim(S),
       [Account,
        #{name => Name,
          name_salt => Salt,
          fee => gen_fee(Protocol),
          name_fee => gen_name_claim_fee(S, Name),
          nonce => gen_nonce()}]).

ns_claim_valid(S = #{height := Height}, [Account, #{name := Name} = Tx]) ->
  Protocol = aec_hard_forks:protocol_effective_at_height(Height),
  valid([{account, is_account(S, Account)},
         {balance, check_balance(S, Account, maps:get(fee, Tx) + name_fee(Tx))},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {preclaim, is_valid_preclaim(Protocol, S, Tx, Account)},  %% after Lima Salt distinguishes
         {valid_name, valid_name(Protocol, maps:get(name,Tx))},
         {unclaimed, not is_claimed(S, Name)},
         {unprotected, not is_protected(S, Name)},
         {valid_name_fee, is_valid_name_fee(Protocol, Name, maps:get(name_fee, Tx))},
         {valid_bid, is_valid_bid(Protocol, S, Name, maps:get(name_fee, Tx))}]).

ns_claim_tx(S, [Account, Tx]) ->
  %% FixTx = case maps:get(name_fee, Tx) == prelima orelse P < ?LIMA_PROTOCOL_VSN of
  %%           true -> maps:remove(name_fee, Tx);
  %%           false -> Tx
  %%         end,
  Tx1       = update_nonce(S, Account, Tx),
  AccountId = aeser_id:create(account, get_account_key(S, Account)),
  aens_claim_tx:new(Tx1#{ account_id => AccountId }).

ns_claim_next(S = #{height := Height}, _Value, [Account, Tx] = Args) ->
  case ns_claim_valid(S, Args) of
    true  ->
      #{ fee := Fee, name := Name} = Tx,
      Protocol = aec_hard_forks:protocol_effective_at_height(Height),
      case aec_governance:name_claim_bid_timeout(Name, Protocol) of
        0 ->
          Claim = #claim{name    = Name,
                         height  = Height,
                         expires_by = Height + aec_governance:name_claim_max_expiration(),
                         claimer = Account,
                         protocol = Protocol},
          remove_preclaim(Tx,
            reserve_fee(Fee,
              bump_and_charge(Account, Fee + name_fee(Tx), add(claims, Claim, S))));
        Timeout ->
          NameFee = maps:get(name_fee, Tx),
          NewBid = #auction{name = Name,
                            height = Height,
                            expires_by = Height + Timeout,
                            bid = NameFee,
                            claimer = Account,
                            protocol = Protocol},
          S1 = add(auctions, NewBid, remove(auctions, Name, #auction.name, S)),
          case find_auction(S, Name) of
            false ->
              remove_preclaim(Tx,
                reserve_fee(Fee,
                  bump_and_charge(Account, Fee + NameFee, S1)));
            #auction{claimer = PrevBidder,
                     bid = PrevBid} ->
              reserve_fee(Fee,
                credit(PrevBidder, PrevBid,
                  bump_and_charge(Account, Fee + NameFee, S1)))
          end
      end;
    _ -> S
  end.

ns_claim_post(S, Args, Res) ->
  common_postcond(ns_claim_valid(S, Args), Res).

ns_claim_features(S =  #{height := Height}, [_Account, Tx] = Args, Res) ->
  Correct = ns_claim_valid(S, Args),
  Name = maps:get(name, Tx),
  Salt = maps:get(name_salt, Tx),
  [{correct, if Correct -> ns_claim; true -> false end},
   {ns_claim, Res}] ++
    [{ns_claim_, maps:get(name, Tx)} || Res == ok] ++
    [{ns_claim_, {name_in_auction, if Salt == 0 -> right_salt;
                                     true -> wrong_salt end}} ||
      find_auction(S, Name) =/= false ] ++
    [{ns_claim_, {already_claimed, if Salt == 0 -> zero_salt;
                                     true -> salt end}} ||
      is_claimed_name(S, Name) ] ++
    [ {ns_claim_, {protocol,
                  aec_hard_forks:protocol_effective_at_height(Height) -
                    get_preclaim_protocol(Tx,S)}} || Correct andalso Salt =/= 0 ].

%% --- Operation: ns_update ---

ns_update_pre(S) ->
  maps:is_key(accounts, S).

ns_update_args(S = #{protocol := Protocol}) ->
  ?LET({{Name, Account}, Pointers},
       {gen_claimed_name(S), gen_pointers(S)},
       [Account, Name, Pointers,
        #{name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
          name_ttl => frequency([{10, nat()}, {1, 36000}, {10, 25000}, {1, choose(30000, 60000)}]),
          client_ttl => nat(),
          fee => gen_fee(Protocol),
          nonce => gen_nonce()
         }]).

ns_update_valid(S, [Account, Name, _Pointers, Tx]) ->
  valid([{account, is_account(S, Account)},
         {balance, check_balance(S, Account, maps:get(fee, Tx) + aec_governance:name_claim_locked_fee())},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {name_expiry, maps:get(name_ttl, Tx) =< aec_governance:name_claim_max_expiration()},
         {claimed_name, is_claimed_name(S, Name)},
         {owner, owns_name(S, Account, Name)}]).

ns_update_tx(S, [Account, _Name, Pointers, Tx]) ->
  Tx1       = update_nonce(S, Account, Tx),
  AccountId = aeser_id:create(account, get_account_key(S, Account)),
  Pointers1 = [ aens_pointer_new(S, Kind, Key) || {Kind, Key} <- Pointers ],
  aens_update_tx:new(Tx1#{ account_id => AccountId, pointers => Pointers1 }).

aens_pointer_new(_S, fake, Key) -> aens_pointer_new(fake, Key);
aens_pointer_new(S, oracle, Key = ?ORACLE(_)) ->
  aens_pointer_new(oracle, txs_oracles_eqc:get_oracle_key(S, Key));
aens_pointer_new(S, Kind,  Key) ->
  aens_pointer_new(Kind, get_account_key(S, Key)).

aens_pointer_new(account, Id) -> aens_pointer:new(<<"account_pubkey">>, aeser_id:create(account, Id));
aens_pointer_new(oracle,  Id) -> aens_pointer:new(<<"oracle">>,         aeser_id:create(oracle,  Id));
aens_pointer_new(fake,    Id) -> aens_pointer:new(<<"fake">>,           aeser_id:create(account, Id)).

ns_update_next(#{height := Height} = S, _, [Account, Name, Pointers, Tx] = Args) ->
  case ns_update_valid(S, Args) of
    true  ->
      #{ fee := Fee, name_ttl := TTL } = Tx,
      S1 = case lists:keyfind(account, 1, Pointers) of
             false -> remove_named_account(Name, S);
             {_, AccId} -> add_named_account(Name, AccId, S)
           end,
      reserve_fee(Fee,
                  bump_and_charge(Account, Fee,
                                  update_claim_height(Name, Height, TTL, S1)));
    _ -> S
  end.

ns_update_post(S, Args, Res) ->
  common_postcond(ns_update_valid(S, Args), Res).

ns_update_features(S, [_Account, _Name, Pointers, _Tx] = Args, Res) ->
  Correct = ns_update_valid(S, Args),
  [{correct, case Correct of true -> ns_update; _ -> false end},
   {ns_update, Res}] ++
    [{ns_update_, [ Kind || {Kind, _} <- Pointers]}].


%% --- Operation: ns_revoke ---
ns_revoke_pre(S) ->
  maps:is_key(accounts, S).

ns_revoke_args(#{protocol := Protocol} = S) ->
  ?LET({Name, Account}, gen_claimed_name(S),
       [Account, Name,
        #{name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
          fee => gen_fee(Protocol),
          nonce => gen_nonce()
         }]).

ns_revoke_valid(S, [Account, Name, Tx]) ->
  valid([{account, is_account(S, Account)},
         {balance, check_balance(S, Account, maps:get(fee, Tx))},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {claimed_name, is_claimed_name(S, Name)},
         {owner, owns_name(S, Account, Name)}]).

ns_revoke_tx(S, [Account, _Name, Tx]) ->
  Tx1       = update_nonce(S, Account, Tx),
  AccountId = aeser_id:create(account, get_account_key(S, Account)),
  aens_revoke_tx:new(Tx1#{ account_id => AccountId }).

ns_revoke_next(#{height := Height} = S, _Value, [Account, Name, Tx] = Args) ->
    case ns_revoke_valid(S, Args) of
        true  ->
            #{ fee := Fee } = Tx,
            reserve_fee(Fee,
            bump_and_charge(Account, Fee,
                remove_named_account(Name,
                                     revoke_claim(Name, Height, S))));
      _ -> S
    end.

ns_revoke_post(S, Args, Res) ->
  common_postcond(ns_revoke_valid(S, Args), Res).


ns_revoke_features(#{height := Height} = S, [Account, Name, _Tx] = Args, Res) ->
  Correct = ns_revoke_valid(S, Args),
  [{correct, case Correct of true -> ns_revoke; _ -> false end},
   {ns_revoke, Res}] ++
    [ {protocol, ns_revoke,
       aec_hard_forks:protocol_effective_at_height(Height) -
         get_claim_protocol({Name, Account}, S)} ||
      Correct == true
    ].

%% --- Operation: ns_transfer ---
ns_transfer_pre(S) ->
  maps:is_key(accounts, S).

ns_transfer_args(#{protocol := Protocol} = S) ->
  ExistingNames = maps:keys(maps:get(named_accounts, S, #{})),
  ?LET({{Name, Account}, To},
       {gen_claimed_name(S),
        frequency([{29, {account, gen_account(1, 49, S)}},
                   {1,  ?LET(R, gen_registrar(Protocol), {name, list_to_binary("not_a_name." ++ R)})}] ++
                  [{10, {name, elements(ExistingNames)}} || ExistingNames /= []])},
       [Account, To, Name,
        #{name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
          fee     => gen_fee(Protocol),
          nonce   => gen_nonce()
         }]).

ns_transfer_valid(S, [Account, To, Name, Tx]) ->
  valid([{account, is_account(S, Account)},
         {balance, check_balance(S, Account, maps:get(fee, Tx))},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {claimed_name, is_claimed_name(S, Name)},
         {owner, owns_name(S, Account, Name)},
         {receiver_account,
          resolve_account(S, To) =/= false} %%  Assumption the recipient does not need to exist
        ]).

ns_transfer_tx(S, [Account, Recipient, _Name, Tx0]) ->
  Tx1         = update_nonce(S, Account, Tx0),
  AccountId   = aeser_id:create(account, get_account_key(S, Account)),
  RecipientId =
    case Recipient of
      {account, RId} -> aeser_id:create(account, get_account_key(S, RId));
      {oracle,  RId} -> aeser_id:create(oracle, get_account_key(S, RId));
      {name,    N}   -> aeser_id:create(name, aens_hash:name_hash(N))
    end,

  aens_transfer_tx:new(Tx1#{ account_id => AccountId, recipient_id => RecipientId }).

ns_transfer_next(S, _, [Account, To, Name, Tx] = Args) ->
    case ns_transfer_valid(S, Args) of
        true  ->
            #{ fee := Fee } = Tx,
            ReceiverKey = resolve_account(S, To),
            reserve_fee(Fee,
            bump_and_charge(Account, Fee,
                transfer_name(ReceiverKey, Name,
                              credit(ReceiverKey, 0, S))));   %% to create it if it doesn't exist
      _ -> S
    end.

ns_transfer_post(S, Args, Res) ->
  common_postcond(ns_transfer_valid(S, Args), Res).

ns_transfer_features(S, [_Account, _To, _Name, _Tx] = Args, Res) ->
  Correct = ns_transfer_valid(S, Args),
  [{correct, case Correct of true -> ns_transfer; _ -> false end},
   {ns_transfer, Res}].


%% -- weight ---------------------------------------------------------------

weight(S, ns_preclaim) ->
  case maps:get(preclaims, S, []) of
    [] -> good_weight(S, 10);
    _  -> good_weight(S, 3) end;
weight(S, ns_claim)    ->
  case good_preclaims(S) of
    [] -> case maps:get(auctions, S) of
            [] -> 0;
            _  -> good_weight(S, 7) end;
    _  -> 10 end;
weight(S, ns_update) ->
  case good_claims(S) of
    [] -> 0;
    _  -> 9 end;
weight(S, ns_revoke) ->
  case good_claims(S) of
    [] -> 0;
    _  -> 3 end;
weight(S, ns_transfer) ->
  case good_claims(S) of
    [] -> 0;
    _  -> 5 end;
weight(_S, _) -> 0.

good_weight(S, Base) ->
  case good_accounts(S) of
    [] -> 0;
    _  -> Base
  end.

%% -- State update and query functions ---------------------------------------
expired_preclaims(S, Height) ->
  [ P || P <- maps:get(preclaims, S, []), P#preclaim.expires_by < Height].

expired_claims(S, Height) ->
  [ C || C <- maps:get(claims, S, []),
         C#claim.expires_by < Height ].

expired_auctions(S, Height) ->
  [ A || A <- maps:get(auctions, S, []),
         A#auction.expires_by < Height ].

expired_protection(S, Height) ->
  [ {N, H} || {N, H} <- maps:get(protected_names, S), H < Height ].

good_preclaims(S = #{ preclaims := Ps, height := H}) ->
  [ P || P = #preclaim{ expires_by = H0, claimer = C } <- Ps, H0 >= H,
         is_good(S, C), H0 < H + aec_governance:name_preclaim_expiration() ].

good_claims(S = #{ claims := Cs, height := H}) ->
  [ Cl || Cl = #claim{ expires_by = H0, claimer = C } <- Cs, H0 >= H, is_good(S, C) ].

is_good(S, Acc) ->
  WGA = maps:get(with_ga, S, false),
  case get_account(S, Acc) of
    #account{ ga = #ga{} } when WGA     -> true;
    #account{ ga = false } when not WGA -> true;
    _                                   -> false
  end.

add(Tag, X, S) ->
  S#{ Tag => maps:get(Tag, S, []) ++ [X] }.

remove(Tag, X, I, S) ->
  S#{ Tag := lists:keydelete(X, I, maps:get(Tag, S)) }.

remove_named_account(Name, S) ->
  S#{ named_accounts => maps:remove(Name, maps:get(named_accounts, S, #{})) }.

add_named_account(Name, Acc, S) ->
  S#{ named_accounts => maps:merge(maps:get(named_accounts, S, #{}), #{ Name => Acc }) }.

transfer_name(?ACCOUNT(NewOwner), Name, S) ->
  transfer_name(NewOwner, Name, S);
transfer_name({NewOwner, ?KEY(_)}, Name, S) ->
  transfer_name(NewOwner, Name, S);
transfer_name(NewOwner, Name, S) when is_atom(NewOwner) ->
  on_claim(Name, fun(C) -> C#claim{ claimer = ?ACCOUNT(NewOwner) } end, S).

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

backward_compatible(Height, Name) ->
  Domains = string:lexemes(Name, "."),
  length(Domains) == 2 andalso
  ((aec_hard_forks:protocol_effective_at_height(Height) >= 4
   andalso
   lists:last(Domains) == <<"chain">>)
    orelse
      (aec_hard_forks:protocol_effective_at_height(Height) < 4  andalso
       length(Domains) == 2)).


%% --- local helpers ------


name_fee(#{ name_fee := NFee })      -> name_fee(NFee);
name_fee(prelima)                    -> aec_governance:name_claim_locked_fee();
name_fee(NFee) when is_integer(NFee) -> NFee.

new_name_and_salt(Ps, Name, Salt) ->
  [ P || P = #preclaim{name = Na, salt = Sa} <- Ps,
         Na == Name andalso Sa == Salt ] == [].

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

is_claimed_name(#{claims := Names, height := Height}, Name) ->
  case lists:keyfind(Name, #claim.name, Names) of
    false -> false;
    Claim -> Height =< Claim#claim.expires_by
  end.

is_protected(S, Name) ->
  proplists:get_value(Name, maps:get(protected_names, S)) =/= undefined.

is_valid_name_fee(Protocol, _Name, NameFee) when Protocol < ?LIMA_PROTOCOL_VSN ->
  NameFee == prelima;
is_valid_name_fee(Protocol, Name, NameFee) ->
  is_integer(NameFee) andalso
  NameFee >= name_claim_fee(Name, Protocol).

name_claim_fee(Name, P) ->
  try aec_governance:name_claim_fee(Name, P)
  catch _:_ -> 1000000000000 end.

is_valid_bid(Protocol, _S, _Name, _NameFee) when Protocol < ?LIMA_PROTOCOL_VSN ->
  true;
is_valid_bid(_, S, Name, NameFee) ->
  NameFee =/= prelima andalso
    case find_auction(S, Name) of
      false -> true;
      #auction{bid = PrevBid} ->
        (NameFee - PrevBid) * 100 >= PrevBid * aec_governance:name_claim_bid_increment()
    end.

is_valid_preclaim(Protocol, S, Tx, Claimer) when Protocol < ?LIMA_PROTOCOL_VSN ->
  is_valid_preclaim_no_auction(S, Tx, Claimer);
is_valid_preclaim(_Protocol, #{auctions := Auctions} = S, #{name := Name, name_salt := Salt} = Tx, Claimer) ->
  %% Name should be in auction
  case Salt == 0 of
    true -> lists:keymember(Name, #auction.name, Auctions);
    false -> not lists:keymember(Name, #auction.name, Auctions) andalso
               is_valid_preclaim_no_auction(S, Tx, Claimer)
  end.

is_valid_preclaim_no_auction( #{preclaims := Ps, height := Height},
                              #{name := Name, name_salt := Salt}, Claimer) ->
  case [ PC || PC = #preclaim{name = N, salt = Sa, claimer = C} <- Ps,
               Name == N, Salt == Sa, Claimer == C ] of
    [] -> false;
    [#preclaim{ height = H }] ->
      H + aec_governance:name_claim_preclaim_delta() =< Height
        andalso Height =< H +  aec_governance:name_preclaim_expiration()
  end.

%% names may not have dots in between, only at the end (.test)
%% This also holds for Lima, creating subnames is a different transaction
valid_name(Protocol, Name) ->
  case string:lexemes(Name, ".") of
    [_, Registery] -> lists:member(Registery, aec_governance:name_registrars(Protocol));
    _ -> false
  end.

find_auction(S, Name) ->
  lists:keyfind(Name, #auction.name, maps:get(auctions, S)).

%% -- Generators -------------------------------------------------------------
gen_name(P) ->
  ?LET({SubName, Suffix}, {gen_subname(), gen_registrar(P)},
       return(iolist_to_binary(lists:join(".", [SubName] ++ [Suffix])))).

gen_registrar(P) when P < ?LIMA_PROTOCOL_VSN ->
  weighted_default({49, "test"}, {1, "chain"});
gen_registrar(_P) ->
  weighted_default({49, "chain"}, {1, "test"}).

gen_subname() ->
  ?LET(NFs, frequency([{1, non_empty(list(elements(?NAMEFRAGS)))},
                       {90, [elements(?NAMEFRAGS)]}]),
       return(iolist_to_binary(lists:join(".", NFs)))).

gen_salt() -> choose(270, 280).

gen_salt(X) ->
  weighted_default({49, X}, {1, oneof([0, gen_salt()])}).

gen_name_claim_fee(#{ protocol := P }, _Name) when P < ?LIMA_PROTOCOL_VSN ->
  frequency([{99, prelima}, {1, choose(1, 1000000000000000)}]);
gen_name_claim_fee(S = #{ protocol := P }, Name) ->
  F = case find_auction(S, Name) of
          false                 -> name_claim_fee(Name, P);
          #auction{ bid = Bid } -> (Bid * 105) div 100
      end,
  frequency([{49, elements([F, F + 1, F * 2])}, {1, elements([F - 1, F div 2])}]).

nc_pair(#preclaim{ name = N, claimer = C }) -> {N, C};
nc_pair(#auction{ name = N, claimer = C })  -> {N, C};
nc_pair(#claim{ name = N, claimer = C })    -> {N, C}.

gen_claim(#{preclaims := Ps, auctions := As} = S) ->
  ?LET({N, C}, frequency([{19, gen_nc_pair(S, Ps)} || Ps /= []] ++
                         [{10, gen_nc_pair(S, As)} || As /= []] ++
                         [{20, gen_auction(S, As)} || As /= []] ++
                         [{1,  gen_bad_nc_pair(S, lists:map(fun nc_pair/1, Ps ++ As))}]),
       begin
       case {[ Pr || Pr <- Ps, Pr#preclaim.name == N ], [ A || A <- As, A#auction.name == N ]} of
         {[], []}                        -> {N, oneof([0, gen_salt()]), C};
         {[#preclaim{ salt = Salt }], _} -> {N, gen_salt(Salt), C};
         {_, _}                          -> {N, gen_salt(0), C}
       end end).

gen_auction(S, As) ->
  ?LET(N, elements([Nx || #auction{ name = Nx } <- As ]), {N, gen_account(1, 49, S)}).

gen_claimed_name(#{claims := Cs} = S) ->
  gen_nc_pair(S, Cs).

gen_nc_pair(S = #{ protocol := P }, []) -> {gen_name(P), gen_account(1, 1, S)};
gen_nc_pair(S, Ns) ->
  NCs = lists:map(fun nc_pair/1, Ns),
  weighted_default({19, gen_good_nc_pair(S, NCs)}, {1, gen_bad_nc_pair(S, NCs)}).

gen_bad_nc_pair(#{protocol := P} = S, NCs) ->
  frequency([{1, {gen_name(P), gen_account(1, 1, S)}}] ++
            [{1, ?LET({N, _}, elements(NCs), {N, gen_account(0, 1, S)})} || NCs /= []] ++
            [{1, ?LET({_, C}, elements(NCs), {gen_name(P), C})}          || NCs /= []]).

gen_good_nc_pair(S = #{ with_ga := true }, NCs) ->
  gen_elem(NCs, [ NC || NC = {_, C} <- NCs, is_ga(S, C) ]);
gen_good_nc_pair(S, NCs) ->
  gen_elem(NCs, [ NC || NC = {_, C} <- NCs, not is_ga(S, C) ]).

gen_elem(Cs, [])  -> elements(Cs);
gen_elem(Cs0, Cs) -> weighted_default({29, elements(Cs)}, {1, elements(Cs0)}).

gen_pointers(S) ->
  ?LET(Pointers, [?LET({Kind, AccountKey},
                       oneof([
                              {account, gen_account(1, 5, S)},
                              {oracle, gen_oracle(1, 5, S)}
                             ]),
                       {Kind, AccountKey}), {fake, binary(32)}, {fake, binary(32)}],
       sublist(Pointers)).

%% Keep this lazy such that it mimics 'andalso'. In that way, one can first check whether
%% the account exists and only if so, check its balance.
valid([]) ->
  true;
valid([{_, true} | Rest]) ->
  valid(Rest);
valid([Tag | _Rest]) ->
  Tag.
