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
-import(txs_spend_eqc, [is_account/2, reserve_fee/2, bump_and_charge/3, check_balance/3, credit/3]).

-define(NAMEFRAGS, ["foo", "longer-name",
                    "31-bytes-minimum-as-auctionname",
                    "this-name-is-32-bytes-ascii-name",
                    "this-name-is-more-than-32-bytes-ascii-name"  %% do not enter auction
                   ]).

-record(preclaim,{name, salt, height, claimer, protocol, expires_by}).
-record(claim,{name, height, expires_by, claimer, protocol}).
-record(auction, {name, height, expires_by, bid, claimer, protocol}).


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
  ExpiredPreclaims = expired_preclaims(S, Height + Blocks),
  ExpiredClaims = expired_claims(S, Height + Blocks),
  ExpiredNames = [ {C#claim.name, C#claim.expires_by + aec_governance:name_protection_period()} || C <- ExpiredClaims ],
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

%% We cannot reject invalid names here, because we only get teh hash of it.
ns_preclaim_args(S = #{protocol := Protocol}) ->
  ?LET([Sender, Name, Salt],
       [gen_account(1, 49, S), gen_name(), gen_salt()],
       [Sender, {Name, Salt},
        #{account_id => aeser_id:create(account, Sender),
          fee => gen_fee(Protocol),
          commitment_id =>
            aeser_id:create(commitment,
                            aens_hash:commitment_hash(Name, Salt)),
          nonce => gen_nonce()}]).

ns_preclaim_valid(S, [Sender, {Name, Salt}, Tx]) ->
  valid([{account, is_account(S, Sender)},
         {balance, check_balance(S, Sender, maps:get(fee, Tx))},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {new_name_and_salt, new_name_and_salt(maps:get(preclaims, S, []), Name, Salt)}]).

ns_preclaim_tx(S, [Sender, {_Name, _Salt}, Tx]) ->
  aens_preclaim_tx:new(update_nonce(S, Sender, Tx)).

ns_preclaim_next(S = #{height := Height}, _Value, [Sender, {Name, Salt}, Tx] = Args) ->
  case ns_preclaim_valid(S, Args) of
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
                                  add(preclaims, Preclaim, S)));
    _ -> S
  end.

ns_preclaim_post(S, Args, Res) ->
  common_postcond(ns_preclaim_valid(S, Args), Res).

ns_preclaim_features(S, [_Sender, {_Name, _Salt}, _Tx] = Args, Res) ->
  Correct = ns_preclaim_valid(S, Args),
  [{correct, case Correct of true -> ns_preclaim; _ -> false end},
   {ns_preclaim, Res} ].

%% --- Operation: ns_claim ---
ns_claim_pre(S) ->
  maps:is_key(accounts, S) andalso maps:get(preclaims, S, []) /= [].

ns_claim_args(S = #{protocol := Protocol}) ->
  ?LET({Name, Salt, Sender}, gen_claim(S),
       [Sender,
        #{account_id => aeser_id:create(account, Sender),
          name => Name,
          name_salt => Salt,
          fee => gen_fee(Protocol),
          name_fee => gen_name_claim_fee(S, Name),
          nonce => gen_nonce()}]).

ns_claim_valid(S = #{height := Height}, [Sender, #{name := Name} = Tx]) ->
  Protocol = aec_hard_forks:protocol_effective_at_height(Height),
  valid([{account, is_account(S, Sender)},
         {balance, check_balance(S, Sender, maps:get(fee, Tx) + name_fee(Tx))},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {preclaim, is_valid_preclaim(Protocol, S, Tx, Sender)},  %% after Lima Salt distinguishes
         {valid_name,  valid_name(Protocol, maps:get(name,Tx))},
         {unclaimed, not is_claimed(S, Name)},
         {unprotected, not is_protected(S, Name)},
         {valid_name_fee, is_valid_name_fee(Protocol, Name, maps:get(name_fee, Tx))},
         {valid_bid, is_valid_bid(Protocol, S, Name, maps:get(name_fee, Tx))}]).

ns_claim_tx(S, [Sender, Tx]) ->
  Protocol = aec_hard_forks:protocol_effective_at_height(maps:get(height, S)),
  FixTx = case maps:get(name_fee, Tx) == prelima orelse Protocol < 4 of
            true -> maps:remove(name_fee, Tx);
            false -> Tx
          end,
  aens_claim_tx:new(update_nonce(S, Sender, FixTx)).

ns_claim_next(S = #{height := Height}, _Value, [Sender, Tx] = Args) ->
  case ns_claim_valid(S, Args) of
    true  ->
      #{ fee := Fee, name := Name} = Tx,
      Protocol = aec_hard_forks:protocol_effective_at_height(Height),
      case aec_governance:name_claim_bid_timeout(Name, Protocol) of
        0 ->
          Claim = #claim{name    = Name,
                         height  = Height,
                         expires_by = Height + aec_governance:name_claim_max_expiration(),
                         claimer = Sender,
                         protocol = Protocol},
          remove_preclaim(Tx,
            reserve_fee(Fee,
              bump_and_charge(Sender, Fee + name_fee(Tx), add(claims, Claim, S))));
        Timeout ->
          NameFee = maps:get(name_fee, Tx),
          NewBid = #auction{name = Name,
                            height = Height,
                            expires_by = Height + Timeout,
                            bid = NameFee,
                            claimer = Sender,
                            protocol = Protocol},
          S1 = add(auctions, NewBid, remove(auctions, Name, #auction.name, S)),
          case find_auction(S, Name) of
            false ->
              remove_preclaim(Tx,
                reserve_fee(Fee,
                  bump_and_charge(Sender, Fee + NameFee, S1)));
            #auction{claimer = PrevBidder,
                     bid = PrevBid} ->
              reserve_fee(Fee,
                credit(PrevBidder, PrevBid,
                  bump_and_charge(Sender, Fee + NameFee, S1)))
          end
      end;
    _ -> S
  end.

ns_claim_post(S, Args, Res) ->
  common_postcond(ns_claim_valid(S, Args), Res).


ns_claim_features(S =  #{height := Height}, [_Sender, Tx] = Args, Res) ->
  Correct = ns_claim_valid(S, Args),
  Name = maps:get(name, Tx),
  Salt = maps:get(name_salt, Tx),
  [{correct, if Correct -> ns_claim; true -> false end},
   {ns_claim, Res}] ++
    [{ns_claim, maps:get(name, Tx)} || Res == ok] ++
    [{ns_claim, {name_in_auction, if Salt == 0 -> right_salt;
                                     true -> wrong_salt end}} ||
      find_auction(S, Name) =/= false ] ++
    [{ns_claim, {already_claimed, if Salt == 0 -> zero_salt;
                                     true -> salt end}} ||
      is_claimed_name(S, Name) ] ++
    [ {ns_claim, {protocol,
                  aec_hard_forks:protocol_effective_at_height(Height) -
                    get_preclaim_protocol(Tx,S)}} || Correct andalso Salt =/= 0 ].

%% --- Operation: ns_update ---

ns_update_pre(S) ->
  maps:is_key(accounts, S).

ns_update_args(S = #{protocol := Protocol}) ->
  ?LET({{Name, Sender}, Pointers},
       {gen_claimed_name(S), gen_pointers(S)},
       [Name, Sender, Pointers,
        #{account_id => aeser_id:create(account, Sender),
          name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
          name_ttl => frequency([{10, nat()}, {1, 36000}, {10, 25000}, {1, choose(30000, 60000)}]),
          client_ttl => nat(),
          fee => gen_fee(Protocol),
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

ns_update_valid(S, [Name, Sender, _Pointers, Tx]) ->
  valid([{account, is_account(S, Sender)},
         {balance, check_balance(S, Sender, maps:get(fee, Tx) + aec_governance:name_claim_locked_fee())},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {name_expiry, maps:get(name_ttl, Tx) =< aec_governance:name_claim_max_expiration()},
         {claimed_name, is_claimed_name(S, Name)},
         {owner, owns_name(S, Sender, Name)}]).

ns_update_tx(S, [_Name, Sender, _Pointers, Tx]) ->
  aens_update_tx:new(update_nonce(S, Sender, Tx)).

ns_update_next(#{height := Height} = S, _, [Name, Sender, Pointers, Tx] = Args) ->
  case ns_update_valid(S, Args) of
    true  ->
      #{ fee := Fee, name_ttl := TTL } = Tx,
      S1 = case lists:keyfind(account, 1, Pointers) of
             false -> remove_named_account(Name, S);
             {_, Key}  -> add_named_account(Name, Key, S)
           end,
      reserve_fee(Fee,
                  bump_and_charge(Sender, Fee,
                                  update_claim_height(Name, Height, TTL, S1)));
    _ -> S
  end.

ns_update_post(S, Args, Res) ->
  common_postcond(ns_update_valid(S, Args), Res).

ns_update_features(S, [_Name, _Sender, Pointers, _Tx] = Args, Res) ->
  Correct = ns_update_valid(S, Args),
  [{correct, case Correct of true -> ns_update; _ -> false end},
   {ns_update, Res}] ++
    [{ns_update, [ Kind || {Kind, _} <- Pointers]}].


%% --- Operation: ns_revoke ---
ns_revoke_pre(S) ->
  maps:is_key(accounts, S).

ns_revoke_args(#{protocol := Protocol} = S) ->
  ?LET({Name, Sender}, gen_claimed_name(S),
       [Sender, Name,
        #{account_id => aeser_id:create(account, Sender),
          name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
          fee => gen_fee(Protocol),
          nonce => gen_nonce()
         }]).

ns_revoke_valid(S, [Sender, Name, Tx]) ->
  valid([{account, is_account(S, Sender)},
         {balance, check_balance(S, Sender, maps:get(fee, Tx))},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {claimed_name, is_claimed_name(S, Name)},
         {owner, owns_name(S, Sender, Name)}]).

ns_revoke_tx(S, [Sender, _Name, Tx]) ->
  aens_revoke_tx:new(update_nonce(S, Sender, Tx)).

ns_revoke_next(#{height := Height} = S, _Value, [Sender, Name, Tx] = Args) ->
    case ns_revoke_valid(S, Args) of
        true  ->
            #{ fee := Fee } = Tx,
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                remove_named_account(Name,
                                     revoke_claim(Name, Height, S))));
      _ -> S
    end.

ns_revoke_post(S, Args, Res) ->
  common_postcond(ns_revoke_valid(S, Args), Res).


ns_revoke_features(#{height := Height} = S, [Sender, Name, _Tx] = Args, Res) ->
  Correct = ns_revoke_valid(S, Args),
  [{correct, case Correct of true -> ns_revoke; _ -> false end},
   {ns_revoke, Res}] ++
    [ {protocol, ns_revoke,
       aec_hard_forks:protocol_effective_at_height(Height) -
         get_claim_protocol({Name, Sender}, S)} ||
      Correct == true
    ].

%% --- Operation: ns_transfer ---
ns_transfer_pre(S) ->
  maps:is_key(accounts, S).

ns_transfer_args(#{protocol := Protocol} = S) ->
  ?LET({{Name, Sender}, To},
       {gen_claimed_name(S),
        oneof([{account, gen_account(1, 49, S)},
               {name, elements(maps:keys(maps:get(named_accounts, S, #{})) ++ [<<"ta.test">>, <<"ta.aet">>])}])},
       [Sender, To, Name,
        #{account_id => aeser_id:create(account, Sender),  %% The sender is asserted to never be a name.
          recipient_id =>
            case To of
              {account, Receiver} ->
                aeser_id:create(account, Receiver);
              {name, ToName} ->
                aeser_id:create(name, aens_hash:name_hash(ToName))
            end,
          name_id => aeser_id:create(name, aens_hash:name_hash(Name)),
          fee => gen_fee(Protocol),
          nonce => gen_nonce()
         }]).

ns_transfer_valid(S, [Sender, To, Name, Tx]) ->
  valid([{account, is_account(S, Sender)},
         {balance, check_balance(S, Sender, maps:get(fee, Tx))},
         {nonce, maps:get(nonce, Tx) == good},
         {fee, tx_utils:valid_fee(S, Tx)},
         {claimed_name, is_claimed_name(S, Name)},
         {owner, owns_name(S, Sender, Name)},
         {receiver_account,
          resolve_account(S, To) =/= false} %%  Assumption the recipient does not need to exist
        ]).

ns_transfer_tx(S, [Sender, _To, _Name, Tx]) ->
  aens_transfer_tx:new(update_nonce(S, Sender, Tx)).

ns_transfer_next(S, _, [Sender, To, Name, Tx] = Args) ->
    case ns_transfer_valid(S, Args) of
        true  ->
            #{ fee := Fee } = Tx,
            ReceiverKey = resolve_account(S, To),
            reserve_fee(Fee,
            bump_and_charge(Sender, Fee,
                transfer_name(ReceiverKey, Name,
                              credit(ReceiverKey, 0, S))));   %% to create it if it doesn't exist
      _ -> S
    end.

ns_transfer_post(S, Args, Res) ->
  common_postcond(ns_transfer_valid(S, Args), Res).


ns_transfer_features(S, [_Sender, _To, _Name, _Tx] = Args, Res) ->
  Correct = ns_transfer_valid(S, Args),
  [{correct, case Correct of true -> ns_transfer; _ -> false end},
   {ns_transfer, Res}].


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

backward_compatible(Height, Name) ->
  Domains = string:lexemes(Name, "."),
  length(Domains) == 2 andalso
  ((aec_hard_forks:protocol_effective_at_height(Height) >= 4
   andalso
   lists:last(Domains) == <<"aet">>)
    orelse
      (aec_hard_forks:protocol_effective_at_height(Height) < 4  andalso
       length(Domains) == 2)).


%% --- local helpers ------

name_fee(#{ name_fee := NFee })      -> name_fee(NFee);
name_fee(prelima)                    -> aec_governance:name_claim_locked_fee();
name_fee(NFee) when is_integer(NFee) -> NFee.

resolve_account(S, {name, Name}) ->
  maps:get(Name, maps:get(named_accounts, S, #{}), false);
resolve_account(_S, {account, Key}) ->
  Key.

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

is_valid_name_fee(Protocol, _Name, _NameFee) when Protocol < 4 ->
  true;  %% we remove the field part
is_valid_name_fee(Protocol, Name, NameFee) ->
  is_integer(NameFee) andalso
  NameFee >= name_claim_fee(Name, Protocol).

name_claim_fee(Name, P) ->
  try aec_governance:name_claim_fee(Name, P)
  catch _:_ -> 1000000000000 end.

is_valid_bid(Protocol, _S, _Name, _NameFee) when Protocol < 4 ->
  true;
is_valid_bid(_, S, Name, NameFee) ->
  NameFee =/= prelima andalso
    case find_auction(S, Name) of
      false -> true;
      #auction{bid = PrevBid} ->
        (NameFee - PrevBid) * 100 >= PrevBid * aec_governance:name_claim_bid_increment()
    end.

is_valid_preclaim(Protocol, S, Tx, Claimer) when Protocol < 4 ->
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
gen_name() ->
  ?LET({SubName, Suffix}, {gen_subname(), oneof(["test", "aet"])},
       return(iolist_to_binary(lists:join(".", [SubName] ++ [Suffix])))).

gen_subname() ->
  ?LET(NFs, frequency([{1, non_empty(list(elements(?NAMEFRAGS)))},
                       {90, [elements(?NAMEFRAGS)]}]),
       return(iolist_to_binary(lists:join(".", NFs)))).

gen_salt() -> choose(270, 280).

gen_name_claim_fee(#{ protocol := P }, _Name) when P < ?LIMA_PROTOCOL_VSN ->
  frequency([{99, prelima}, {1, choose(1, 1000000000000000)}]);
gen_name_claim_fee(S = #{ protocol := P }, Name) ->
  F = case find_auction(S, Name) of
          false                 -> name_claim_fee(Name, P);
          #auction{ bid = Bid } -> (Bid * 105) div 100
      end,
  frequency([{49, elements([F, F + 1, F * 2])}, {1, elements([F - 1, F div 2])}]).

gen_claim(#{preclaims := Ps, auctions := As} = S) ->
  frequency([{20, ?LET(#preclaim{name = N, salt = Salt, claimer = C}, elements(Ps),
                       begin
                         frequency([{1, {N, gen_salt(), C}}, {1, {gen_name(), Salt, C}}, {50, {N, Salt, C}}])
                       end)} || Ps =/= [] ] ++
              [{30, oneof([ {N, 0, C} || #auction{name = N, claimer = C} <- As])} || As =/= [] ] ++
              [{10, ?LET({Name, Account}, gen_claimed_name(S),
                         {Name, oneof([0, gen_salt()]), Account})}]).

gen_claimed_name(#{claims := [], auctions := []} = S) ->
  {gen_name(), gen_account(1, 1, S)};
gen_claimed_name(#{claims := Cs, auctions := As} = S) ->
  weighted_default(
    {39, ?LET({N, C}, frequency([ {10, {N, C}} || #claim{name = N, claimer = C} <- Cs ] ++
                                  [ {1, {N, C}} || #auction{name = N, claimer = C} <- As]),
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

%% Keep this lazy such that it mimics 'andalso'. In that way, one can first check whether
%% the account exists and only if so, check its balance.
valid([]) ->
  true;
valid([{_, true} | Rest]) ->
  valid(Rest);
valid([Tag | _Rest]) ->
  Tag.
