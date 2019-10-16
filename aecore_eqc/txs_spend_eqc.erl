%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Thomas Arts
%%% @doc Spend transaction
%%%
%%% Created : 24 May 2019 by Thomas Arts

-module(txs_spend_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

-import(txs_ga_eqc, [is_ga/2, credit_ga/2]).

-include("txs_eqc.hrl").

%% -- State and state functions ----------------------------------------------
initial_state(S) -> S.

%% -- Common pre-/post-conditions --------------------------------------------

%% --- Operation: spend ---
spend_pre(S) ->
  maps:is_key(accounts, S).

%% here we should add spending to oracle and contract
%% aeser_id:specialize_type(Recv),
%% names are always accounts, hard coded in tx_processor
spend_args(#{protocol := Protocol} = S) ->
  ?LET([Sender, To], [gen_account_id(1, 49, S),
                      frequency([{10, {account, gen_account_id(2, 1, S)}},
                                 {0, {oracle, gen_account_id(1, 49, S)}}] ++      %% There is no check account really is an oracle!
                                [{2, {name, gen_name(S)}} || maps:get(named_accounts, S, #{}) /= #{} ] ++
                                [{1, {contract, gen_contract_id(1, 49, maps:get(contracts, S))}} || maps:get(contracts, S, []) /= []]
                               )]
       ,
       [Sender, To,
        #{%sender_id => Sender,  %% The sender is asserted to never be a name.
          %recipient_id => To,
          amount  => gen_spend_amount(S, Sender),
          fee     => gen_fee(Protocol),
          nonce   => gen_nonce(),
          payload => utf8()}]).

spend_valid(S, [Sender, {ReceiverTag, Receiver}, Tx]) ->
  is_account(S, Sender)
    andalso maps:get(nonce, Tx) == good
    andalso check_balance(S, Sender, maps:get(amount, Tx) + maps:get(fee, Tx))
    andalso valid_fee(S, Tx)
    andalso case ReceiverTag of
              account  -> true;
              oracle   -> true; %% an account is generated if oracle does not exist
              contract -> txs_contracts_eqc:is_payable_contract(S, Receiver);
              name     -> maps:is_key(Receiver, maps:get(named_accounts, S, #{}))
            end.

spend_tx(S, [Sender, Recipient, Tx0]) ->
  Tx1 = update_nonce(S, Sender, Tx0),

  SenderId    = aeser_id:create(account, get_account_key(S, Sender)),
  RecipientId =
    case Recipient of
      {account, RId} -> aeser_id:create(account, get_account_key(S, RId))
    end,

  aec_spend_tx:new(Tx1#{ sender_id => SenderId, recipient_id => RecipientId }).

spend_next(S, _Value, [Sender, TaggedReceiver, Tx] = Args) ->
  case spend_valid(S, Args) of
    false -> S;
    true  ->
      #{ amount := Amount, fee := Fee } = Tx,
      case resolve_account(S, TaggedReceiver) of
        false -> S;
        {contract, ContractId} ->
          reserve_fee(Fee,
                      bump_and_charge(Sender, Amount + Fee,
                                      credit_contract(ContractId, Amount, S)));
        RKey ->
          reserve_fee(Fee,
                      bump_and_charge(Sender, Amount + Fee,
                                      credit(RKey, Amount, S)))
      end
  end.

spend_post(S, Args, Res) ->
  common_postcond(spend_valid(S, Args), Res).

spend_features(S, [Sender, {Tag, Receiver}, _Tx] = Args, Res) ->
  Correct = spend_valid(S, Args),
  [{correct, if Correct -> spend; true -> false end}] ++
    [ {spend_to, self} || Sender == Receiver andalso Correct] ++
    [ {spend_to, Tag} || Sender =/= Receiver andalso Correct] ++
    [ {spend, Res}].

%% -- weight ---------------------------------------------------------------
weight(S, spend) ->
  case maps:size(maps:get(accounts, S, #{})) of
    0 -> 20;
    N -> max(3, 10 - N) end;
weight(_S, _) -> 0.

%% -- State update and query functions ---------------------------------------
resolve_account(S, {name, Name})    -> maps:get(Name, maps:get(named_accounts, S, #{}), false);
resolve_account(_, {contract, Key}) -> {contract, Key};
resolve_account(_, {_, Key})        -> Key.

check_balance(S, AccId, Amount) ->
  case get_account(S, AccId) of
    false   -> false;
    #account{ amount = Amount1 } -> Amount1 >= Amount %% + 100000000000000000000
  end.

credit(AccId, Amount, S = #{ accounts := Accounts }) ->
  case get_account(S, AccId) of
    Acc = #account{ amount = Amount1 } ->
      update_account(S, AccId, Acc#account{ amount = Amount1 + Amount });
    false ->
      {NewId, ?KEY(Key)} = AccId,
      S#{ accounts => Accounts#{NewId => #account{ key = Key, amount = Amount } } }
  end.

credit_contract(_Key, _Amount, S = #{ contracts := _Contracts}) ->
  S.

charge(Key, Amount, S) -> credit(Key, -Amount, S).

bump_nonce(AccId, S) ->
  Acc = #account{ nonce = Nonce } = get_account(S, AccId),
  update_account(S, AccId, Acc#account{ nonce = Nonce + 1 }).

reserve_fee(Fee, S = #{fees := Fees, height := H}) ->
  S#{fees => Fees ++ [{Fee, H}]}.

bump_and_charge(AccId, Fee, S) ->
  bump_nonce(AccId, charge(AccId, Fee, S)).

is_account(S, A) ->
  false /= get_account(S, A).

get_account(S, ?ACCOUNT(A)) ->
  maps:get(A, maps:get(accounts, S), false);
get_account(_S, _) ->
  false.

get_account_key(S, ?ACCOUNT(A)) ->
  #account{ key = Key } = maps:get(A, maps:get(accounts, S, #{})),
  get_pubkey(S, Key);
get_account_key(S, {_A, Key}) ->
  get_pubkey(S, Key).

get_pubkey(S, ?KEY(Key)) ->
  get_pubkey(S, Key);
get_pubkey(S, Key) when is_atom(Key) ->
  #key{ public = PK } = maps:get(Key, maps:get(keys, S)),
  PK.

update_account(S, ?ACCOUNT(A), Acc) -> update_account(S, A, Acc);
update_account(S = #{ accounts := As }, A, Acc) ->
  S#{ accounts := As#{ A => Acc } }.

%% --- local helpers ------


%% -- Generators -------------------------------------------------------------
gen_account_id(New, Exist, #{accounts := Accounts, keys := Keys}) ->
  case [ Key || Key <- maps:keys(Keys), not lists:keymember(Key, #account.key, maps:values(Accounts)) ] of
    [] ->
      ?LET(A, elements(maps:keys(Accounts)), ?ACCOUNT(A));
    NewKeys ->
      NewId = list_to_atom(lists:concat(["account_", maps:size(Accounts)])),
      weighted_default(
        {Exist, ?LET(A, elements(maps:keys(Accounts)), ?ACCOUNT(A))},
        {New,   {NewId, ?LET(K, elements(NewKeys), ?KEY(K))}})
  end.

gen_contract_id(Invalid, Valid, Contracts) ->
  frequency([{Invalid, noshrink(binary(32))},
             {Valid, ?LET(C, elements(Contracts), element(4, C))}]).

gen_name(S) ->
  frequency([{49, elements(maps:keys(maps:get(named_accounts, S, #{})))},
             {1,  elements([N || {N, _} <- maps:get(protected_names, S, [])] ++ [<<"ta.test">>])}]).

gen_spend_amount(S, Key) ->
  case get_account(S, Key) of
    false ->
      choose(0, 10000000);
    #account{ amount = Amount } ->
      weighted_default({49, Amount div 5}, {1, choose(0, 10000000)})
  end.
