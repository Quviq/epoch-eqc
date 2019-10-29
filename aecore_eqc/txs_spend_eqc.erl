%%% -*- erlang-indent-level:2; indent-tabs-mode: nil -*-
%%% @author Thomas Arts
%%% @doc Spend transaction
%%%
%%% Created : 24 May 2019 by Thomas Arts

-module(txs_spend_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).

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
                                 {2, {oracle, gen_account_id(1, 49, S)}}] ++      %% There is no check account really is an oracle!
                                [{2, {name, gen_name(S)}}                || maps:get(named_accounts, S, #{}) /= #{} ] ++
                                [{1, {contract, gen_contract(1, 49, S)}} || maps:get(contracts, S, #{}) /= #{}]
                               )]
       ,
       [Sender, To,
        #{ amount  => gen_spend_amount(S, Sender),
           fee     => gen_fee(Protocol),
           nonce   => gen_nonce(),
           payload => utf8() }]).

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
      {account,  RId} -> aeser_id:create(account, get_account_key(S, RId));
      {oracle,   RId} -> aeser_id:create(oracle, get_account_key(S, RId));
      {contract, C}   -> aeser_id:create(contract, txs_contracts_eqc:get_contract_key(S, C));
      {name,     N}   -> aeser_id:create(name, aens_hash:name_hash(N))
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
  case good_accounts(S) of
    [] -> 0;
    As -> max(3, 10 - length(As)) end;
weight(_S, _) -> 0.

%% -- State update and query functions ---------------------------------------

%% --- local helpers ------
credit_contract(_Key, _Amount, S = #{ contracts := _Contracts}) ->
  S.

%% -- Generators -------------------------------------------------------------

gen_account_id(New, Exist, S = #{ ga := _ }) ->
  P = maps:get(paying_for, S, false),
  gen_account_id(New, Exist, S, fun(A) -> ?ACCOUNT(A) /= P andalso is_ga_account(S, ?ACCOUNT(A)) end);
  %% gen_account_id(New, Exist, S, fun(A) -> is_ga_account(S, ?ACCOUNT(A)) end);
gen_account_id(New, Exist, S) ->
  P = maps:get(paying_for, S, false),
  gen_account_id(New, Exist, S, fun(A) -> ?ACCOUNT(A) /= P andalso not is_ga_account(S, ?ACCOUNT(A)) end).
  %% gen_account_id(New, Exist, S, fun(A) -> not is_ga_account(S, ?ACCOUNT(A)) end).

gen_account_id(New, Exist, #{accounts := Accounts, keys := Keys}, Filter) ->
  case [ Key || Key <- maps:keys(Keys), not lists:keymember(Key, #account.key, maps:values(Accounts)) ] of
    [] ->
      ?LET(A, gen_account_id(maps:keys(Accounts), Filter), ?ACCOUNT(A));
    NewKeys ->
      weighted_default(
        {Exist, ?LET(A, gen_account_id(maps:keys(Accounts), Filter), ?ACCOUNT(A))},
        {New,   ?LET(K, elements(NewKeys), {mk_acc_id(K), ?KEY(K)})})
  end.

gen_account_id(As, Filter) ->
  case lists:filter(Filter, As) of
    []  -> elements(As);
    As1 -> weighted_default({29, elements(As1)}, {1, elements(As)})
  end.

mk_acc_id(K) ->
  StrId = lists:last(string:lexemes(atom_to_list(K), "_")),
  list_to_atom("account_" ++ StrId).

gen_name(S) ->
  frequency([{49, elements(maps:keys(maps:get(named_accounts, S, #{})))},
             {1,  elements([N || {N, _} <- maps:get(protected_names, S, [])] ++ [<<"ta.test">>])}]).

gen_spend_amount(S, Key) ->
  case get_account(S, Key) of
    #account{ amount = Amount } when Amount >= 0 ->
      weighted_default({49, rnd(Amount div 5)}, {1, gen_amount()});
    _ ->
      gen_amount()
  end.

gen_amount() -> ?LET(X, choose(1, 9), X * 10000000).
rnd(X) when X < 1000000000000 -> X;
rnd(X) -> (X div 1000000000000) * 1000000000000.
