-module(txs_utils).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-eqc_group_commands(false).
-compile([export_all, nowarn_export_all]).

-define(LIMA, false).

-include("txs_data.hrl").

%% Governance API
protocol_at_height(HardForks, Height) ->
    lists:last([ P || {P, H} <- maps:to_list(HardForks), H =< Height]).

minimum_gas_price(HardForks, Height) ->
    aec_governance:minimum_gas_price(protocol_at_height(HardForks, Height)).

%% in case of lima-rc, fall back to old definitions
minimum_gas_price(Protocol) when ?LIMA ->
    {ok, Forks} = application:get_env(aecore, hard_forks),
    Height = maps:get(integer_to_binary(Protocol), Forks),
    aec_governance:minimum_gas_price(Height);
minimum_gas_price(Protocol) ->
    aec_governance:minimum_gas_price(Protocol).


%% Chain API

%% Apply operations on all trees being at Height going to Height + 1
%% If we bump protocol, we need to updtae the trees with additional accounts and contracts
%% Only when Height + 1 is in different protocol
pre_transformations(_HardForks, Trees, Height) when ?LIMA ->
    TxEnv = aetx_env:tx_env(Height),
    aec_trees:perform_pre_transformations(Trees, TxEnv);
pre_transformations(HardForks, Trees, Height) ->
    Protocol = protocol_at_height(HardForks, Height),
    TxEnv = aetx_env:tx_env(Height),
    aec_trees:perform_pre_transformations(Trees, TxEnv, Protocol).

%% Utility

protocol_name(P)  ->
    maps:get(P, #{?ROMA_PROTOCOL_VSN    => roma,
                  ?MINERVA_PROTOCOL_VSN => minerva,
                  ?FORTUNA_PROTOCOL_VSN => fortuna,
                  ?LIMA_PROTOCOL_VSN    => lima,
                  ?IRIS_PROTOCOL_VSN    => iris
                 }).

%% State depending utility functions
%% By making the functions depend on the state, we don't need to update
%% the calling location, but just make sure we have enough info in state.

valid_fee(#{protocol := P}, #{ fee := Fee }) ->
    Fee >= 20000 * minimum_gas_price(P).   %% not precise, but we don't generate borderline fees

%% Shared generators

gen_fee(Protocol) ->
    frequency([{98, ?LET(F, choose(20000, 30000), F * minimum_gas_price(Protocol))},
               {1,  ?LET(F, choose(0, 15000), F)},   %%  too low (and very low for hard fork)
               {1,  ?LET(F, choose(0, 15000), F * minimum_gas_price(Protocol))}]).    %% too low

gen_fee_above(Protocol, Amount) ->
    frequency([{198, ?LET(F, choose(Amount, Amount + 10000), F * minimum_gas_price(Protocol))},
               {1,  ?LET(F, choose(0, Amount - 5000), F)},   %%  too low (and very low for hard fork)
               {1,  ?LET(F, choose(0, Amount - 5000), F * minimum_gas_price(Protocol))}]).    %% too low

gen_nonce() ->
    weighted_default({99, good}, {1, {bad, elements([-1, 1, -5, 5, 10000])}}).

gen_gas_price(Protocol) ->
    frequency([{198, minimum_gas_price(Protocol)},
               {1,  minimum_gas_price(Protocol) - 1},
               {1,  1}]).

gen_gas(GasUsed) ->
    frequency([{96, ?LET(Delta, choose(0, 10), GasUsed + Delta)},
               {2, ?LET(Delta, choose(0, 10), GasUsed + 3000000 + Delta)},
               {1, 10},
               {1, ?LET(Delta, choose(1, 250), max(1, GasUsed - Delta))}]).

gen_deposit() ->
    frequency([{8, 0}, {2, ?LET(X, choose(1, 9), X * 10000000000000)}]).

gen_account(New, Exist, S) ->
  txs_spend_eqc:gen_account_id(New, Exist, S).

gen_account(New, Exist, S, Filter) ->
  txs_spend_eqc:gen_account_id(New, Exist, S, Filter).

gen_contract(New, Exist, S) ->
  txs_contracts_eqc:gen_contract_id(New, Exist, S).

gen_oracle(New, Exist, S) ->
  txs_oracles_eqc:gen_oracle_id(New, Exist, S).

%% -- Transactions modifiers

update_nonce(S, Sender, #{nonce := Nonce} = Tx) ->
  case get_account(S, Sender) of
    false ->
      Tx#{nonce => 1};
    #account{ ga = #ga{} } ->
      case Nonce of
        good     -> Tx#{ nonce => 0 };
        {bad, N} -> Tx#{ nonce => abs(N) }
      end;
    Account ->
      case Nonce of
        good ->
          Tx#{nonce => Account#account.nonce };
        {bad, N} ->
          Tx#{nonce => max(0, Account#account.nonce + N) }
      end
  end.

%% -- Accounts handling
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

charge(Key, Amount, S) -> credit(Key, -Amount, S).

bump_nonce(AccId, S) ->
  Acc = #account{ nonce = Nonce } = get_account(S, AccId),
  update_account(S, AccId, Acc#account{ nonce = Nonce + 1 }).

reserve_fee(Fee, S = #{fees := Fees, height := H}) ->
  S#{fees => Fees ++ [{Fee, H}]}.

bump_and_charge(AccId, Fee, S) ->
  bump_nonce(AccId, charge(AccId, Fee, S)).

is_account(S = #{ with_ga := true }, A) ->
  false /= get_account(S, A);
is_account(S, A) ->
  case get_account(S, A) of
    #account{ ga = #ga{} } -> false;
    _                      -> true
  end.

good_accounts(S) ->
  WGA = maps:is_key(ga, S),
  Pay = maps:get(paying_for, S, false),
  [ A || {A, #account{ ga = GA }} <- maps:to_list(maps:get(accounts, S, #{})),
         Pay /= ?ACCOUNT(A) andalso ((WGA andalso GA /= false) orelse (not WGA andalso GA == false)) ].

get_account(S, ?ACCOUNT(A)) ->
  maps:get(A, maps:get(accounts, S), false);
get_account(_S, _) ->
  false.

get_account_nonce(S, ?ACCOUNT(A)) ->
  #account{ nonce = Nonce } = maps:get(A, maps:get(accounts, S, #{})),
  Nonce.

get_account_key(S, ?ACCOUNT(A)) ->
  #account{ key = Key } = maps:get(A, maps:get(accounts, S, #{})),
  get_pubkey(S, Key);
get_account_key(S, {_A, Key}) ->
  get_pubkey(S, Key);
get_account_key(_S, <<_:32/unit:8>> = Key) ->
  Key.

get_pubkey(S, ?KEY(Key)) ->
  get_pubkey(S, Key);
get_pubkey(S, Key) when is_atom(Key) ->
  #key{ public = PK } = maps:get(Key, maps:get(keys, S)),
  PK.

update_account(S, ?ACCOUNT(A), Acc) -> update_account(S, A, Acc);
update_account(S = #{ accounts := As }, A, Acc) ->
  S#{ accounts := As#{ A => Acc } }.

resolve_account(S, {name, Name})    ->
  case maps:get(Name, maps:get(named_accounts, S, #{}), false) of
    false           -> false;
    A = ?ACCOUNT(_)   -> A;
    A = {Ax, ?KEY(_)} -> case get_account(S, ?ACCOUNT(Ax)) of
                           false      -> A;
                           #account{} -> ?ACCOUNT(Ax)
                         end
  end;
resolve_account(_, {contract, Key}) -> {contract, Key};
resolve_account(_, {_, Key})        -> Key.

is_ga(S, A = ?ACCOUNT(_)) -> is_ga_account(S, A);
is_ga(S, O = ?ORACLE(_))  -> is_ga(S, txs_oracles_eqc:get_oracle_account(S, O));
is_ga(S, Q = ?QUERY(_))   -> is_ga(S, txs_oracles_eqc:get_query_oracle(S, Q));
is_ga(_S, X) -> error({todo, X}).

is_ga_account(S, AccId) ->
  case get_account(S, AccId) of
    #account{ ga = #ga{} } -> true;
    _                      -> false
  end.

%% --- Common eqc functions
common_postcond(Correct, Res) ->
    case Res of
        {error, _} when Correct -> eq(Res, ok);
        {error, _}              -> true;
        ok when Correct         -> true;
        ok                      -> eq(ok, {error, '_'})
    end.

%% --- Symbolic ids

init_ids() -> #{ channel => 0, query => 0, contract => 0, key => 0 }.

next_id(Type) ->
  Ids = #{ Type := X } = case get(ids) of undefined -> init_ids(); Ids0 -> Ids0 end,
  put(ids, Ids#{ Type := X + 1 }),
  list_to_atom(lists:concat([Type, "_", X])).

