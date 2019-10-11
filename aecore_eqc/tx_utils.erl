-module(tx_utils).

-include_lib("eqc/include/eqc.hrl").
-compile([export_all, nowarn_export_all]).

-define(LIMA, false).

-define(ABI_AEVM_1, 1).
-define(ABI_FATE_1, 3).

-define(ROMA_PROTOCOL_VSN,    1).
-define(MINERVA_PROTOCOL_VSN, 2).
-define(FORTUNA_PROTOCOL_VSN, 3).
-define(LIMA_PROTOCOL_VSN,    4).
-define(IRIS_PROTOCOL_VSN,    5).

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
    maps:get(P, #{?ROMA_PROTOCOL_VSN => roma,
                  ?MINERVA_PROTOCOL_VSN => minerva,
                  ?FORTUNA_PROTOCOL_VSN => fortuna,
                  ?LIMA_PROTOCOL_VSN => lima,
                  ?IRIS_PROTOCOL_VSN => iris
                  %% Add additional names here
                 }).

%% State depending utility functions
%% By making the functions depend on the state, we don't need to update
%% the calling location, but just make sure we have enough info in state.


valid_fee(#{protocol := P}, #{ fee := Fee }) ->
    Fee >= 20000 * minimum_gas_price(P).   %% not precise, but we don't generate fees in the shady range

%% Shared generators

gen_fee(Protocol) ->
    frequency([{29, ?LET(F, choose(20000, 30000), F * minimum_gas_price(Protocol))},
               {1,  ?LET(F, choose(0, 15000), F)},   %%  too low (and very low for hard fork)
               {1,  ?LET(F, choose(0, 15000), F * minimum_gas_price(Protocol))}]).    %% too low

gen_fee_above(Protocol, Amount) ->
    frequency([{29, ?LET(F, choose(Amount, Amount + 10000), F * minimum_gas_price(Protocol))},
               {1,  ?LET(F, choose(0, Amount - 5000), F)},   %%  too low (and very low for hard fork)
               {1,  ?LET(F, choose(0, Amount - 5000), F * minimum_gas_price(Protocol))}]).    %% too low


gen_nonce() ->
    weighted_default({49, good}, {1, {bad, elements([-1, 1, -5, 5, 10000])}}).
