-module(tx_utils).

-compile([export_all, nowarn_export_all]).


%% Governance API
protocol_at_height(HardForks, Height) ->
    lists:last([ P || {P, H} <- maps:to_list(HardForks), H =< Height]).

minimum_gas_price(HardForks, Height) ->
  aec_governance:minimum_gas_price(protocol_at_height(HardForks, Height)).


%% Chain API

%% Apply operations on all trees being at Height going to Height + 1
%% If we bump protocol, we need to updtae the trees with additional accounts and contracts
%% Only when Height + 1 is in different protocol
pre_transformations(HardForks, Trees, Height) ->
    Protocol = protocol_at_height(HardForks, Height),
    TxEnv = aetx_env:tx_env(Height + 1),
    aec_trees:perform_pre_transformations(Trees, TxEnv, Protocol).

%% Utility

protocol_name(P)  ->
    maps:get(P, #{1 => roma,
                  2 => minerva,
                  3 => fortuna,
                  4 => lima,
                  5 => iris
                  %% Add additional names here
               }).
