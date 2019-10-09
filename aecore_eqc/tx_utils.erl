-module(tx_utils).

-compile([export_all, nowarn_export_all]).

protocol_at_height(Height) ->
  [{P, _} | _] = lists:dropwhile(fun({_, X}) -> X < Height end, get(hard_forks)),
  P.

minimum_gas_price(Height) ->
  aec_governance:minimum_gas_price(protocol_at_height(Height)).

