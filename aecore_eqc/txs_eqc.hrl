-import(txs_utils, [gen_fee/1, valid_fee/2, gen_fee_above/2, gen_nonce/0,
                    gen_gas/1, gen_gas_price/1, gen_deposit/0,
                    gen_account/3, gen_account/4, gen_contract/3, gen_oracle/3,
                    update_nonce/3, good_accounts/1,
                    minimum_gas_price/1, next_id/1,
                    common_postcond/2]).

-import(txs_utils, [check_balance/3, check_balance/4, credit/3, charge/3, charge/4,
                    bump_nonce/2, bump_and_charge/3, bump_and_charge/4,
                    reserve_fee/2, is_ga/2, is_account/2, is_ga_account/2, get_account/2,
                    get_account_key/2, get_pubkey/2, get_account_nonce/2,
                    update_account/3, resolve_account/2]).

-define(tx(Tx), list_to_atom(lists:concat([Tx, "_tx"]))).
-define(next(Tx), list_to_atom(lists:concat([Tx, "_next"]))).
-define(pre(Tx), list_to_atom(lists:concat([Tx, "_pre"]))).
-define(post(Tx), list_to_atom(lists:concat([Tx, "_post"]))).
-define(valid(Tx), list_to_atom(lists:concat([Tx, "_valid"]))).
-define(features(Tx), list_to_atom(lists:concat([Tx, "_features"]))).

-include("txs_data.hrl").
