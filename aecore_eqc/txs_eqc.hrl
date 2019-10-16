-import(txs_utils, [gen_fee/1, valid_fee/2, gen_fee_above/2, gen_nonce/0,
                    gen_gas/1, gen_gas_price/1, gen_deposit/0,
                    gen_account/3,
                    update_nonce/3,
                    minimum_gas_price/1,
                    common_postcond/2]).

-include("txs_data.hrl").
