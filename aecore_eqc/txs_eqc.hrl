-import(tx_utils, [gen_fee/1, valid_fee/2, gen_fee_above/2, gen_nonce/0,
                   gen_gas/1, gen_gas_price/1, gen_deposit/0,
                   gen_account/3,
                   minimum_gas_price/1,
                   common_postcond/2]).

-define(ROMA_PROTOCOL_VSN,    1).
-define(MINERVA_PROTOCOL_VSN, 2).
-define(FORTUNA_PROTOCOL_VSN, 3).
-define(LIMA_PROTOCOL_VSN,    4).
-define(IRIS_PROTOCOL_VSN,    5).

-define(SOPHIA_ROMA,      1).
-define(SOPHIA_MINERVA,   2).
-define(SOPHIA_FORTUNA,   3).
-define(SOPHIA_LIMA_AEVM, 4).
-define(SOPHIA_LIMA_FATE, 5).

-define(ABI_AEVM_1, 1).
-define(ABI_FATE_1, 3).

-record(account, {key, amount, nonce = 1}).
