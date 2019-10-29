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

-record(account, {key, amount, nonce = 1, ga = false}).
-record(ga, {contract, auth_fun}).
-record(key,     {public, private}).
-record(contract, {name, pubkey, amount, deposit, vm, abi,
                   compiler_version, protocol, functions = []}).
-record(oracle, {account, qfee, oracle_ttl}).
-record(query,  {sender, oracle, id, fee, response_ttl, query_ttl, response_due, expired = false}).

-record(preclaim,{name, salt, height, claimer, protocol, expires_by}).
-record(claim,{name, height, expires_by, claimer, protocol}).
-record(auction, {name, height, expires_by, bid, claimer, protocol}).

-record(channel, {id, initiator, responder, amount, round = 1, ch_resv, lockp}).

-define(ACCOUNT(A),  {'$acc', A}).
-define(KEY(K),      {'$key', K}).
-define(CONTRACT(C), {'$con', C}).
-define(ORACLE(O),   {'$orc', O}).
-define(QUERY(Q),    {'$qry', Q}).
-define(CHANNEL(C),  {'$chn', C}).
