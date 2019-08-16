-module(aec_keys_mock).

-compile(export_all).
-compile(nowarn_export_all).

peer_pubkey() ->
    {ok, <<42:32/unit:8>>}.
