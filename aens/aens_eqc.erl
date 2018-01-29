%%% File        : aens_eqc.erl
%%% Author      : Hans Svensson
%%% Description :
%%% Created     : 18 Dec 2017 by Hans Svensson
-module(aens_eqc).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_component.hrl").

-record(state,
    { names = []
    , preclaims = []
    , accounts = []
    , patron
    , height = 0 }).

-record(account, { pubkey, balance, height, privkey, nonce = 0 }).

-record(claim, {hash, fee}).

-record(preclaim, {pubkey, name, salt, fee, commitment, height}).

-record(name, {pubkey, name, hash, pointers = [], state = claimed, ttl}).

-record(update, {ttl, pointers}).

initial_state() ->
    #state{}.

%% -- Generators -------------------------------------------------------------
-define(NAMEFRAGS, ["foo", "bar", "baz"]).

gen_account(AtHeight) ->
    ?LET({PubKey, PrivKey}, gen_key_pair(),
         #account{ pubkey = shorthash(PubKey), privkey = shorthash(PrivKey),
                   balance = choose(5, 200), height = AtHeight }).

gen_key_pair() ->
    return(crypto:generate_key(ecdh, crypto:ec_curve(secp256k1))).

gen_preclaim(_S) ->
    #preclaim{ name = gen_name(), salt = noshrink(largeint()), fee = gen_fee() }.

gen_name() ->
    ?LET(NFs, non_empty(list(elements(?NAMEFRAGS))),
         return(string:join(NFs ++ ["aet"], "."))).

gen_fee() -> choose(3, 7).

gen_claim(_PC) ->
    #claim{ fee = gen_fee() }.

gen_update(_H) ->
    #update{ ttl = choose(5, 11), pointers = gen_pointers() }.

gen_pointers() ->
    ?LET(Xs, list({elements([p1, p2, p3]), non_empty(list(choose($a, $z)))}), lists:usort(Xs)).


%% -- Operations -------------------------------------------------------------

%% --- init ---
init_pre(S) ->
    S#state.patron == undefined.

init_args(_S) ->
    ?LET({PubKey, PrivKey}, gen_key_pair(),
         [#account{ pubkey = shorthash(PubKey), balance = 1000000,
                    height = 0, privkey = shorthash(PrivKey) }]).

init(#account{ pubkey = PK, balance = B }) ->
    {Genesis, Trees} = aec_block_genesis:genesis_block_with_state(#{ preset_accounts => [{longhash(PK), B}] }),
    {ok, GenesisHash} = aec_blocks:hash_internal_representation(Genesis),
    Chain = aec_chain_state:new_from_persistance([Genesis], [{GenesisHash, Trees}]),
    state_start(Chain).

init_next(S, _V, [Patron]) ->
    S#state{ patron = Patron }.


%% --- tick ---

tick_args(_S) -> [].

tick() -> apply_noop().

tick_next(S, _V, []) ->
    S#state{ height = S#state.height + 1 }.

%% --- add_account ---
add_account_args(S) ->
    [S#state.patron, gen_account(S#state.height + 1)].

add_account_pre(S, [_Patron, NewAccount]) ->
    S#state.height + 1 == NewAccount#account.height.

add_account_adapt(S, [Patron, NewAccount]) ->
    [Patron, NewAccount#account{ height = S#state.height + 1}].

add_account(Patron, NewAccount) ->
    apply_tx(mk_spend_tx(Patron, NewAccount)).

add_account_next(S, _V, [Patron = #account{ balance = PB, nonce = PN },
                         NewAccount = #account{ balance = NB }]) ->
  S#state{ patron   = Patron#account{ balance = PB - NB - 1, nonce = PN + 1 },
           accounts = S#state.accounts ++ [NewAccount],
           height   = S#state.height + 1 }.

add_account_post(_S, [_Patron, _NewAccount], Res) ->
  eq(Res, ok).


%% --- preclaim ---
preclaim_pre(S) -> S#state.accounts /= [].

preclaim_args(S) -> [elements(S#state.accounts), gen_preclaim(S)].

preclaim_pre(S, [A, _PC]) ->
    lists:member(A, S#state.accounts).

preclaim_adapt(S, [A, PC]) ->
    case lists:keyfind(A#account.pubkey, #account.pubkey, S#state.accounts) of
        false -> false;
        A1    -> [A1, PC]
    end.

preclaim(A, PC) ->
    apply_tx(mk_preclaim_tx(A, PC)).

preclaim_next(S, _V, [A = #account{ nonce = N, balance = B, pubkey = PK },
                      PC = #preclaim{ fee = Fee, name = Name, salt = Salt } ]) ->
    case preclaim_tx_status(S, A, PC) of
        ok ->
            Commitment = aens_hash:commitment_hash(list_to_binary(Name), Salt),
            S1 = update_account(A#account{ nonce = N+1, balance = B - Fee }, S),
            S2 = add_preclaim(PC#preclaim{ pubkey = PK, commitment = Commitment,
                                           height = S#state.height + 1 }, S1),
            S2#state{ height = S#state.height + 1 };
        _ ->
            S
    end.

preclaim_post(S, [A, PC], Res) ->
    PCStatus = preclaim_tx_status(S, A, PC),
    case Res of
        ok -> eq(ok, PCStatus);
        {bad_tx, _Tx, _} when PCStatus == ok -> eq(bad_tx, ok);
        _ -> true
    end.

preclaim_tx_status(S, #account{ pubkey = PK }, #preclaim{ fee = F }) ->
    check([check_balance(balance(PK, S), F)]).

check_balance(B1, B2) when B1 >= B2 -> ok;
check_balance(_B1, _B2) -> {error, insufficient_funds}.

%% --- claim ---
claim_pre(S) -> S#state.preclaims /= [].

claim_args(S) ->
    ?LET(PC, elements(S#state.preclaims),
         [lists:keyfind(PC#preclaim.pubkey, #account.pubkey, S#state.accounts), PC, gen_claim(PC)]).

claim_pre(S, [A, PC, _C]) ->
    lists:member(PC, S#state.preclaims)
        andalso lists:member(A, S#state.accounts).

claim_adapt(S, [_A, PC, C]) ->
    case lists:keyfind(PC#preclaim.commitment, #preclaim.commitment, S#state.preclaims) of
        false -> false;
        PC1   -> case lists:keyfind(PC1#preclaim.pubkey, #account.pubkey, S#state.accounts) of
                     false -> false;
                     A1    -> [A1, PC1, C]
                 end
    end.

claim(A, PC, C) ->
    apply_tx(mk_claim_tx(A, PC, C)).

claim_next(S, _V, [A  = #account{ pubkey = PK, nonce = N, balance = B },
                   PC = #preclaim{ commitment = Ct, name = Name },
                   C  = #claim{ fee = Fee } ]) ->
    case claim_tx_status(S, A, PC, C) of
        ok ->
            Hash   = shorthash(aens_hash:name_hash(list_to_binary(Name))),
            %% io:format("ADD ~p with TTL: ~p (at ~p)\n", [Name, S#state.height + 1 + aec_governance:name_claim_max_expiration(), S#state.height+1]),
            TotFee = Fee + aec_governance:name_claim_burned_fee(),
            S1 = update_account(A#account{ nonce = N+1, balance = B - TotFee }, S),
            S2 = add_name(#name{ pubkey = PK, name = Name, hash = Hash,
                                 ttl = {block, S#state.height + 1 + aec_governance:name_claim_max_expiration()} }, S1),
            S2#state{ preclaims = lists:keydelete(Ct, #preclaim.commitment, S#state.preclaims),
                      height = S#state.height + 1 };
        _ ->
            S
    end.

claim_post(S, [A, PC, C], Res) ->
    CStatus = claim_tx_status(S, A, PC, C),
    case Res of
        ok -> eq(ok, CStatus);
        {bad_tx, _Tx, _} when CStatus == ok -> eq(bad_tx, ok);
        _ -> true
    end.

claim_tx_status(S, #account{ pubkey = PK }, PC, #claim{ fee = F }) ->
    check([check_balance(balance(PK, S), F + aec_governance:name_claim_burned_fee()),
           check_expired(PC#preclaim.height, aec_governance:name_preclaim_expiration(),
                         S#state.height + 1),
           check_taken(PC#preclaim.name, S#state.names),
           check_owned(PK, PC)]).

check_taken(Name, Names) ->
    case lists:keyfind(Name, #name.name, Names) of
        #name{ } -> {error, {name_taken, Name}};
        _ -> ok
    end.

check_owned(PK, #preclaim{ pubkey = PK })   -> ok;
check_owned(PK1, #preclaim{ pubkey = PK2 }) -> {PK2, not_owned_by, PK1}.

check_expired(H0, Delta, H) ->
    case expired(H0, Delta, H) of
        false -> ok;
        true  -> {error, preclaim_expired}
    end.

%% --- transfer ---
transfer_pre(S) ->
    claimed_names(S) /= [] andalso S#state.accounts /= [].

transfer_args(S) ->
    ?LET(Name, elements(S#state.names),
         [lists:keyfind(Name#name.pubkey, #account.pubkey, S#state.accounts), Name,
          elements(S#state.accounts)]).

transfer_pre(S, [A1, N, A2]) ->
    lists:member(N, S#state.names)
        andalso lists:member(A1, S#state.accounts)
        andalso lists:member(A2, S#state.accounts).

transfer_adapt(S, [_A1, N, A2]) ->
    case lists:keyfind(N#name.name, #name.name, claimed_names(S)) of
        false -> false;
        N1    -> case {lists:keyfind(N1#name.pubkey, #account.pubkey, S#state.accounts),
                       lists:keyfind(A2#account.pubkey, #account.pubkey, S#state.accounts)} of
                     {A1 = #account{}, NewA2 = #account{}} -> [A1, N1, NewA2];
                     _ -> false
                 end
    end.

transfer(A1, N, A2) ->
    apply_tx(mk_transfer_tx(A1, N, A2)).

transfer_next(S, _V, [A1 = #account{ nonce = N, balance = B },
                      Name,
                      #account{ pubkey = PK2 } ]) ->
    case transfer_tx_status(S, A1, Name) of
        ok ->
            TotFee = aec_governance:name_transfer_burned_fee(),
            S1 = update_account(A1#account{ nonce = N+1, balance = B - TotFee }, S),
            S2 = update_name(Name#name{ pubkey = PK2 }, S1),
                                    %% ttl = {block, S#state.height + 1 + aec_governance:name_transfer_max_expiration()} }, S1),
            S2#state{ height = S#state.height + 1 };
        _ ->
            S
    end.

transfer_post(S, [A1, N, _A2], Res) ->
    CStatus = transfer_tx_status(S, A1, N),
    case Res of
        ok -> eq(ok, CStatus);
        {bad_tx, _Tx, _} when CStatus == ok -> eq(bad_tx, ok);
        _ -> true
    end.

transfer_tx_status(S, #account{ pubkey = PK }, #name{ name = N}) ->
    check([check_balance(balance(PK, S), aec_governance:name_transfer_burned_fee()),
           check_name_claimed_and_owned(N, PK, S)]).

check_name_claimed_and_owned(Name, PK, #state{ names = Ns }) ->
    case lists:keyfind(Name, #name.name, Ns) of
        #name{ pubkey = PK, state = claimed } -> ok;
        #name{ state = claimed } -> {error, {Name, not_owned_by, PK}};
        #name{} -> {error, {Name, not_claimed}}
    end.

%% --- update ---
update_pre(S) ->
    claimed_names(S) /= [] andalso S#state.accounts /= [].

update_args(S) ->
    ?LET(Name, elements(S#state.names),
         [lists:keyfind(Name#name.pubkey, #account.pubkey, S#state.accounts), Name,
          gen_update(S#state.height)]).

update_pre(S, [A, N, _]) ->
    lists:member(N, S#state.names)
        andalso lists:member(A, S#state.accounts).

update_adapt(S, [_A, N, U]) ->
    case lists:keyfind(N#name.name, #name.name, claimed_names(S)) of
        false -> false;
        N1    -> case lists:keyfind(N1#name.pubkey, #account.pubkey, S#state.accounts) of
                     A1 = #account{} -> [A1, N1, U];
                     _               -> false
                 end
    end.

update(A, N, U) ->
    apply_tx(mk_update_tx(A, N, U)).

update_next(S, _V, [A = #account{ nonce = N, balance = B }, Name, U = #update{ ttl = TTL, pointers = Ps } ]) ->
    case update_tx_status(S, A, Name, U) of
        ok ->
            TotFee = aec_governance:name_update_burned_fee(),
            S1 = update_account(A#account{ nonce = N+1, balance = B - TotFee }, S),
            S2 = update_name(Name#name{ ttl = {block, S#state.height + 1 + TTL}, pointers = Ps }, S1),
            S2#state{ height = S#state.height + 1 };
        _ ->
            S
    end.

update_post(S, [A, N, U], Res) ->
    CStatus = update_tx_status(S, A, N, U),
    case Res of
        ok -> eq(ok, CStatus);
        {bad_tx, _Tx, _} when CStatus == ok -> eq(bad_tx, ok);
        _ -> true
    end.

update_tx_status(S, #account{ pubkey = PK }, #name{ name = N}, #update{ ttl = TTL }) ->
    check([check_balance(balance(PK, S), aec_governance:name_update_burned_fee()),
           check_ttl(TTL),
           check_name_claimed_and_owned(N, PK, S)]).

check_ttl(TTL) when TTL > 10 -> {error, too_long_ttl};
check_ttl(_) -> ok.

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(S, Cmd) ->
    S#state.patron =/= undefined orelse Cmd == init.

next_state_common(S, _, _) ->
    S#state{ names = prune_names(S#state.height, S#state.names),
             preclaims = prune_preclaims(S#state.height, S#state.preclaims) }.

prune_names(Height, Names) ->
    Prune = fun(N = #name{ ttl = {block, H0}, state = claimed }) when H0 =< Height ->
                [N#name{ ttl = {block, Height + aec_governance:name_protection_period()},
                          state = revoked }];
               (#name{ ttl = {block, H0}, state = revoked }) when H0 =< Height -> [];
               (N) -> [N]
            end,
    lists:append([ Prune(Name) || Name <- Names ]).

%% Keep expired preclaims for a short while, for negative testing...
prune_preclaims(Height, PCs) ->
    Prune = fun(#preclaim{ height = H0 }) when H0 + 10 < Height -> [];
               (N) -> [N]
            end,
    lists:append([ Prune(PC) || PC <- PCs ]).


%% This is ugly... We need the state after the operation next state, but
%% before next_state_common...
postcondition_common(S0, Cmd, Res) ->
    S = next_state_(S0, Res, Cmd),
    case S#state.height > S0#state.height of
        false -> true;
        true  -> state_invariant(S)
    end.

state_invariant(#state{ patron = undefined }) -> true;
state_invariant(S = #state{ height = Height }) ->
    Chain = state_get(),
    {_LastBlock, Trees} = top_block_with_state(Chain),
    eqc_statem:conj([tag(accounts, check_accounts(S#state.accounts, Trees)),
                     tag(preclaims, check_preclaims(S#state.preclaims, Trees, Height)),
                     tag(names, check_names(S#state.names, Trees, Height))
                    ]).

check_accounts(As, Trees) ->
    ATree = aec_trees:accounts(Trees),
    case lists:usort([ check_account(A, ATree) || A <- As ]) -- [true] of
        []     -> true;
        Err    -> Err
    end.

check_account(#account{ pubkey = PK, balance = B, nonce = N }, ATree) ->
    case aec_accounts_trees:lookup(longhash(PK), ATree) of
        none -> {account_missing, PK};
        {value, Account} ->
            tag(PK, eqc_statem:conj([tag(balance, eq(aec_accounts:balance(Account), B)),
                                     tag(nonce, eq(aec_accounts:nonce(Account), N))]))
    end.

check_preclaims(ModelPCs, Trees, Height) ->
    PCTree = aec_trees:ns(Trees),
    ExpectedPCs = [ {C, PK}
                    || #preclaim{ pubkey = PK, commitment = C, height = H0 } <- ModelPCs,
                       not expired(H0, aec_governance:name_preclaim_expiration(), Height) ],
    ActualPCs   = [ {aens_commitments:id(PC), shorthash(aens_commitments:owner(PC))}
                    || PC <- aens_state_tree:commitment_list(PCTree) ],
    case {ExpectedPCs -- ActualPCs, ActualPCs -- ExpectedPCs} of
        {[], []}     -> true;
        {[], PCs}    -> {extra_preclaims_in_state_tree, PCs};
        {PCs, []}    -> {premature_pruning, PCs};
        {PCs1, PCs2} -> {extra, PCs1, missing, PCs2}
    end.

check_names(ModelNs, Trees, Height) ->
    NTree = aec_trees:ns(Trees),
    ExpectedNs = [ {H, S, PK, Ps, TTL}
                    || #name{ pubkey = PK, hash = H, ttl = {block, TTL}, state = S, pointers = Ps } <- ModelNs ],
    ActualNs   = [ {shorthash(aens_names:id(N)), aens_names:status(N),
                    shorthash(aens_names:owner(N)), aens_names:pointers(N), aens_names:expires(N)}
                   || N <- aens_state_tree:name_list(NTree) ],
    case {ExpectedNs -- ActualNs, ActualNs -- ExpectedNs} of
        {[], []}   -> true;
        {[], Ns}   -> {extra_claims_in_state_tree, Ns};
        {Ns, []}   -> {premature_pruning, Ns};
        {Ns1, Ns2} -> {model_has, Ns1, state_tree_has, Ns2}
    end.

%% -- Property ---------------------------------------------------------------
weight(_S, _Cmd) -> 1.

prop_ok() ->
    ?SETUP(fun() -> setup(), fun() -> teardown() end end,
    ?FORALL(Cmds, commands(?MODULE),
    eqc_statem:show_states(
    begin
        HSR = {H, _S, Res} = run_commands(Cmds),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            aggregate(call_features(H),
            pretty_commands(?MODULE, Cmds, HSR, Res == ok))))
    end))).

setup() ->
    eqc_mocking:start_mocking(api_spec()).

teardown() ->
    eqc_mocking:stop_mocking().

tag(_, true) -> true;
tag(Tag, X)  -> {Tag, X}.

api_spec() ->
    #api_spec{
        modules = [aec_tx_sign(), aec_target(), aec_governance()]
    }.

aec_target() ->
    #api_module{ name = aec_target, fallback = aens_mock }.

aec_tx_sign() ->
    #api_module{ name = aec_tx_sign, fallback = aens_mock }.

aec_governance() ->
    #api_module{ name = aec_governance, fallback = aens_mock }.

%% -- Transaction helpers ----------------------------------------------------
apply_noop() ->
    Chain = state_get(),
    {LastBlock, Trees0} = top_block_with_state(Chain),
    {ok, Tx} = aec_coinbase_tx:new(#{account => <<0:(8*65)>>}),
    NewBlock = aec_blocks:new(LastBlock, [Tx], Trees0),
    {ok, Chain1} = aec_chain_state:insert_block(NewBlock, Chain),
    state_put(Chain1),
    ok.

apply_tx(Tx) ->
    Chain = state_get(),
    {LastBlock, Trees0} = top_block_with_state(Chain),
    try
        NewBlock = aec_blocks:new(LastBlock, [Tx], Trees0),
        {ok, Chain1} = aec_chain_state:insert_block(NewBlock, Chain),
        state_put(Chain1),
        ok
    catch E:R ->
        {bad_tx, Tx, {E, R, erlang:get_stacktrace()}}
    end.

mk_spend_tx(Sender, Receiver) ->
    {ok, Tx} =
        aec_spend_tx:new(#{ sender    => longhash(Sender#account.pubkey),
                            recipient => longhash(Receiver#account.pubkey),
                            amount    => Receiver#account.balance,
                            fee       => 1,
                            nonce     => Sender#account.nonce + 1 }),
    Tx.

mk_preclaim_tx(Account, PC) ->
    Commitment = aens_hash:commitment_hash(list_to_binary(PC#preclaim.name), PC#preclaim.salt),
    {ok, Tx} =
        aens_preclaim_tx:new(#{ account    => longhash(Account#account.pubkey),
                                nonce      => Account#account.nonce + 1,
                                commitment => Commitment,
                                fee        => PC#preclaim.fee }),
    Tx.

mk_claim_tx(Account, PC, C) ->
    {ok, Tx} =
        aens_claim_tx:new(#{ account   => longhash(Account#account.pubkey),
                             nonce     => Account#account.nonce + 1,
                             name      => list_to_binary(PC#preclaim.name),
                             name_salt => PC#preclaim.salt,
                             fee       => C#claim.fee }),
    Tx.

mk_transfer_tx(A1, N, A2) ->
    {ok, Tx} =
        aens_transfer_tx:new(#{ account           => longhash(A1#account.pubkey),
                                nonce             => A1#account.nonce + 1,
                                name_hash         => longhash(N#name.hash),
                                recipient_account => longhash(A2#account.pubkey),
                                fee               => aec_governance:name_transfer_burned_fee() }),
    Tx.

mk_update_tx(A, N, U) ->
    {ok, Tx} =
        aens_update_tx:new(#{ account           => longhash(A#account.pubkey),
                              nonce             => A#account.nonce + 1,
                              name_hash         => longhash(N#name.hash),
                              name_ttl          => 5,
                              pointers          => U#update.pointers,
                              ttl               => U#update.ttl,
                              fee               => aec_governance:name_update_burned_fee() }),
    Tx.
%% -- Misc helpers -----------------------------------------------------------
update_account(A, S = #state{ accounts = As }) ->
    S#state{ accounts = lists:keystore(A#account.pubkey, #account.pubkey, As, A) }.

add_preclaim(PC, S = #state{ preclaims = PCs }) ->
    S#state{ preclaims = PCs ++ [PC] }.

add_name(N, S = #state{ names = Ns }) ->
    S#state{ names = Ns ++ [N] }.

update_name(N, S = #state{ names = Ns }) ->
    S#state{ names = lists:keystore(N#name.hash, #name.hash, Ns, N) }.

balance(PK, #state{ accounts = As }) ->
    #account{ balance = B } = lists:keyfind(PK, #account.pubkey, As),
    B.

check([])        -> ok;
check([ok | Xs]) -> check(Xs);
check([E | _])   -> E.

expired({block, H1}, H2) -> H1 < H2.

expired(H0, {delta, D}, H) ->
    expired(H0, D, H);
expired(H0, Delta, H) ->
    H0 + Delta < H.

claimed_names(S) ->
    [ N || N = #name{ state = claimed } <- S#state.names ].

%% -- Hash shortening ---------------------------------------------------------
shorthash(Hash) when is_binary(Hash) ->
    <<Pref:64, _Rest/binary>> = Hash,
    Short = <<(byte_size(Hash)-8):8, Pref:64>>,
    put(Short, Hash),
    Short;
shorthash(Any) -> Any.

longhash(Short = <<Len:8, Pref:64>>) ->
    case get(Short) of
        undefined -> <<Pref:64,0:(8*Len)>>;
        Hash      -> Hash
    end;
longhash(Any) -> Any.

get_hashmap() ->
    case get(hashmap) of
        undefined -> #{};
        Map       -> Map
    end.

%% -- State service ----------------------------------------------------------
-define(SERVER, epoch_eqc).

state_start(Chain) ->
    (catch erlang:exit(whereis(?SERVER), kill)),
    timer:sleep(1),
    register(?SERVER, spawn(fun() -> loop(Chain) end)).

state_get() ->
    state_rpc(get).

state_put(Chain) ->
    state_rpc({put, Chain}).

state_rpc(Cmd) ->
    Ref = make_ref(),
    ?SERVER ! {epoch, self(), Ref, Cmd},
    receive
        {epoch, Ref, Res} -> Res
    after 200 ->
        error({rpc_timeout, Cmd})
    end.

loop(Chain) ->
    receive
        {epoch, From, Ref, get} ->
            From ! {epoch, Ref, Chain},
            loop(Chain);
        {epoch, From, Ref, {put, NewChain}} ->
            From ! {epoch, Ref, ok},
            loop(NewChain)
    end.

top_block_with_state(Chain) ->
    Block = aec_chain_state:top_block(Chain),
    {ok, BlockHash} = aec_blocks:hash_internal_representation(Block),
    {ok, Trees} = aec_chain_state:get_block_state(BlockHash, Chain),
    {Block, Trees}.
