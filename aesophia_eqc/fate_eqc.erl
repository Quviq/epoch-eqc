%%% File        : fate_eqc.erl
%%% Author      : Ulf Norell
%%% Description : Properties for the FATE VM.
%%% Created     : 8 Oct 2019 by Ulf Norell
-module(fate_eqc).

-compile([export_all, nowarn_export_all]).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-define(TODO(Fmt, Args), io:format("TODO: " Fmt "\n", Args)).
-define(TODO(Fmt), ?TODO(Fmt, [])).

%% -- Instruction specs ------------------------------------------------------

-type type()     :: term(). %% TODO
-type arg_mode() :: immediate | any.
-type arg_spec() :: {in | out, arg_mode(), type()}.

-type mnemonic() :: atom().

%% Simple instruction (no jumping or stack expectations).
-record(instr,  {op     :: mnemonic(),
                 args   :: [arg_spec()]}).
-type instr_spec() :: #instr{}.

-spec instructions() -> [instr_spec()].
instructions() ->
    I = fun(Op, Ins, Out) ->
            fix_types(
            #instr{ op   = Op,
                    args = [{out, any, Out} | [{in, any, In} || In <- Ins]] })
        end,
    lists:filter(fun(#instr{ op = Op }) -> not black_listed(Op) end,
        [ I(Op, tuple_to_list(ArgTypes), ResType)
         || #{ arg_types := ArgTypes,
               res_type  := ResType,
               format    := Format,
               end_bb    := false,
               opname    := Op
             } <- aeb_fate_generate_ops:get_ops(),
            [a] == lists:usort(Format),
            length(Format) == tuple_size(ArgTypes) + 1
        ] ++ more_instructions()).

more_instructions() ->
    [#instr{ op = 'TUPLE', args = [{out, any, tuple}, {in, immediate, integer}] },
     #instr{ op = 'PUSH', args = [{in, any, any}] },
     #instr{ op = 'DUP',  args = [{in, any, any}] },
     #instr{ op = 'DUPA', args = [] },
     #instr{ op = 'POP',  args = [{out, any, any}] },
     #instr{ op = 'INCA', args = [] },
     #instr{ op = 'DECA', args = [] },
     #instr{ op = 'INC',  args = [{inout, any, integer}] },
     #instr{ op = 'DEC',  args = [{inout, any, integer}] },
     #instr{ op = 'BITS_ALLA',  args = [] },
     #instr{ op = 'BITS_NONEA', args = [] },
     #instr{ op = 'SPEND', args = [{in, any, address}, {in, any, integer}] },
     #instr{ op = 'JUMP', args = [] },
     #instr{ op = 'JUMPIF', args = [{in, any, boolean}] },
     #instr{ op = 'SWITCH_V2', args = [{in, any, variant}] },
     #instr{ op = 'SWITCH_V3', args = [{in, any, variant}] },
     #instr{ op = 'SWITCH_VN', args = [{in, any, variant}] },
     #instr{ op = 'CALL', args = [{in, immediate, integer}] },
     #instr{ op = 'RETURN', args = [] },
     #instr{ op = 'RETURNR', args = [{in, any, any}] }
    ].

spec_overrides() ->
    #{ 'VARIANT' =>
        [{out, any, variant},
         {in, any, {list, integer}},
         {in, any, integer},
         {in, any, integer}],
       'MAP_FROM_LIST' =>
        [{out, any, {map, not_map, any}},
         {in, any, {list, {tuple, [not_map, any]}}}]
     }.

fix_types(#instr{ op = Op } = I) ->
    case maps:get(Op, spec_overrides(), none) of
        none -> I#instr{ args = [ {Dir, Mode, fix_type(T)} || {Dir, Mode, T} <- I#instr.args ] };
        Args -> #instr{op = Op, args = Args}
    end.

fix_type(list)      -> {list, any};
fix_type(map)       -> {map, any, any};
fix_type(bool)      -> boolean;
fix_type(hash)      -> {bytes, 32};
fix_type(signature) -> {bytes, 64};
fix_type(T)         -> T.

black_listed('MICROBLOCK')           -> true;   %% Not implemented
black_listed('DUP')                  -> true;   %% Bugged
black_listed('GAS')                  -> true;   %% Not modelling gas costs
black_listed('ORACLE_REGISTER')      -> true;   %% TODO: Oracle/AENS/Crypto
black_listed('ORACLE_QUERY')         -> true;
black_listed('ORACLE_GET_ANSWER')    -> true;
black_listed('ORACLE_GET_QUESTION')  -> true;
black_listed('ORACLE_QUERY_FEE')     -> true;
black_listed('ORACLE_CHECK')         -> true;
black_listed('ORACLE_CHECK_QUERY')   -> true;
black_listed('AENS_RESOLVE')         -> true;
black_listed('VERIFY_SIG')           -> true;
black_listed('VERIFY_SIG_SECP256K1') -> true;
black_listed('ECVERIFY_SECP256K1')   -> true;
black_listed('ECRECOVER_SECP256K1')  -> true;
black_listed(_)                      -> false.

other_instructions() ->
    Simple = maps:from_list([{Op, true} || #instr{ op = Op } <- instructions() ]),
    [ Op || #{ opname := Op } <- aeb_fate_generate_ops:get_ops(),
            not maps:is_key(Op, Simple),
            not black_listed(Op) ].

-define(InstrSpecCache, '$ispec_cache').
-spec instruction_spec() -> #{ mnemonic() => instr_spec() }.
instruction_spec() ->
    case get(?InstrSpecCache) of
        undefined ->
            Spec = maps:from_list([ {I#instr.op, I} || I <- instructions() ]),
            put(?InstrSpecCache, Spec),
            Spec;
        Spec -> Spec
    end.

instruction_spec(Op) ->
    maps:get(Op, instruction_spec()).

%% -- VM state model ---------------------------------------------------------

-type pubkey() :: <<_:256>>.

-type account() :: #{ balance := non_neg_integer(),
                      creator := none | pubkey() }.

-type chain_env() :: #{ caller     := pubkey(),
                        origin     := pubkey(),
                        address    := pubkey(),
                        accounts   := #{ pubkey() => account() },
                        timestamp  := non_neg_integer(),
                        difficulty := non_neg_integer(),
                        height     := pos_integer() }.

-record(frame, { vars  :: #{ integer() => value() },
                 args  :: #{ integer() => value() } }).

-type frame() :: #frame{}.

-record(state, { stack      = []    :: [value()],
                 vars       = #{}   :: #{ integer() => value() },
                 store      = #{}   :: #{ integer() => value() },
                 args       = #{}   :: #{ integer() => value() },
                 failed     = false :: boolean() | skip,
                 chain_env  = #{}   :: chain_env(),
                 call_stack = []    :: [frame()] }).

-type state() :: #state{}.

-type arg()   :: aeb_fate_ops:fate_arg().
-type instr() :: {mnemonic(), [arg()]}.

-type value() :: aeb_fate_data:fate_type().

-spec initial_state(chain_env(), [value()]) -> state().
initial_state(ChainEnv, Args) ->
    #state{ args      = maps:from_list(indexed(0, Args)),
            chain_env = ChainEnv }.

-spec chain_env(chain_env(), atom()) -> term().
chain_env(#state{chain_env = Env}, Key) -> maps:get(Key, Env).

get_account(S, Pubkey, Field, Default) ->
    case maps:get(Pubkey, chain_env(S, accounts), not_found) of
        not_found -> Default;
        Acc       -> maps:get(Field, Acc)
    end.

push_call_stack(S, N) ->
    {FunArgs, Stack1} = lists:split(N, S#state.stack),
    Frame = #frame{ vars = S#state.vars, args = S#state.args },
    S#state{ stack      = Stack1,
             vars       = #{},
             args       = maps:from_list(indexed(0, FunArgs)),
             call_stack = [Frame | S#state.call_stack] }.

pop_call_stack(S = #state{ call_stack = [Frame | CallStack] }, V) ->
    S#state{ stack      = [V | S#state.stack],
             args       = Frame#frame.args,
             vars       = Frame#frame.vars,
             call_stack = CallStack }.

new_account() ->
    #{ balance => 0, creator => none }.

on_account(Pubkey, Field, Fun, S = #state{ chain_env = Env = #{ accounts := Accounts } }) ->
    Upd = fun(Acc) -> maps:update_with(Field, Fun, Acc) end,
    S#state{ chain_env = Env#{ accounts := maps:update_with(Pubkey, Upd, Upd(new_account()), Accounts) } }.

spend(From, To, Amount, S) ->
    on_account(From, balance, fun(V) -> V - Amount end,
    on_account(To,   balance, fun(V) -> V + Amount end, S)).

-spec get_instr(mnemonic()) -> instr_spec() | undefined.
get_instr(Op) ->
    maps:get(Op, instruction_spec(), undefined).

-spec get_value(state(), arg()) -> value().
get_value(_, {immediate, V})      -> V;
get_value(S, {arg, N})            -> maps:get(N, S#state.args, void);
get_value(S, {var, N}) when N < 0 -> maps:get(-N - 1, S#state.store, void);
get_value(S, {var,  N})           -> maps:get(N, S#state.vars, void);
get_value(S, {var_, N})           -> maps:get(N, S#state.vars, void);
get_value(S, {store, N})          -> maps:get(N, S#state.store, void);
get_value(S, {stack, 0})          -> hd(S#state.stack ++ [void]).

-spec get_type(state(), arg()) -> type() | void.
get_type(S, Arg) -> infer_type(get_value(S, Arg)).

-spec pop(non_neg_integer(), state()) -> state().
pop(N, S) ->
    S#state{ stack = drop(N, S#state.stack) }.

-spec write_arg(arg(), value(), state()) -> state().
write_arg({stack, 0}, Val, S) -> S#state{ stack = [Val | S#state.stack] };
write_arg({var_, N},  Val, S) -> S#state{ vars  = (S#state.vars)#{ N => Val } };
write_arg({store, N}, Val, S) -> S#state{ store = (S#state.store)#{ N => Val } };
write_arg({arg, N},   Val, S) -> S#state{ args  = (S#state.args)#{ N => Val } }.

-spec matching_regs(state(), fun((value()) -> boolean())) -> [arg()].
matching_regs(#state{ vars = VarMap, store = StoreMap, args = ArgMap }, Valid) ->
    Vars  = [ {{var_, I}, V} || {I, V}  <- maps:to_list(VarMap) ],
    Store = [ {{store, I}, V} || {I, V} <- maps:to_list(StoreMap) ],
    Args  = [ {{arg,  I}, V} || {I, V}  <- maps:to_list(ArgMap) ],
    [ A || {A, V} <- Vars ++ Store ++ Args, Valid(V) ].

-spec infer_type(value()) -> type().
infer_type(N) when is_integer(N) -> integer;
infer_type(true) -> boolean;
infer_type(false) -> boolean;
infer_type(S) when is_binary(S) -> string;
infer_type({bits, _}) -> bits;
infer_type({bytes, B}) -> {bytes, byte_size(B)};
infer_type({address, _}) -> address;
infer_type({contract, _}) -> contract;
infer_type({oracle, _}) -> oracle;
infer_type({oracle_query, _}) -> oracle_query;
infer_type(L) when is_list(L) ->
    {list, lists:foldl(fun(V, T) -> isect_type(infer_type(V), T) end,
                       any, L)};
infer_type({tuple, T}) ->
    {tuple, [infer_type(V) || V <- tuple_to_list(T)]};
infer_type({variant, Arities, Tag, Args}) ->
    ArgTypes = fun({I, _}) when I == Tag -> infer_type({tuple, Args});
                  ({_, Ar}) -> {tuple, lists:duplicate(Ar, any)} end,
    Tss = lists:map(ArgTypes, indexed(0, Arities)),
    {variant, Tss};
infer_type(M) when is_map(M) ->
    case infer_type([ {tuple, E} || E <- maps:to_list(M) ]) of
        {list, {tuple, [K, V]}} ->
            case contains(map, K) of
                true  -> void;
                false -> {map, K, V}
            end;
        {list, any} -> {map, not_map, any};
        _           -> void
    end;
infer_type(void) -> void;
infer_type(V) ->
    ?TODO("infer_type(~p)", [V]),
    void.

isect_type(any, T) -> T;
isect_type(T, any) -> T;
isect_type(not_map, T) -> case contains(map, T) of true -> void; false -> T end;
isect_type(T, not_map) -> case contains(map, T) of true -> void; false -> T end;
isect_type({list, S}, {list, T}) -> {list, isect_type(S, T)};
isect_type({tuple, Ss}, {tuple, Ts}) when length(Ss) == length(Ts) ->
    {tuple, lists:zipwith(fun isect_type/2, Ss, Ts)};
isect_type({map, K1, V1}, {map, K2, V2}) ->
    {map, isect_type(K1, K2), isect_type(V1, V2)};
isect_type({variant, Sss}, {variant, Tss}) when length(Sss) == length(Tss) ->
    {variant, lists:zipwith(fun isect_type/2, Sss, Tss)};
isect_type(T, T) -> T;
isect_type(_, _) -> void.

is_variant({variant, _, _, _}) -> true;
is_variant(_) -> false.

is_variant({variant, Ar, _, _}, N) -> length(Ar) == N;
is_variant(_, _) -> false.

%% Check that an instruction can be executed in the given state.
-spec check_instr(state(), instr()) -> boolean().
check_instr(S, {Op, Args}) ->
    case get_instr(Op) of
        undefined ->
            ?TODO("non-simple instruction ~s", [Op]),
            false;
        #instr{ args = ArgsSpec } ->
            check_arguments(S, ArgsSpec, Args);
        _ -> false
    end.

-spec check_arguments(state(), [instr_spec()], [instr()]) -> boolean().
check_arguments(_S, [], []) -> true;
check_arguments(S, [{out, Mode, _} | ArgSpec], [Arg | Args]) ->
    check_mode(out, Mode, Arg) andalso
    check_arguments(S, ArgSpec, Args);
check_arguments(S, [{in, Mode, Type} | ArgSpec], [Arg | Args]) ->
    S1 = case Arg of
             {stack, 0} -> pop(1, S);
             _          -> S
         end,
    check_mode(in, Mode, Arg) andalso
    match_type(Type, get_type(S, Arg)) andalso
    check_arguments(S1, ArgSpec, Args);
check_arguments(S, [{inout, Mode, Type} | ArgSpec], [Arg | Args]) ->
    check_mode(out, Mode, Arg) andalso
    check_arguments(S, [{in, Mode, Type} | ArgSpec], [Arg | Args]);
check_arguments(_, _, _) -> false.

-spec check_mode(in | out, arg_mode(), arg()) -> boolean().
check_mode(out, _, {immediate, _})        -> false;
check_mode(out, any, _)                   -> true;
check_mode(in, any, _)                    -> true;
check_mode(in, immediate, {immediate, _}) -> true;
check_mode(in, immediate, _)              -> false.

-spec match_type(Need :: type(), Have :: type()) -> boolean().
match_type(T, T)                             -> true;
match_type(_, void)                          -> false;
match_type(_, any)                           -> true;
match_type(any, _)                           -> true;
match_type(not_map, T)                       -> not contains(map, T);
match_type(_, not_map)                       -> false;
match_type(S, T) when is_atom(S), is_atom(T) -> false;
match_type(bytes, {bytes, _})                -> true;
match_type({bytes, _}, _)                    -> false;
match_type(_, {bytes, _})                    -> false;
match_type({list, S}, {list, T})             -> match_type(S, T);
match_type({list, _}, _)                     -> false;
match_type(_, {list, _})                     -> false;
match_type({map, K1, V1}, {map, K2, V2})     -> match_type(K1, K2) andalso match_type(V1, V2);
match_type({map, _, _}, _)                   -> false;
match_type(_, {map, _, _})                   -> false;
match_type(tuple, {tuple, _}) -> true;
match_type({tuple, Ss}, {tuple, Ts}) when length(Ss) == length(Ts) ->
    all(lists:zipwith(fun(S, T) -> match_type(S, T) end, Ss, Ts));
match_type({tuple, _}, _)                    -> false;
match_type(_, {tuple, _})                    -> false;
match_type(variant, {variant, _}) -> true;
match_type({variant, Sss}, {variant, Tss}) when length(Sss) == length(Tss) ->
    all(lists:zipwith(fun match_type/2, Sss, Tss));
match_type({variant, _}, _) -> false;
match_type(_, {variant, _}) -> false;
match_type(S, T)                             ->
    ?TODO("match_type(~p, ~p)", [S, T]),
    false.

has_type(V, T) -> match_type(T, infer_type(V)).

read_arguments(S, Args) ->
    {S1, Vals} = lists:foldl(fun read_arg/2, {S, []}, Args),
    {S1, lists:reverse(Vals)}.

read_arg(Arg, {S, Acc}) ->
    Val = get_value(S, Arg),
    S1  = case Arg of
              {stack, 0} -> pop(1, S);
              _          -> S
          end,
    {S1, [Val | Acc]}.

hash(Alg, Val) ->
    Bin = case Val of
            {bytes, V}            -> V;
            _ when is_binary(Val) -> Val;
            _                     -> aeb_fate_encoding:serialize(Val)
          end,
    Hash = case Alg of
               sha3    -> aec_hash:hash(evm, Bin);
               sha256  -> aec_hash:sha256_hash(Bin);
               blake2b -> aec_hash:blake2b_256_hash(Bin)
           end,
    {bytes, Hash}.

-define(When(B, X), case B of true -> X; false -> skip end).
-define(WhenBetween(A, X, B, Go), ?When(A =< X andalso X =< B, Go)).
-define(MaxBits, 2048).
-define(MaxBlockGas, 6000000).

-define(WhenS(B, S, Out), case B of true -> {S, Out}; false -> {#state{ failed = skip }, Out} end).

eval_instr('INC', [A])     -> A + 1;
eval_instr('DEC', [A])     -> A - 1;
eval_instr('ADD', [A, B])  -> A + B;
eval_instr('SUB', [A, B])  -> A - B;
eval_instr('MUL', [A, B])  -> A * B;
eval_instr('DIV', [A, B])  -> ?When(B /= 0, A div B);
eval_instr('MOD', [A, B])  -> ?When(B /= 0, A rem B);
eval_instr('POW', [A, B])  -> ?When(B >= 0 andalso pow_bytes(A, B) < 512, pow(A, B));
eval_instr('STORE', [A])   -> A;
eval_instr('SHA3', [A])    -> hash(sha3, A);
eval_instr('SHA256', [A])  -> hash(sha256, A);
eval_instr('BLAKE2B', [A]) -> hash(blake2b, A);
eval_instr('LT', [A, B])   -> A < B;
eval_instr('GT', [A, B])   -> A > B;
eval_instr('EQ', [A, B])   -> A == B;
eval_instr('ELT', [A, B])  -> A =< B;
eval_instr('EGT', [A, B])  -> A >= B;
eval_instr('NEQ', [A, B])  -> A /= B;
eval_instr('AND', [A, B])  -> A and B;
eval_instr('OR', [A, B])   -> A or B;
eval_instr('NOT', [A])     -> not A;
eval_instr('ELEMENT', [A, {tuple, B}]) ->
    ?WhenBetween(0, A, tuple_size(B) - 1, element(A + 1, B));
eval_instr('SETELEMENT', [A, {tuple, B}, C]) ->
    ?WhenBetween(0, A, tuple_size(B) - 1,
       {tuple, setelement(A + 1, B, C)});
eval_instr('MAP_EMPTY', [])           -> #{};
eval_instr('MAP_LOOKUP', [M, K])      -> ?When(maps:is_key(K, M), maps:get(K, M));
eval_instr('MAP_LOOKUPD', [M, K, D])  -> maps:get(K, M, D);
eval_instr('MAP_UPDATE', [M, K, V])   -> M#{ K => V };
eval_instr('MAP_DELETE', [M, K])      -> maps:remove(K, M);
eval_instr('MAP_MEMBER', [M, K])      -> maps:is_key(K, M);
eval_instr('MAP_FROM_LIST', [L])      -> maps:from_list([E || {tuple, E} <- L]);
eval_instr('MAP_SIZE', [M])           -> maps:size(M);
eval_instr('MAP_TO_LIST', [M])        -> [{tuple, E} || E <- maps:to_list(M)];
eval_instr('IS_NIL', [L])             -> L == [];
eval_instr('CONS', [X, Xs])           -> [X | Xs];
eval_instr('HD', [L])                 -> ?When(length(L) > 0, hd(L));
eval_instr('TL', [L])                 -> ?When(length(L) > 0, tl(L));
eval_instr('LENGTH', [L])             -> length(L);
eval_instr('NIL', [])                 -> [];
eval_instr('APPEND', [Xs, Ys])        -> Xs ++ Ys;
eval_instr('STR_JOIN', [S, T])        -> <<S/binary, T/binary>>;
eval_instr('INT_TO_STR', [N])         -> iolist_to_binary(io_lib:format("~w", [N]));
eval_instr('ADDR_TO_STR', [{address, A}]) -> aeser_api_encoder:encode(account_pubkey, A);
eval_instr('STR_REVERSE', [S])        -> list_to_binary(lists:reverse(binary_to_list(S)));
eval_instr('STR_LENGTH', [S])         -> byte_size(S);
eval_instr('BYTES_TO_INT', [{bytes, B}]) ->
    Size = byte_size(B),
    <<N:Size/unit:8>> = B,
    N;
eval_instr('BYTES_TO_STR', [{bytes, B}]) ->
    case B of
        <<>> -> <<>>;
        _    ->
            Size = byte_size(B),
            <<N:Size/unit:8>> = B,
            iolist_to_binary(io_lib:format("~*.16.0B", [Size * 2, N]))
    end;
eval_instr('BYTES_CONCAT', [{bytes, A}, {bytes, B}]) ->
    {bytes, <<A/binary, B/binary>>};
eval_instr('BYTES_SPLIT', [{bytes, Bin}, N]) ->
    ?WhenBetween(0, N, byte_size(Bin),
    begin
        <<A:N/binary, B/binary>> = Bin,
        {tuple, {{bytes, A}, {bytes, B}}}
    end);
eval_instr('INT_TO_ADDR', [N])        -> {address, <<N:256>>};
eval_instr('VARIANT_TEST', [{variant, _, Tag, _}, Tag1]) ->
    ?When(Tag1 >= 0, Tag == Tag1);
eval_instr('VARIANT_ELEMENT', [{variant, _Ar, _Tag, Args}, N]) ->
    ?WhenBetween(0, N, tuple_size(Args) - 1,
                 element(N + 1, Args));
eval_instr('BITS_NONE',  [])                     -> {bits, 0};
eval_instr('BITS_ALL',   [])                     -> {bits, -1};
eval_instr('BITS_ALL_N', [N])                    -> ?WhenBetween(0, N, ?MaxBits, {bits, (1 bsl N) - 1});
eval_instr('BITS_SET',   [{bits, N}, I])         -> ?WhenBetween(0, I, ?MaxBits, {bits, N bor (1 bsl I)});
eval_instr('BITS_CLEAR', [{bits, N}, I])         -> ?WhenBetween(0, I, ?MaxBits, {bits, N band bnot (1 bsl I)});
eval_instr('BITS_TEST',  [{bits, N}, I])         -> ?WhenBetween(0, I, ?MaxBits, N band (1 bsl I) /= 0);
eval_instr('BITS_SUM',   [{bits, A}])            -> ?When(A >= 0, pop_count(A));
eval_instr('BITS_OR',    [{bits, A}, {bits, B}]) -> {bits, A bor B};
eval_instr('BITS_AND',   [{bits, A}, {bits, B}]) -> {bits, A band B};
eval_instr('BITS_DIFF',  [{bits, A}, {bits, B}]) -> {bits, A band bnot B};
eval_instr('IS_ORACLE', [_])                       -> false;
eval_instr('AUTH_TX_HASH', _)                      -> {variant, [0, 1], 0, {}};
eval_instr('CONTRACT_TO_ADDRESS', [{contract, A}]) -> {address, A};
eval_instr('ADDRESS_TO_CONTRACT', [{address, A}])  -> {contract, A}.

eval_instr(S, 'BLOCKHASH', [H])  ->
    Current = chain_env(S, height),
    Hash = case 0 =< H andalso Current - 256 < H andalso H < Current of
               false -> {variant, [0, 1], 0, {}};
               true  -> {variant, [0, 1], 1, {{bytes, <<0:256>>}}}
           end,
    {S, [Hash]};
eval_instr(S, 'IS_PAYABLE',  [{address, _}]) -> {S, [true]};
eval_instr(S, 'IS_CONTRACT', [{address, A}]) -> {S, [get_account(S, A, creator, none) /= none]};
eval_instr(S, 'BENEFICIARY', []) -> {S, [{address, chain_env(S, beneficiary)}]};
eval_instr(S, 'GASLIMIT', [])    -> {S, [?MaxBlockGas]};
eval_instr(S, 'GASPRICE', [])    -> {S, [chain_env(S, gas_price)]};
eval_instr(S, 'CREATOR', [])     -> {S, [{address, get_account(S, chain_env(S, address), creator, void)}]};
eval_instr(S, 'GENERATION', [])  -> {S, [chain_env(S, height)]};
eval_instr(S, 'DIFFICULTY', [])  -> {S, [chain_env(S, difficulty)]};
eval_instr(S, 'TIMESTAMP', [])   -> {S, [chain_env(S, timestamp)]};
eval_instr(S, 'CALL_VALUE', [])  -> {S, [chain_env(S, call_value)]};
eval_instr(S, 'ORIGIN', [])      -> {S, [{address, chain_env(S, origin)}]};
eval_instr(S, 'CALLER', [])      -> {S, [{address, chain_env(S, caller)}]};
eval_instr(S, 'ADDRESS', [])     -> {S, [{address, chain_env(S, address)}]};
eval_instr(S, 'BALANCE', [])     -> {S, [get_account(S, chain_env(S, address), balance, 0)]};
eval_instr(S, 'BALANCE_OTHER', [{address, A}]) -> {S, [get_account(S, A, balance, 0)]};
eval_instr(S = #state{ stack = Stack }, 'TUPLE', [N]) ->
    case N >= 0 andalso N =< length(Stack) of
        false -> {S, [skip]};
        true  ->
            {Args, Stack1} = lists:split(N, Stack),
            {S#state{ stack = Stack1 }, [{tuple, list_to_tuple(lists:reverse(Args))}]}
    end;
eval_instr(S = #state{ stack = Stack }, 'VARIANT', [Ar, Tag, N]) ->
    Between = fun(A, X, B) -> A =< X andalso X =< B end,
    case Between(0, N, length(Stack))    andalso
         Between(0, Tag, length(Ar) - 1) andalso
         lists:nth(Tag + 1, Ar) == N of
        false -> {S, [skip]};
        true  ->
            {Args, Stack1} = lists:split(N, Stack),
            {S#state{ stack = Stack1 }, [{variant, Ar, Tag, list_to_tuple(lists:reverse(Args))}]}
    end;
eval_instr(S = #state{ stack = Stack }, 'PUSH', [V]) ->
    {S#state{ stack = [V | Stack] }, []};
eval_instr(S = #state{ stack = Stack }, 'DUPA', []) ->
    {S#state{ stack = [hd(Stack ++ [skip]) | Stack] }, []};
eval_instr(S = #state{ stack = Stack }, 'DUP', [N]) ->
    ?WhenS(0 =< N andalso N < length(Stack),
           S#state{ stack = [lists:nth(N + 1, Stack) | Stack] }, []);
eval_instr(S = #state{ stack = Stack }, 'POP', []) ->
    {pop(1, S), [?When([] /= Stack, hd(Stack))]};
eval_instr(S, Op, []) when Op == 'INCA'; Op == 'DECA' ->
    Bump = if Op == 'INCA' -> fun(V) -> V + 1 end;
              Op == 'DECA' -> fun(V) -> V - 1 end end,
    case S#state.stack of
        [V | Stack1] when is_integer(V) ->
            {S#state{ stack = [Bump(V) | Stack1] }, []};
        _ -> {S#state{ failed = skip }, []}
    end;
eval_instr(S, 'BITS_ALLA', []) ->
    {S#state{ stack = [{bits, -1} | S#state.stack] }, []};
eval_instr(S, 'BITS_NONEA', []) ->
    {S#state{ stack = [{bits, 0} | S#state.stack] }, []};
eval_instr(S, 'SPEND', [{address, A}, Amount]) ->
    Self    = chain_env(S, address),
    Balance = get_account(S, Self, balance, 0),
    ?WhenS(0 =< Amount andalso Amount =< Balance,
           spend(Self, A, Amount, S), []);
eval_instr(S, 'JUMP', []) -> {S, []};
eval_instr(S, 'JUMPIF', [V]) ->
    ?WhenS(lists:member(V, [true, false]), S, []);
eval_instr(S, 'SWITCH_V2', [V]) -> ?WhenS(is_variant(V, 2), S, []);
eval_instr(S, 'SWITCH_V3', [V]) -> ?WhenS(is_variant(V, 3), S, []);
eval_instr(S, 'SWITCH_VN', [V]) -> ?WhenS(is_variant(V), S, []);
eval_instr(S = #state{ stack = Stack }, 'CALL', [N]) ->
    ?WhenS(length(Stack) >= N, push_call_stack(S, N), []);
eval_instr(S = #state{ stack = [V | Stack] }, 'RETURN', []) ->
    ?WhenS([] /= S#state.call_stack,
           pop_call_stack(S#state{ stack = Stack }, V), []);
eval_instr(S, 'RETURN', []) -> ?WhenS(false, S, []);
eval_instr(S, 'RETURNR', [V]) ->
    ?WhenS([] /= S#state.call_stack,
           pop_call_stack(S, V), []);
eval_instr(S, Op, Vs)           -> {S, [eval_instr(Op, Vs)]}.

-spec step_instr(state(), instr()) -> state().
step_instr(S, {Op, Args}) ->
    #instr{ args = ArgsSpec } = get_instr(Op),
    Args1 = lists:zip(ArgsSpec, Args),
    InArgs  = [ Arg || {{Tag, _, _}, Arg} <- Args1, lists:member(Tag, [in, inout]) ],
    OutArgs = [ Arg || {{Tag, _, _}, Arg} <- Args1, lists:member(Tag, [out, inout]) ],
    {S1, InVals}  = read_arguments(S, InArgs),
    {S2, OutVals} =
        try eval_instr(S1, Op, InVals)
        catch _:Err ->
            io:format("** Error on ~s ~p -> ~p:\n~p\n~p\n", [Op, InArgs, OutArgs, Err, erlang:get_stacktrace()]),
            {S1#state{ failed = true }, lists:duplicate(length(OutArgs), void)}
        end,
    lists:foldl(fun({Arg, Val}, St) -> write_arg(Arg, Val, St) end,
                S2, lists:zip(OutArgs, OutVals)).

%% -- Generators -------------------------------------------------------------

small_nat() -> ?SIZED(N, resize(N div 3, nat())).

out_arg_g() ->
    oneof([{stack, 0},
           {var_, small_nat()},
           {store, small_nat()},
           {arg, small_nat()}]).

-define(constrained(Args, Local, Gen, V, Pred),
        {in, any, {constrained, fun(Args) -> Local, {Gen, fun(V) -> Pred end} end}}).
-define(constrained(Args, Gen, V, Pred), ?constrained(Args, ok, Gen, V, Pred)).

-define(constrained_t(Args, Type),
        ?constrained(Args, __T = Type, value_g(__T), V, has_type(V, __T))).

args_g(S, 'DUP', _) ->
    H = length(S#state.stack),
    args_g(S, [?constrained(_, if H == 0 -> void; true -> choose(0, H - 1) end,
                            V, V >= 0 andalso V < H)]);
args_g(S, Elem, _) when Elem == 'ELEMENT'; Elem == 'SETELEMENT' ->
    Regs  = matching_regs(S, fun({tuple, T}) -> tuple_size(T) > 0; (_) -> false end),
    Sizes = lists:usort([ tuple_size(T) || R <- Regs, {tuple, T} <- [get_value(S, R)] ] ++ [3]),
    ?LET(N, elements(Sizes),
         args_g(S, [{out, any, any},
                    ?constrained(_, choose(0, N - 1), V, V >= 0 andalso V < N),
                    ?constrained([I], {tuple, eqc_gen:fmap(fun list_to_tuple/1, vector(N, value_g()))},
                                 V, case V of
                                        {tuple, T} -> tuple_size(T) > I;
                                        _          -> false
                                    end)] ++
                   [?constrained_t([I, {tuple, T}], infer_type(element(I + 1, T)))
                    || Elem == 'SETELEMENT']));
args_g(S, 'CONS', _) ->
    Regs  = matching_regs(S, fun is_list/1),
    Types = [ T || R <- Regs, {list, T} <- [get_type(S, R)], T /= any ],
    ?LET(T, frequency([{20, T} || T <- Types] ++ [{1, any}]),
         args_g(S, [{out, any, any},
                    {in, any, T},
                    ?constrained_t([H], {list, infer_type(H)})]));
args_g(S, 'APPEND', _) ->
    Regs  = matching_regs(S, fun is_list/1),
    Types = [ {list, T} || R <- Regs, {list, T} <- [get_type(S, R)], T /= any ],
    ?LET(ListT, frequency([{20, T} || T <- Types] ++ [{1, {list, any}}]),
         args_g(S, [{out, any, any},
                    {in, any, ListT},
                    ?constrained_t([Xs], infer_type(Xs))]));
args_g(S, MapOp, _) when MapOp == 'MAP_UPDATE'; MapOp == 'MAP_LOOKUPD' ->
    map_and_key_args_g(S, [?constrained_t([M, _], begin {map, _, ValT} = infer_type(M), ValT end)]);
args_g(S, 'MAP_DELETE', _) -> map_and_key_args_g(S, []);
args_g(S, 'MAP_MEMBER', _) -> map_and_key_args_g(S, []);
args_g(S, 'MAP_LOOKUP', _) ->
    map_args_g(S, [?constrained([M], Keys = maps:keys(M),
                                if Keys == [] -> void;
                                   true       -> elements(Keys) end,
                                V, lists:member(V, Keys))]);
args_g(S, 'MAP_FROM_LIST', _) ->
    args_g(S, [{out, any, any},
               ?constrained([], value_g({list, {tuple, [not_map, any]}}),
                            V, case infer_type(V) of
                                   {list, {tuple, [K, _]}} -> not contains(map, K);
                                   _                       -> false
                               end)]);
args_g(S, 'TUPLE', _) ->
    StackH = length(S#state.stack),
    args_g(S, [{out, any, any},
               ?constrained([], choose(0, StackH),
                            _, false)]);    %% immediate
args_g(S, 'VARIANT', _) ->
    StackH = length(S#state.stack),
    CheckAr = fun(Ar) -> is_list(Ar) andalso Ar /= [] andalso
                         lists:all(fun(N) -> 0 =< N andalso N < 256 end, Ar) andalso
                         lists:any(fun(N) -> N =< StackH end, Ar) end,
    Between = fun(A, X, B) -> A =< X andalso X =< B end,
    args_g(S, [{out, any, any},
               ?constrained([], ?SUCHTHAT(Ar, list(3, choose(0, 3)), CheckAr(Ar)),
                            Ar, CheckAr(Ar)),
               ?constrained([Ar], elements([ I || {I, A} <- indexed(0, Ar), A =< StackH ]),
                            Tag, 0 =< Tag andalso Tag < length(Ar) andalso
                                 Between(0, lists:nth(Tag + 1, Ar), StackH)),
               ?constrained([Ar, Tag], N = lists:nth(Tag + 1, Ar),
                            N, V, V == N)]);
args_g(S, 'VARIANT_ELEMENT', _) ->
    args_g(S, [{out, any, any}, {in, any, variant},
               ?constrained([{variant, _, _, Args}], N = tuple_size(Args),
                            if N == 0 -> void; true -> choose(0, N) end,
                            I, 0 =< I andalso I < N)]);
args_g(S, 'BYTES_SPLIT', _) ->
    args_g(S, [{out, any, any}, {in, any, bytes},
               ?constrained([{bytes, B}], N = byte_size(B),
                            choose(0, N), I, 0 =< I andalso I =< N)]);
args_g(S, 'SWITCH_V2', _) ->
    args_g(S, [?constrained([], value_g({variant, [tuple, tuple]}),
                            V, is_variant(V, 2))]);
args_g(S, 'SWITCH_V3', _) ->
    args_g(S, [?constrained([], value_g({variant, [tuple, tuple, tuple]}),
                            V, is_variant(V, 3))]);
args_g(S, 'CALL', _) ->
    args_g(S, [?constrained([], choose(0, length(S#state.stack)),
                            _, false)]);
args_g(S, _Op, Spec) -> args_g(S, Spec).

map_args_g(S, Rest) ->
    Regs     = matching_regs(S, fun is_map/1),
    KeyTypes = [ K || R <- Regs, {map, K, _} <- [get_type(S, R)], K /= any ],
    ?LET(MapT, frequency([{20, {map, K, any}} || K <- KeyTypes] ++ [{1, {map, any, any}}]),
         args_g(S, [{out, any, any}, {in, any, MapT}] ++ Rest)).

map_and_key_args_g(S, Rest) ->
    map_args_g(S, [?constrained_t([M], begin {map, KeyT, _} = infer_type(M),
                                             substitute(any, not_map, KeyT) end)
                  | Rest]).

args_g(S, Spec) ->
    args_g(S, Spec, [], []).

args_g(_, [], _, Args) -> lists:reverse(Args);
args_g(S, [{out, _, _} | ArgsSpec], Vs, Acc) ->
    ?LET(Arg, out_arg_g(), args_g(S, ArgsSpec, Vs, [Arg | Acc]));
args_g(S, [{in, immediate, Type} | ArgsSpec], Vs, Acc) ->
    ?LET(V, value_g(Type),
         args_g(S, ArgsSpec, [V | Vs], [{immediate, V} | Acc]));
args_g(S, [{in, any, Spec} | ArgsSpec], Vs, Acc) ->
    ?LET(Arg, arg_g(S, lists:reverse(Vs), Spec),
    begin
        S1 = case Arg of
                {stack, 0} -> pop(1, S);
                _          -> S
             end,
        args_g(S1, ArgsSpec, [get_value(S, Arg) | Vs], [Arg | Acc])
    end);
args_g(S, [{inout, any, {constrained, _} = Spec} | ArgsSpec], Vs, Acc) ->
    args_g(S, [{in, any, Spec} | ArgsSpec], Vs, Acc);
args_g(S, [{inout, any, Type} | ArgsSpec], Vs, Acc) ->
    args_g(S, [?constrained(_, skip, V, has_type(V, Type)) | ArgsSpec], Vs, Acc).

arg_g(S, Vs, {constrained, Spec}) ->
    {Gen, Pred} = Spec(Vs),
    Regs = matching_regs(S, Pred),
    frequency(
      [{1, {immediate, Gen}}] ++
      [{5, elements(Regs)} || Regs /= []]);
arg_g(S, Vs, Type) ->
    arg_g(S, Vs, {constrained, fun(_) -> {value_g(Type),
                                          fun(V) -> match_type(Type, infer_type(V)) end}
                               end}).

pubkey_g() -> noshrink(binary(32)).

-define(TypeDepth, 2).

type_g() ->
    type_g(?TypeDepth).

type_g(D) ->
    ?LAZY(?SUCHTHAT(T,
    frequency(
      [{5, elements([integer, boolean, address, bits, contract, {bytes, 32}, {bytes, 64},
                     oracle, oracle_query, string])}] ++
      [{1, {bytes, frequency([{3, choose(0, 6)}, {1, choose(0, 128)}])}}] ++
      [{1, ?LETSHRINK([T], [type_g(D - 1)], {list, T})}               || D > 0] ++
      [{1, ?LETSHRINK(Ts, list(3, type_g(D - 1)), {tuple, Ts})}       || D > 0] ++
      [{1, ?LETSHRINK([K, V], vector(2, type_g(D - 1)), {map, K, V})} || D > 0] ++
      [{1, ?LET(Tss, non_empty(list(3, list(2, type_g(D - 1)))),
           ?LETSHRINK(_, lists:append(Tss),
           {variant, [{tuple, Ts} || Ts <- Tss]}))}]), valid_type(T))).

%% Shallow
valid_type({map, K, _}) -> not contains(map, K);
valid_type(_) -> true.

nomap(G) -> ?SUCHTHAT(T, G, not contains(map, T)).

instantiate_any(any) -> type_g();
instantiate_any(not_map) -> nomap(type_g());
instantiate_any({map, K, V}) ->
    {map, nomap(instantiate_any(K)), instantiate_any(V)};
instantiate_any(T) when is_tuple(T) ->
    eqc_gen:fmap(fun list_to_tuple/1, instantiate_any(tuple_to_list(T)));
instantiate_any(L) when is_list(L) ->
    [ instantiate_any(T) || T <- L ];
instantiate_any(T) -> return(T).

value_g() -> value_g(any).

value_g(Type) ->
    ?LET(Type1, instantiate_any(Type), value1_g(Type1)).

value1_g(integer)      -> int();
value1_g(boolean)      -> bool();
value1_g(address)      -> {address, pubkey_g()};
value1_g(bits)         -> {bits, int()};
value1_g(bytes)        -> {bytes, binary()};
value1_g({bytes, N})   -> {bytes, binary(N)};
value1_g(contract)     -> {contract, pubkey_g()};
value1_g(hash)         -> value1_g({bytes, 32});
value1_g(signature)    -> value1_g({bytes, 64});
value1_g(oracle)       -> {oracle, pubkey_g()};
value1_g(oracle_query) -> {oracle_query, pubkey_g()};
value1_g(string)       -> eqc_gen:fmap(fun list_to_binary/1, list(choose($!, $~)));
value1_g({list, T})    -> list(3, value1_g(T));
value1_g({tuple, Ts})  -> {tuple, eqc_gen:fmap(fun list_to_tuple/1, [value1_g(T) || T <- Ts])};
value1_g({variant, Tss}) ->
    ?LET({I, ArgTy}, elements(indexed(0, Tss)),
    ?LET({tuple, V}, value1_g(ArgTy),
    ?LET(Ar, [ case Ty of
                   _ when I == J -> tuple_size(V);
                   {tuple, Ts}   -> length(Ts);
                   tuple         -> choose(0, 3)
               end || {J, Ty} <- indexed(0, Tss) ],
    {variant, Ar, I, V})));
value1_g({map, K, V})  ->
    MkMap = fun(L) -> maps:from_list([T || {tuple, T} <- L]) end,
    eqc_gen:fmap(MkMap, value1_g({list, {tuple, [K, V]}}));
value1_g(tuple)        -> ?LET(Ts, list(3, type_g()), value_g({tuple, Ts}));
value1_g(variant)      ->
    ?LET(Ar, non_empty(list(3, choose(0, 3))),
    ?LET(Tag, choose(0, length(Ar) - 1),
    ?LET(Args, vector(lists:nth(Tag + 1, Ar), value_g()),
         {variant, Ar, Tag, list_to_tuple(Args)})));
%% value1_g(typerep)      -> {todo, typerep};
value1_g(void)         -> void.

no_todo(X) -> not contains(todo, X).

timestamp_g() -> choose(1550000000000, 1900000000000).

balance_g() ->
    oneof([0, choose(0, 1000000)]).

chain_env_g() ->
    Acct = fun(C) -> #{ balance => balance_g(), creator => C } end,
    ?LET({[Caller, Origin, Address, Creator, Beneficiary], Value}, {vector(5, pubkey_g()), balance_g()},
    #{ timestamp   => timestamp_g(),
       caller      => Caller,
       origin      => Origin,
       address     => Address,
       beneficiary => Beneficiary,
       gas_limit   => choose(3000000, 6000000),
       gas_price   => choose(1, 5),
       height      => choose(1, 10000),
       difficulty  => choose(0, 1000),
       call_value  => Value,
       accounts    => #{ Caller      => Acct(none),
                         Origin      => Acct(none),
                         Creator     => Acct(none),
                         Address     => Acct(Creator),
                         Beneficiary => Acct(none) } }).

state_g() ->
    ?LET({ChainEnv, Stack, Vars, Args}, {chain_env_g(), list(value_g()), map(int(), value_g()), map(nat(), value_g())},
         return(#state{ stack = Stack, vars = Vars, args = Args, chain_env = ChainEnv })).

%% -- State machine ----------------------------------------------------------

instr_weight(S, Op) when Op == 'INCA'; Op == 'DECA' ->
    case S#state.stack of
        [N | _] when is_integer(N) -> 5;
        _ -> 0
    end;
instr_weight(_, Op) ->
    try eval_instr(Op, undef) of
        todo -> 0;
        _    -> 1
    catch _:_ -> 1 end.

instr_args(S) ->
    ?LET(#instr{ op = Op, args = ArgsSpec }, frequency([ {instr_weight(S, I#instr.op), I}
                                                         || I <- maps:values(instruction_spec()) ]),
         [{Op, args_g(S, Op, ArgsSpec)}]).

instr_pre(S, [I]) ->
    no_todo(I) andalso not contains(void, I) andalso
    check_instr(S, I) andalso
    begin
        S1 = instr_next(S, {var, -1}, [I]),
        no_todo(S1) andalso not contains(skip, S1) andalso
        valid_state(S1#state{ failed = false })
    end.

instr_next(S, _, [I]) ->
    S1 = step_instr(S, I),
    case contains(void, S1) of
        true  -> S1#state{ failed = true };
        false -> S1
    end.

return_instrs(S) ->
    ?LET(Cmd, return_instr(S),
    case S#state.call_stack of
        []    -> [Cmd];
        [_|_] -> [Cmd | return_instrs(pop_call_stack(S, get_return_value(S, Cmd)))]
    end).

return_instr(S) ->
    ?LET(Reg, frequency([ {10, {stack, 0}} || S#state.stack /= [] ] ++
                        [ {10, elements([{var, I} || I <- maps:keys(S#state.vars)])}
                           || #{} /= S#state.vars ]++
                        [ {10, elements([{store, I} || I <- maps:keys(S#state.store)])}
                           || #{} /= S#state.store ]++
                        [ {10, elements([{arg, I} || I <- maps:keys(S#state.args)])}
                           || #{} /= S#state.args ] ++
                        [ {1, {immediate, value_g()}} ]),
    ?LET(Arg, case Reg of
                  {stack, 0} -> elements([{'RETURN', []}, {'RETURNR', [Reg]}]);
                  _          -> {'RETURNR', [Reg]}
              end,
        {set, {var, 0}, {call, ?MODULE, instr, [Arg]}})).

%% -- Running the code -------------------------------------------------------

build_code([{model, _}, {init, S} | Instrs]) ->
    ArgTypes = [ infer_type(Arg) || Arg <- maps:values(S#state.args) ],
    build_fcode(init_code_st(S, ArgTypes), Instrs).

-type bb() :: list().

-record(code_fr, {ref, instrs, bbs, extra_bbs, current_fun, arg_types}).

-record(code_st, { ref   :: reference(),
                   state :: #state{},
                   instrs     = [],
                   bbs        = [],
                   extra_bbs  = [],
                   current_fun,
                   fun_ix     = 1,
                   arg_types  = [],
                   fcode      = aeb_fate_code:new(),
                   call_stack = [] :: [#code_fr{}] }).

init_code_st(InitS, ArgTypes) ->
    #code_st{ state       = InitS,
              ref         = make_ref(),
              arg_types   = ArgTypes,
              current_fun = fun_name(1) }.

fun_name(Fn) -> list_to_binary(lists:concat(["fun_", Fn])).
fun_sym(Fn)  -> aeb_fate_code:symbol_identifier(fun_name(Fn)).

-spec finalize_bbs(#code_st{}) -> #{non_neg_integer() => bb()}.
finalize_bbs(#code_st{ ref = Ref,  instrs = Acc,
                       bbs = BBsR, extra_bbs = ExtraBBsR }) ->
    BBs      = lists:reverse([{Ref, Acc} | BBsR]),
    ExtraBBs = lists:reverse(ExtraBBsR),
    Lbls     = maps:from_list([ {R, Lbl} || {Lbl, {R, _}} <- indexed(0, BBs ++ ExtraBBs) ]),
    Lbl      = fun(R) -> maps:get(R, Lbls) end,
    LblIm    = fun(R) -> {immediate, Lbl(R)} end,
    UpdI     = fun({'JUMP', R})                    -> {'JUMP', LblIm(R)};
                  ({'JUMPIF', Arg, R})             -> {'JUMPIF', Arg, LblIm(R)};
                  ({'SWITCH_V2', Arg, R1, R2})     -> {'SWITCH_V2', Arg, LblIm(R1), LblIm(R2)};
                  ({'SWITCH_V3', Arg, R1, R2, R3}) -> {'SWITCH_V3', Arg, LblIm(R1), LblIm(R2), LblIm(R3)};
                  ({'SWITCH_VN', Arg, Rs})         -> {'SWITCH_VN', Arg, {immediate, lists:map(Lbl, Rs)}};
                  (I)                              -> I end,
    UpdIs    = fun([I | Is]) -> lists:reverse([UpdI(I) | Is]) end,

    maps:from_list([{Lbl(R), UpdIs(Is)} || {R, Is} <- BBs ++ ExtraBBs]).

pop_code(CS) ->
    case CS#code_st.call_stack of
        [] -> CS;
        [#code_fr{ ref         = Ref,
                   current_fun = Fun,
                   instrs      = Acc,
                   bbs         = BBs,
                   extra_bbs   = ExtraBBs,
                   arg_types   = ArgTypes } | CallStack] ->
            CS#code_st{ ref         = Ref,
                        current_fun = Fun,
                        instrs      = Acc,
                        bbs         = BBs,
                        extra_bbs   = ExtraBBs,
                        arg_types   = ArgTypes,
                        call_stack  = CallStack }
    end.

push_code(CS, Fun, Args) ->
    Frame = #code_fr{ ref         = CS#code_st.ref,
                      instrs      = CS#code_st.instrs,
                      bbs         = CS#code_st.bbs,
                      extra_bbs   = CS#code_st.extra_bbs,
                      current_fun = CS#code_st.current_fun,
                      arg_types   = CS#code_st.arg_types },
    CS#code_st{ current_fun = Fun,
                ref         = make_ref(),
                instrs      = [],
                bbs         = [],
                extra_bbs   = [],
                arg_types   = lists:map(fun infer_type/1, Args),
                call_stack  = [Frame | CS#code_st.call_stack] }.

do_return_instr(#code_st{ arg_types   = ArgTypes,
                          current_fun = Fun,
                          instrs      = Is,
                          fcode       = FCode } = CS, I, V) ->
    RetType  = infer_type(V),
    TypeSpec = substitute(not_map, any, {ArgTypes, RetType}),
    BBs      = finalize_bbs(CS#code_st{ instrs = [I | Is] }),
    pop_code(CS#code_st{ fcode = aeb_fate_code:insert_fun(Fun, [payable], TypeSpec, BBs, FCode) }).

build_fcode(#code_st{ fcode = FCode }, []) -> FCode;
build_fcode(CS, [{set, X, Call = {call, ?MODULE, instr, Args}} | Instrs]) ->
    #code_st{ state = S, ref = Ref, instrs = Acc, bbs = BBs, extra_bbs = ExtraBBs } = CS,
    CS1    = CS#code_st{ state = next_state(S, X, Call) },
    Var    = fun({var_, I})  -> {var, I};
                ({store, I}) -> {var, -I - 1};
                (A)          -> A end,
    I      = case Args of
                 [{Op, []}] -> Op;
                 [{Op, As}] -> list_to_tuple([Op | lists:map(Var, As)])
             end,
    DeadBB = fun(R) -> {R, [{'ABORT', {immediate, <<"Unreachable">>}}]} end,
    case I of
        'RETURN'       -> build_fcode(do_return_instr(CS1, I, get_value(S, {stack, 0})), Instrs);
        {'RETURNR', R} -> build_fcode(do_return_instr(CS1, I, get_value(S, R)), Instrs);
        {'CALL', {immediate, N}} ->
            FunArgs = lists:reverse(take(N, S#state.stack)),
            Ix1     = CS#code_st.fun_ix + 1,
            FunName = fun_name(Ix1),
            FunSym  = aeb_fate_code:symbol_identifier(FunName),
            Ref1    = make_ref(),
            BBs1    = [{Ref, [{'CALL', {immediate, FunSym}} | Acc]} | BBs],
            CS2     = CS1#code_st{ ref = Ref1, instrs = [], bbs = BBs1, fun_ix = Ix1 },
            build_fcode(push_code(CS2, FunName, FunArgs), Instrs);
        'JUMP' ->
            Ref1 = make_ref(),
            BBs1 = [DeadBB(make_ref()), {Ref, [{'JUMP', Ref1} | Acc]} | BBs],
            build_fcode(CS1#code_st{ref = Ref1, instrs = [], bbs = BBs1}, Instrs);
        {'JUMPIF', Arg} ->
            Ref1 = make_ref(),
            This = {Ref, [{'JUMPIF', Arg, Ref1} | Acc]},
            case get_value(S, Arg) of
                true  -> build_fcode(CS1#code_st{ref = Ref1, instrs = [],
                                                 bbs = [DeadBB(make_ref()), This | BBs]},
                                   Instrs);
                false -> build_fcode(CS1#code_st{ref = make_ref(), instrs = [],
                                                 bbs = [This | BBs],
                                                 extra_bbs = [DeadBB(Ref1) | ExtraBBs]},
                                   Instrs)
            end;
        {Switch, Arg} when Switch == 'SWITCH_V2'; Switch == 'SWITCH_V3'; Switch == 'SWITCH_VN' ->
            {variant, Ar, Tag, _} = get_value(S, Arg),
            Refs = [ make_ref() || _ <- Ar ],
            Instr = case Switch of
                        'SWITCH_VN' -> {'SWITCH_VN', Arg, Refs};
                        _           -> list_to_tuple([Switch, Arg | Refs])
                    end,
            This = {Ref, [Instr | Acc]},
            {Take, Skip} = extract_nth(Tag + 1, Refs),
            build_fcode(CS1#code_st{ ref = Take, instrs = [],
                                   bbs = [DeadBB(make_ref()), This | BBs],
                                   extra_bbs = lists:map(DeadBB, Skip) ++ ExtraBBs },
                      Instrs);
        _ -> build_fcode(CS1#code_st{ instrs = [I | Acc] }, Instrs)
    end.

make_store(undefined) -> aefa_stores:initial_contract_store();
make_store(Store)     -> Store.

make_trees(#{ accounts := Accounts } = Env, Cache) ->
    %% All contracts and the caller must have accounts
    Trees = aec_trees:new_without_backend(),
    Get   = fun(Key, Pubkey, Default) -> get_account(#state{ chain_env = Env }, Pubkey, Key, Default) end,
    ATrees = lists:foldl(fun({Pubkey, #{balance := Balance}}, Acc) ->
                                 Account = aec_accounts:new(Pubkey, Balance),
                                 aec_accounts_trees:enter(Account, Acc)
                         end, aec_trees:accounts(Trees), maps:to_list(Accounts)),
    CTrees = lists:foldl(fun(Pubkey, Acc) ->
                                 Creator   = Get(creator, Pubkey, Pubkey),
                                 Contract0 = aect_contracts:new(Creator, 1, #{vm => 5, abi => 3}, <<>>, 0),
                                 Contract  = aect_contracts:set_pubkey(Pubkey, Contract0),
                                 aect_state_tree:enter_contract(Contract, Acc)
                         end, aec_trees:contracts(Trees), maps:keys(Cache)),
    aec_trees:set_contracts(aec_trees:set_accounts(Trees, ATrees), CTrees).

call_spec(#{ address := Contract, call_value := Value, gas_limit := GasLimit }, Args, Store) ->
    Fun = fun_sym(1),
    #{ contract => Contract,
       gas      => GasLimit,
       value    => Value,
       call     => aeb_fate_encoding:serialize({tuple, {Fun, {tuple, list_to_tuple(Args)}}}),
       store    => make_store(Store) }.

call_env(#{ caller      := Caller,
            origin      := Origin,
            beneficiary := Beneficiary,
            timestamp   := Time,
            difficulty  := Difficulty,
            gas_price   := GasPrice,
            height      := Height } = Env, Cache) ->
    %% tx_env is opaque lacks setters
    BeneficiaryIx = 3,
    DifficultyIx  = 8,
    TimeFieldIx   = 13,
    TxEnv        = lists:foldl(fun({Key, Val}, Acc) -> setelement(Key, Acc, Val) end,
                               aetx_env:tx_env(Height),
                               [{TimeFieldIx,  Time},
                                {DifficultyIx, Difficulty},
                                {BeneficiaryIx, Beneficiary}]),
    #{ trees     => make_trees(Env, Cache),
       caller    => Caller,
       origin    => Origin,
       gas_price => GasPrice,
       tx_env    => TxEnv }.

gas_used(#{ gas_limit := GasLimit }, ES) ->
    GasLimit - aefa_engine_state:gas(ES).

gas_per_us(Env, Time, ES) ->
    gas_used(Env, ES) / Time.

stats(Env, Time, ES) ->
    #{ gas_per_us => gas_per_us(Env, Time, ES),
       gas_used   => gas_used(Env, ES),
       time       => Time }.

run(Env0 = #{ address := Contract }, FCode, Args, Store) ->
    Spec  = call_spec(Env0, Args, Store),
    Cache = #{ Contract => FCode },
    Env   = call_env(Env0, Cache),
    erlang:garbage_collect(),
    case timer:tc(fun() -> aefa_fate:run_with_cache(Spec, Env, Cache) end) of
        {Time, {ok, ES}} ->
            Res = aefa_engine_state:accumulator(ES),
            {Res, stats(Env0, Time, ES)};
        {Time, {ErrTag, Err, ES}} when ErrTag == error; ErrTag == revert ->
            {{ErrTag, binary_to_list(Err)}, stats(Env0, Time, ES)}
    end.

%% -- Property ---------------------------------------------------------------

prop_infer() ->
    in_parallel(
    ?FORALL(V1, value_g(),
    ?LET(T1,    return(infer_type(V1)),
    ?FORALL(V2, value_g(T1),
    ?LET(T2,    return(infer_type(V2)),
    ?WHENFAIL(io:format("T1 = ~p\nT2 = ~p\n", [T1, T2]),
        not contains(void, [V1, V2, T1, T2]))))))).

prop_args_g() ->
    in_parallel(
    ?FORALL(S,   state_g(),
    ?FORALL([I], instr_args(S),
    begin
        S1 = instr_next(S, {var, -1}, [I]),
        ?IMPLIES(not contains(skip, S1),
            conjunction([{check_instr, check_instr(S, I)},
                         {no_void, not contains(void, I)},
                         {valid, check_valid_state(S1)}]))
    end))).

prop_instr() ->
    in_parallel(
    ?FORALL(ChainEnv, chain_env_g(),
    ?FORALL(Args, list(3, value_g()),
    ?FORALL(Instrs, commands(?MODULE, initial_state(ChainEnv, Args)),
    begin
        FinalState = state_after(Instrs),
        ?FORALL(RetInstrs, return_instrs(FinalState),
        ?TIMEOUT(1000,
        try
            RetValue = get_return_value(FinalState, RetInstrs),
            FCode = build_code(Instrs ++ RetInstrs),
            Store = undefined,
            BBs   = [ BB || {_, _, BBs} <- maps:values(aeb_fate_code:functions(FCode)),
                            BB <- maps:values(BBs) ],
            UsedInstrs = [ if is_atom(I) -> I; true -> element(1, I) end || BB <- BBs, I <- BB ],
            ?WHENFAIL(io:format("~s", [pp_fcode(FCode)]),
            aggregate(UsedInstrs,
            aggregate(fun check_instrs/1, UsedInstrs,
            try
                FCode1 = aeb_fate_code:deserialize(aeb_fate_code:serialize(FCode)),
                {Res, Stats} = run(ChainEnv, FCode1, Args, Store),
                ?WHENFAIL([ io:format("Deserialized fcode\n~s", [pp_fcode(FCode1)]) || FCode1 /= FCode ],
                measure(block_time, 6 / maps:get(gas_per_us, Stats),
                measure(bb_size, lists:map(fun length/1, BBs),
                collect(with_title(gas_used),   maps:get(gas_used, Stats) div 1000 * 1000,
                collect(classify(Res),
                conjunction([ {result,   check_result(Res, RetValue)},
                              {state,    check_state(FinalState)},
                              {gas_cost, check_gas_cost(Stats)} ]))))))
            catch _:Err ->
                equals(ok, {'EXIT', Err, erlang:get_stacktrace()})
            end)))
        catch _:Err ->
            equals(ok, {'EXIT', Err, erlang:get_stacktrace()})
        end))
    end)))).

get_return_value(S, {set, _, {call, ?MODULE, instr, [{'RETURN', []}]}}) ->
    get_value(S, {stack, 0});
get_return_value(S, {set, _, {call, ?MODULE, instr, [{'RETURNR', [R]}]}}) ->
    get_value(S, R);
get_return_value(S0, Instrs) ->
    {Instrs0, [Ret]} = lists:split(length(Instrs) - 1, Instrs),
    S = state_after([{model, ?MODULE}, {init, S0} | Instrs0]),
    get_return_value(S, Ret).

pp_fcode(FCode) ->
    try
        aeb_fate_asm:pp(FCode)
    catch _:_ ->
        "Bad fcode\n"
    end.

check_instrs(Data) ->
    Used = [ I || {I, _} <- Data ],
    All  = [ I || #instr{op = I} <- instructions() ],
    case All -- Used of
        []      -> true;
        Missing ->
            io:format("Unused instructions:\n  ~p\n", [Missing]),
            false
    end.

check_result(Res, void) -> equals({have, Res}, {want, void});
check_result(Val, Val)     -> true;
check_result({error, Err}, Val) ->
    ?WHENFAIL(io:format("~s\n", [Err]),
    equals({error, Err}, Val));
check_result(Have, Want) -> equals(Have, Want).

    %% case Err of
    %%     "Undefined var" ++ _ -> equals(error, Val);
    %%     "Type error" ++ _    -> equals(error, Val);
    %%     _                    -> true
    %% end);

check_state(S) ->
    ?WHENFAIL(io:format("Bad state:\n~p\nbecause", [S]),
              check_valid_state(S)).

check_valid_state(S) ->
    equals([], state_badness(S)).

valid_state(S) -> [] == state_badness(S).

state_badness(S) ->
    Check = fun(Tag, IVs) -> [ {{Tag, I}, '=', V, ':', T}
                               || {I, V} <- IVs,
                                  T      <- [infer_type(V)],
                                  contains(void, T) ] end,
    [ contains_void || contains(void, S) ] ++
    [ failed        || S#state.failed ] ++
    Check(stack, indexed(0, S#state.stack)) ++
    Check(var, maps:to_list(S#state.vars)) ++
    Check(store, maps:to_list(S#state.store)) ++
    Check(arg, maps:to_list(S#state.args)).

check_gas_cost(#{ gas_used := Gas }) when Gas < 1000 -> true;
check_gas_cost(#{ gas_used := GasUsed, time := Time, gas_per_us := GasRate }) ->
    BlockTime = 6 / GasRate,
    ?WHENFAIL(io:format("Gas used: ~p\nTime: ~.2fms\nBlockTime: ~.3fs\n", [GasUsed, Time / 1000, BlockTime]),
              BlockTime < 300.0).

classify({error, Str}) ->
    {error, hd(string:split(Str, ":"))};
classify(Val) ->
    case infer_type(Val) of
        T when is_atom(T) -> {ok, T};
        T                 -> {ok, element(1, T)}
    end.

%% -- Utility functions ------------------------------------------------------

drop(N, Xs) ->
    Len = length(Xs),
    case N >= Len of
        true  -> [];
        false -> lists:sublist(Xs, N + 1, Len)
    end.

take(N, Xs) ->
    lists:sublist(Xs, 1, N).

indexed(Xs) -> indexed(1, Xs).

indexed(I, Xs) ->
    lists:zip(lists:seq(I, length(Xs) - 1 + I), Xs).

extract_nth(N, Xs) ->
    {Ys, [X | Zs]} = lists:split(N - 1, Xs),
    {X, Ys ++ Zs}.

all(Bs) ->
    lists:all(fun(B) -> B end, Bs).

contains(X, X) -> true;
contains(X, [H | T])            -> contains(X, H) orelse contains(X, T);
contains(X, T) when is_tuple(T) -> contains(X, tuple_to_list(T));
contains(X, M) when is_map(M)   -> contains(X, maps:to_list(M));
contains(_, _)                  -> false.

substitute(X, Y, X) -> Y;
substitute(X, Y, L) when is_list(L) -> [substitute(X, Y, E) || E <- L];
substitute(X, Y, T) when is_tuple(T) ->
    list_to_tuple([ substitute(X, Y, E) || E <- tuple_to_list(T) ]);
substitute(X, Y, M) when is_map(M) ->
    maps:from_list([ {substitute(X, Y, K), substitute(X, Y, V)}
                     || {K, V} <- maps:to_list(M) ]);
substitute(_, _, X) -> X.

log8(N) -> log8(N, 1).

log8(N, Lg) when N < 256 -> Lg;
log8(N, Lg) -> log8(N div 256, Lg + 1).

%% log(a^b) = b * log(a)
pow_bytes(A, B) -> B * log8(abs(A)).

pow(A, B) when B >= 0 -> pow(A, B, 1).

pow(_, 0, R) -> R;
pow(A, B, R) ->
    R1 = if B rem 2 == 1 -> A * R;
            true         -> R
         end,
    pow(A * A, B div 2, R1).

pop_count(N) -> pop_count(N, 0).
pop_count(0, C) -> C;
pop_count(N, C) -> pop_count(N div 2, N rem 2 + C).

