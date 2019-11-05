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
            length(Format) == tuple_size(ArgTypes) + 1,
            not lists:member(Op, ['AENS_RESOLVE'])
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
     #instr{ op = 'CALL_T', args = [{in, immediate, integer}] },
     #instr{ op = 'RETURN', args = [] },
     #instr{ op = 'RETURNR', args = [{in, any, any}] },
     #instr{ op = 'CALL_R', args = [{in, immediate, integer}, {in, any, contract}, {in, any, integer}] },
     #instr{ op = 'CALL_GR', args = [{in, immediate, integer}, {in, any, contract}, {in, any, integer}, {in, any, integer}] },
     #instr{ op = 'LOG0', args = [{in, any, [string, bytes]}]},
     #instr{ op = 'LOG1', args = [{in, any, [string, bytes]}, {in, any, any}]},
     #instr{ op = 'LOG2', args = [{in, any, [string, bytes]}, {in, any, any}, {in, any, any}]},
     #instr{ op = 'LOG3', args = [{in, any, [string, bytes]}, {in, any, any}, {in, any, any}, {in, any, any}]},
     #instr{ op = 'LOG4', args = [{in, any, [string, bytes]}, {in, any, any}, {in, any, any}, {in, any, any}, {in, any, any}]},
     #instr{ op = 'AENS_RESOLVE', args = [{out, any, variant}, {in, any, string}, {in, any, string}, {in, immediate, typerep} ] }
    ].

spec_overrides() ->
    #{ 'VARIANT' =>
        [{out, any, variant},
         {in, any, {list, integer}},
         {in, any, integer},
         {in, any, integer}],
       'MAP_FROM_LIST' =>
        [{out, any, {map, not_map, any}},
         {in, any, {list, {tuple, [not_map, any]}}}],
       'VERIFY_SIG' =>
        [{out, any, boolean},
         {in, any, hash},
         {in, any, address},
         {in, any, signature}],
       'VERIFY_SIG_SECP256K1' =>
        [{out, any, boolean},
         {in, any, hash},
         {in, any, {bytes, 64}},
         {in, any, signature}],
       'ECVERIFY_SECP256K1' =>
        [{out, any, boolean},
         {in, any, hash},
         {in, any, {bytes, 20}},
         {in, any, {bytes, 65}}],
       'ECRECOVER_SECP256K1' =>
        [{out, any, variant},
         {in, any, hash},
         {in, any, {bytes, 65}}]
     }.

fix_types(#instr{ op = Op } = I) ->
    case maps:get(Op, spec_overrides(), none) of
        none -> I#instr{ args = fix_arguments(I#instr.args) };
        Args -> #instr{op = Op, args = fix_arguments(Args)}
    end.

fix_arguments(Args) ->
    [ {Dir, Mode, fix_type(T)} || {Dir, Mode, T} <- Args ].

fix_type(list)      -> {list, any};
fix_type(map)       -> {map, any, any};
fix_type(bool)      -> boolean;
fix_type(hash)      -> {bytes, 32};
fix_type(signature) -> {bytes, 64};
fix_type(T)         -> T.

black_listed('MICROBLOCK')           -> true;   %% Not implemented
black_listed('DUP')                  -> true;   %% Bugged
black_listed('GAS')                  -> true;   %% Not modelling gas costs
black_listed('INT_TO_ADDR')          -> true;
black_listed('ORACLE_REGISTER')      -> true;   %% TODO: Oracle/AENS/Crypto
black_listed('ORACLE_QUERY')         -> true;
black_listed('ORACLE_GET_ANSWER')    -> true;
black_listed('ORACLE_GET_QUESTION')  -> true;
black_listed('ORACLE_QUERY_FEE')     -> true;
black_listed('ORACLE_CHECK')         -> true;
black_listed('ORACLE_CHECK_QUERY')   -> true;
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

-type amount() :: non_neg_integer().
-type account() :: #{ balance := amount(),
                      creator := none | pubkey(),
                      store   := store() }.

-type store() :: #{ integer() => value() }.

-type chain_env() :: #{ caller     := pubkey(),
                        origin     := pubkey(),
                        address    := pubkey(),
                        accounts   := #{ pubkey() => account() },
                        timestamp  := non_neg_integer(),
                        difficulty := non_neg_integer(),
                        height     := pos_integer() }.

-record(frame, { stack = []  :: [value()],
                 vars  = #{} :: store(),
                 args  = #{} :: store() }).

-record(r_frame, { stack = []  :: [value()],
                   vars  = #{} :: store(),
                   args  = #{} :: store(),
                   contract    :: pubkey(),
                   caller      :: pubkey(),
                   call_value  :: amount() }).

-type frame() :: #frame{} | #r_frame{}.

-record(event, {contract :: pubkey(),
                payload  :: string(),
                indices  :: [integer()] }).
-type event() :: #event{}.

-record(state, { stack      = []    :: [value()],
                 vars       = #{}   :: store(),
                 store      = #{}   :: store(),
                 args       = #{}   :: store(),
                 failed     = false :: boolean() | skip,
                 events     = []    :: [event()],
                 chain_env  = #{}   :: chain_env(),
                 call_stack = []    :: [frame()] }).

-type state() :: #state{}.

-type arg()   :: aeb_fate_ops:fate_arg().
-type instr() :: {mnemonic(), [arg()]}.

-type value() :: aeb_fate_data:fate_type().

-spec arg_store([value()]) -> store().
arg_store(Args) ->
    maps:from_list(indexed(0, Args)).

-spec initial_state(chain_env()) -> state().
initial_state(ChainEnv) ->
    #state{ chain_env  = ChainEnv }.

-spec chain_env(chain_env(), atom()) -> term().
chain_env(#state{chain_env = Env}, Key) -> maps:get(Key, Env).

new_account(Creator) ->
    #{ balance => 0, creator => Creator, store => #{} }.

get_account(S, Pubkey, Field, Default) ->
    case maps:get(Pubkey, chain_env(S, accounts), not_found) of
        not_found -> Default;
        Acc       -> maps:get(Field, Acc)
    end.

get_account(S, Pubkey, Field) ->
    case get_account(S, Pubkey, Field, not_found) of
        not_found -> error({not_found, Pubkey, Field});
        Val       -> Val
    end.

get_balance(S) ->
    get_balance(S, chain_env(S, address)).

get_balance(S, Pubkey) ->
    get_account(S, Pubkey, balance, 0).

get_creator(S)    -> get_creator(S, chain_env(S, address)).
get_creator(S, A) -> get_account(S, A, creator, void).

is_contract(S, A) ->
    get_account(S, A, creator, none) /= none.

resolve_name(S, Name, Key) ->
    case maps:get(Name, chain_env(S, names), undefined) of
        #{Key := Val} -> Val;
        _             -> not_found
    end.

all_accounts(S) -> maps:keys(chain_env(S, accounts)).
all_contracts(S) ->
    [ Ct || {Ct, #{creator := Cr}} <- maps:to_list(chain_env(S, accounts)), Cr /= none ].

on_account(Pubkey, Field, Fun, S = #state{ chain_env = Env = #{ accounts := Accounts } }) ->
    Upd = fun(Acc) -> maps:update_with(Field, Fun, Acc) end,
    S#state{ chain_env = Env#{ accounts := maps:update_with(Pubkey, Upd, Upd(new_account(none)), Accounts) } }.

-spec set_store(pubkey(), store(), state()) -> state().
set_store(Pubkey, Store, S) ->
    on_account(Pubkey, store, fun(_) -> Store end, S).

-spec add_event(string(), [integer()], state()) -> state().
add_event(Payload, Indices, S) ->
    Bin = fun({bytes, B}) -> B; (B) -> B end,
    Event = #event{ contract = chain_env(S, address),
                    payload  = Bin(Payload),
                    indices  = lists:map(fun event_index_/1, Indices) },
    S#state{ events = [Event | S#state.events] }.

-spec valid_event_index(value()) -> boolean().
valid_event_index(V) ->
    case event_index(V) of
        {ok, _} -> true;
        false   -> false
    end.

event_index_(V) ->
    {ok, N} = event_index(V),
    N.

event_index(N) when is_integer(N), 0 =< N, N < 1 bsl 256 -> {ok, N};
event_index(true) -> {ok, 1};
event_index(false) -> {ok, 0};
event_index({address, <<N:256>>}) -> {ok, N};
event_index({contract, <<N:256>>}) -> {ok, N};
event_index({oracle, <<N:256>>}) -> {ok, N};
event_index({oracle_query, <<N:256>>}) -> {ok, N};
event_index({bytes, Bin}) when byte_size(Bin) =< 32 ->
    Bytes = byte_size(Bin),
    <<N:Bytes/unit:8>> = Bin,
    {ok, N};
event_index({bits, N}) -> event_index(N);
event_index(_) -> false.

valid_aens_name_char($-) -> true;
valid_aens_name_char(C) ->
    lists:any(fun({A, B}) -> A =< C andalso C =< B end,
              [{$0, $9}, {$a, $z}, {$A, $Z}]).

valid_aens_name_part(<<>>) -> false;
valid_aens_name_part(<<_, _, "--", _/binary>>) -> false;
valid_aens_name_part(Name) ->
    Chars = binary_to_list(Name),
    lists:all(fun valid_aens_name_char/1, Chars) andalso
    hd(Chars) /= $- andalso lists:last(Chars) /= $-.

valid_aens_name(Name) when is_binary(Name) ->
    case binary:split(Name, <<".">>) of
        [Part, Ext] ->
            valid_aens_name_part(Part) andalso
            lists:member(Ext, [<<"chain">>, <<"test">>]);
        _ -> false
    end;
valid_aens_name(_) -> false.

push_call(S, N) -> push_call_stack(S, false, N).
push_tailcall(S, N) -> push_call_stack(S, true, N).

-spec push_remote_call(state(), pubkey(), amount(), non_neg_integer()) -> state().
push_remote_call(S, Addr, Value, N) ->
    {FunArgs, Stack1} = lists:split(N, S#state.stack),
    Frame = #r_frame{ stack      = Stack1,
                      vars       = S#state.vars,
                      args       = S#state.args,
                      contract   = chain_env(S, address),
                      caller     = chain_env(S, caller),
                      call_value = chain_env(S, call_value) },
    Caller = chain_env(S, address),
    spend(Caller, Addr, Value,
    set_store(Caller, S#state.store,
    S#state{ stack      = [],
             vars       = #{},
             args       = arg_store(FunArgs),
             store      = get_account(S, Addr, store, #{}),
             chain_env  = (S#state.chain_env)#{ caller     => Caller,
                                                address    => Addr,
                                                call_value => Value },
             call_stack = [Frame | S#state.call_stack] })).

push_call_stack(S, TailCall, N) ->
    {FunArgs, Stack1} = lists:split(N, S#state.stack),
    Frame = #frame{ stack = Stack1, vars = S#state.vars, args = S#state.args },
    S#state{ stack      = [],
             vars       = #{},
             args       = arg_store(FunArgs),
             call_stack = [Frame || not TailCall] ++ S#state.call_stack }.

pop_call_stack(S = #state{ call_stack = [Frame | CallStack] }, V) ->
    case Frame of
        #frame{stack = Stack, args = Args, vars = Vars} ->
            S#state{ stack      = [V | Stack],
                     args       = Args,
                     vars       = Vars,
                     call_stack = CallStack };
        #r_frame{ stack      = Stack,
                  vars       = Vars,
                  args       = Args,
                  contract   = Contract,
                  caller     = Caller,
                  call_value = CallValue } ->
            set_store(chain_env(S, address), S#state.store,
            S#state{ stack      = [V | Stack],
                     vars       = Vars,
                     args       = Args,
                     store      = if Contract == undefined -> #{};
                                     true                  -> get_account(S, Contract, store) end,
                     call_stack = CallStack,
                     chain_env  = (S#state.chain_env)#{ caller     => Caller,
                                                        address    => Contract,
                                                        call_value => CallValue } })
    end.

remote_call_stack(S) ->
    [chain_env(S, address) | [ Contract || #r_frame{ contract = Contract } <- S#state.call_stack ]].

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

typerep(T) -> {typerep, substitute(not_map, any, T)}.

is_variant({variant, _, _, _}) -> true;
is_variant(_) -> false.

is_variant({variant, Ar, _, _}, N) -> length(Ar) == N;
is_variant(_, _) -> false.

%% Check that an instruction can be executed in the given state.
-spec check_instr(state(), instr()) -> boolean().
check_instr(_, {'AENS_RESOLVE', _}) -> true;
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
    has_type(get_value(S, Arg), Type) andalso
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

-spec match_type(Need :: type() | [type()], Have :: type()) -> boolean().
match_type(Ts, T) when is_list(Ts)           -> lists:any(fun(S) -> match_type(S, T) end, Ts);
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

%% Would really want this to be a generator, but we compute the type at code
%% generation time, where it's too late to do random generation.
-spec make_polymorphic({[type()], type()}) -> {[type()], type()}.
make_polymorphic({ArgTypes, RetType}) ->
    Candidates = [ T || {T, N} <- maps:to_list(subtypes1([RetType | ArgTypes], #{})),
                        T /= any, N >= 2 ],
    %% Arbitrary: generalize over all but the first repeated type
    Sub = case Candidates of
            [_ | ToGen] -> maps:from_list([{T, {tvar, I}} || {I, T} <- indexed(0, ToGen)]);
            [] -> #{}
          end,
    {[substitute_type(Sub, Arg) || Arg <- ArgTypes],
     substitute_type(Sub, RetType)}.

add_subtype(T, Types) ->
    maps:update_with(T, fun(N) -> N + 1 end, 1, Types).

subtypes(T, Acc) ->
    subtypes1(T, add_subtype(T, Acc)).

subtypes1([], Acc)                -> Acc;
subtypes1([H | T], Acc)           -> subtypes(H, subtypes1(T, Acc));
subtypes1(T, Acc) when is_atom(T) -> Acc;
subtypes1({bytes, _}, Acc)        -> Acc;
subtypes1({list, T}, Acc)         -> subtypes(T, Acc);
subtypes1({tuple, Ts}, Acc)       -> subtypes1(Ts, Acc);
subtypes1({variant, Cs}, Acc)     -> lists:foldl(fun subtypes1/2, Acc, Cs);  %% not subtypes/2
subtypes1({map, K, V}, Acc)       -> subtypes(K, subtypes(V, Acc)).

substitute_type(Sub, T) when Sub == #{} -> T;
substitute_type(Sub, T) ->
    case maps:get(T, Sub, not_found) of
        not_found -> substitute_type1(Sub, T);
        NewT      -> NewT
    end.
substitute_type1(_, T) when is_atom(T) -> T;
substitute_type1(_, T = {bytes, _})    -> T;
substitute_type1(Sub, {list, T})       -> {list, substitute_type1(Sub, T)};
substitute_type1(Sub, {tuple, Ts})     -> {tuple, [substitute_type(Sub, T) || T <- Ts]};
substitute_type1(Sub, {map, K, V})     -> {map, substitute_type(Sub, K), substitute_type(Sub, V)};
substitute_type1(Sub, {variant, Cs})   -> {variant, [substitute_type1(Sub, C) || C <- Cs]}.

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
-define(MinGasCap, 3000000).    %% Don't want to run out of gas

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
eval_instr('VERIFY_SIG', _)                        -> false;
eval_instr('VERIFY_SIG_SECP256K1', _)              -> false;
eval_instr('ECVERIFY_SECP256K1', _)                -> false;
eval_instr('ECRECOVER_SECP256K1', [{bytes, Hash}, {bytes, Sig}]) ->
    case ecrecover:recover(Hash, Sig) of
        <<0:256>>                       -> {variant, [0, 1], 0, {}};
        <<_:12/binary, Addr:20/binary>> -> {variant, [0, 1], 1, {{bytes, Addr}}}
    end;
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
eval_instr(S, 'IS_CONTRACT', [{address, A}]) -> {S, [is_contract(S, A)]};
eval_instr(S, 'BENEFICIARY', []) -> {S, [{address, chain_env(S, beneficiary)}]};
eval_instr(S, 'GASLIMIT', [])    -> {S, [?MaxBlockGas]};
eval_instr(S, 'GASPRICE', [])    -> {S, [chain_env(S, gas_price)]};
eval_instr(S, 'CREATOR', [])     -> {S, [{address, get_creator(S)}]};
eval_instr(S, 'GENERATION', [])  -> {S, [chain_env(S, height)]};
eval_instr(S, 'DIFFICULTY', [])  -> {S, [chain_env(S, difficulty)]};
eval_instr(S, 'TIMESTAMP', [])   -> {S, [chain_env(S, timestamp)]};
eval_instr(S, 'CALL_VALUE', [])  -> {S, [chain_env(S, call_value)]};
eval_instr(S, 'ORIGIN', [])      -> {S, [{address, chain_env(S, origin)}]};
eval_instr(S, 'CALLER', [])      -> {S, [{address, chain_env(S, caller)}]};
eval_instr(S, 'ADDRESS', [])     -> {S, [{address, chain_env(S, address)}]};
eval_instr(S, 'BALANCE', [])     -> {S, [get_balance(S)]};
eval_instr(S, 'BALANCE_OTHER', [{address, A}]) -> {S, [get_balance(S, A)]};
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
    Balance = get_balance(S, Self),
    ?WhenS(0 =< Amount andalso Amount =< Balance,
           spend(Self, A, Amount, S), []);
eval_instr(S, 'JUMP', []) -> {S, []};
eval_instr(S, 'JUMPIF', [V]) ->
    ?WhenS(lists:member(V, [true, false]), S, []);
eval_instr(S, 'SWITCH_V2', [V]) -> ?WhenS(is_variant(V, 2), S, []);
eval_instr(S, 'SWITCH_V3', [V]) -> ?WhenS(is_variant(V, 3), S, []);
eval_instr(S, 'SWITCH_VN', [V]) -> ?WhenS(is_variant(V), S, []);
eval_instr(S = #state{ stack = Stack }, 'CALL', [N]) ->
    ?WhenS(length(Stack) >= N, push_call(S, N), []);
eval_instr(S = #state{ stack = Stack }, 'CALL_T', [N]) ->
    ?WhenS(length(Stack) >= N, push_tailcall(S, N), []);
eval_instr(S = #state{ stack = Stack }, CALL_R, [N, {contract , Remote}, Value | Rest]) when CALL_R == 'CALL_R'; CALL_R == 'CALL_GR' ->
    CapOk = case Rest of [] -> true; [Cap] -> Cap > ?MinGasCap end,
    ?WhenS(length(Stack) >= N andalso
           get_balance(S) >= Value andalso
           is_contract(S, Remote) andalso
           CapOk andalso
           not lists:member(Remote, remote_call_stack(S)),
        push_remote_call(S, Remote, Value, N), []);
eval_instr(S = #state{ stack = [V | Stack] }, 'RETURN', []) ->
    ?WhenS(S#state.call_stack /= [],
           pop_call_stack(S#state{ stack = Stack }, V), []);
eval_instr(S, 'RETURN', []) -> ?WhenS(false, S, []);
eval_instr(S, 'RETURNR', [V]) ->
    ?WhenS(S#state.call_stack /= [],
           pop_call_stack(S, V), []);
eval_instr(S, LOG, [Payload | Indices]) when LOG == 'LOG0'; LOG == 'LOG1';
                                             LOG == 'LOG2'; LOG == 'LOG3'; LOG == 'LOG4' ->
    ?WhenS(not lists:member(Payload, [<<>>, {bytes, <<>>}]) andalso   %% BUG: empty payload crashes VM
           lists:all(fun valid_event_index/1, Indices),
           add_event(Payload, Indices, S), []);
eval_instr(S, 'AENS_RESOLVE', [Name, Key, {typerep, Type}]) ->
    None = {variant, [0, 1], 0, {}},
    Some = fun(X) -> {variant, [0, 1], 1, {X}} end,
    ?WhenS(valid_aens_name(Name), S,
    case resolve_name(S, Name, Key) of
        not_found -> [None];
        Val -> case has_type(Val, Type) of
                   true  -> [Some(Val)];
                   false -> [None]
               end
    end);
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
args_g(S, Call, _) when Call == 'CALL'; Call == 'CALL_T' ->
    args_g(S, [?constrained([], choose(0, length(S#state.stack)),
                            _, false)]);
args_g(S, CALL_R, _) when CALL_R == 'CALL_R'; CALL_R == 'CALL_GR' ->
    Balance = get_balance(S),
    StackH  = length(S#state.stack),
    args_g(S, [?constrained(_, choose(0, StackH), _, false),
               ?constrained(_, {contract, elements(all_contracts(S))},
                            V, case V of {contract, R} -> is_contract(S, R) andalso not lists:member(R, remote_call_stack(S));
                                         _ -> false end),
               ?constrained(_, weighted_default({3, 0}, {1, choose(0, Balance)}),
                            Value, 0 =< Value andalso Value =< Balance)] ++
              [?constrained(_, choose(?MinGasCap, ?MaxBlockGas),
                            V, ?MinGasCap =< V andalso V =< ?MaxBlockGas)
               || CALL_R == 'CALL_GR' ]);
args_g(S, LOG, _) when LOG == 'LOG1'; LOG == 'LOG2'; LOG == 'LOG3'; LOG == 'LOG4' ->
    Ar = case LOG of 'LOG1' -> 1; 'LOG2' -> 2; 'LOG3' -> 3; 'LOG4' -> 4 end,
    args_g(S, [{in, any, [string, bytes]}] ++
              lists:duplicate(Ar,
                ?constrained(_, event_index_g(),
                             V, valid_event_index(V))));
args_g(S, 'AENS_RESOLVE', _) ->
    args_g(S, [{out, any, variant},
               ?constrained(_, aens_name_g(S),
                            V, lists:member(V, maps:keys(chain_env(S, names)))),
               ?constrained([Name], aens_key_g(S, Name),
                            Key, not_found /= resolve_name(S, Name, Key)),
               ?constrained([Name, Key], {typerep, aens_key_type_g(S, Name, Key)},
                            _, false) ]);
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

value_g(Types) when is_list(Types) ->
    ?LET(Type, elements(Types), value_g(Type));
value_g(Type) ->
    ?LET(Type1, instantiate_any(Type), value1_g(Type1)).

value1_g(nat)          -> nat();
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
value1_g(string)       -> oneof([eqc_gen:fmap(fun list_to_binary/1, list(choose($!, $~))),
                                 aens_name_key_g(),
                                 aens_name_part_g(),
                                 aens_name_g()]);
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
value1_g(void)         -> void.

event_index_g()   ->
    ?SUCHTHAT(V, value_g([nat, boolean, address, bits, bytes, contract, oracle, oracle_query]),
              valid_event_index(V)).

aens_name_char_g() ->
    oneof([choose($A, $Z), choose($a, $z), choose($0, $9), $-]).

fixed_aens_names() ->
    [<<"aeternity">>,
     <<"google">>,
     <<"coca-cola">>,
     <<"twitter-analytics-marketing-department">>].

aens_name_part_g() ->
    weighted_default({3, elements(fixed_aens_names())},
                     {1, ?SUCHTHAT(Name,
                            eqc_gen:fmap(fun list_to_binary/1, non_empty(list(aens_name_char_g()))),
                            valid_aens_name_part(Name))}).

fixed_aens_keys() ->
    [<<"address">>, <<"reply-to">>, <<"redirect">>].

aens_name_key_g() ->
    weighted_default({3, elements(fixed_aens_keys())},
                     {1, value_g(string)}).

prop_name() ->
    ?FORALL(Name, aens_name_part_g(),
            valid_aens_name_part(Name)).

aens_name_g() ->
    ?LET({S, Ext}, {aens_name_part_g(), elements([<<"test">>, <<"chain">>])},
         <<S/binary, ".", Ext/binary>>).

aens_name_g(S) ->
    Names = maps:keys(chain_env(S, names)),
    oneof(Names ++ [aens_name_g()]).

aens_key_g(S, Name) ->
    case maps:get(Name, chain_env(S, names), not_found) of
        not_found -> value_g(string);
        Pointers  ->
            Keys = maps:keys(maps:remove(owner, Pointers)),
            frequency([{9, elements(Keys)} || Keys /= []] ++
                      [{1, value_g(string)}])
    end.

aens_key_type_g(S, Name, Key) ->
    case resolve_name(S, Name, Key) of
        not_found -> elements([address, contract, oracle]);
        Val       -> infer_type(Val)
    end.

timestamp_g() -> choose(1550000000000, 1900000000000).

balance_g() ->
    oneof([0, choose(0, 1000000)]).

-define(NumAccounts,  5).
-define(NumContracts, 5).

name_pointers_g() ->
    eqc_gen:fmap(fun maps:from_list/1,
                 list({aens_name_key_g(), value_g([address, contract, oracle])})).

name_g(Accounts) ->
    ?LET({Name, Owner, Pointers}, {aens_name_g(), elements(Accounts), name_pointers_g()},
         {Name, Pointers#{owner => Owner}}).

names_g(Accounts) ->
    eqc_gen:fmap(fun maps:from_list/1, list(name_g(Accounts))).

chain_env_g() ->
    ?LET({Accounts, Contracts}, {vector(?NumAccounts, pubkey_g()), vector(?NumContracts, pubkey_g())},
    begin
        GenAccount = noshrink(elements(Accounts ++ Contracts)),
        ?LET(Creators, maps:from_list([ {C, GenAccount} || C <- Contracts ]),
        ?LET(Beneficiary, GenAccount,
        ?LET(Names, names_g(Accounts ++ Contracts),
        begin
            Acct = fun(C) -> {C, #{ balance => balance_g(), creator => maps:get(C, Creators, none), store => #{} }} end,
            #{ timestamp   => timestamp_g(),
               beneficiary => Beneficiary,
               gas_limit   => choose(3000000, 6000000),
               gas_price   => choose(1, 5),
               height      => choose(1, 10000),
               difficulty  => choose(0, 1000),
               names       => Names,
               accounts    => eqc_gen:fmap(fun maps:from_list/1, lists:map(Acct, Accounts ++ Contracts)) }
        end)))
    end).

state_g() ->
    StoreGen = map(nat(), value_g()),
    ?LET({ChainEnv, Stack, Vars, Store, Args}, {chain_env_g(), list(value_g()), StoreGen, StoreGen, StoreGen},
         return(#state{ stack = Stack, vars = Vars, store = Store, args = Args, chain_env = ChainEnv })).

%% -- State machine ----------------------------------------------------------

instr_weight(S, Op) when Op == 'INCA'; Op == 'DECA' ->
    case S#state.stack of
        [N | _] when is_integer(N) -> 5;
        _ -> 0
    end;
instr_weight(S, 'RETURN') -> if S#state.stack /= [] -> 15; true -> 0 end;
instr_weight(_, 'RETURNR') -> 15;
instr_weight(_, 'ECRECOVER_SECP256K1') -> 1;
instr_weight(_, 'ECVERIFY_SECP256K1') -> 1;
instr_weight(_, 'VERIFY_SIG_SECP256K1') -> 1;
instr_weight(_, 'VERIFY_SIG') -> 1;
instr_weight(_, _) -> 5.

instr_args(S) ->
    ?LET(#instr{ op = Op, args = ArgsSpec }, frequency([ {instr_weight(S, I#instr.op), I}
                                                         || I <- maps:values(instruction_spec()) ]),
         [{Op, args_g(S, Op, ArgsSpec)}]).

instr_pre(S) -> S#state.call_stack /= [].

instr_pre(S, [I]) ->
    S#state.call_stack /= [] andalso
    not contains(void, I) andalso
    check_instr(S, I) andalso
    begin
        S1 = instr_next(S, {var, -1}, [I]),
        not contains(skip, S1) andalso
        valid_state(S1#state{ failed = false })
    end.

instr_next(S, _, [I]) ->
    S1 = step_instr(S, I),
    case contains(void, S1) of
        true  -> S1#state{ failed = true };
        false -> S1
    end.

new_call_pre(S) -> S#state.call_stack == [].

new_call_args(S) ->
    [elements(all_accounts(S)),
     elements(all_contracts(S)),
     balance_g(),
     list(5, value_g())].

new_call_next(S, _, [Caller, Contract, Value, Args]) ->
    S#state{ stack      = [],
             vars       = #{},
             store      = get_account(S, Contract, store, #{}),
             args       = arg_store(Args),
             call_stack = [#r_frame{}],
             chain_env  = (S#state.chain_env)
                          #{ caller     => Caller,
                             origin     => Caller,
                             address    => Contract,
                             call_value => Value } }.

return_instrs(#state{ call_stack = [] }) -> [];
return_instrs(S) ->
    ?LET(Cmd, return_instr(S),
        [Cmd | return_instrs(pop_call_stack(S, get_return_value(S, Cmd)))]).

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

-type bb()         :: list().
-type fate_instr() :: aeb_fate_ops:fate_code().

-record(code_fr, { ref          :: reference(),
                   instrs       :: [fate_instr()],
                   bbs          :: [{reference(), bb()}],
                   extra_bbs    :: [{reference(), bb()}],
                   current_fun  :: string(),
                   arg_types    :: [type()],
                   tail_call    :: boolean() }).

-record(call, { caller   :: pubkey(),
                contract :: pubkey(),
                function :: string(),
                value    :: amount(),
                args     :: [value()],
                result = void :: value() }).

-record(code_st, { ref   :: reference(),
                   prev_state :: #state{},
                   state :: #state{},
                   instrs     = [],
                   bbs        = [],
                   extra_bbs  = [],
                   current_fun,
                   fun_ix     = 1,
                   arg_types  = [],
                   code       = #{} :: #{ pubkey() => aeb_fate_code:fcode() },
                   calls      = [] :: [#call{}],
                   call_stack = [] :: [#code_fr{}] }).

init_code_st(InitS, ArgTypes) ->
    #code_st{ state       = InitS,
              ref         = make_ref(),
              arg_types   = ArgTypes,
              current_fun = fun_name(1),
              code        = #{} }.

on_fcode(Pubkey, Fun, CS) ->
    CS#code_st{ code = maps:update_with(Pubkey, Fun, Fun(aeb_fate_code:new()), CS#code_st.code) }.

fun_name(Fn) -> list_to_binary(lists:concat(["fun_", Fn])).
fun_sym(Fn)  -> aeb_fate_code:symbol_identifier(fun_name(Fn)).

-spec finalize_bbs(#code_st{}) -> #{non_neg_integer() => bb()}.
finalize_bbs(#code_st{ ref = Ref,  instrs = Acc,
                       bbs = BBsR, extra_bbs = ExtraBBsR }) ->
    BBs      = lists:reverse([{Ref, Acc} | BBsR]),
    ExtraBBs = lists:reverse(ExtraBBsR),
    AllBBs   = [ BB || BB = {_, [_ | _]} <- BBs ++ ExtraBBs ],
    Lbls     = maps:from_list([ {R, Lbl} || {Lbl, {R, _}} <- indexed(0, AllBBs) ]),
    Lbl      = fun(R) -> maps:get(R, Lbls) end,
    LblIm    = fun(R) -> {immediate, Lbl(R)} end,
    UpdI     = fun({'JUMP', R})                    -> {'JUMP', LblIm(R)};
                  ({'JUMPIF', Arg, R})             -> {'JUMPIF', Arg, LblIm(R)};
                  ({'SWITCH_V2', Arg, R1, R2})     -> {'SWITCH_V2', Arg, LblIm(R1), LblIm(R2)};
                  ({'SWITCH_V3', Arg, R1, R2, R3}) -> {'SWITCH_V3', Arg, LblIm(R1), LblIm(R2), LblIm(R3)};
                  ({'SWITCH_VN', Arg, Rs})         -> {'SWITCH_VN', Arg, {immediate, lists:map(Lbl, Rs)}};
                  (I)                              -> I end,
    UpdIs    = fun([I | Is]) -> lists:reverse([UpdI(I) | Is]) end,

    maps:from_list([{Lbl(R), UpdIs(Is)} || {R, Is} <- AllBBs]).

push_code(CS, TailCall, Fun, Args) ->
    Frame = #code_fr{ ref         = CS#code_st.ref,
                      instrs      = CS#code_st.instrs,
                      bbs         = CS#code_st.bbs,
                      extra_bbs   = CS#code_st.extra_bbs,
                      current_fun = CS#code_st.current_fun,
                      arg_types   = CS#code_st.arg_types,
                      tail_call   = TailCall },
    CS#code_st{ current_fun = Fun,
                ref         = make_ref(),
                instrs      = [],
                bbs         = [],
                extra_bbs   = [],
                arg_types   = lists:map(fun infer_type/1, Args),
                call_stack  = [Frame | CS#code_st.call_stack] }.

set_call_result(#code_st{ calls = [Call | Calls] } = S, V) ->
    S#code_st{ calls = [Call#call{ result = V } | Calls] }.

-define(RetTypePlaceHolder, place_holder).

update_result_type(#code_st{ bbs = [{Ref, [Call | Rest]} | BBs] } = S, Type) ->
    RetType = {immediate, typerep(Type)},
    NewCall =
        case Call of
            {'CALL_R', Remote, Fun, ArgTypes, ?RetTypePlaceHolder, Value} ->
                {'CALL_R', Remote, Fun, ArgTypes, RetType, Value};
            {'CALL_GR', Remote, Fun, ArgTypes, ?RetTypePlaceHolder, Value, GasCap} ->
                {'CALL_GR', Remote, Fun, ArgTypes, RetType, Value, GasCap};
            {'CALL', _} -> Call
        end,
    S#code_st{ bbs = [{Ref, [NewCall | Rest]} | BBs] }.

pop_code(#code_st{ prev_state  = S,
                   current_fun = Fun,
                   arg_types   = ArgTypes } = CS, V, RetType) ->
    TypeSpec = make_polymorphic(substitute(not_map, any, {ArgTypes, RetType})),
    BBs      = finalize_bbs(CS),
    CS1      = on_fcode(chain_env(S, address),
                        fun(FCode) -> aeb_fate_code:insert_fun(Fun, [payable], TypeSpec, BBs, FCode) end, CS),
    [Frame = #code_fr{} | CallStack] = CS#code_st.call_stack,
    CS2 = CS1#code_st{ ref         = Frame#code_fr.ref,
                       current_fun = Frame#code_fr.current_fun,
                       instrs      = Frame#code_fr.instrs,
                       bbs         = Frame#code_fr.bbs,
                       extra_bbs   = Frame#code_fr.extra_bbs,
                       arg_types   = Frame#code_fr.arg_types,
                       call_stack  = CallStack },
    case Frame#code_fr.tail_call of
        false ->
            case CallStack == [] of %% top-call?
                true  -> set_call_result(CS2, V);
                false -> update_result_type(CS2, RetType)
            end;
        true  -> pop_code(CS2, V, RetType)
    end.

do_return_instr(#code_st{ instrs = Is } = CS, I, V) ->
    RetType = infer_type(V),
    pop_code(CS#code_st{ instrs = [I | Is] }, V, RetType).

do_call_instr(CS = #code_st{ ref = Ref, prev_state = S, instrs = Acc, bbs = BBs }, CALL, N, Args) ->
    FunArgs = take(N, S#state.stack),
    Ix      = CS#code_st.fun_ix,
    FunName = fun_name(Ix),
    FunSym  = {immediate, aeb_fate_code:symbol_identifier(FunName)},
    Ref1    = make_ref(),
    Instr   =
        case CALL of
            'CALL' -> {CALL, FunSym};
            'CALL_T' -> {CALL, FunSym};
            _ ->
                ArgTypes = typerep(infer_type({tuple, list_to_tuple(FunArgs)})),
                RetType  = ?RetTypePlaceHolder, %% Filled in on return
                [Remote | Rest] = Args,
                list_to_tuple([CALL, Remote, FunSym, {immediate, ArgTypes}, RetType | Rest])
        end,
    BBs1    = [{Ref, [Instr | Acc]} | BBs],
    CS1     = CS#code_st{ ref = Ref1, instrs = [], bbs = BBs1, fun_ix = Ix + 1 },
    push_code(CS1, CALL == 'CALL_T', FunName, FunArgs).

build_fcode(#code_st{ calls = Calls, code = Code }, []) -> {lists:reverse(Calls), Code};
build_fcode(CS, [{set, X, Call = {call, ?MODULE, new_call, [Caller, Contract, Value, Args]}} | Instrs]) ->
    #code_st{ state = S, calls = Calls, fun_ix = FunIx } = CS,
    Fun = fun_name(FunIx),
    CS1 = CS#code_st{ prev_state = S,
                      state      = next_state(S, X, Call),
                      fun_ix     = FunIx + 1,
                      calls =
                        [#call{ caller   = Caller,
                                contract = Contract,
                                function = fun_name(FunIx),
                                value    = Value,
                                args     = Args } | Calls] },
    build_fcode(push_code(CS1, false, Fun, Args), Instrs);
build_fcode(CS, [{set, X, Call = {call, ?MODULE, instr, Args}} | Instrs]) ->
    #code_st{ state = S, ref = Ref, instrs = Acc, bbs = BBs, extra_bbs = ExtraBBs } = CS,
    CS1    = CS#code_st{ prev_state = S,
                         state      = next_state(S, X, Call) },
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
        {CALL, {immediate, N}} when CALL == 'CALL'; CALL == 'CALL_T' ->
            build_fcode(do_call_instr(CS1, CALL, N, []), Instrs);
        {'CALL_R', {immediate, N}, Remote, Value} ->
            build_fcode(do_call_instr(CS1, 'CALL_R', N, [Remote, Value]), Instrs);
        {'CALL_GR', {immediate, N}, Remote, Value, GasCap} ->
            build_fcode(do_call_instr(CS1, 'CALL_GR', N, [Remote, Value, GasCap]), Instrs);
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
        {'AENS_RESOLVE', Dst, Name, Key, {immediate, {typerep, Type}}} ->
            I1 = {'AENS_RESOLVE', Dst, Name, Key, {immediate, typerep({variant, [{tuple, []}, {tuple, [Type]}]})}},
            build_fcode(CS1#code_st{ instrs = [I1 | Acc] }, Instrs);
        _ -> build_fcode(CS1#code_st{ instrs = [I | Acc] }, Instrs)
    end.

make_store(undefined) -> aefa_stores:initial_contract_store();
make_store(Store)     -> Store.

make_trees(Cache, #{ accounts := Accounts, names := Names }) ->
    %% All contracts and the caller must have accounts
    Trees = aec_trees:new_without_backend(),
    ATrees = lists:foldl(fun({Pubkey, #{balance := Balance}}, Acc) ->
                                 Account = aec_accounts:new(Pubkey, Balance),
                                 aec_accounts_trees:enter(Account, Acc)
                         end, aec_trees:accounts(Trees), maps:to_list(Accounts)),
    CTrees = maps:fold(fun(_,      #{ creator := none    }, Acc) -> Acc;
                          (Pubkey, #{ creator := Creator }, Acc) ->
                                 Code      = maps:get(Pubkey, Cache, <<>>),
                                 Contract0 = aect_contracts:new(Creator, 1, #{vm => 5, abi => 3}, Code, 0),
                                 Contract  = aect_contracts:set_state(aefa_stores:initial_contract_store(),
                                             aect_contracts:set_pubkey(Pubkey, Contract0)),
                                 aect_state_tree:insert_contract(Contract, Acc)
                         end, aec_trees:contracts(Trees), Accounts),
    NTrees = maps:fold(fun(NameStr, #{owner := Owner} = Pointers0, Acc) ->
                                TTL  = 100,
                                Pointers = [ begin
                                                 Enc = case Val of
                                                           {address, A}  -> aeser_id:create(account, A);
                                                           {contract, A} -> aeser_id:create(contract, A);
                                                           {oracle, A}   -> aeser_id:create(oracle, A)
                                                       end,
                                                 aens_pointer:new(Key, Enc)
                                             end || {Key, Val} <- maps:to_list(Pointers0),
                                                    Key /= owner ],
                                {ok, NameStr1} = aens_utils:to_ascii(NameStr),
                                NameHash = aens_hash:name_hash(NameStr1),
                                Name0 = aens_names:new(NameHash, Owner, TTL),
                                Name  = aens_names:update(Name0, 1000, 1000, Pointers),
                                aens_state_tree:enter_name(Name, Acc)
                       end, aec_trees:ns(Trees), Names),
    aec_trees:set_contracts(
        aec_trees:set_accounts(aec_trees:set_ns(Trees, NTrees),
                               ATrees),
        aect_state_tree:commit_to_db(CTrees)).

call_spec(#{ address := Contract, call_value := Value, gas_limit := GasLimit }, Code, Function, Args, Store) ->
    Fun = aeb_fate_code:symbol_identifier(Function),
    #{ contract => Contract,
       gas      => GasLimit,
       code     => Code,
       value    => Value,
       call     => aeb_fate_encoding:serialize({tuple, {Fun, {tuple, list_to_tuple(Args)}}}),
       store    => make_store(Store) }.

call_env(#{ caller      := Caller,
            origin      := Origin,
            beneficiary := Beneficiary,
            timestamp   := Time,
            difficulty  := Difficulty,
            gas_price   := GasPrice,
            height      := Height }, Trees) ->
    %% tx_env is opaque lacks setters
    BeneficiaryIx = 3,
    DifficultyIx  = 8,
    TimeFieldIx   = 13,
    TxEnv        = lists:foldl(fun({Key, Val}, Acc) -> setelement(Key, Acc, Val) end,
                               aetx_env:tx_env(Height),
                               [{TimeFieldIx,  Time},
                                {DifficultyIx, Difficulty},
                                {BeneficiaryIx, Beneficiary}]),
    #{ trees     => Trees,
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

add_stats(#{ gas_used   := GasUsed1,
             time       := Time1 },
          #{ gas_used   := GasUsed2,
             time       := Time2 }) ->
    GasUsed = GasUsed1 + GasUsed2,
    Time    = Time1 + Time2,
    #{ gas_per_us => GasUsed / Time,
       gas_used   => GasUsed,
       time       => Time }.

run1(Env0 = #{ address := Pubkey }, Cache, Function, Args, Trees) ->
    {value, Contract} = aect_state_tree:lookup_contract(Pubkey, aec_trees:contracts(Trees)),
    Store = aect_contracts:state(Contract),
    #{ byte_code := Code } = aect_sophia:deserialize(maps:get(Pubkey, Cache)),
    Spec  = call_spec(Env0, Code, Function, Args, Store),
    Env   = call_env(Env0, Trees),
    case timer:tc(fun() -> aefa_fate:run(Spec, Env) end) of
        {Time, {ok, ES}} ->
            Res    = aefa_engine_state:accumulator(ES),
            Events = aefa_engine_state:logs(ES),
            Trees1 = aefa_fate:final_trees(ES),
            {Res, lists:reverse(Events), Trees1, stats(Env0, Time, ES)};
        {Time, {ErrTag, Err, ES}} when ErrTag == error; ErrTag == revert ->
            {{ErrTag, binary_to_list(Err)}, stats(Env0, Time, ES)}
    end.

run(Env, Cache, Calls) ->
    run(Env, Cache, Calls, make_trees(Cache, Env), #{ gas_per_us => 0.001, gas_used => 0, time => 0 }, [], []).

run(_, _, [], _, Stats, Events, Acc) ->
    {lists:reverse(Acc), lists:append(lists:reverse(Events)), Stats};
run(Env0, Cache, [Call | Calls], Trees, Stats, Events, Acc) ->
    Env = Env0#{ caller     => Call#call.caller,
                 origin     => Call#call.caller,
                 address    => Call#call.contract,
                 call_value => Call#call.value },
    {Res, Events1, Trees1, Stats1} = run1(Env, Cache, Call#call.function, Call#call.args, Trees),
    run(Env0, Cache, Calls, Trees1, add_stats(Stats, Stats1), [Events1 | Events], [Res | Acc]).

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
    ?FORALL(Op, elements(maps:keys(instruction_spec())),
            prop_args_g(Op))).

prop_args_g(Op) ->
    #instr{op = Op, args = ArgsSpec } = instruction_spec(Op),
    StoreGen = map(nat(), value_g()),
    ?FORALL(ChainEnv, chain_env_g(),
    ?LET(S0, return(initial_state(ChainEnv)),
    ?FORALL(CallArgs, new_call_args(S0),
    ?FORALL({Stack, Vars, Store, Args}, {list(value_g()), StoreGen, StoreGen, StoreGen},
    begin
        S  = (new_call_next(S0, {var, 0}, CallArgs))
                #state{ stack = Stack,
                        vars  = Vars,
                        store = Store,
                        args  = Args },
        ?FORALL(OpArgs, args_g(S, Op, ArgsSpec),
        ?IMPLIES(not contains(skip, OpArgs),
        begin
            I  = {Op, OpArgs},
            S1 = instr_next(S, {var, 0}, [I]),
            ?IMPLIES(not contains(skip, S1),
            ?WHENFAIL(io:format("Op = ~s\nArgs = ~p\ncheck_instr = ~p\n",
                                [Op, [get_value(S, Arg) || Arg <- OpArgs], check_instr(S, I)]),
                instr_pre(S, [I])))
        end))
    end)))).


prop_instr() ->
    in_parallel(
    ?LET(Verbose, parameter(verbose, false),
    ?FORALL(ChainEnv, chain_env_g(),
    ?FORALL(Instrs, more_commands(20, commands(?MODULE, initial_state(ChainEnv))),
    begin
        FinalState0 = state_after(Instrs),
        ?FORALL(RetInstrs, return_instrs(FinalState0),
        ?WHENFAIL([ print_states(Instrs ++ RetInstrs) || Verbose ],
        try
            FinalState    = state_after([{model, ?MODULE}, {init, FinalState0} | RetInstrs]),
            {Calls, Code} = build_code(Instrs ++ RetInstrs),
            RetValues     = [Call#call.result || Call <- Calls],
            BBs   = [ BB || FCode <- maps:values(Code),
                            {_, _, BBs} <- maps:values(aeb_fate_code:functions(FCode)),
                            BB <- maps:values(BBs) ],
            UsedInstrs = [ if is_atom(I) -> I; true -> element(1, I) end || BB <- BBs, I <- BB ],
            ?WHENFAIL(begin
               io:format("Calls: ~p\n", [Calls]),
               [ io:format("Code for ~p:\n~s", [Pubkey, pp_fcode(FCode)]) || {Pubkey, FCode} <- maps:to_list(Code) ] end,
            aggregate(UsedInstrs,
            aggregate(fun check_instrs/1, UsedInstrs,
            try
                SerCode = maps:map(fun(_, FCode) -> serialize(FCode) end, Code),
                {Res, Events, Stats} = run(ChainEnv, SerCode, Calls),
                NCalls  = length([ 1 || {set, _, {call, _, new_call, _}} <- Instrs ]),
                NInstrs = length([ 1 || {set, _, {call, _, instr, _}} <- Instrs ]),
                measure(block_time, 6 / maps:get(gas_per_us, Stats),
                measure(bb_size___, lists:map(fun length/1, BBs),
                measure(n_calls___, NCalls,
                measure(n_instrs__, if NCalls > 0 -> NInstrs / NCalls; true -> [] end,
                measure(gas_used__, maps:get(gas_used, Stats),
                aggregate(lists:map(fun classify/1, Res),
                conjunction([ {result,   check_result(Res, RetValues)},
                              {events,   check_events(Events, FinalState#state.events)},
                              {state,    check_state(FinalState)},
                              {gas_cost, check_gas_cost(Stats)} ])))))))
            catch _:Err ->
                equals(ok, {'EXIT', Err, erlang:get_stacktrace()})
            end)))
        catch _:Err ->
            equals(ok, {'EXIT', Err, erlang:get_stacktrace()})
        end))
    end)))).

serialize(FCode) ->
    aect_sophia:serialize(#{source_hash => <<0:256>>,
                            byte_code   => aeb_fate_code:serialize(FCode),
                            type_info   => [],
                            payable     => true}, 3).

get_return_value(S, {set, _, {call, ?MODULE, instr, [{'RETURN', []}]}}) ->
    get_value(S, {stack, 0});
get_return_value(S, {set, _, {call, ?MODULE, instr, [{'RETURNR', [R]}]}}) ->
    get_value(S, R).

get_return_value(S) ->
    get_value(S, {stack, 0}).

print_states([{model, ?MODULE}, {init, S} | Code]) ->
    print_states(S, Code).

print_states(S, []) ->
    print_state(S);
print_states(S, [{set, X, Call = {call, ?MODULE, Fun, Args}} | Cmds]) ->
    print_state(S),
    case {Fun, Args} of
        {instr, [{Op, OpArgs}]} ->
            io:format("~s\n", [string:join([atom_to_list(Op) | [format_arg(Arg) || Arg <- OpArgs]], " ")]);
        {new_call, _} ->
            io:format("new_call ~p\n", [Args])
    end,
    print_states(next_state(S, X, Call), Cmds).

print_state(S) ->
    io:format("  ~p\n", [S]).
    %% io:format("  ~p\n", [S#state{ chain_env = maps:remove(accounts, S#state.chain_env) }]).

format_arg(Arg) -> io_lib:format("~p", [Arg]).

pp_fcode(FCode) ->
    try
        aeb_fate_asm:pp(FCode)
    catch _:_ ->
        io_lib:format("Bad fcode\n  ~p", [FCode])
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

check_events(Have, Want) ->
    Ix = fun(<<N:256>>)            -> N;
            (N) when is_integer(N) -> N;
            (X)                    -> {bad_ix, X} end,
    Ev = fun({C, Is, P})   -> #{ contract => C, payload => P, indices => lists:map(Ix, Is) } end,
    Have1 = [ Ev(H) || H <- Have ],
    Want1 = [ Ev({C, Is, P}) || #event{ contract = C, payload = P, indices = Is } <- lists:reverse(Want) ],
    equals(Have1, Want1).

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
              BlockTime < infinity).

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

