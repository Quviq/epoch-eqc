%%% File        : aeso_maps_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 16 Aug 2019 by Ulf Norell
-module(aeso_maps_eqc).

-compile([export_all, nowarn_export_all]).

%% -define(PROFILE, true).
-include_lib("eqc/include/eqc_profile.hrl").

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-include_lib("eqc/include/eqc_mocking.hrl").

%% -- State ------------------------------------------------------------------

-record(contract, {id,
                   state_type,
                   state        %% No symbolic variables
                  }).

-record(value, {val, from_store = false}).

-record(state, {backend,
                contracts :: [#contract{}],
                values = [], %% Can contain symbolic variables
                env    = #{}, %% Maps symbolic variables to concrete values
                sequence = none
               }).

init_state(Backend) ->
    ?LET(MapTypes, ne_list(2, map_type()),
    ?LET(Types, ?LET(N, weighted_default({4, 2}, {1, 3}),
                        ne_list(N, state_type(MapTypes))),
    #state{ backend = Backend,
            %% sequence = [map_upd_s, cut, get_state, map_upd2, set_state],
            contracts = [ #contract{ id = I, state_type = T,
                                     state = init_value(T) }
                          || {I, T} <- ix(Types) ] })).

init_value({map, _, _}) -> #{};
init_value(Types)       -> list_to_tuple(lists:map(fun init_value/1, Types)).

get_contract(S, Id) ->
    lists:keyfind(Id, #contract.id, S#state.contracts).

ref_type(S, {Id, R}) ->
    #contract{ state_type = T } = get_contract(S, Id),
    case R of
        top        -> T;
        {field, I} -> lists:nth(I, T)
    end.

ref_value(S, {Id, R}) ->
    #contract{ state = V } = get_contract(S, Id),
    case R of
        top        -> V;
        {field, I} -> element(I, V)
    end.

set_ref({Id, R}, Val, S) ->
    C  = get_contract(S, Id),
    C1 = C#contract{ state = set_ref1(R, Val, C#contract.state) },
    S#state{ contracts = lists:keyreplace(Id, #contract.id, S#state.contracts, C1) }.

set_ref1(top, Val, _) -> Val;
set_ref1({field, I}, Val, Old) ->
    setelement(I, Old, Val).

evaluate(S, {var, X})           -> (maps:get(X, S#state.env))#value.val;
evaluate(S, L) when is_list(L)  -> [evaluate(S, V) || V <- L];
evaluate(S, T) when is_tuple(T) -> list_to_tuple(evaluate(S, tuple_to_list(T)));
evaluate(S, M) when is_map(M)   -> maps:map(fun(_, V) -> evaluate(S, V) end, M);
evaluate(_S, X) -> X.

add_value(S, {var, X} = V, Type, Val, FromStore) ->
    S#state{ values = [{V, Type} | S#state.values]
           , env    = (S#state.env)#{ X => #value{val = Val, from_store = FromStore} } }.

from_store(S, {var, X}) -> (maps:get(X, S#state.env))#value.from_store;
from_store(_, _)        -> false.

%% -- Operations -------------------------------------------------------------

%% Where we cut up the chunks.
cut_args(S) -> [elements([C#contract.id || C <- S#state.contracts])].

%% --- get ---

get_state_args(S) ->
    ?LET(R, reference(S), [R, ref_value(S, R)]).

get_state_pre(S, [R, V]) -> V == ref_value(S, R).

get_state(_, _) -> ok.

get_state_next(S, V, [Ref, Val]) ->
    add_value(S, V, ref_type(S, Ref), Val, true).

get_state_adapt(S, [Ref, _]) ->
    [Ref, ref_value(S, Ref)].

%% --- put ---

set_state_args(S) ->
    ?LET(R, reference(S),
    ?LET(V, value(S, ref_type(S, R), ref_value(S, R)),
    [R, V])).

set_state(_, _) -> ok.

set_state_next(S, _V, [Ref, Val]) ->
  set_ref(Ref, evaluate(S, Val), S).

%% --- Map functions ---

map_funs() -> [ map_get
              , map_upd
              , map_upd2
              , map_del
              , map_member
              , map_lookup
              , map_lookup_d
              , map_size
              , map_to_list].

map_fun_signature(map_get)      -> {[existing_key, map], val};
map_fun_signature(map_upd)      -> {[key, val, map], map};
map_fun_signature(map_upd2)     -> {[key1, key2, inner_val, nested_map], nested_map};
map_fun_signature(map_del)      -> {[key, map], map};
map_fun_signature(map_lookup)   -> {[key, map], {option, val}};
map_fun_signature(map_lookup_d) -> {[key, map, val], val};
map_fun_signature(map_member)   -> {[key, map], bool};
map_fun_signature(map_size)     -> {[map], int};
map_fun_signature(map_to_list)  -> {[map], {list, {tuple, [key, val]}}}.

map_fun_body(map_get)      -> "map[key]";
map_fun_body(map_upd)      -> "map{[key] = val}";
map_fun_body(map_upd2)     -> "map{[key1 = {}][key2] = val}";
map_fun_body(map_del)      -> "Map.delete(key, map)";
map_fun_body(map_lookup)   -> "Map.lookup(key, map)";
map_fun_body(map_lookup_d) -> "Map.lookup_default(key, map, val)";
map_fun_body(map_member)   -> "Map.member(key, map)";
map_fun_body(map_size)     -> "Map.size(map)";
map_fun_body(map_to_list)  -> "Map.to_list(map)".

map_get_pre(S)      -> pre(S, map_get).
map_upd_pre(S)      -> pre(S, map_upd).
map_upd2_pre(S)     -> pre(S, map_upd2).
map_del_pre(S)      -> pre(S, map_del).
map_member_pre(S)   -> pre(S, map_member).
map_lookup_pre(S)   -> pre(S, map_lookup).
map_lookup_d_pre(S) -> pre(S, map_lookup_d).
map_size_pre(S)     -> pre(S, map_size).
map_to_list_pre(S)  -> pre(S, map_to_list).

map_get_args(S)      -> args(S, map_get).
map_upd_args(S)      -> args(S, map_upd).
map_upd2_args(S)     -> args(S, map_upd2).
map_del_args(S)      -> args(S, map_del).
map_member_args(S)   -> args(S, map_member).
map_lookup_args(S)   -> args(S, map_lookup).
map_lookup_d_args(S) -> args(S, map_lookup_d).
map_size_args(S)     -> args(S, map_size).
map_to_list_args(S)  -> args(S, map_to_list).

map_get_adapt(S, Args)      -> adapt(S, map_get, Args).
map_upd_adapt(S, Args)      -> adapt(S, map_upd, Args).
map_upd2_adapt(S, Args)     -> adapt(S, map_upd2, Args).
map_del_adapt(S, Args)      -> adapt(S, map_del, Args).
map_member_adapt(S, Args)   -> adapt(S, map_member, Args).
map_lookup_adapt(S, Args)   -> adapt(S, map_lookup, Args).
map_lookup_d_adapt(S, Args) -> adapt(S, map_lookup_d, Args).
map_size_adapt(S, Args)     -> adapt(S, map_size, Args).
map_to_list_adapt(S, Args)  -> adapt(S, map_to_list, Args).

map_get(Key, Map)           -> maps:get(Key, Map, error).
map_upd(Key, Val, Map)      -> Map#{ Key => Val }.
map_upd2(Key1, Key2, Val, Map) -> Map#{ Key1 => (maps:get(Key1, Map, #{}))#{ Key2 => Val } }.
map_del(Key, Map)           -> maps:remove(Key, Map).
map_member(Key, Map)        -> maps:is_key(Key, Map).
map_to_list(Map)            -> maps:to_list(Map).
map_size(Map)               -> maps:size(Map).
map_lookup_d(Key, Map, Val) -> maps:get(Key, Map, Val).

map_lookup(Key, Map) ->
    case maps:get(Key, Map, not_found) of
        not_found -> none;
        Val       -> {some, Val}
    end.

requires_nested(Fun) ->
    {Args, _} = map_fun_signature(Fun),
    lists:member(nested_map, Args).

%% Generate a pair of references of the same type
ref_pair(S) ->
    ?LET(InRef, reference(S),
    begin
        Type = ref_type(S, InRef),
        {InRef, reference(S, Type), Type}
    end).

map_upd_s_args(S) ->
    ?LET({InRef, OutRef, Type = {map, _, ValT}}, ref_pair(S),
    ?LET(Id, id_for_type(S, Type),
    ?LET(Key, maybe_existing_key(1, 1, ref_value(S, InRef), Type),
    ?LET(Val, oneof([value(S, ValT), tombstone]),
    [Id, Type, Key, Val, InRef, OutRef])))).

map_upd_s_next(S, V, [_, _, Key, Val, InRef, OutRef]) ->
    OldMap  = ref_value(S, InRef),
    NewMap = case Val of
                 tombstone -> maps:remove(Key, OldMap);
                 _         -> OldMap#{ Key => evaluate(S, Val) }
             end,
    set_state_next(S, V, [OutRef, NewMap]).

%% -- Common -----------------------------------------------------------------

pre(S, Fun) ->
    not requires_nested(Fun) orelse has_nested(S).

args(S, Fun) ->
    Nested = case requires_nested(Fun) of true -> nested; false -> any end,
    ?LET({Id, Type, Map}, map(S, Nested),
    begin
        {ArgSig, _} = map_fun_signature(Fun),
        ?LET(Args, [arg_gen(S, Type, Map, Arg) || Arg <- ArgSig],
             [Id, Type | Args] ++ [apply_map_fun(S, Fun, Args)])
    end).

apply_map_fun(S, Fun, Args) ->
    Args1 = evaluate(S, Args),
    apply(?MODULE, Fun, Args1).

arg_gen(S, Type = {map, _, ValT}, Map, K) ->
    shrink_to_evaluated(S,
    case K of
        map          -> return(Map);
        nested_map   -> return(Map);
        existing_key -> existing_key(evaluate(S, Map), Type);
        key          -> maybe_existing_key(1, 1, evaluate(S, Map), Type);
        key1         -> maybe_existing_key(1, 1, evaluate(S, Map), Type);
        key2         ->
            Evaled    = evaluate(S, Map),
            InnerMaps = maps:fold(fun(_, Inner, Acc) -> maps:merge(Inner, Acc) end,
                                  #{}, Evaled),
            maybe_existing_key(1, 1, InnerMaps, ValT);
        val          -> value(S, ValT);
        inner_val    ->
            {map, _, Inner} = ValT,
            value(S, Inner)
    end).

shrink_to_evaluated(S, Gen) ->
    ?SHRINK(Gen, [eqc_gen:fmap(fun(V) -> evaluate(S, V) end, Gen)]).

adapt(S, Fun, [Id, Type | Args0]) ->
    try
        Args  = lists:droplast(Args0),
        Args1 = Args ++ [apply_map_fun(S, Fun, Args)],
        [Id, Type | Args1]
    catch _:_ ->
        false
    end.

command_precondition_common(S, Fun) -> check_sequence(S, Fun).

precondition_common(S, {call, ?MODULE, Fun, [Id, Type | Args0]}) ->
    not lists:member(Fun, map_funs()) orelse
    begin
        {ArgsT, _} = map_fun_signature(Fun),
        Args = lists:droplast(Args0),
        Res  = lists:last(Args0),
        Res /= error
            andalso Res == apply_map_fun(S, Fun, Args)
            andalso lists:all(fun({V, T}) -> type_check(S, V, signature_type_val(Type, T))
                              end, lists:zip(Args, ArgsT))
            andalso lists:member(Type, map_types((get_contract(S, Id))#contract.state_type))
    end;
precondition_common(_, _) -> true.

check_sequence(#state{ sequence = Seq }, Fun) when is_list(Seq) ->
    lists:sublist(Seq, 1) == [Fun];
check_sequence(_, _) -> true.

step_sequence(S = #state{ sequence = [_ | Seq] }) -> S#state{ sequence = Seq };
step_sequence(S) -> S.

next_state_common(S, X, {call, ?MODULE, Fun, [_, Type | Args0]}) ->
    case lists:member(Fun, map_funs()) of
        false -> step_sequence(S);
        true  ->
            Val = lists:last(Args0),
            {_, RetSig} = map_fun_signature(Fun),
            FromStore = lists:any(fun(Arg) -> from_store(S, Arg) end, Args0),
            RetType = signature_type_val(Type, RetSig),
            step_sequence(add_value(S, X, RetType, Val, FromStore))
    end;
next_state_common(S, _, _) -> step_sequence(S).

%% -- Generators -------------------------------------------------------------

ne_list(N, G) -> non_empty(eqc_gen:list(N, G)).

%% -- Types --

state_type() ->
    weighted_default({1, map_type()},
                     {1, record_type()}).

state_type(MapTypes) ->
    weighted_default({1, elements(MapTypes)},
                     {1, ne_list(3, elements(MapTypes))}).

record_type() ->
    ne_list(3, map_type()).

-define(MAX_DEPTH, 3).
map_type() ->
    ?LET(D, choose(1, ?MAX_DEPTH), map_type1(D)).

map_type(S, Kind) ->
    elements([ M || #contract{ state_type = T } <- S#state.contracts,
                  M <- map_types(T), Kind == any orelse is_nested(M) ]).

is_nested({map, _, {map, _, _}}) -> true;
is_nested(_)                     -> false.

has_nested(#state{ contracts = Cs }) ->
    lists:any(fun is_nested/1, map_types([ C#contract.state_type || C <- Cs ])).

key_type() -> elements([int, string, {tuple, [int, string]}]).

map_type1(0) -> key_type();
map_type1(N) -> {map, key_type(), map_type1(N - 1)}.

string_part() ->
    oneof([ ?LET(N, nat(), integer_to_list(N))
          , elements(["x", "foo", "abcXYZ"]) ]).

existing_key(Map, Type) ->
    maybe_existing_key(1, 0, Map, Type).

maybe_existing_key(_, _, Map, {map, KeyType, _}) when Map == #{} ->
    value(KeyType);
maybe_existing_key(A, B, Map, {map, KeyType, _}) ->
    weighted_default(
        {A, elements(maps:keys(Map))},
        {B, value(KeyType)}).

id_for_type(S, Type) ->
    elements([ Id || #contract{id = Id, state_type = T} <- S#state.contracts,
                     lists:member(Type, map_types(T)) ]).
map(S, Kind) ->
    ?LET(Type, map_type(S, Kind),
    ?LET(Map,  value(S, Type),
    ?LET(Id,   id_for_type(S, Type),
        {Id, Type, Map}))).

%% Try to avoid the third argument
value(S, Type, Val) ->
    case [V || {V, T} <- S#state.values, T == Type, evaluate(S, V) /= Val, from_store(S, V) ] of
        []  -> value(S, Type);
        Vs  -> frequency([{4, elements(Vs)},
                          {1, value(S, Type)}])
    end.

value(S, Type) ->
    AllVals   = [V || {V, T} <- S#state.values, T == Type ],
    StoreVals = [V || V <- AllVals, from_store(S, V) ],
    case AllVals of
        []  -> value(Type);
        _   -> frequency([{19, shrink_to_evaluated(S, elements(StoreVals))} || StoreVals /= []] ++
                         [{3,  shrink_to_evaluated(S, elements(AllVals))},
                          {1, value(Type)}])
    end.

value(int)    -> nat();
value(string) ->
    ?SUCHTHAT(Bin,
        ?LET(Parts, list(2, string_part()), list_to_binary(string:join(Parts, "-"))),
        byte_size(Bin) /= 32);   %% To not confuse the auto-address machinery.
value({tuple, Ts}) ->
    ?LET(Vs, [ value(T) || T <- Ts ], list_to_tuple(Vs));
value({map, Key, Val}) ->
    ?LET(KVs, list(5, {value(Key), value(Val)}),
         maps:from_list(KVs));
value(Fields) ->
    ?LET(Vs, [ value(T) || T <- Fields ],
         list_to_tuple(Vs)).

%% -- Stuff --

reference(#state{ contracts = Cs }) ->
    ?LET(#contract{ id = Id, state_type = T }, elements(Cs),
    case T of
        {map, _, _} -> {Id, top};
        _           -> {Id, {field, choose(1, length(T))}}
    end).

reference(#state{ contracts = Cs }, Type) ->
    elements([ {Id, R} || #contract{ id = Id, state_type = T } <- Cs,
                          {R, Type1} <- references(T),
                          Type1 == Type ]).

chunks([])  -> [[]];
chunks([X]) -> [[X]];
chunks(Xs)  ->
    ?LET(Splits, resize(length(Xs), list(choose(1, length(Xs) - 1))),
    begin
        Usplits = lists:usort(Splits),
        try do_split(0, Usplits, Xs)
        catch _:_ ->
            [{error, Usplits, Xs}]
        end
    end).

do_split(_N, [], Xs) -> [Xs];
do_split(N, [I | Is], Xs) ->
    {Ys, Zs} = lists:split(I - N, Xs),
    Zss = do_split(I, Is, Zs),
    [Ys | Zss].

prop_chunks() ->
    ?FORALL(Xs, list(nat()),
    ?FORALL(Xss, chunks(Xs),
    collect(with_title(chunks), length(Xss),
    aggregate(with_title(chunk_size), [length(Ys) || Ys <- Xss],
    equals(lists:append(Xss), Xs))))).

command_chunks([{model, ?MODULE}, {init, _} | Cmds]) ->
    cut(Cmds, [[]]).

cut([], [[] | Acc]) ->
    lists:reverse(Acc);
cut([], [Chunk | Acc]) ->
    lists:reverse([{1, lists:reverse(Chunk)} | Acc]);
cut([{set, _, {call, _, cut, [_]}} | Cmds], [[] | Acc]) ->
    cut(Cmds, [[] | Acc]);
cut([{set, _, {call, _, cut, [Id]}} | Cmds], [Chunk | Acc]) ->
    cut(Cmds, [[], {Id, lists:reverse(Chunk)} | Acc]);
cut([Cmd | Cmds], [Chunk | Acc]) ->
    cut(Cmds, [[Cmd | Chunk] | Acc]).

nice_chunks(Cs) ->
    %% AEVM stack-limit workaround
    lists:all(fun(C) -> length(C) =< 12 end, Cs).

%% -- Types and values -------------------------------------------------------

initial_value({map, _, _}) -> #{};
initial_value(Types) when is_list(Types) ->
    {record, [ initial_value(T) || T <- Types ]}.

type_check(Val, Type) -> type_check(#state{}, Val, Type).

type_check(S, {var, _} = V, T) ->
    {V, T} == lists:keyfind(V, 1, S#state.values);
type_check(S, Map, {map, KeyT, ValT}) ->
    is_map(Map) andalso
    maps:fold(fun(_, _, false) -> false;
                 (K, V, true)  -> type_check(S, K, KeyT) andalso type_check(S, V, ValT)
              end, true, Map);
type_check(_, N, int) -> is_integer(N);
type_check(_, B, string) -> is_binary(B);
type_check(S, T, {tuple, Ts}) ->
    is_tuple(T) andalso
    tuple_size(T) == length(Ts) andalso
    lists:all(fun({V, Type}) -> type_check(S, V, Type) end, lists:zip(tuple_to_list(T), Ts));
type_check(_, _, _) -> false.

%% -- Compiling --------------------------------------------------------------

-record(rt_state, { backend, accounts = [], contracts = [] }).

contracts_source(#state{ contracts = Cs } = S, CmdChunks) ->
    ACIs = [ contract_aci(S, C) || C <- Cs ],
    [ contract_source(S, ACIs, C, [Chunk || {I, Chunk} <- CmdChunks, I == Id ])
        || C = #contract{id = Id} <- Cs ].

contract_name(I) -> lists:concat(["Test", I]).

contract_aci(S, #contract{id = I, state_type = Type}) ->
    [ "contract ", contract_name(I), " =\n"
    , ind(2, state_type_to_sophia(Type))
    , ind(2, "entrypoint init : () => state\n")
    , ind(2, [ [getter_proto(R, T), setter_proto(R, T)] || {R, T} <- references(Type) ])
    , ind(2, [ map_function_protos(T) || T <- map_types(S, Type) ]) ].

contract_source(S, ACIs, #contract{id = I, state_type = Type}, CmdChunks) ->
    lists:flatten(
    [ [ ACI || {J, ACI} <- ix(ACIs), I /= J ]
    , [ "contract ", contract_name(I), " =\n"
      , ind(2, state_type_to_sophia(Type))
      , ind(2, init_function(Type))
      , ind(2, [ [getter(R, T), setter(R, T)] || {R, T} <- references(Type) ])
      , ind(2, [ map_functions(T) || T <- map_types(S, Type) ])
      , ind(2, [ chunk_code(S, I, Chunk) || Chunk <- CmdChunks ])
      ] ]).

chunk_code(S, Id, Cmds) ->
    RemoteArgs = chunk_contract_vars(Id, Cmds),
    VarArgs    = chunk_vars(Cmds),
    [ "stateful entrypoint ", chunk_entrypoint(Cmds)
    , "(", lists:join(", ", [[X, " : ", T] || {X, T} <- RemoteArgs ++ VarArgs]), ") =\n"
    , ind(2, chunk_body(S, Id, Cmds)) ].

chunk_contract_vars(Id, Cmds) ->
    Js = chunk_references(Id, Cmds),
    [ {contract_var(J), contract_name(J)} || J <- Js ].

chunk_references(Id, Cmds) ->
    lists:usort([ J || Cmd <- Cmds, J <- cmd_references(Cmd), J /= Id ]).

contract_var(J) -> "r" ++ integer_to_list(J).

cmd_references({set, _, {call, ?MODULE, Fun, Args}}) ->
    call_references(Fun, Args);
cmd_references({set, _, {call, ?MODULE, Fun, Args, _Meta}}) ->
    call_references(Fun, Args).

call_references(set_state, [{Id, _}, _]) -> [Id];
call_references(get_state, [{Id, _}, _]) -> [Id];
call_references(map_upd_s, [Id, _Ty, _Key, _Val, {InId, _}, {OutId, _}]) ->
    [Id, InId, OutId];
call_references(_Fun, [Id | _]) when is_integer(Id) -> [Id].

chunk_vars(Cmds) ->
    [ {var(X), "_"} || X <- chunk_vars([], Cmds, []) ].

chunk_vars(Local, [], Acc) ->
    lists:usort(lists:flatten(Acc)) -- Local;
chunk_vars(Local, [{set, {var, X}, Call} | Cmds], Acc) ->
    chunk_vars([X | Local], Cmds, [vars(Call), Acc]).

vars({var, N}) -> [N];
vars(T) when is_tuple(T) -> vars(tuple_to_list(T));
vars(L) when is_list(L) -> lists:map(fun vars/1, L);
vars(_) -> [].

var(I) -> lists:concat(["x", I]).

chunk_body(S, Id, Cmds) ->
    Code  = [ cmd_to_sophia(S, Id, Cmd) || Cmd <- Cmds ],
    Bound = [ X || {{bind, X, _, _}, _} <- Code ],
    [ [ Src || {_, Src} <- Code ]
    , to_sophia_val(list_to_tuple(Bound))
    ].

cmd_to_sophia(S, Id, {set, {var, N}, Call}) ->
    case call_to_sophia(S, Id, Call) of
        {bind, T, V, Code} -> {{bind, {var, N}, T, V}, ["let ", var(N), " = ", Code, "\n"]};
        {nobind, T, Code}  -> {{nobind, T}, [Code, "\n"]}
    end.

call_to_sophia(S, Id, {call, ?MODULE, Fun, Args}) ->
    call_to_sophia(S, Id, Fun, Args);
call_to_sophia(S, Id, {call, ?MODULE, Fun, Args, _Meta}) ->
    call_to_sophia(S, Id, Fun, Args).

call_to_sophia(S, Id, get_state, [Ref, Val]) ->
    Type = ref_type(S, Ref),
    {bind, Type, Val, [ getter_name(Id, Ref), "()" ]};
call_to_sophia(_S, Id, set_state, [Ref, Val]) ->
    {nobind, {tuple, []}, [ setter_name(Id, Ref), "(", to_sophia_val(Val), ")" ]};
call_to_sophia(S, Id, map_upd_s, [J, Type, Key, Val, InRef, OutRef]) ->
    GetCall = [getter_name(Id, InRef), "()"],
    UpdCall =
        case Val of
            tombstone ->
                [map_fun_name(S, Id, J, map_del, Type),
                 "(", lists:join(", ", [ to_sophia_val(Key), GetCall ]),
                 ")"];
            _ ->
                [map_fun_name(S, Id, J, map_upd, Type),
                 "(", lists:join(", ", [ to_sophia_val(Key), to_sophia_val(Val), GetCall ]),
                 ")"]
        end,
    {nobind, {tuple, []}, [ setter_name(Id, OutRef), "(", UpdCall, ")" ]};
call_to_sophia(S, Id, MapFun, [J, Type | Args0]) ->
    Res       = lists:last(Args0),
    Args      = lists:droplast(Args0),
    {_, ResT} = map_fun_signature(MapFun),
    {bind, signature_type_val(Type, ResT), Res,
     [map_fun_name(S, Id, J, MapFun, Type), to_sophia_arguments(Args)]}.

to_sophia_arguments(Vals) ->
    ["(", lists:join(", ", [to_sophia_val(V) || V <- Vals]), ")"].

chunk_entrypoint([{set, {var, N}, _} | _]) -> lists:concat(["chunk_", N]).

poly_map() -> {map, {tvar, key}, {tvar, val}}.

map_types(#state{ backend = {fate, _} }, _) -> [poly_map()];
map_types(_, Type)                          -> map_types(Type).

map_types({map, K, V}) ->
    [{map, K, V} | map_types(V)];
map_types(Ts) when is_list(Ts) ->
    lists:usort(lists:flatmap(fun map_types/1, Ts));
map_types(_) -> [].

references(T = {map, _, _})     -> [{top, T}];
references(Ts) when is_list(Ts) -> [ {{field, I}, T} || {I, T} <- ix(Ts) ].

getter_name(Id, {Id, Ref}) -> getter_name(Ref);
getter_name(_,  {Id, Ref}) -> [contract_var(Id), ".", getter_name(Ref)].

setter_name(Id, {Id, Ref}) -> setter_name(Ref);
setter_name(_,  {Id, Ref}) -> [contract_var(Id), ".", setter_name(Ref)].

getter_name(top)        -> "get_state";
getter_name({field, I}) -> "get_" ++ field_name(I).

setter_name(top)        -> "set_state";
setter_name({field, I}) -> "set_" ++ field_name(I).

getter_proto(R, T) ->
    ["entrypoint ", getter_name(R), " : () => ", to_sophia_type(T), "\n"].

getter(R, T) ->
    ["entrypoint ", getter_name(R), "() : ", to_sophia_type(T), " = ", getter_body(R), "\n"].

getter_body(top)        -> "state";
getter_body({field, I}) -> ["state.", field_name(I)].

setter_proto(R, T) ->
    ["entrypoint ", setter_name(R), " : ", to_sophia_type(T), " => unit\n"].

setter(R, T) ->
    ["stateful entrypoint ", setter_name(R), "(x : ", to_sophia_type(T), ") = ", setter_body(R), "\n"].

setter_body(top) -> "put(x)";
setter_body({field, I}) ->
    ["put(state{", field_name(I), " = x})"].

type_suffix(int)         -> "i";
type_suffix(string)      -> "s";
type_suffix({map, K, V}) -> [type_suffix(K), "2", type_suffix(V)];
type_suffix({tuple, Ts}) -> lists:map(fun type_suffix/1, Ts).

map_fun_name(S, Id, Id, Fun, Type) ->
    map_fun_name(S, Fun, Type);
map_fun_name(S, _, Id, Fun, Type) ->
    [contract_var(Id), ".", map_fun_name(S, Fun, Type)].

map_fun_name(#state{ backend = {fate, _} }, Fun, _) ->
    map_fun_name(Fun, poly_map());
map_fun_name(_, Fun, Type) ->
    map_fun_name(Fun, Type).

map_fun_name(Fun, {map, {tvar, _}, {tvar, _}}) ->
    atom_to_list(Fun);
map_fun_name(Fun, Type) ->
    [atom_to_list(Fun), "_", type_suffix(Type)].

signature_type_val({map, Key, Val} = Type, K) ->
    case K of
        map          -> Type;
        nested_map   -> Type;
        key          -> Key;
        key1         -> Key;
        key2         -> {map, Key2, _} = Val, Key2;
        existing_key -> Key;
        val          -> Val;
        inner_val    -> {map, _, Val2} = Val, Val2;
        bool         -> bool;
        int          -> int;
        {list, T}    -> {list, signature_type_val(Type, T)};
        {tuple, Ts}  -> {tuple, [signature_type_val(Type, T) || T <- Ts]};
        {option, T}  -> {option, signature_type_val(Type, T)}
    end.

arg_to_list(existing_key) -> "key";
arg_to_list(Arg) -> atom_to_list(Arg).

map_fun_proto(map_upd2, _) ->
    ["entrypoint map_upd2 : ('key1, 'key2, 'val, map('key1, map('key2, 'val))) => map('key1, map('key2, 'val))\n"];
map_fun_proto(Fun, Type) ->
    {Args, Ret} = map_fun_signature(Fun),
    T = fun(K) -> to_sophia_type(signature_type_val(Type, K)) end,
    ["entrypoint ", map_fun_name(Fun, Type), " : (", lists:join(", ", [T(Arg) || Arg <- Args]), ") => ", T(Ret), "\n"].

map_fun_lhs(map_upd2, _) ->
    ["entrypoint map_upd2(key1, key2, val, map)"];
map_fun_lhs(Fun, Type) ->
    {Args, Ret} = map_fun_signature(Fun),
    T = fun(K) -> to_sophia_type(signature_type_val(Type, K)) end,
    ["entrypoint ", map_fun_name(Fun, Type),
        "(", lists:join(", ", [[arg_to_list(Arg), " : ", T(Arg)] || Arg <- Args]), ") : ", T(Ret)].

map_function_protos(Type) ->
    [ map_fun_proto(Fun, Type) || Fun <- map_funs() ].

map_functions(Type) ->
    [ [map_fun_lhs(Fun, Type), " = ", map_fun_body(Fun), "\n"]
      || Fun <- map_funs() ].

state_type_to_sophia(T = {map, _, _}) ->
    ["type state = ", to_sophia_type(T)];
state_type_to_sophia(Ts) when is_list(Ts) ->
    [ "record state =\n"
    , ind(2, ["{ ", lists:join("\n, ", [ [field_name(I), " : ", to_sophia_type(T)]
                                        || {I, T} <- ix(Ts) ]),
              " }\n"]) ].

init_function(Type) ->
    [ "entrypoint init() =\n"
    , ind(2, to_sophia_val(initial_value(Type))) ].

to_sophia_type({tvar, X})   -> ["'", atom_to_list(X)];
to_sophia_type(int)         -> "int";
to_sophia_type(string)      -> "string";
to_sophia_type(bool)        -> "bool";
to_sophia_type({map, K, V}) -> ["map(", to_sophia_type(K), ", ", to_sophia_type(V), ")"];
to_sophia_type({list, T})   -> ["list(", to_sophia_type(T), ")"];
to_sophia_type({option, T}) -> ["option(", to_sophia_type(T), ")"];
to_sophia_type({tuple, Ts}) -> ["(", string:join([ to_sophia_type(T) || T <- Ts ], " * "), ")"].

to_vm_type(int)         -> word;
to_vm_type(bool)        -> bool;
to_vm_type(string)      -> string;
to_vm_type({list, T})   -> {list, to_vm_type(T)};
to_vm_type({option, T}) -> {option, to_vm_type(T)};
to_vm_type({map, K, V}) -> {map, to_vm_type(K), to_vm_type(V)};
to_vm_type({tuple, Ts}) -> {tuple, lists:map(fun to_vm_type/1, Ts)}.

to_sophia_val(Map) when is_map(Map) ->
    ["{", lists:join(", ", [ ["[", to_sophia_val(K), "] = ", to_sophia_val(V)]
                           || {K, V} <- maps:to_list(Map) ]), "}"];
to_sophia_val({record, Fields}) ->
    ["{", lists:join(", ", [ [ field_name(I), " = ", to_sophia_val(V) ]
                           || {I, V} <- ix(Fields) ]), "}"];
to_sophia_val(N) when is_integer(N) -> integer_to_list(N);
to_sophia_val(<<>>) -> "\"\"";
to_sophia_val(S) when is_binary(S) -> io_lib:format("~p", [binary_to_list(S)]);
to_sophia_val({var, N}) -> var(N);
to_sophia_val(T) when is_tuple(T) ->
    ["(", lists:join(", ", [to_sophia_val(V) || V <- tuple_to_list(T)]), ")"].

field_name(I) -> [lists:nth(I, lists:seq($a, $z))].

compile_commands(InitS = #state{ contracts = Cs, backend = Backend }, Chunks) ->
    Account = {var, 1},
    Sources = contracts_source(InitS, Chunks),
    [ {init, #rt_state{ backend = Backend }} ] ++
    [ {set, Account, {call, ?MODULE, new_account, []}} ] ++
    [ {set, {var, Id + 1}, {call, ?MODULE, create_contract, [Account, Source, {}]}}
      || {#contract{id = Id}, Source} <- lists:zip(Cs, Sources) ] ++
    compile_chunks(InitS, #{}, length(Cs) + 2, protocol_height(Backend), Chunks).

compile_chunks(_, _, _, _, []) -> [];
compile_chunks(S, Binds, Var, Height, [hardfork | Chunks]) ->
    compile_chunks(S, Binds, Var, next_height(Height), Chunks);
compile_chunks(S, Binds, Var, Height, [{Id, Cmds} | Chunks]) ->
    Account  = {var, 1},
    Contract = {var, Id + 1},
    Fun      = list_to_atom(chunk_entrypoint(Cmds)),
    Args     = chunk_arguments(Binds, Id, Cmds),
    {Xs, Expect, Type} = chunk_return_type(S, Id, Cmds),
    NewBinds = case Xs of
                 [X] -> #{X => Var};
                 _   -> maps:from_list([{X, {Var, I}} || {I, X} <- ix(Xs)])
               end,
    Binds1 = maps:merge(Binds, NewBinds),
    [{set, {var, Var}, {call, ?MODULE, call_contract, [Account, Contract, Fun, to_vm_type(Type), Height, Args, Expect]}} |
     compile_chunks(S, Binds1, Var + 1, Height, Chunks)].

chunk_arguments(Binds, Id, Cmds) ->
    MakeArg = fun(X) -> make_arg(Binds, X) end,
    Refs = [{'@ct', {var, J + 1}} || J <- chunk_references(Id, Cmds)],
    Args = lists:map(MakeArg, chunk_vars([], Cmds, [])),
    list_to_tuple(Refs ++ Args).

make_arg(Binds, X) ->
    case maps:get(X, Binds, undefined) of
        undefined -> error({chunk_arguments, Binds, X});
        {Var, I}  -> {call, erlang, element, [I, {var, Var}]};
        Var       -> {var, Var}
    end.

chunk_return_type(S, Id, Cmds) ->
    {Xs, Ts, Vs} = lists:unzip3(
                     [ {X, T, V}
                       || Cmd = {set, {var, X}, _} <- Cmds,
                          {{bind, _, T, V}, _} <- [cmd_to_sophia(S, Id, Cmd)] ]),
    case Ts of
        [T] -> {Xs, hd(Vs), T};
        _   ->
            V = case lists:keyfind(error, 1, Vs) of
                    {error, _} = Err -> Err;
                    false -> list_to_tuple(Vs)
                end,
            {Xs, V, {tuple, Ts}}
    end.

%% -- Property ---------------------------------------------------------------

backends() -> [aevm, {fate, lima}, {fate, iris}].

%% The property.
prop_compile() -> prop_compile(?MODULE).

prop_compile(Mod) ->
    ?FORALL(Backend, elements(backends()),
            prop_compile(Backend, Mod)).

prop_compile(Backend, Mod) ->
    ?FORALL(InitS, init_state(Backend),
    ?FORALL(Cmds, ?SUCHTHAT(Cmds, commands(Mod, InitS), length(Cmds) > 2),
    ?FORALL(Chunks, command_chunks(Cmds),
    begin
        Sources = contracts_source(InitS, Chunks),
        ?WHENFAIL([eqc:format("~s\n", [Source]) || Source <- Sources],
        begin
            Results = [ {I, catch aeso_compiler:from_string(Source, [{backend, Backend}, no_implicit_stdlib])}
                             || {I, Source} <- ix(Sources) ],
            IsOk = fun({ok, _})       -> true;
                      ({'EXIT', Err}) -> ?WHENFAIL(eqc:format("~p\n", [Err]), false);
                      ({error, Err})  -> ?WHENFAIL(eqc:format("~s\n", [Err]), false)
                   end,
            conjunction([{I, IsOk(Res)} || {I, Res} <- Results])
        end)
    end))).

hardfork_point({fate, lima}, N) when N >= 2 ->
  weighted_default({1, no_hardfork},
                   {4, {hardfork, choose(1, N - 1)}});
hardfork_point(_, _) -> no_hardfork.

insert_hardfork(no_hardfork, Chunks) -> Chunks;
insert_hardfork({hardfork, N}, Chunks) ->
  {Before, After} = lists:split(N, Chunks),
  Before ++ [hardfork] ++ After.

prop_run() ->
    ?SETUP(fun() -> init(), fun() -> ok end end,
    ?FORALL(Backend, weighted_default({1, iris}, {4, lima}),
    prop_run({fate, Backend}))).

prop_run(Backend) ->
    ?FORALL(InitS, init_state(Backend),
    ?FORALL(Cmds, ?SUCHTHAT(Cmds, more_commands(20, commands(?MODULE, InitS)), length(Cmds) > 2),
    begin
        Chunks = command_chunks(Cmds),
        ?FORALL(Hardfork, hardfork_point(Backend, length(Chunks)),
        begin
            CompiledCmds = compile_commands(InitS, insert_hardfork(Hardfork, Chunks)),
            ?WHENFAIL([eqc:format("~s\n", [Source]) || Source <- contracts_source(InitS, Chunks)],
            begin
                init_run(Backend),
                HSR={Hist, _, Res} = run_commands(?MODULE, CompiledCmds),
                S = state_after(InitS, Cmds),
                aggregate(command_names(Cmds),
                aggregate(with_title(set_state_value), set_state_stats(S, Cmds),
                aggregate(with_title(state_type), [ case T of
                                                        {map, _, {map, _, _}} -> nested;
                                                        {map, _, _}           -> not_nested
                                                    end || #contract{ state_type = Ts } <- InitS#state.contracts,
                                                           T <- if is_list(Ts) -> Ts; true -> [Ts] end ],
                aggregate(call_features(Hist),
                measure(calls,     length([ x || {set, _, {call, _, call_contract, _}} <- CompiledCmds]),
                measure(chunk_len, [length(Chunk) || {_, Chunk} <- Chunks],
                pretty_commands(?MODULE, CompiledCmds, HSR,
                case Res of
                    ok -> true;
                    {exception, {'EXIT', {function_clause, [{aeso_icode_to_asm, dup, _, _} | _]}}} ->
                        ?IMPLIES(false, false);
                    _ -> false
                end)))))))
            end)
        end)
    end)).

set_state_stats(S, Cmds) ->
    Classify = fun(X = {var, _}) -> case from_store(S, X) of true -> store_var; false -> var end;
                  (_)            -> value end,
    [ Classify(Val) || {set, _, {call, _, set_state, [_, Val]}} <- Cmds ].

invariant(#rt_state{ backend = aevm }) -> true;          %% Only checking FATE store
invariant(#rt_state{ backend = {fate, lima} }) -> true;  %% Known to be buggy
invariant(#rt_state{ contracts = Contracts }) ->
    S = aecontract_SUITE:state(),
    conj([ store_invariant(get_contract_store(Pubkey, S)) || Pubkey <- Contracts ]).

store_invariant(Store) ->
    Regs0 = #{ 0 := Meta } =
        maps:from_list(
            [ {binary:decode_unsigned(Reg), aeb_fate_encoding:deserialize(Val)}
            || {<<0, Reg/binary>>, Val} <- maps:to_list(Store) ]),
    Regs = maps:without([0], Regs0),
    GetMap = fun(Id) ->
                maps:from_list(
                  [ {aeb_fate_encoding:deserialize(Key), aeb_fate_encoding:deserialize(Val)}
                  || {<<1, Id1:32, Key/binary>>, Val} <- maps:to_list(Store),
                     Key /= <<>>, Id1 == Id ])
             end,
    Maps = maps:map(fun(_, {tuple, {RawId, RefCount, _}}) -> {RefCount, GetMap(RawId)}
                    end, Meta),
    Refcount = refcount([Regs, Maps]),
    eqc_statem:conj(
      [ eqc_statem:tag(refcounts,
        eqc_statem:tag([{regs, Regs}, {maps, Maps}],
            eqc_statem:eq(Refcount, maps:map(fun(_, {R, _}) -> R end, Maps)))) ]).

get_contract_store(Pubkey, S) ->
    CTree = aect_test_utils:contracts(S),
    Ct    = aect_state_tree:get_contract(Pubkey, CTree, [full_store_cache]),
    aect_contracts_store:contents(aect_contracts:state(Ct)).

refcount(X) -> refcount(X, #{}).
refcount({store_map, _, Id}, Acc) -> maps:update_with(Id, fun(N) -> N + 1 end, 1, Acc);
refcount([H | T], Acc)            -> refcount(T, refcount(H, Acc));
refcount(T, Acc) when is_tuple(T) -> refcount(tuple_to_list(T), Acc);
refcount(M, Acc) when is_map(M)   -> refcount(maps:values(M), Acc);
refcount(_, Acc)                  -> Acc.


%% -- Low-level operations ---------------------------------------------------

-define(LIMA_HEIGHT, 1).
-define(IRIS_HEIGHT, 2).

init() ->
    eqc_mocking:start_mocking(api_spec()),
    eqc_mocking:init_lang({repl, ?XALT(?XALT(?EVENT(aec_hard_forks, protocol_effective_at_height, [?LIMA_HEIGHT], 4),
                                             ?EVENT(aec_hard_forks, protocol_effective_at_height, [?IRIS_HEIGHT], 5)),
                                       ?EVENT(aec_hard_forks, sorted_protocol_versions, [], [4, 5]))}).

protocol_height({fate, lima}) -> ?LIMA_HEIGHT;
protocol_height({fate, iris}) -> ?IRIS_HEIGHT;
protocol_height(aevm)         -> ?LIMA_HEIGHT.

next_height(?LIMA_HEIGHT) -> ?IRIS_HEIGHT.

protocol({fate, iris}) -> 5;
protocol({fate, lima}) -> 4;
protocol(aevm) -> 4.

vm_version({fate, iris}) -> 7;
vm_version({fate, lima}) -> 5;
vm_version(aevm)         -> 6.

sophia_version({fate, iris}) -> 6;
sophia_version({fate, lima}) -> 5;
sophia_version(aevm)         -> 4.

abi_version({fate, _}) -> 3;
abi_version(aevm)      -> 1.

api_spec() ->
  #api_spec
  { modules  =
    [ #api_module
      { name      = aec_hard_forks
      , fallback  = aec_hard_forks
      , functions =
          [ #api_fun{ name = protocol_effective_at_height, arity = 1 }
          , #api_fun{ name = sorted_protocol_versions,     arity = 0 }
          ]
      } ] }.

init_run(Backend) ->
    put(backend, Backend),
    put('$vm_version',     vm_version(Backend)),
    put('$sophia_version', sophia_version(Backend)),
    put('$abi_version',    abi_version(Backend)),
    put('$protocol_version', protocol(Backend)),
    aecontract_SUITE:state(aect_test_utils:new_state()),
    ok.

-define(MAX_GAS, 6000000 * 1000 * 1000).
-define(BALANCE, 1000 * 1000 * 1000 * 1000 * 1000 * 1000 * 1000 * 1000).

new_account() ->
    call(new_account, [?BALANCE]).

new_account_next(S, V, _) ->
    S#rt_state{ accounts = [V | S#rt_state.accounts] }.

-define(SOPHIA_CONTRACT_VSN, 3).

create_contract(Owner, Source, Args) ->
    Backend = get(backend),
    VM      = case Backend of {fate, _} -> fate; aevm -> aevm end,
    Height  = protocol_height(Backend),
    case ?BENCHMARK(compile, aeso_compiler:from_string(Source, [{backend, VM}, no_implicit_stdlib])) of
        {ok, Code} ->
            ByteCode = aect_sophia:serialize(Code, ?SOPHIA_CONTRACT_VSN),
            call(create_contract_with_code, [Owner, ByteCode, Args, #{height => Height}]);
        {error, Err} ->
            io:format("~s\n", [Err]),
            {error, binary_to_list(Err)}
    end.

create_contract_next(S, V, _) ->
    S#rt_state{ contracts = [V | S#rt_state.contracts] }.

call_contract(Caller, ContractKey, Fun, Type, Height, Args, _Expect) ->
    {Res, _Gas} = call(call_contract, [Caller, ContractKey, Fun, Type, Args, #{gas => ?MAX_GAS, height => Height, return_gas_used => true}]),
    case Res of
        error -> {Res, _Gas};
        _     -> Res
    end.

%% Silence warnings.
new_account_args(_) -> [].
create_contract_args(_) -> [].
call_contract_args(_) -> [].

new_account_post(_, _, Res) ->
    is_binary(Res) andalso byte_size(Res) == 32.

create_contract_post(_, _, Res) ->
    is_binary(Res) andalso byte_size(Res) == 32.

call_contract_post(_, [_, _, _, _, _, _, {error, Expect}], {error, Actual}) ->
    eq_err(Actual, Expect);
call_contract_post(_, _, {error, Err}) ->
    case is_binary(Err) of
        true  ->
            io:format("~s\n", [Err]),
            binary_to_list(Err);
        false -> {error, Err}
    end;
call_contract_post(Backend, [_, _, _, _, _, _, Expect], Actual) ->
    %% Map.to_list sorts differently on AEVM
    eq(sort_lists(Backend, Actual), sort_lists(Backend, Expect)).

call_contract_features(_S, [_Caller, _ContractKey, _Fun, _Type, Height, _Args, _Expect], _V) ->
  [{height, Height}].

sort_lists(aevm, X) -> sort_lists(X);
sort_lists(_, X) -> X.

sort_lists(L) when is_list(L) ->
    lists:sort(lists:map(fun sort_lists/1, L));
sort_lists(T) when is_tuple(T) ->
    list_to_tuple(lists:map(fun sort_lists/1, tuple_to_list(T)));
sort_lists(M) when is_map(M) ->
    %% No lists in map keys (currently)
    maps:map(fun(_, V) -> sort_lists(V) end, M);
sort_lists(X) -> X.

eq_err(<<"Maps: Key does not exist">>, not_found) -> true;
eq_err(Actual, Expected) when is_binary(Actual) ->
    eq(binary_to_list(Actual), Expected);
eq_err(Actual, Expected) -> eq(Actual, Expected).

%% -- Common -----------------------------------------------------------------

weight(_, new_account)     -> 0;
weight(_, create_contract) -> 0;
weight(_, call_contract)   -> 0;
weight(_, map_upd_s)       -> 20;
weight(_, map_upd2)        -> 30;
weight(_, map_upd)         -> 20;
weight(_, map_del)         -> 20;
weight(_, set_state)       -> 30;
weight(_, cut)             -> 30;
weight(_, _)               -> 5.

call(Fun, Args) ->
    S = aecontract_SUITE:state(),
    {Res, S1} = erlang:apply(aecontract_SUITE, Fun, Args ++ [S]),
    aecontract_SUITE:state(S1),
    Res.

ix(Xs) -> lists:zip(lists:seq(1, length(Xs)), Xs).

ind(N, S) ->
    Lines = string:split(lists:flatten(S), "\n", all),
    Lines1 = case lists:last(Lines) of
                 [] -> lists:droplast(Lines);
                 _  -> Lines
             end,
    [ [lists:duplicate(N, 32), L, "\n"] || L <- Lines1 ].

counterexample_1() ->
    Call = fun(Fun, Args) -> {call, aeso_maps_eqc, Fun, Args} end,
    MapFun = fun(Fun, Args) -> Call(Fun, [1, {map, int, {map, int, int}} | Args]) end,
    [{state,{fate,iris},
            [{contract,1,{map,int,{map,int,int}},#{}}],
            [],#{}},
     [{model,aeso_maps_eqc},
      {init,{state,{fate,iris},
                   [{contract,1,{map,int,{map,int,int}},#{}}],
                   [],#{}}},
      {set, {var,1}, MapFun(map_upd_s, [0, #{}, {1, top}, {1, top}])},
      {set, {var,2}, Call(cut, [1])},
      {set, {var,3}, Call(get_state, [{1, top}, #{0 => #{}}])},
      {set, {var,4}, MapFun(map_get, [0, {var, 3}, #{}])},
      {set, {var,5}, MapFun(map_upd, [0, 1, {var, 4}, #{0 => 1}])},
      {set, {var,6}, MapFun(map_upd_s, [0, {var, 5}, {1, top}, {1, top}])}]].

counter_example2() ->
    Call = fun(Fun, Args) -> {call, aeso_maps_eqc, Fun, Args} end,
    MapFun = fun(Fun, Args) -> Call(Fun, [1, {map, int, {map, int, int}} | Args]) end,
    [{state,{fate,iris},
            [{contract,1,{map,int,{map,int,int}},#{}}],
            [],#{}},
     [{model,aeso_maps_eqc},
      {init,{state,{fate,iris},
                   [{contract,1,{map,int,{map,int,int}},#{}}],
                   [],#{}}},
      {set, {var,1}, MapFun(map_upd_s, [0, #{}, {1, top}, {1, top}])},
      {set, {var,2}, Call(cut, [1])},
      {set, {var,3}, Call(get_state, [{1, top}, #{0 => #{}}])},
      {set, {var,4}, MapFun(map_upd2, [0, 0, 1, {var, 3}, #{0 => #{0 => 1}}])},
      {set, {var,5}, Call(set_state, [{1, top}, {var, 4}])}]].

