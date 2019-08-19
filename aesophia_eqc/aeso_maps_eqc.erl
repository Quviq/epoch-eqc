%%% File        : aeso_maps_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 16 Aug 2019 by Ulf Norell
-module(aeso_maps_eqc).

-compile([export_all, nowarn_export_all]).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").
-include_lib("eqc/include/eqc_mocking.hrl").

%% -- State ------------------------------------------------------------------

-record(contract, {id, state_type, state}).
-record(state, {contracts :: [#contract{}], values = []}).

init_state() ->
    ?LET(Types, ne_list(3, state_type()),
    #state{ contracts = [ #contract{ id = I, state_type = T }
                          || {I, T} <- ix(Types) ] }).

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

%% -- Operations -------------------------------------------------------------

%% --- get ---

get_state_args(S) -> [reference(S)].

get_state(_) -> ok.

get_state_next(S, V, [Ref]) ->
  S#state{ values = [{V, ref_type(S, Ref)} | S#state.values] }.

%% --- put ---

set_state_args(S) ->
    ?LET(R, reference(S),
    ?LET(V, value(S, ref_type(S, R)),
    [R, V])).

set_state(_, _) -> ok.

%% -- Common -----------------------------------------------------------------

%% -- Generators -------------------------------------------------------------

ne_list(N, G) -> non_empty(eqc_gen:list(N, G)).

%% -- Types --

state_type() ->
    weighted_default({1, map_type()},
                     {1, record_type()}).

record_type() ->
    ne_list(3, map_type()).

-define(MAX_DEPTH, 3).
map_type() ->
    ?LET(D, choose(1, ?MAX_DEPTH), map_type(D)).

key_type() -> elements([int, string, {tuple, [int, string]}]).

map_type(0) -> key_type();
map_type(N) -> {map, key_type(), map_type(N - 1)}.

string_part() ->
    oneof([ ?LET(N, nat(), integer_to_list(N))
          , elements(["x", "foo", "abcXYZ"]) ]).

value(S, Type) ->
    case [V || {V, T} <- S#state.values, T == Type] of
        []  -> value(Type);
        Vs  -> weighted_default({3, elements(Vs)}, {1, value(Type)})
    end.

value(int)    -> int();
value(string) ->
    ?SUCHTHAT(Bin,
        ?LET(Parts, list(string_part()), list_to_binary(string:join(Parts, "-"))),
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

command_chunks([{model, ?MODULE}, {init, #state{ contracts = Cs }} | Cmds]) ->
    ?LET(Chunks, ?SUCHTHAT(Chunks, chunks(Cmds), nice_chunks(Chunks)),
         [ {elements([ C#contract.id || C <- Cs ]), Chunk}
           || Chunk <- Chunks ]).

nice_chunks(Cs) ->
    %% AEVM stack-limit workaround
    lists:all(fun(C) -> length(C) =< 16 end, Cs).

%% -- Types and values -------------------------------------------------------

initial_value({map, _, _}) -> #{};
initial_value(Types) when is_list(Types) ->
    {record, [ initial_value(T) || T <- Types ]}.

%% -- Compiling --------------------------------------------------------------

contracts_source(#state{ contracts = Cs } = S, CmdChunks) ->
    ACIs = [ contract_aci(C) || C <- Cs ],
    [ contract_source(S, ACIs, C, [Chunk || {I, Chunk} <- CmdChunks, I == Id ])
        || C = #contract{id = Id} <- Cs ].

contract_name(I) -> lists:concat(["Test", I]).

contract_aci(#contract{id = I, state_type = Type}) ->
    [ "contract ", contract_name(I), " =\n"
    , ind(2, state_type(Type))
    , ind(2, "entrypoint init : () => state\n")
    , ind(2, [ [getter_proto(R, T), setter_proto(R, T)] || {R, T} <- references(Type) ])
    ].

contract_source(S, ACIs, #contract{id = I, state_type = Type}, CmdChunks) ->
    lists:flatten(
    [ [ ACI || {J, ACI} <- ix(ACIs), I /= J ]
    , [ "contract ", contract_name(I), " =\n"
      , ind(2, state_type(Type))
      , ind(2, init_function(Type))
      , ind(2, [ [getter(R, T), setter(R, T)] || {R, T} <- references(Type) ])
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
call_references(get_state, [{Id, _}])    -> [Id].

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
    Bound = [ X || {{bind, X, _}, _} <- Code ],
    [ [ Src || {_, Src} <- Code ]
    , to_sophia_val(list_to_tuple(Bound))
    ].

cmd_to_sophia(S, Id, {set, {var, N}, Call}) ->
    case call_to_sophia(S, Id, Call) of
        {bind, T, Code}   -> {{bind, {var, N}, T}, ["let ", var(N), " = ", Code, "\n"]};
        {nobind, T, Code} -> {{nobind, T}, [Code, "\n"]}
    end.

call_to_sophia(S, Id, {call, ?MODULE, Fun, Args}) ->
    call_to_sophia(S, Id, Fun, Args);
call_to_sophia(S, Id, {call, ?MODULE, Fun, Args, _Meta}) ->
    call_to_sophia(S, Id, Fun, Args).

call_to_sophia(S, Id, get_state, [Ref]) ->
    Type = ref_type(S, Ref),
    {bind, Type, [ getter_name(Id, Ref), "()" ]};
call_to_sophia(_S, Id, set_state, [Ref, Val]) ->
    {nobind, {tuple, []}, [ setter_name(Id, Ref), "(", to_sophia_val(Val), ")" ]}.

chunk_entrypoint([{set, {var, N}, _} | _]) -> lists:concat(["chunk_", N]).

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

getter_proto(top, T) ->
    ["entrypoint get_state : () => ", to_sophia_type(T), "\n"];
getter_proto({field, I}, T) ->
    [ "entrypoint get_", field_name(I), " : () => ", to_sophia_type(T), "\n" ].

getter(top, T) ->
    ["entrypoint get_state() : ", to_sophia_type(T), " = state\n"];
getter({field, I}, T) ->
    [ "entrypoint get_", field_name(I), "() : ", to_sophia_type(T), " = state.", field_name(I), "\n" ].

setter_proto(top, T) ->
    ["entrypoint set_state : ", to_sophia_type(T), " => unit\n"];
setter_proto({field, I}, T) ->
    X = field_name(I),
    [ "entrypoint set_", X, " : ", to_sophia_type(T), " => unit\n"].

setter(top, T) ->
    ["stateful entrypoint set_state(s : ", to_sophia_type(T), ") = put(s)\n"];
setter({field, I}, T) ->
    X = field_name(I),
    [ "stateful entrypoint set_", X, "(", X, " : ", to_sophia_type(T), ") = put(state{", X, " = ", X, "})\n" ].

state_type(T = {map, _, _}) ->
    ["type state = ", to_sophia_type(T)];
state_type(Ts) when is_list(Ts) ->
    [ "record state =\n"
    , ind(2, ["{ ", lists:join("\n, ", [ [field_name(I), " : ", to_sophia_type(T)]
                                        || {I, T} <- ix(Ts) ]),
              " }\n"]) ].

init_function(Type) ->
    [ "entrypoint init() =\n"
    , ind(2, to_sophia_val(initial_value(Type))) ].

to_sophia_type({map, K, V}) -> ["map(", to_sophia_type(K), ", ", to_sophia_type(V), ")"];
to_sophia_type(int)         -> "int";
to_sophia_type(string)      -> "string";
to_sophia_type({tuple, Ts}) -> string:join([ to_sophia_type(T) || T <- Ts ], " * ").

to_vm_type(int)         -> word;
to_vm_type(string)      -> string;
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

compile_commands(InitS = #state{ contracts = Cs }, Chunks) ->
    Account = {var, 1},
    Sources = contracts_source(InitS, Chunks),
    [ {init, no_state} ] ++
    [ {set, Account, {call, ?MODULE, new_account, [1000000000000000000]}} ] ++
    [ {set, {var, Id + 1}, {call, ?MODULE, create_contract, [Account, Source, {}]}}
      || {#contract{id = Id}, Source} <- lists:zip(Cs, Sources) ] ++
    compile_chunks(InitS, #{}, length(Cs) + 2, Chunks).

compile_chunks(_, _, _, []) -> [];
compile_chunks(S, Binds, Var, [{Id, Cmds} | Chunks]) ->
    Account  = {var, 1},
    Contract = {var, Id + 1},
    Fun      = list_to_atom(chunk_entrypoint(Cmds)),
    Args     = chunk_arguments(Binds, Id, Cmds),
    {Xs, Type} = chunk_return_type(S, Id, Cmds),
    NewBinds = case Xs of
                 [X] -> #{X => Var};
                 _   -> maps:from_list([{X, {Var, I}} || {I, X} <- ix(Xs)])
               end,
    Binds1 = maps:merge(Binds, NewBinds),
    [{set, {var, Var}, {call, ?MODULE, call_contract, [Account, Contract, Fun, to_vm_type(Type), Args, #{}]}} |
     compile_chunks(S, Binds1, Var + 1, Chunks)].

chunk_arguments(Binds, Id, Cmds) ->
    MakeArg =
        fun(X) ->
            case maps:get(X, Binds, undefined) of
                undefined -> error({chunk_arguments, Binds, X});
                {Var, I}  -> {call, erlang, element, [I, {var, Var}]};
                Var       -> {var, Var}
            end end,
    Refs = [{'@ct', {var, J + 1}} || J <- chunk_references(Id, Cmds)],
    Args = lists:map(MakeArg, chunk_vars([], Cmds, [])),
    list_to_tuple(Refs ++ Args).

chunk_return_type(S, Id, Cmds) ->
    {Xs, Ts} = lists:unzip([ {X, T}
                             || Cmd = {set, {var, X}, _} <- Cmds,
                                {{bind, _, T}, _} <- [cmd_to_sophia(S, Id, Cmd)] ]),
    case Ts of
        [T] -> {Xs, T};
        _   -> {Xs, {tuple, Ts}}
    end.

%% -- Property ---------------------------------------------------------------

%% The property.
prop_compile() -> prop_compile(?MODULE).
prop_compile(Mod) ->
    ?FORALL(InitS, init_state(),
    ?FORALL(Cmds, ?SUCHTHAT(Cmds, commands(Mod, InitS), length(Cmds) > 2),
    ?FORALL(Chunks, command_chunks(Cmds),
    begin
        Sources = contracts_source(InitS, Chunks),
        ?WHENFAIL([eqc:format("~s\n", [Source]) || Source <- Sources],
        begin
            Results = [ {Backend, I, catch aeso_compiler:from_string(Source, [{backend, Backend}, no_implicit_stdlib])}
                             || {I, Source} <- ix(Sources),
                                Backend <- [fate] ], % , aevm] ],
            IsOk = fun({ok, _})       -> true;
                      ({'EXIT', Err}) -> ?WHENFAIL(eqc:format("~p\n", [Err]), false);
                      ({error, Err})  -> ?WHENFAIL(eqc:format("~s\n", [Err]), false)
                   end,
            conjunction([{{Backend, I}, IsOk(Res)} || {Backend, I, Res} <- Results])
        end)
    end))).

prop_run() -> prop_run(fate, ?MODULE).
prop_run(Backend, Mod) ->
    ?SETUP(fun() -> init(Backend), fun() -> ok end end,
    ?FORALL(InitS, init_state(),
    ?FORALL(Cmds, ?SUCHTHAT(Cmds, commands(Mod, InitS), length(Cmds) > 2),
    ?FORALL(Chunks, command_chunks(Cmds),
    begin
        CompiledCmds = compile_commands(InitS, Chunks),
        ?WHENFAIL([eqc:format("~s\n", [Source]) || Source <- contracts_source(InitS, Chunks)],
        begin
            init_run(Backend),
            HSR={_, _, Res} = run_commands(Mod, CompiledCmds),
            pretty_commands(Mod, CompiledCmds, HSR,
                Res == ok)
        end)
    end)))).


%% -- Low-level operations ---------------------------------------------------

init(Backend) ->
    eqc_mocking:start_mocking(api_spec(Backend)),
    eqc_mocking:init_lang({repl, ?EVENT(aec_hard_forks, protocol_effective_at_height, ['_'], 4)}).

api_spec(_) ->
  #api_spec
  { modules  =
    [ #api_module
      { name      = aec_hard_forks
      , fallback  = aec_hard_forks
      , functions =
          [ #api_fun{ name = protocol_effective_at_height, arity = 1 }
          ]
      } ] }.

init_run(Backend) ->
    VM = fun(_, FATE) when Backend == fate -> FATE;
            (AEVM, _) when Backend == aevm -> AEVM end,
    put(backend, Backend),
    put('$vm_version',     VM(6, 5)),
    put('$sophia_version', VM(4, 5)),
    put('$abi_version',    VM(1, 3)),
    put('$protocol_version', 4),
    aecontract_SUITE:state(aect_test_utils:new_state()),
    ok.

new_account(Balance) ->
    call(new_account, [Balance]).

-define(SOPHIA_CONTRACT_VSN, 2).

create_contract(Owner, Source, Args) ->
    Backend = get(backend),
    {ok, Code} = aeso_compiler:from_string(Source, [{backend, Backend}, no_implicit_stdlib]),
    ByteCode = aect_sophia:serialize(Code, ?SOPHIA_CONTRACT_VSN),
    call(create_contract_with_code, [Owner, ByteCode, Args, #{}]).

call_contract(Caller, ContractKey, Fun, Type, Args, Options) ->
    call(call_contract, [Caller, ContractKey, Fun, Type, Args, Options]).

%% Silence warnings.
new_account_args(_) -> [].
create_contract_args(_) -> [].
call_contract_args(_) -> [].

new_account_post(_, _, Res) ->
    is_binary(Res) andalso byte_size(Res) == 32.

create_contract_post(_, _, Res) ->
    is_binary(Res) andalso byte_size(Res) == 32.

call_contract_post(_, _, {error, Err}) ->
    case is_binary(Err) of
        true  ->
            io:format("~s\n", [Err]),
            binary_to_list(Err);
        false -> {error, Err}
    end;
call_contract_post(_, _, _)            -> true.

%% -- Common -----------------------------------------------------------------

weight(_, new_account)     -> 0;
weight(_, create_contract) -> 0;
weight(_, call_contract)   -> 0;
weight(_, _)               -> 1.

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

