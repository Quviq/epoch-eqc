%%% File        : fate_compiler_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 8 Apr 2019 by Ulf Norell
-module(fate_compiler_eqc).

-compile([export_all, nowarn_export_all]).

-include_lib("eqc/include/eqc.hrl").

%% -- Compiling and running --------------------------------------------------

-define(VM_FATE_1, 5).
-define(VM_FATE_2, 7).

run(Code, Contract, Function0, Arguments) ->
    try
        Function = aeb_fate_code:symbol_identifier(Function0),
        Cache = cache(Code),
        Call  = make_call(Contract, Function, Arguments),
        Spec  = dummy_spec(),
        case aefa_fate:run_with_cache(Call, Spec, Cache) of
            {ok, ES}       -> aefa_engine_state:accumulator(ES);
            {error, E, _}  -> {error, binary_to_list(E)};
            {revert, E, _} -> {error, binary_to_list(E)}
        end
    catch _:Err ->
        {'EXIT', Err, erlang:get_stacktrace()}
    end.

compile_contract(Code) ->
    compile_contract(Code, []).

compile_contract(Code, Options) ->
    Ast       = aeso_parser:string(Code),
    TypedAst  = aeso_ast_infer_types:infer(Ast, Options),
    FCode     = aeso_ast_to_fcode:ast_to_fcode(TypedAst, Options),
    Fate      = aeso_fcode_to_fate:compile(FCode, Options),
    Bin       = aeb_fate_code:serialize(Fate),
    case aeb_fate_code:deserialize(Bin) of
        Fate  -> Fate;
        Fate1 -> {Fate1, '/=', Fate}
    end.

dummy_spec() ->
    #{ trees     => aec_trees:new_without_backend(),
       caller    => <<123:256>>,
       origin    => <<123:256>>,
       gas_price => 1,
       tx_env    => aetx_env:tx_env(1) }.

cache(Code) ->
    Key = pad_contract_name(<<"test">>),
    #{Key => Code}.

make_call(Contract, Function, Arguments) ->
    EncArgs  = list_to_tuple([aefate_test_utils:encode(A) || A <- Arguments]),
    Calldata = {tuple, {Function, {tuple, EncArgs}}},
    #{ contract => pad_contract_name(Contract),
       gas      => 1000000,
       value    => 0,
       store    => aefa_stores:initial_contract_store(),
       call     => aeb_fate_encoding:serialize(Calldata),
       vm_version => ?VM_FATE_1}.

pad_contract_name(Name) ->
    PadSize = 32 - byte_size(Name),
    iolist_to_binary([Name, lists:duplicate(PadSize, "_")]).

%% -- Generators -------------------------------------------------------------

-record(env, {types = [], constrs = []}).

bind_type(X, Env) -> Env#env{ types = [X | Env#env.types] }.
bind_type(X, Def, Env) -> bind_type(X, bind_constrs(def_con_names(Def), Env)).

bind_constr(C, Env) -> bind_constrs([C], Env).
bind_constrs(Cs, Env) -> Env#env{ constrs = Cs ++ Env#env.constrs }.

is_type(#env{types = Ts}, T) -> lists:member(T, Ts).
is_constr(#env{constrs = Cs}, C) -> lists:member(C, Cs).

ukeylist(Key, Val) ->
    ?LET(Xs, list({Key, seal(Val)}),
    begin
        Us = lists:usort(fun({X, _}, {Y, _}) -> X =< Y end, Xs),
        Xs1 = Xs -- (Xs -- Us),
        [{K, open(V)} || {K, V} <- Xs1]
    end).

gen_field_name() -> elements(["x", "y", "z"]).

gen_typedef(X, TEnv = #env{}) ->
    oneof([{alias_t, ?SIZED(N, gen_type(TEnv, N div 10))},
           {variant_t, X, gen_constrs(TEnv)},
           {record_t, X, gen_fields(TEnv)}]).

gen_typename() ->
    gen_typename([]).

gen_typename(TEnv) ->
    gen_name(TEnv#env.types, ["r", "s", "t"]).

gen_conname(TEnv) ->
    gen_name(TEnv#env.constrs, ["A", "B", "C", "D"]).

gen_name(Taken, Names) ->
    ?SUCHTHAT(Name,
    ?LET({X, Suf}, {elements(Names),
                    choose(0, 5)},
        return(lists:concat([X] ++ [Suf || Suf > 0]))),
    not lists:member(Name, Taken)).

gen_typedefs() ->
    ?LET(I, weighted_default({3, 0}, {1, choose(1, 3)}),
         gen_typedefs(I, #env{})).

gen_typedefs(0, _) -> [];
gen_typedefs(I, TEnv) ->
    ?LET(X, gen_typename(TEnv),
    ?LET(Def, gen_typedef(X, TEnv),
    [{type_def, X, Def}|
     gen_typedefs(I - 1, bind_type(X, Def, TEnv))])).

def_con_names({variant_t, _, Cons}) -> [C || {C, _} <- Cons];
def_con_names(_) -> [].

gen_fields(TEnv) ->
    non_empty(ukeylist(gen_field_name(), ?SIZED(N, gen_type(TEnv, N div 20)))).

gen_constrs(TEnv) ->
    ?LET(N, choose(1, 4),
    gen_constrs(TEnv, N)).

gen_constrs(_, 0) -> [];
gen_constrs(TEnv, N) ->
    ?LET(C, gen_conname(TEnv),
         [{C, ?SIZED(Size, gen_types(TEnv, Size div 20))} |
          gen_constrs(bind_constr(C, TEnv), N - 1)]).

gen_type() -> gen_type(#env{}).
gen_type(TEnv) ->
    ?SIZED(N, gen_type(TEnv, N div 5)).

gen_type(_, 0) -> elements([bool, int, string]);
gen_type(Env = #env{types = TEnv}, N) ->
    ?LAZY(frequency(
      [{1, {id, elements(TEnv)}} || [] /= TEnv] ++
      [{1, gen_type(Env, 0)},
       {1, ?LETSHRINK([T], [gen_type(Env, N div 2)],
             {list, T})},
       {3, ?LETSHRINK(Ts, gen_types(Env, N),
             return(tuple_t(Ts)))}])).

tuple_t([T]) -> T;
tuple_t(Ts)  -> {tuple, Ts}.

gen_types(TEnv, N) ->
    ?LET(I, choose(0, 3),
    vector(I, gen_type(TEnv, N div max(I, 1)))).

gen_subtype(bool) -> bool;
gen_subtype(int) -> int;
gen_subtype(string) -> string;
gen_subtype(T = {id, _}) -> T;
gen_subtype({list, T}) ->
    weighted_default({3, gen_subtype(T)}, {1, return(T)});
gen_subtype({tuple, []}) -> {tuple, []};
gen_subtype(T = {tuple, Ts}) ->
    weighted_default({3, ?LET(S, elements(Ts), gen_subtype(S))},
                     {1, return(T)}).

gen_var() ->
    {var, elements(["_", "x", "y", "z"])}.

gen_pat(Defs, Type) ->
    gen_pat(expand_defs(Defs, Type)).

gen_pat(Type) ->
    ?LET(Pat, ?SIZED(N, gen_pat1(N, Type)),
         freshen(Pat)).

gen_pat1(N, Type) ->
    weighted_default( {1, gen_var()}, {2, gen_pat2(N, Type)}).

strings() ->
    [<<"">>, <<"x">>, <<"foo">>, <<"bar">>,
     << <<C>> || _ <- lists:seq(1, 4), C <- lists:seq($a, $z) >>].

gen_pat2(_, int) -> {int, nat()};
gen_pat2(_, string) -> {string, elements(strings())};
gen_pat2(_, bool) -> {bool, bool()};
gen_pat2(_, {record_t, _, []})  -> {var, "_"};
gen_pat2(N, {record_t, _, Fields}) ->
    ?LET(Fs, non_empty(sublist(Fields)),
    ?LET(Fs1, shuffle(Fs),
        {record, [ {Y, gen_pat1(N div length(Fs1), T)} || {Y, T} <- Fs1 ]}));
gen_pat2(N, {variant_t, _, Cons}) ->
    ?LET({Con, Args}, elements(Cons),
         {con, Con, [gen_pat2(N div length(Args), T) || T <- Args]});
gen_pat2(N, {list, T}) ->
    ?LAZY(weighted_default({1, {list, []}},
                           {2, {'::', gen_pat1(N div 3, T), gen_pat1(2 * N div 2, {list, T})}}));
gen_pat2(N, {tuple, Ts}) -> {tuple, [gen_pat1(N, T) || T <- Ts]}.

freshen(Pat) ->
    {_, Pat1} = freshen([], Pat),
    Pat1.

freshen(Taken, {var, X}) ->
    {Taken1, Y} = fresh(Taken, X),
    {Taken1, {var, Y}};
freshen(Taken, {bool, _} = P)   -> {Taken, P};
freshen(Taken, {int, _} = P)    -> {Taken, P};
freshen(Taken, {string, _} = P)    -> {Taken, P};
freshen(Taken, {list, Ps}) ->
    {Taken1, Ps1} = freshen(Taken, Ps),
    {Taken1, {list, Ps1}};
freshen(Taken, {con, C, Ps}) ->
    {Taken1, Ps1} = freshen(Taken, Ps),
    {Taken1, {con, C, Ps1}};
freshen(Taken, {record, Fs}) ->
    {Xs, Ps}      = lists:unzip(Fs),
    {Taken1, Ps1} = freshen(Taken, Ps),
    {Taken1, {record, lists:zip(Xs, Ps1)}};
freshen(Taken, {tuple, Ps}) ->
    {Taken1, Ps1} = freshen(Taken, Ps),
    {Taken1, {tuple, Ps1}};
freshen(Taken, {'::', P, Q}) ->
    {Taken1, P1} = freshen(Taken, P),
    {Taken2, Q1} = freshen(Taken1, Q),
    {Taken2, {'::', P1, Q1}};
freshen(Taken, [H | T]) ->
    {Taken1, H1} = freshen(Taken, H),
    {Taken2, T1} = freshen(Taken1, T),
    {Taken2, [H1 | T1]};
freshen(Taken, []) -> {Taken, []}.


fresh(Taken, "_") -> {Taken, "_"};
fresh(Taken, X)   -> fresh(Taken, X, 0).

fresh(Taken, X, Suf) ->
    X1 = lists:concat([X | [Suf || Suf > 0]]),
    case lists:member(X1, Taken) of
        false -> {[X1 | Taken], X1};
        true  -> fresh(Taken, X, Suf + 1)
    end.

mk_env(Defs) -> #env{ types = [X || {type_def, X, _} <- Defs] }.

prune(_, _,      {var, _}     = P) -> P;
prune(_, bool,   {bool, _}    = P) -> P;
prune(_, int,    {int,  _}    = P) -> P;
prune(_, string, {string,  _} = P) -> P;
prune(Defs, {list, T}, {list, Ps}) ->
    {list, [prune(Defs, T, P) || P <- Ps]};
prune(Defs, {list, T}, {'::', P, Q}) ->
    {'::', prune(Defs, T, P), prune(Defs, {list, T}, Q)};
prune(Defs, {tuple, Ts}, {tuple, Ps}) ->
    {Ts1, Ps1} =
        case length(Ts) - length(Ps) of
            0 -> {Ts, Ps};
            N when N < 0 -> {Ts, lists:sublist(Ps, length(Ts))};
            N when N > 0 -> {Ts, Ps ++ lists:duplicate(N, {var, "_"})}
        end,
    {tuple, lists:zipwith(fun(T, P) -> prune(Defs, T, P) end, Ts1, Ps1)};
prune(Defs, {id, X}, P) ->
    {type_def, _, Def} = lists:keyfind(X, 2, Defs),
    prune(Defs, Def, P);
prune(Defs, {alias_t, Type}, P) ->
    prune(Defs, Type, P);
prune(Defs, {record_t, _, Ts}, {record, Ps}) ->
    case [{X, prune(Defs, T, P)} || {X, P} <- Ps, {Y, T} <- Ts, X == Y] of
        [] -> {var, "_"};
        Ps1 -> {record, Ps1}
    end;
prune(Defs, {variant_t, _, Cons}, {con, C, Ps}) ->
    case lists:keyfind(C, 1, Cons) of
        {C, Ts} ->
            {tuple, Ps1} = prune(Defs, {tuple, Ts}, {tuple, Ps}),
            {con, C, Ps1};
        _ -> {var, "_"}
    end;
prune(_, _, _) -> {var, "_"}.

gen_value(Defs, T) ->
    ?SIZED(N, gen_value1(N, expand_defs(Defs, T))).

gen_value1(_, bool) -> bool();
gen_value1(_, int)  -> int();
gen_value1(_, string) -> elements(strings());
gen_value1(N, {alias_t, Type}) -> gen_value1(N, Type);
gen_value1(N, {record_t, _, Fields}) ->
    gen_value1(N, {tuple, [T || {_, T} <- Fields]});
gen_value1(N, {variant_t, _, Cons}) ->
    ?LET(I, choose(0, length(Cons) - 1),
    begin
        Arities   = [length(As) || {_, As} <- Cons],
        {_, Args} = lists:nth(I + 1, Cons),
        {variant, Arities, I, gen_value1(N, {tuple, Args})}
    end);
gen_value1(N, {list, T}) ->
    N1 = N div type_size(T),
    ?LET(L, choose(0, N1),
    eqc_gen:list(L, gen_value1(N div max(1, L), T)));
gen_value1(N, {tuple, Ts}) ->
    eqc_gen:fmap(fun list_to_tuple/1, [gen_value1(N, T) || T <- Ts]).

type_size(T) when is_atom(T)    -> 1;
type_size({list, _})            -> 1;
type_size({tuple, Ts})          -> 1 + type_size(Ts);
type_size({record_t, _, Fs})    -> 1 + type_size([T || {_, T} <- Fs]);
type_size({variant_t, _, Cons}) -> 1 + lists:max([type_size(Ts) || {_, Ts} <- Cons]);
type_size(Ts) when is_list(Ts)  -> lists:sum([ type_size(T) || T <- Ts ]).

gen_expr(Vars, Type) ->
    ?SIZED(N, gen_expr(Vars, Type, N)).

gen_expr(Vars, Type, N) ->
    case [ X || {X, T} <- Vars, T == Type ] of
        [] -> gen_expr1(Vars, Type, N);
        Xs -> weighted_default({2, {var, elements(Xs)}}, {1, gen_expr1(Vars, Type, N)})
    end.

gen_expr1(_, bool, _) -> {bool, bool()};
gen_expr1(_, int, _) -> {int, nat()};  %% TODO: int()?
gen_expr1(_, string, _) -> {string, elements(strings())};
gen_expr1(Vars, {tuple, Types}, N) ->
    ?LET(Es, [gen_expr(Vars, T, N) || T <- Types],
    {tuple, Es});
gen_expr1(Vars, {list, T}, N) ->
    ?LAZY(
    frequency(
      [{1, {list, []}}] ++
      [{2, {'::', gen_expr(Vars, T, N div 2), gen_expr(Vars, {list, T}, N div 2)}}
        || N > 0] ++
      [{2, {list, ?LET(L, choose(1, 3),
                  vector(L, gen_expr(Vars, T, N div L - 1)))}}
        || N > 0]
    ));
gen_expr1(Vars, {record_t, _, Fields}, N) ->
    {Xs, Ts} = lists:unzip(Fields),
    ?LET(Es, [gen_expr(Vars, T, N) || T <- Ts],
         {record, lists:zip(Xs, Es)});
gen_expr1(Vars, {variant_t, _, Cons}, N) ->
    ?LET({C, Args}, elements(Cons),
    {con, C, [gen_expr(Vars, T, N) || T <- Args]}).

%% -- Pretty printing --------------------------------------------------------

pp_type(bool)        -> "bool";
pp_type(int)         -> "int";
pp_type(string)      -> "string";
pp_type({id, X})     -> X;
pp_type({list, T})   -> "list(" ++ pp_type(T) ++ ")";
pp_type({tuple, []}) -> "unit";
pp_type({tuple, Ts}) -> "(" ++ string:join([pp_type(T) || T <- Ts], " * ") ++ ")";
pp_type({args, Ts})  -> "(" ++ string:join([pp_type(T) || T <- Ts], ", ") ++ ")".

pp_pat({var, X})    -> X;
pp_pat({bool, B})   -> atom_to_list(B);
pp_pat({int, N})    -> integer_to_list(N);
pp_pat({string, <<>>}) -> "\"\"";
pp_pat({string, S}) -> io_lib:format("~p", [binary_to_list(S)]);
pp_pat({list, Ps})  -> "[" ++ string:join([pp_pat(P) || P <- Ps], ", ") ++ "]";
pp_pat({'::', P, Q}) -> "(" ++ pp_pat(P) ++ " :: " ++ pp_pat(Q) ++ ")";
pp_pat({tuple, Ps}) -> "(" ++ string:join([pp_pat(P) || P <- Ps], ", ") ++ ")";
pp_pat({con, C, []}) -> C;
pp_pat({con, C, Ps}) -> C ++ pp_pat({tuple, Ps});
pp_pat({record, Ps}) -> "{" ++ string:join([[X, " = ", pp_pat(P)] || {X, P} <- Ps], ", ") ++ "}".

pp_def({type_def, Name, {alias_t, Type}}) ->
    ["type ", Name, " = ", pp_type(Type)];
pp_def({type_def, Name, {record_t, _, Fields}}) ->
    ["record ", Name, " = {", string:join([[X, " : ", pp_type(T)] || {X, T} <- Fields], ", "), "}"];
pp_def({type_def, Name, {variant_t, _, Cons}}) ->
    ["datatype ", Name, " = ", string:join([[Con, [pp_type({args, Args}) || Args /= []]] || {Con, Args} <- Cons], " | ")].

pp_expr(E) -> pp_pat(E).

expand_defs(_, int) -> int;
expand_defs(_, string) -> string;
expand_defs(_, bool) -> bool;
expand_defs(Defs, {id, X}) ->
    {type_def, _, Def} = lists:keyfind(X, 2, Defs),
    expand_defs(Defs, Def);
expand_defs(Defs, {alias_t, Type}) -> expand_defs(Defs, Type);
expand_defs(Defs, {record_t, R, Fields}) ->
    {record_t, R, [{X, expand_defs(Defs, T)} || {X, T} <- Fields]};
expand_defs(Defs, {variant_t, D, Cons}) ->
    {variant_t, D, [{C, [expand_defs(Defs, T) || T <- Args]} || {C, Args} <- Cons]};
expand_defs(Defs, {list, T}) -> {list, expand_defs(Defs, T)};
expand_defs(Defs, {tuple, Ts}) ->
    {tuple, [expand_defs(Defs, T) || T <- Ts]}.

vars_of_type(S, T, P) ->
    [ X || {X, R} <- pat_vars(T, P), S == R ].

pat_vars(T, {var, X})    -> [{X, T} || X /= "_"];
pat_vars(_, {bool, _})   -> [];
pat_vars(_, {int, _})    -> [];
pat_vars(_, {string, _}) -> [];
pat_vars({list, T}, {list, Ps}) ->
    lists:append([pat_vars(T, P) || P <- Ps]);
pat_vars({list, T}, {'::', P, Q}) ->
    pat_vars(T, P) ++ pat_vars({list, T}, Q);
pat_vars({tuple, Ts}, {tuple, Ps})  ->
    [ X || {T, P} <- lists:zip(Ts, Ps),
           X      <- pat_vars(T, P) ];
pat_vars({variant_t, _, Cons}, {con, C, Ps}) ->
    case lists:keyfind(C, 1, Cons) of
        {_, Ts} -> pat_vars({tuple, Ts}, {tuple, Ps});
        false -> error({wtf, Cons, C, Ps})
    end;
pat_vars({record_t, _, Ts}, {record, Ps}) ->
    [Z || {X, P} <- Ps, {Y, T} <- Ts, X == Y,
          Z      <- pat_vars(T, P)].

%% -- Interpretation ---------------------------------------------------------

match_clauses(_Type, [], _Val) -> false;
match_clauses(Type, [{Pat, Body} | Clauses], Val) ->
    case match(Type, Pat, Val) of
        false -> match_clauses(Type, Clauses, Val);
        Sub   -> {Sub, Body}
    end.

match(Type, Pat, Val) ->
    try match1(Type, Pat, Val)
    catch throw:no_match -> false
    end.

match1(_, {var, "_"}, _)  -> [];
match1(_, {var, X}, V)    -> [{X, V}];
match1(_, {bool, B}, B)   -> [];
match1(_, {int,  N}, N)   -> [];
match1(_, {string, S}, S) -> [];
match1({list, T}, {list, Ps}, Xs) when length(Xs) == length(Ps) ->
    lists:append([match1(T, P, X) || {P, X} <- lists:zip(Ps, Xs)]);
match1({list, Type}, {'::', P, Q}, [H | T]) ->
    match1(Type, P, H) ++ match1({list, Type}, Q, T);
match1({variant_t, _, Cons}, {con, C, Ps}, {variant, _, I, Vs}) ->
    case lists:nth(I + 1, Cons) of
        {C, Ts} -> match1({tuple, Ts}, {tuple, Ps}, Vs);
        _ -> throw(no_match)
    end;
match1({tuple, Ts}, {tuple, Ps}, V) ->
    lists:append(lists:zipwith3(fun match1/3, Ts, Ps, tuple_to_list(V)));
match1({record_t, _, Fs}, {record, Ps}, V) ->
    FVs = [ {X, T, U} || {{X, T}, U} <- lists:zip(Fs, tuple_to_list(V)) ],
    lists:append([ begin
                       {_, T, U} = lists:keyfind(X, 1, FVs),
                       match1(T, P, U)
                   end || {X, P} <- Ps ]);
match1(_, _, _) -> throw(no_match).

eval(Env, _, {var, X})  -> maps:get(X, Env);
eval(_, _,   {int, N})  -> N;
eval(_, _,   {bool, B}) -> B;
eval(_, _,   {string, S}) -> S;
eval(Env, {tuple, Ts}, {tuple, Es}) ->
    list_to_tuple([eval(Env, T, E) || {T, E} <- lists:zip(Ts, Es)]);
eval(Env, {list, T}, {list, Es}) ->
    [eval(Env, T, E) || E <- Es];
eval(Env, {list, T}, {'::', Hd, Tl}) ->
    [eval(Env, T, Hd) | eval(Env, {list, T}, Tl)];
eval(Env, {record_t, _, Fields}, {record, Es}) ->
    list_to_tuple([ eval(Env, T, proplists:get_value(X, Es))
                    || {X, T} <- Fields ]);
eval(Env, {variant_t, _, Cons}, {con, C, Es}) ->
    Size = [ length(Ts) || {_, Ts} <- Cons ],
    [{Tag, Ts}] = [ {I - 1, Ts} || {I, {C1, Ts}} <- ixs(Cons), C1 == C ],
    {variant, Size, Tag, list_to_tuple([eval(Env, T, E) || {T, E} <- lists:zip(Ts, Es)])};
eval(_Env, T, E) -> {todo, T, E}.

untup({tuple, T}) ->
    list_to_tuple(untup(tuple_to_list(T)));
untup({variant, Ar, I, Args}) ->
    {variant, Ar, I, list_to_tuple(untup(tuple_to_list(Args)))};
untup([H | T]) ->
    [untup(H) | untup(T)];
untup(X) -> X.

%% -- Properties -------------------------------------------------------------

pp_fun(Defs, {Args, CaseType, Type, Expr, Clauses}) -> lists:flatten(
    ["contract Test =\n",
     [["  ", pp_def(Def), "\n"] || Def <- Defs],
     "  entrypoint test(", string:join([[X, " : ", pp_type(T)] || {X, T} <- Args], ", "),
                    ") : ", pp_type(Type), " =\n",
     "    switch(", pp_expr(Expr), " : ", pp_type(CaseType), ")\n",
     [ ["      ", pp_pat(Pat), " => ", pp_expr(Body), "\n"]
       || {Pat, Body} <- Clauses ]]).

gen_clause(CaseType, ResType) ->
    ?LET(Pat, gen_pat(CaseType),
    ?LET(Body, gen_expr(pat_vars(CaseType, Pat), ResType),
    return({Pat, Body}))).

gen_fun(Defs) ->
    ?LET([ResType, CaseType | ArgTypes], ?SUCHTHAT(Ts, eqc_gen:list(6, gen_type(mk_env(Defs))), length(Ts) >= 2),
    begin
        Vars  = [ {"arg" ++ integer_to_list(I), T} || {I, T} <- ixs(ArgTypes) ],
        VarsE = [ {X, expand_defs(Defs, T)} || {X, T} <- Vars ],
        CaseTypeE = expand_defs(Defs, CaseType),
        ResTypeE  = expand_defs(Defs, ResType),
        ?LET(Expr, gen_expr(VarsE, CaseTypeE),
        ?LET(Clauses, non_empty(eqc_gen:list(5, gen_clause(CaseTypeE, ResTypeE))),
            return({Vars, CaseType, ResType, Expr, Clauses})))
    end).

interpret_fun(Defs, {Vars, CaseType, ResType, Expr, Clauses}, Args) ->
    CaseType1 = expand_defs(Defs, CaseType),
    ResType1  = expand_defs(Defs, ResType),
    Env       = maps:from_list([ {X, V} || {{X, _}, V} <- lists:zip(Vars, Args) ]),
    CaseVal   = eval(Env, CaseType1, Expr),
    case match_clauses(CaseType1, Clauses, CaseVal) of
        false        -> {error, "Incomplete patterns"};
        {Env1, Body} -> eval(maps:merge(Env, maps:from_list(Env1)), ResType1, Body)
    end.

prop_fun() ->
    in_parallel(
    ?LET(Verbose, parameter(verbose, false),
    ?FORALL(Defs, gen_typedefs(),
    ?FORALL({Args, _CaseType, _Type, _Expr, _Clauses} = Fun, gen_fun(Defs),
    ?FORALL(Vals, eqc_gen:list(10, [gen_value(Defs, T) || {_, T} <- Args]),
    begin
        Contract = pp_fun(Defs, Fun),
        ?WHENFAIL(eqc:format("// Contract\n~s\n", [Contract]),
        ?TIMEOUT(60000,
        case catch compile_contract(Contract, [{debug, all} || Verbose]) of
            Compiled when is_tuple(Compiled), element(1, Compiled) == fcode ->
                ?WHENFAIL([eqc:format("// Compiled\n~s\n", [aeb_fate_asm:pp(Compiled)]) || Verbose],
                begin
                    Expect   = [ interpret_fun(Defs, Fun, Val) || Val <- Vals ],
                    Results  = [ untup(run(Compiled, <<"test">>, <<"test">>, Val)) || Val <- Vals ],
                    Tag = fun({error, _}) -> error; (_) -> value end,
                    aggregate(lists:map(Tag, Results),
                        equals(Results, Expect))
                end);
            Err -> equals(Err, ok)
        end))
    end))))).

ixs(Xs) -> lists:zip(lists:seq(1, length(Xs)), Xs).
