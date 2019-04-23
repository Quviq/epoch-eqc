%%% File        : fate_compiler_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 8 Apr 2019 by Ulf Norell
-module(fate_compiler_eqc).

-compile([export_all, nowarn_export_all]).

-include_lib("eqc/include/eqc.hrl").

%% -- Compiling and running --------------------------------------------------

run(Code, Contract, Function, Arguments) ->
    try
        Cache = cache(Code),
        Call  = make_call(Contract, Function, Arguments),
        Spec  = dummy_spec(),
        {ok, #{ accumulator := Result }} = aefa_fate:run_with_cache(Call, Spec, Cache),
        Result
    catch _:{error, op_not_implemented_yet} ->
        {error, abort}
    end.

compile_contract(Code) ->
    compile_contract(Code, []).

compile_contract(Code, Options) ->
    {ok, Ast} = aeso_parser:string(Code),
    TypedAst  = aeso_ast_infer_types:infer(Ast, Options),
    FCode     = aeso_ast_to_fcode:ast_to_fcode(TypedAst, Options),
    aeso_fcode_to_fate:compile(FCode, Options).

dummy_spec() ->
    #{ trees     => aec_trees:new_without_backend(),
       caller    => <<123:256>>,
       origin    => <<123:256>>,
       gas_price => 1,
       tx_env    => aetx_env:tx_env(1) }.

cache(Code) ->
    Key = aeb_fate_data:make_address(pad_contract_name(<<"test">>)),
    #{Key => Code}.

make_call(Contract, Function, Arguments) ->
    EncArgs  = list_to_tuple([aefate_test_utils:encode(A) || A <- Arguments]),
    Calldata = {tuple, {Function, {tuple, EncArgs}}},
    #{ contract => pad_contract_name(Contract),
       gas      => 1000000,
       call     => aeb_fate_encoding:serialize(Calldata) }.

pad_contract_name(Name) ->
    PadSize = 32 - byte_size(Name),
    iolist_to_binary([Name, lists:duplicate(PadSize, "_")]).

%% -- Generators -------------------------------------------------------------

ulist(Key, Val) ->
    ?LET(Xs, list({Key, seal(Val)}),
    begin
        Us = lists:usort(fun({X, _}, {Y, _}) -> X =< Y end, Xs),
        Xs1 = Xs -- (Xs -- Us),
        [{K, open(V)} || {K, V} <- Xs1]
    end).

gen_field_name() -> elements(["x", "y", "z"]).

gen_typedef(X, TEnv) ->
    oneof([{alias_t, ?SIZED(N, gen_type(TEnv, N div 10))},
           % variant_t
           {record_t, X, gen_fields(TEnv)}]).

gen_typename() ->
    gen_typename([]).

gen_typename(TEnv) ->
    ?SUCHTHAT(Name,
    ?LET({X, Suf}, {elements(["r", "s", "t"]),
                    choose(0, 5)},
        return(lists:concat([X] ++ [Suf || Suf > 0]))),
    not lists:member(Name, TEnv)).

gen_typedefs() ->
    ?LET(I, weighted_default({3, 0}, {1, choose(1, 3)}),
         gen_typedefs(I, [])).

gen_typedefs(0, _) -> [];
gen_typedefs(I, TEnv) ->
    ?LET(X, gen_typename(TEnv),
    [{type_def, X, gen_typedef(X, TEnv)}|
     gen_typedefs(I - 1, [X | TEnv])]).

gen_fields(TEnv) ->
    ulist(gen_field_name(), ?SIZED(N, gen_type(TEnv, N div 20))).

gen_type() -> gen_type([]).
gen_type(TEnv) ->
    ?SIZED(N, gen_type(TEnv, N div 5)).

gen_type(_, 0) -> elements([bool, int]);
gen_type(TEnv, N) ->
    ?LAZY(frequency(
      [{1, {id, elements(TEnv)}} || [] /= TEnv] ++
      [{1, gen_type(TEnv, 0)},
       {1, ?LETSHRINK([T], [gen_type(TEnv, N div 2)],
             {list, T})},
       {3, ?LET(I, choose(2, 3),
           ?LETSHRINK(Ts, vector(I, gen_type(TEnv, N div I)),
             {tuple, Ts}))}])).

gen_subtype(bool) -> bool;
gen_subtype(int) -> int;
gen_subtype(T = {id, _}) -> T;
gen_subtype({list, T}) ->
    weighted_default({3, gen_subtype(T)}, {1, return(T)});
gen_subtype(T = {tuple, Ts}) ->
    weighted_default({3, ?LET(S, elements(Ts), gen_subtype(S))},
                     {1, return(T)}).

gen_var() ->
    {var, elements(["_", "x", "y", "z"])}.

gen_pat(Defs, Type) ->
    ?LET(Pat, ?SIZED(N, gen_pat1(Defs, N, Type)),
         freshen(Pat)).

gen_pat1(Defs, N, Type) ->
    weighted_default( {1, gen_var()}, {2, gen_pat2(Defs, N, Type)}).


gen_pat2(_, _, int) -> {int, nat()};
gen_pat2(_, _, bool) -> {bool, bool()};
gen_pat2(Defs, N, {id, X}) ->
    {type_def, _, Def} = lists:keyfind(X, 2, Defs),
    gen_pat2(Defs, N, Def);
gen_pat2(Defs, N, {alias_t, Type}) -> gen_pat2(Defs, N, Type);
gen_pat2(_, _, {record_t, _, []})  -> {var, "_"};
gen_pat2(Defs, N, {record_t, _, Fields}) ->
    ?LET(Fs, non_empty(sublist(Fields)),
    ?LET(Fs1, shuffle(Fs),
        {record, [ {Y, gen_pat1(Defs, N, T)} || {Y, T} <- Fs1 ]}));
gen_pat2(Defs, N, {list, T}) ->
    ?LAZY(weighted_default({1, nil},
                           {2, {'::', gen_pat1(Defs, N div 3, T), gen_pat1(Defs, 2 * N div 2, {list, T})}}));
gen_pat2(Defs, N, {tuple, Ts}) -> {tuple, [gen_pat1(Defs, N, T) || T <- Ts]}.

freshen(Pat) ->
    {_, Pat1} = freshen([], Pat),
    Pat1.

freshen(Taken, {var, X}) ->
    {Taken1, Y} = fresh(Taken, X),
    {Taken1, {var, Y}};
freshen(Taken, {bool, _} = P)   -> {Taken, P};
freshen(Taken, {int, _} = P)    -> {Taken, P};
freshen(Taken, nil = P)         -> {Taken, P};
freshen(Taken, {record, []} = P) -> {Taken, P};
freshen(Taken, {record, [{X, P} | Fs]}) ->
    {Taken1, P1} = freshen(Taken, P),
    {Taken2, {record, Fs1}} = freshen(Taken1, {record, Fs}),
    {Taken2, {record, [{X, P1} | Fs1]}};
freshen(Taken, {tuple, []} = P) -> {Taken, P};
freshen(Taken, {tuple, [P | Ps]}) ->
    {Taken1, P1}           = freshen(Taken, P),
    {Taken2, {tuple, Ps1}} = freshen(Taken1, {tuple, Ps}),
    {Taken2, {tuple, [P1 | Ps1]}};
freshen(Taken, {'::', P, Q}) ->
    {Taken1, P1} = freshen(Taken, P),
    {Taken2, Q1} = freshen(Taken1, Q),
    {Taken2, {'::', P1, Q1}}.

fresh(Taken, "_") -> {Taken, "_"};
fresh(Taken, X)   -> fresh(Taken, X, 0).

fresh(Taken, X, Suf) ->
    X1 = lists:concat([X | [Suf || Suf > 0]]),
    case lists:member(X1, Taken) of
        false -> {[X1 | Taken], X1};
        true  -> fresh(Taken, X, Suf + 1)
    end.

gen_fun(Defs) ->
    TEnv = [X || {type_def, X, _} <- Defs],
    ?LET(TypeBox, seal(gen_type(TEnv)),
    ?LET({Type, Pats}, {open(TypeBox), non_empty(eqc_gen:list(5, gen_pat(Defs, peek(TypeBox))))},
        {Type, [prune(Defs, Type, Pat) || Pat <- Pats]})).

prune(_, _,    {var, _}  = P) -> P;
prune(_, bool, {bool, _} = P) -> P;
prune(_, int,  {int,  _} = P) -> P;
prune(_, {list, _}, nil = P) -> P;
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
prune(_, _, _) -> {var, "_"}.

gen_value(_, bool) -> bool();
gen_value(_, int)  -> int();
gen_value(Defs, {id, X}) ->
    {type_def, _, Def} = lists:keyfind(X, 2, Defs),
    case Def of
        {alias_t, Type}       -> gen_value(Defs, Type);
        {record_t, _, Fields} -> gen_value(Defs, {tuple, [T || {_, T} <- Fields]})
    end;
gen_value(Defs, {list, T}) -> list(gen_value(Defs, T));
gen_value(Defs, {tuple, Ts}) ->
    eqc_gen:fmap(fun list_to_tuple/1, [gen_value(Defs, T) || T <- Ts]).

%% -- Pretty printing --------------------------------------------------------

pp_type(bool)        -> "bool";
pp_type(int)         -> "int";
pp_type({id, X})     -> X;
pp_type({list, T})   -> "list(" ++ pp_type(T) ++ ")";
pp_type({tuple, Ts}) -> "(" ++ string:join([pp_type(T) || T <- Ts], ", ") ++ ")".

pp_pat({var, X})    -> X;
pp_pat({bool, B})   -> atom_to_list(B);
pp_pat({int, N})    -> integer_to_list(N);
pp_pat(nil)         -> "[]";
pp_pat({'::', P, Q}) -> "(" ++ pp_pat(P) ++ " :: " ++ pp_pat(Q) ++ ")";
pp_pat({tuple, Ps}) -> "(" ++ string:join([pp_pat(P) || P <- Ps], ", ") ++ ")";
pp_pat({record, Ps}) -> "{" ++ string:join([[X, " = ", pp_pat(P)] || {X, P} <- Ps], ", ") ++ "}".

pp_def({type_def, Name, {alias_t, Type}}) ->
    ["type ", Name, " = ", pp_type(Type)];
pp_def({type_def, Name, {record_t, _, Fields}}) ->
    ["record ", Name, " = {", string:join([[X, " : ", pp_type(T)] || {X, T} <- Fields], ", "), "}"].

body(Defs, Type, Subtype, I, Pat) ->
    Type1    = expand_defs(Defs, Type),
    Subtype1 = expand_defs(Defs, Subtype),
    lists:concat(["(", I, ", a, [", string:join(vars_of_type(Subtype1, Type1, Pat), ", "), "])"]).

expand_defs(_, int) -> int;
expand_defs(_, bool) -> bool;
expand_defs(Defs, {id, X}) ->
    {type_def, _, Def} = lists:keyfind(X, 2, Defs),
    expand_defs(Defs, Def);
expand_defs(Defs, {alias_t, Type}) -> expand_defs(Defs, Type);
expand_defs(Defs, {record_t, R, Fields}) ->
    {record_t, R, [{X, expand_defs(Defs, T)} || {X, T} <- Fields]};
expand_defs(Defs, {list, T}) -> {list, expand_defs(Defs, T)};
expand_defs(Defs, {tuple, Ts}) ->
    {tuple, [expand_defs(Defs, T) || T <- Ts]}.

vars_of_type(T, T, {var, X}) when X /= "_" -> [X];
vars_of_type(_, _, {var, _})               -> [];
vars_of_type(_, _, {bool, _})              -> [];
vars_of_type(_, _, {int, _})               -> [];
vars_of_type(_, _, nil)                    -> [];
vars_of_type(S, {list, T}, {'::', P, Q}) ->
    vars_of_type(S, T, P) ++ vars_of_type(S, {list, T}, Q);
vars_of_type(S, {tuple, Ts}, {tuple, Ps})  ->
    [ X || {T, P} <- lists:zip(Ts, Ps),
           X      <- vars_of_type(S, T, P) ];
vars_of_type(S, {record_t, _, Ts}, {record, Ps}) ->
    [Z || {X, P} <- Ps, {Y, T} <- Ts, X == Y,
          Z      <- vars_of_type(S, T, P)].

mk_contract(Defs, Type, Subtype, Pats) -> lists:flatten(
    ["contract Test =\n",
     [["  ", pp_def(Def), "\n"] || Def <- Defs],
     "  function test(a : ", pp_type(Type), ") : (int, ", pp_type(Type), ", list(", pp_type(Subtype), ")) =\n",
     "    switch(a)\n",
     [ ["      ", pp_pat(Pat), " => ", body(Defs, Type, Subtype, I, Pat), "\n"]
       || {I, Pat} <- lists:zip(lists:seq(1, length(Pats)), Pats) ]]).

%% -- Interpretation ---------------------------------------------------------

match(Type, Pat, Val) ->
    try match1(Type, Pat, Val)
    catch throw:no_match -> false
    end.

match1(_, {var, "_"}, _)  -> [];
match1(T, {var, _}, V)    -> [{V, T}];
match1(_, {bool, B}, B)   -> [];
match1(_, {int,  N}, N)   -> [];
match1(_, nil, [])           -> [];
match1({list, Type}, {'::', P, Q}, [H | T]) ->
    match1(Type, P, H) ++ match1({list, Type}, Q, T);
match1({tuple, Ts}, {tuple, Ps}, V) ->
    lists:append(lists:zipwith3(fun match1/3, Ts, Ps, tuple_to_list(V)));
match1({record_t, _, Fs}, {record, Ps}, V) ->
    lists:append([ match1(T, P, U)
                   || {X, P} <- Ps,
                      {{Y, T}, U} <- lists:zip(Fs, tuple_to_list(V)),
                      X == Y]);
match1(_, _, _) -> throw(no_match).

interpret(Pats, Type, Subtype, Val) ->
    interpret(1, Type, Subtype, Pats, Val).

interpret(_, _, _, [], _Val) -> {error, abort};
interpret(I, Type, Subtype, [Pat | Pats], Val) ->
    case match(Type, Pat, Val) of
        false -> interpret(I + 1, Type, Subtype, Pats, Val);
        Vars  -> {I, Val, [V || {V, T} <- Vars, T == Subtype]}
    end.

untup({tuple, T}) ->
    list_to_tuple(untup(tuple_to_list(T)));
untup([H | T]) ->
    [untup(H) | untup(T)];
untup(X) -> X.

%% -- Properties -------------------------------------------------------------

prop_compile() ->
    in_parallel(
    ?LET(Verbose, parameter(verbose, false),
    ?FORALL(Defs, gen_typedefs(),
    ?FORALL({Type, Pats}, gen_fun(Defs),
    ?FORALL(Subtype, gen_subtype(Type),
    ?FORALL(Vals, list(gen_value(Defs, Type)),
    begin
        Contract = mk_contract(Defs, Type, Subtype, Pats),
        ?WHENFAIL(eqc:format("// Contract\n~s\n", [Contract]),
        ?TIMEOUT(5000,
        case catch compile_contract(Contract, [{debug, all} || Verbose]) of
            Compiled when is_map(Compiled) ->
                begin
                    Type1    = expand_defs(Defs, Type),
                    Subtype1 = expand_defs(Defs, Subtype),
                    Expect   = [ interpret(Pats, Type1, Subtype1, Val) || Val <- Vals ],
                    Results  = [ untup(run(Compiled, <<"test">>, <<"test">>, [Val])) || Val <- Vals ],
                    Tag = fun({error, _}) -> error; (_) -> value end,
                    aggregate(lists:map(Tag, Results),
                        equals(Results, Expect))
                end;
            Err -> equals(Err, ok)
        end))
    end)))))).

