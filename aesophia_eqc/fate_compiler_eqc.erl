%%% File        : fate_compiler_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 8 Apr 2019 by Ulf Norell
-module(fate_compiler_eqc).

-compile([export_all, nowarn_export_all]).

-include_lib("eqc/include/eqc.hrl").

%% -- Compiling and running --------------------------------------------------

run(Chain, Contract, Function, Arguments) ->
    try
        {ok, #{ accumulator := Result }} = aefa_fate:run(make_call(Contract, Function, Arguments), Chain),
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

setup_chain(Code) ->
    #{ contracts => #{<<"test">> => Code} }.

make_call(Contract, Function, Arguments) ->
    EncArgs  = list_to_tuple([aeb_fate_data:encode(A) || A <- Arguments]),
    Calldata = {tuple, {Function, {tuple, EncArgs}}},
    #{ contract => Contract,
       call => aeb_fate_encoding:serialize(Calldata) }.

%% -- Generators -------------------------------------------------------------

gen_type() ->
    ?SIZED(N, gen_type(N)).

gen_type(0) -> bool;
gen_type(N) ->
    ?LAZY(frequency(
      [{1, gen_type(0)},
       {3, ?LET(I, choose(2, 3),
           ?LETSHRINK(Ts, vector(I, gen_type(N div I)),
             {tuple, Ts}))}])).

gen_subtype(bool) -> bool;
gen_subtype(T = {tuple, Ts}) ->
    weighted_default({3, ?LET(S, elements(Ts), gen_subtype(S))},
                     {1, return(T)}).

gen_var() ->
    {var, elements(["_", "x", "y", "z"])}.

gen_pat(Type) ->
    ?LET(Pat, gen_pat1(Type),
         freshen(Pat)).

gen_pat1(Type) ->
    weighted_default( {1, gen_var()}, {2, gen_pat2(Type)}).


gen_pat2(bool) -> {bool, bool()};
gen_pat2({tuple, Ts}) -> {tuple, [gen_pat1(T) || T <- Ts]}.

freshen(Pat) ->
    {_, Pat1} = freshen([], Pat),
    Pat1.

freshen(Taken, {var, X}) ->
    {Taken1, Y} = fresh(Taken, X),
    {Taken1, {var, Y}};
freshen(Taken, {bool, _} = P) ->
    {Taken, P};
freshen(Taken, {tuple, []}) ->
    {Taken, {tuple, []}};
freshen(Taken, {tuple, [P | Ps]}) ->
    {Taken1, P1}           = freshen(Taken, P),
    {Taken2, {tuple, Ps1}} = freshen(Taken1, {tuple, Ps}),
    {Taken2, {tuple, [P1 | Ps1]}}.

fresh(Taken, "_") -> {Taken, "_"};
fresh(Taken, X)   -> fresh(Taken, X, 0).

fresh(Taken, X, Suf) ->
    X1 = lists:concat([X | [Suf || Suf > 0]]),
    case lists:member(X1, Taken) of
        false -> {[X1 | Taken], X1};
        true  -> fresh(Taken, X, Suf + 1)
    end.

gen_fun() ->
    ?LET(TypeBox, seal(gen_type()),
    ?LET({Type, Pats}, {open(TypeBox), non_empty(eqc_gen:list(5, gen_pat(peek(TypeBox))))},
        {Type, [prune(Type, Pat) || Pat <- Pats]})).

prune(bool, {tuple, _})      -> {var, "_"};
prune({tuple, _}, {bool, _}) -> {var, "_"};
prune({tuple, Ts}, {tuple, Ps}) ->
    {Ts1, Ps1} =
        case length(Ts) - length(Ps) of
            0 -> {Ts, Ps};
            N when N < 0 -> {Ts, lists:sublist(Ps, length(Ts))};
            N when N > 0 -> {Ts, Ps ++ lists:duplicate(N, {var, "_"})}
        end,
    {tuple, lists:zipwith(fun prune/2, Ts1, Ps1)};
prune(_, P) -> P.

gen_value(bool) -> bool();
gen_value({tuple, Ts}) ->
    eqc_gen:fmap(fun list_to_tuple/1, [gen_value(T) || T <- Ts]).

%% -- Pretty printing --------------------------------------------------------

pp_type(bool)        -> "bool";
pp_type({tuple, Ts}) -> "(" ++ string:join([pp_type(T) || T <- Ts], ", ") ++ ")".

pp_pat({var, X})    -> X;
pp_pat({bool, B})   -> atom_to_list(B);
pp_pat({tuple, Ps}) -> "(" ++ string:join([pp_pat(P) || P <- Ps], ", ") ++ ")".

body(Type, Subtype, I, Pat) ->
    lists:concat(["(", I, ", a, [", string:join(vars_of_type(Subtype, Type, Pat), ", "), "])"]).

vars_of_type(T, T, {var, X}) when X /= "_" -> [X];
vars_of_type(_, _, {var, _})               -> [];
vars_of_type(_, _, {bool, _})              -> [];
vars_of_type(S, {tuple, Ts}, {tuple, Ps})  ->
    [ X || {T, P} <- lists:zip(Ts, Ps),
           X      <- vars_of_type(S, T, P) ].

mk_contract(Type, Subtype, Pats) -> lists:flatten(
    ["contract Test =\n",
     "  function test(a : ", pp_type(Type), ") : (int, ", pp_type(Type), ", list(", pp_type(Subtype), ")) =\n",
     "    switch(a)\n",
     [ ["      ", pp_pat(Pat), " => ", body(Type, Subtype, I, Pat), "\n"]
       || {I, Pat} <- lists:zip(lists:seq(1, length(Pats)), Pats) ]]).

%% -- Interpretation ---------------------------------------------------------

match(Pat, Val) ->
    try match1(Pat, Val)
    catch throw:no_match -> false
    end.

match1({var, "_"}, _)  -> [];
match1({var, _}, V)    -> [V];
match1({bool, B}, B)   -> [];
match1({bool, _}, _)   -> throw(no_match);
match1({tuple, Ps}, V) ->
    lists:append(lists:zipwith(fun match1/2, Ps, tuple_to_list(V))).

interpret(Pats, Subtype, Val) ->
    interpret(1, Subtype, Pats, Val).

interpret(_, _, [], _Val) -> {error, abort};
interpret(I, Subtype, [Pat | Pats], Val) ->
    case match(Pat, Val) of
        false -> interpret(I + 1, Subtype, Pats, Val);
        Vars  -> {I, Val, [V || V <- Vars, has_type(Subtype, V)]}
    end.

has_type(bool, V)        -> lists:member(V, [false, true]);
has_type({tuple, Ts}, V) ->
    is_tuple(V) andalso tuple_size(V) == length(Ts) andalso
    lists:all(fun({T, X}) -> has_type(T, X) end,
              lists:zip(Ts, tuple_to_list(V))).

untup({tuple, T}) ->
    list_to_tuple(untup(tuple_to_list(T)));
untup([H | T]) ->
    [untup(H) | untup(T)];
untup(X) -> X.

%% -- Properties -------------------------------------------------------------

prop_compile() ->
    ?LET(Verbose, parameter(verbose, false),
    ?FORALL({Type, Pats}, gen_fun(),
    ?FORALL(Subtype, gen_subtype(Type),
    begin
        Contract = mk_contract(Type, Subtype, Pats),
        ?WHENFAIL(eqc:format("// Contract\n~s\n", [Contract]),
        case catch compile_contract(Contract, [{debug, all} || Verbose]) of
            Compiled when is_map(Compiled) ->
                ?FORALL(Vals, list(gen_value(Type)),
                begin
                    Chain   = setup_chain(Compiled),
                    Expect  = [ interpret(Pats, Subtype, Val) || Val <- Vals ],
                    Results = [ untup(run(Chain, <<"test">>, <<"test">>, [Val])) || Val <- Vals ],
                    equals(Results, Expect)
                end);
            Err -> equals(Err, ok)
        end)
    end))).

