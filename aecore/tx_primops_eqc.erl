%%% @author Thomas Arts <thomas@SpaceGrey.lan>
%%% @copyright (C) 2019, Thomas Arts
%%% @doc
%%%
%%%      Start a second epoch node with old code using something like:
%%%            ./rebar3 as test shell --sname oldepoch@localhost --apps ""
%%%            we need the test profile to assure that the cookie is set to aeternity_cookie
%%%            The test profile has a name and a cookie set in {dist_node, ...}
%%% @end
%%% Created : 23 Jan 2019 by Thomas Arts <thomas@SpaceGrey.lan>

-module(tx_primops_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).
-define(REMOTE_NODE, 'oldepoch@localhost').
-define(Patron, <<1, 1, 0:240>>).
-define(NAMEFRAGS, ["foo", "bar", "baz"]).

-record(account, {key, amount, nonce}).
-record(preclaim,{name, salt, height}).
-record(claim,{name, height}).

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{}.

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
    true.

precondition_common(_S, _Call) ->
    true.

postcondition_common(_S, _Call, _Res) ->
    true.

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
init_pre(S) ->
    not maps:is_key(accounts, S) and 
	not maps:is_key(preclaims, S) and
	not maps:is_key(claims, S) .

init_args(_S) ->
    %% CBE: tx_env only accepts one argument
    %%[aetx_env:tx_env(0, 1)].
    [aetx_env:tx_env(0)].

init(_) ->
    Trees = rpc(aec_trees, new_without_backend, [], fun hash_equal/2),
    EmptyAccountTree = rpc(aec_trees, accounts, [Trees]),
    Account = rpc(aec_accounts, new, [?Patron, 1200000]), 
    AccountTree = rpc(aec_accounts_trees, enter, [Account, EmptyAccountTree]),
    InitialTrees = rpc(aec_trees, set_accounts, [Trees, AccountTree], fun hash_equal/2),
    put(trees, InitialTrees),
    InitialTrees, 
    ok.

init_next(S, _Value, [TxEnv]) ->
    S#{tx_env => TxEnv, 
       accounts => [#account{key = ?Patron, amount = 1200000, nonce = 1}],
      preclaims => [],
      claims => []}.

%% --- Operation: mine ---
mine_pre(S) ->
    maps:is_key(accounts, S).

mine_args(#{tx_env := TxEnv}) ->
    Height = aetx_env:height(TxEnv),
    [Height].

mine_pre(#{tx_env := TxEnv}, [H]) ->
    aetx_env:height(TxEnv) == H.

mine_adapt(#{tx_env := TxEnv}, [_]) ->
    [aetx_env:height(TxEnv)];
mine_adapt(_, _) ->
    false.


mine(Height) ->
    Trees = get(trees),
    NewTrees = rpc(aec_trees, perform_pre_transformations, [Trees, Height + 1], fun hash_equal/2),
    put(trees, NewTrees),
    NewTrees,
    ok.

mine_next(#{tx_env := TxEnv} = S, _Value, [H]) ->
    S#{tx_env => aetx_env:set_height(TxEnv, H + 1)}.


%% --- Operation: spend ---
spend_pre(S) ->
    maps:is_key(accounts, S).

spend_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
    ?LET([{SenderTag, Sender}, {ReceiverTag, Receiver}], 
         vector(2, gen_account_pubkey(Accounts)),
         ?LET([Amount, Nonce], [nat(), oneof([0, 1, Sender#account.nonce, 100])],
              [Env, {SenderTag, Sender#account.key}, {ReceiverTag, Receiver#account.key},
               #{sender_id => aec_id:create(account, Sender#account.key), 
                 recipient_id => aec_id:create(account, Receiver#account.key), 
                 amount => Amount, 
                 fee => choose(1, 10), 
                 nonce => Nonce,
                 payload => utf8()}])),
         Args ++ [spend_valid(S, [lists:nth(2, Args), lists:last(Args)])]).

spend_pre(#{accounts := Accounts} = S, [Env, {SenderTag,Sender}, {ReceiverTag, Receiver}, Tx, Correct]) ->
    Valid = spend_valid(S, [{SenderTag,Sender}, Tx]),
    ReceiverOk = 
        case ReceiverTag of 
            new -> lists:keyfind(Receiver, #account.key, Accounts) == false;
            existing -> lists:keyfind(Receiver, #account.key, Accounts) =/= false andalso
                        %CBE: the following is needed to avoid an error
                        % in the old version
                        Receiver =/= Sender
        end,
    ReceiverOk andalso Correct == Valid andalso correct_height(S, Env).

spend_valid(#{accounts := Accounts}, [{_, Sender}, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(amount, Tx) + maps:get(fee, Tx) andalso
                maps:get(fee, Tx) >= 0   %% it seems fee == 0 does not return error
    end.

spend_adapt(#{tx_env := TxEnv} = S, [_, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, _Correct]) ->
    [TxEnv, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, 
     spend_valid(S, [{SenderTag, Sender}, Tx])];
spend_adapt(_, _) ->
    false.    

spend(Env, _Sender, _Receiver, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aec_spend_tx, new, [Tx]),
    {_, SpendTx} = aetx:specialize_type(AeTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aec_spend_tx, check, [SpendTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aec_spend_tx, process, [SpendTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aec_spend_tx, process, [SpendTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.


spend_next(#{accounts := Accounts} = S, _Value, 
           [_Env, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, Correct]) ->
    if Correct ->
            %% Classical mistake if sender and receiver are the same! Update carefully
            SAccount = lists:keyfind(Sender, #account.key, Accounts),
            RAccount = 
                case ReceiverTag of
                    new -> #account{key = Receiver, amount = 0, nonce = 1};
                    existing ->
                        lists:keyfind(Receiver, #account.key, Accounts)
                end,
            case Sender == Receiver of
                false ->
                    S#{accounts => 
                           (Accounts -- [RAccount, SAccount]) ++
                           [SAccount#account{amount = SAccount#account.amount - maps:get(amount,Tx) - maps:get(fee, Tx), 
                                             nonce = maps:get(nonce, Tx) + 1},
                            RAccount#account{amount = maps:get(amount,Tx) + RAccount#account.amount}]};  %% add to end of list
                true ->
                    S#{accounts => 
                           (Accounts -- [SAccount]) ++
                           [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx), 
                                             nonce = maps:get(nonce, Tx) + 1}]}
            end;
       not Correct -> 
            S
    end.

spend_post(_S, [_Env, _, _, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.



spend_features(S, [_Env, {_, Sender}, {_, Receiver}, Tx, Correct], Res) ->
    [{spend_accounts, length(maps:get(accounts, S))}, 
     {spend_correct, Correct}] ++
        [ spend_to_self || Sender == Receiver andalso Correct] ++
             [ {spend, zero} || maps:get(amount, Tx) == 0 andalso Correct] ++
             [ {spend, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [{spend_error, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: name_preclaim ---

name_preclaim_pre(S) ->
    maps:is_key(accounts, S).


%% @doc name_preclaim_pre/1 - Precondition for generation
-spec name_preclaim_pre(S :: eqc_statem:symbolic_state()) -> boolean().
name_preclaim_pre(S, [_Env, {SenderTag,Sender}, {Name,Salt}, Tx, Correct]) ->
    name_preclaim_valid(S, [{SenderTag,Sender}, {Name,Salt}, Tx]) == Correct.

name_preclaim_valid(#{accounts := Accounts} = S, 
		    [{_, Sender}, {Name,Salt},Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) andalso
		different_preclaim(S, {Name,Salt}) 
		
    end.

different_preclaim(#{preclaims := Preclaims},{Name,Salt} ) ->
    [present || #preclaim{name = N, salt = S} <- Preclaims, N == Name, S == Salt] == [].

%% @doc name_preclaim_args - Argument generator
-spec name_preclaim_args(S :: eqc_statem:symbolic_state()) -> eqc_gen:gen([term()]).
name_preclaim_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args,
	 ?LET([{SenderTag, Sender}, Name, Salt], 
	      [gen_account_pubkey(Accounts), gen_name(), choose(270,280)],
	      [Env, {SenderTag, Sender#account.key}, {Name, Salt},
	       #{account_id => aec_id:create(account, Sender#account.key),
		 fee => choose(1, 10), 
		 commitment_id => 
		     aec_id:create(commitment, 
				   aens_hash:commitment_hash(Name,Salt)),
		 nonce => oneof([0, 1, Sender#account.nonce, 100])}]), 
	 Args ++ [name_preclaim_valid(S,
				      [lists:nth(2, Args), 
				       lists:nth(3, Args), 
				       lists:last(Args)])]).


%% @doc name_preclaim - The actual operation
name_preclaim(Env, _Sender, {_Name,_Salt}, Tx, _Correct) ->
    Trees = get(trees),
    {ok, NTx} = rpc(aens_preclaim_tx, new, [Tx]),
    {_, NameTx} = aetx:specialize_type(NTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aens_preclaim_tx, check, [NameTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aens_preclaim_tx, process, [NameTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aens_preclaim_tx, process, [NameTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.


%% @doc name_preclaim_next - Next state function
-spec name_preclaim_next(S, Var, Args) -> NewS
    when S    :: eqc_statem:symbolic_state() | eqc_state:dynamic_state(),
         Var  :: eqc_statem:var() | term(),
         Args :: [term()],
         NewS :: eqc_statem:symbolic_state() | eqc_state:dynamic_state().
name_preclaim_next(#{tx_env := TxEnv,
		     accounts := Accounts, 
		     preclaims := Preclaims} = S,
		   _Value, [_Env,{_,Sender},{Name,Salt},Tx,Correct]) ->
    if Correct ->
	    SAccount = lists:keyfind(Sender, #account.key, Accounts),
	    S#{accounts => 
		   (Accounts -- [SAccount]) ++
		   [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx), 
				     nonce = maps:get(nonce, Tx) + 1}],
	       preclaims => 
		   Preclaims ++ [#preclaim{name = Name, 
					   salt = Salt,
					   height = aetx_env:height(TxEnv)}]};
       not Correct ->
	    S
    end.

%% @doc name_preclaim_post - Postcondition for name_preclaim
-spec name_preclaim_post(S, Args, Res) -> true | term()
    when S    :: eqc_state:dynamic_state(),
         Args :: [term()],
         Res  :: term().
name_preclaim_post(_S, [_Env,_Sender,{_Name,_Salt},_Tx,Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.

name_preclaim_features(#{claims := Claims} = S, 
		       [_Env, {_, _Sender}, {Name,_Salt}, _Tx, Correct], Res) ->
    [{name_preclaim_accounts, Res},{name_preclaim_correct, Correct}] ++
	[{claimed_names, Claims}] ++
	[{preclaim_claimed_name, Res} || lists:keymember(Name, #claim.name, Claims)].
    

%% --- Operation: claim ---
%% @doc claim_pre/1 - Precondition for generation
-spec claim_pre(S :: eqc_statem:symbolic_state()) -> boolean().
claim_pre(S) ->
    maps:is_key(accounts, S).

%% @doc claim_args - Argument generator
-spec claim_args(S :: eqc_statem:symbolic_state()) -> eqc_gen:gen([term()]).
claim_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args,
	 ?LET([Name, {SenderTag, Sender}], 
	      [gen_name(), gen_account_pubkey(Accounts)],
	      [Env, {SenderTag, Sender#account.key},
	       #{account_id => aec_id:create(account, Sender#account.key),
		 name => Name,
		 name_salt => choose(270,280),
		 fee => choose(1, 10), 
		 nonce => oneof([0, 1, Sender#account.nonce, 100])}]), 
	 Args ++ [claim_valid(S,  [lists:nth(2, Args), lists:last(Args)])]).


%% @doc claim_pre/2 - Precondition for claim
-spec claim_pre(S, Args) -> boolean()
    when S    :: eqc_statem:symbolic_state(),
         Args :: [term()].
claim_pre(S, [_Env, {SenderTag, Sender}, Tx, Correct]) ->
    claim_valid(S, [{SenderTag,Sender}, Tx]) == Correct.

claim_valid(#{accounts := Accounts} = S, [{_, Sender}, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) andalso
		case find_preclaim(S,Tx) of
		    false ->
			false;
		    Preclaim ->
			different_blocks(Preclaim,S) 
		end
		andalso valid_name(Tx) andalso 
                not already_claimed(S,Tx)

    end.


% a claim is preceed by a preclaim
find_preclaim(#{preclaims := Preclaims}, Tx) ->
    Name = maps:get(name,Tx),
    Salt = maps:get(name_salt,Tx),
    find_preclaim(Preclaims,Name,Salt).
find_preclaim([], _, _) ->
    false;
find_preclaim([Preclaim = #preclaim{name = N, salt = S} | Rest], Name, Salt) ->
    if N == Name, S == Salt ->
	    Preclaim;
       true ->
	    find_preclaim(Rest, Name, Salt)
    end.
% preclaim and claim are in different blocks
different_blocks(Preclaim, #{tx_env := TxEnv}) ->
    Delta = aec_governance:name_claim_preclaim_delta(),
    Preclaim#preclaim.height + Delta =< aetx_env:height(TxEnv).

% names may not have dots in between, only at the end (.test)
valid_name(Tx) ->
    case string:lexemes(maps:get(name,Tx),".") of
	[T,<<"test">>] ->
	    true;
	_ -> false
    end.

% 
already_claimed(#{claims := Claims}, Tx) ->
    [present || #claim{name = N} <- Claims, N == maps:get(name,Tx)] =/= [].

%% @doc claim - The actual operation
claim(Env, _Sender, Tx,_Correct) ->
    Trees = get(trees),
    {ok, NTx} = rpc(aens_claim_tx, new, [Tx]),
    {_, NameTx} = aetx:specialize_type(NTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aens_claim_tx, check, [NameTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aens_claim_tx, process, [NameTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aens_claim_tx, process, [NameTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.


%% @doc claim_next - Next state function
-spec claim_next(S, Var, Args) -> NewS
    when S    :: eqc_statem:symbolic_state() | eqc_state:dynamic_state(),
         Var  :: eqc_statem:var() | term(),
         Args :: [term()],
         NewS :: eqc_statem:symbolic_state() | eqc_state:dynamic_state().
claim_next(#{tx_env := TxEnv,
	      accounts := Accounts, 
	     claims := Claims} = S, 
	   _Value, [Env, {_, Sender}, Tx, Correct]) ->
    if Correct ->
	    SAccount = lists:keyfind(Sender, #account.key, Accounts),
	    S#{accounts => 
	    	   (Accounts -- [SAccount]) ++
	    	   [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx), 
	    			     nonce = maps:get(nonce, Tx) + 1}],
	      claims => 
		   Claims ++ [#claim{name = maps:get(name, Tx), 
				     height = aetx_env:height(TxEnv)}]};
       not Correct ->
	    S
    end.


%% @doc claim_post - Postcondition for claim
-spec claim_post(S, Args, Res) -> true | term()
    when S    :: eqc_state:dynamic_state(),
         Args :: [term()],
         Res  :: term().
claim_post(_S, [_Env, _Sender, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
	_ -> not Correct andalso valid_mismatch(Res)
    end.

claim_features(S, [_Env, {_, Sender}, Tx, Correct], Res) ->
    [{claim_result, Res},{claim_correct, Correct}] ++
	[{claim_name, maps:get(name,Tx)}].
    

%% -- Property ---------------------------------------------------------------
prop_tx_primops() ->
    ?FORALL(Cmds, commands(?MODULE),
    ?TIMEOUT(3000,
    begin
        %% io:format("Pinging ~p~n", [?REMOTE_NODE]),

        pong = net_adm:ping(?REMOTE_NODE),
        %% io:format("Start run test ~p~n", [Cmds]),

        {H, S, Res} = run_commands(Cmds),
        Height = 
            case maps:get(tx_env, S, undefined) of
                undefined -> 0;
                TxEnv -> aetx_env:height(TxEnv)
            end,
        %% io:format("Did run test"),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            aggregate(call_features(H),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok)))))
    end)).

bugs() -> bugs(10).

bugs(N) -> bugs(N, []).

bugs(Time, Bugs) ->
    more_bugs(eqc:testing_time(Time, prop_tx_primops()), 20, Bugs).


%% --- local helpers ------

strict_equal(X, Y) ->
     case X == Y of 
         true -> X; 
         false -> exit({different, X, Y}) 
     end.

hash_equal(X, Y) ->
     case {X, Y} of 
         {{ok, L}, {ok, R}} -> 
             case aec_trees:hash(L) == aec_trees:hash(R) of
                 true -> X;
                 false -> exit({hash_differs, X, Y})
             end;
         {E, E} -> E;
         _ -> exit({different, X, Y}) 
     end.
 
rpc(Module, Fun, Args) ->
    rpc(Module, Fun, Args, fun(X,Y) -> strict_equal(X, Y) end).

rpc(Module, Fun, Args, InterpretResult) ->
    Local = rpc:call(node(), Module, Fun, Args, 1000),
    Remote = rpc:call(?REMOTE_NODE, Module, Fun, Args, 1000),
    eq_rpc(Local, Remote, InterpretResult).

eq_rpc(Local, Remote, InterpretResult) ->
    case {Local, Remote} of
        {{badrpc, {'EXIT', {E1, _}}},{badrpc, {'EXIT', {E2, _}}}} when E1 == E2 ->
            Local;
        _ ->
            InterpretResult(Local, Remote)
    end.

valid_mismatch({'EXIT',{different, {error, account_nonce_too_low},
                        {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_nonce_too_high},
                         {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_nonce_too_high},
                         {error, multiple_namespaces}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_nonce_too_low},
                         {error, multiple_namespaces}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_not_found},
			 {error, multiple_namespaces}}}) -> true;
valid_mismatch({'EXIT', {different, {error, insufficient_funds},
			 {error, multiple_namespaces}}}) -> true;

valid_mismatch(_) -> false.

%% -- Generators -------------------------------------------------------------


gen_account_pubkey(Accounts) ->
    oneof([?LAZY({existing, elements(Accounts)}), 
           ?LAZY({new, #account{key = noshrink(binary(32)), amount = 0, nonce = 0 }})]).

unique_name(List) ->
    ?LET([W], 
         noshrink(?SUCHTHAT([Word], 
                            eqc_erlang_program:words(1), not lists:member(Word, List))), 
         W).

gen_name() ->
    ?LET(NFs, frequency([{1, non_empty(list(elements(?NAMEFRAGS)))}, 
    			 {9, [elements(?NAMEFRAGS)]}]),
    return(iolist_to_binary(lists:join(".",NFs ++ ["test"])))).
