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

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{accounts => []}.

%% -- Generators -------------------------------------------------------------

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
    not maps:is_key(trees, S).

init_args(_S) ->
    [aetx_env:tx_env(0, 1)].

init(_) ->
    Trees = rpc(aec_trees, new_without_backend, []),
    EmptyAccountTree = rpc(aec_trees, accounts, [Trees]),
    Account = rpc(aec_accounts, new, [?Patron, 1200000]), 
    AccountTree = rpc(aec_accounts_trees, enter, [Account, EmptyAccountTree]),
    rpc(aec_trees, set_accounts, [Trees, AccountTree]).

init_next(S, Value, [TxEnv]) ->
    S#{trees => Value, 
       tx_env => TxEnv, 
       accounts => [{?Patron, 1200000, 1}]}.

%% --- Operation: mine ---
mine_pre(S) ->
    maps:is_key(trees, S).

mine_args(#{trees := Trees, tx_env := TxEnv}) ->
    Height = aetx_env:height(TxEnv),
    [Trees, Height].

mine_pre(#{tx_env := TxEnv}, [_, H]) ->
    aetx_env:height(TxEnv) == H.

mine(Trees, Height) ->
    rpc(aec_trees, perform_pre_transformations, [Trees, Height + 1]).

mine_next(#{tx_env := TxEnv} = S, Value, [_, H]) ->
    S#{trees => Value, tx_env => aetx_env:set_height(TxEnv, H + 1)}.


%% --- Operation: spend ---
spend_pre(S) ->
    maps:is_key(trees, S).

spend_args(#{accounts := Accounts, trees := Trees, tx_env := Env}) ->
    ?LET([{Sender, _, Nonce}, {Receiver, _, _}], 
         vector(2, gen_account_pubkey(Accounts)), 
         [Trees, Env, 
          #{sender_id => aec_id:create(account, Sender), 
            recipient_id => aec_id:create(account, Receiver), 
            amount => nat(), 
            fee => choose(1, 100), 
            nonce => Nonce,
            payload => utf8()},
          lists:keymember(Sender, 1, Accounts)
         ]).

spend_pre(_S, [_Trees, _Env, _Tx, _]) ->
    true.

spend(Trees, Env, Tx, Correct) ->
    {ok, AeTx} = rpc(aec_spend_tx, new, [Tx]),
    {_CB, SpendTx} = aetx:specialize_callback(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aec_spend_tx, check, [SpendTx, Trees, Env]) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aec_spend_tx, process, [SpendTx, Ts, Env]);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aec_spend_tx, process, [SpendTx, Trees, Env]),
    eq_rpc(Local, Remote, Correct).

spend_next(S, Value, [_, _, _, Correct]) ->
    if Correct -> S#{trees => Value};
       not Correct -> S
    end.




%% -- Property ---------------------------------------------------------------
prop_tx_primops() ->
    ?FORALL(Cmds, commands(?MODULE),
    begin
        pong = net_adm:ping(?REMOTE_NODE),
        {H, S, Res} = run_commands(Cmds),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok)))
    end).

bugs() -> bugs(10).

bugs(N) -> bugs(N, []).

bugs(Time, Bugs) ->
    more_bugs(eqc:testing_time(Time, prop_tx_primops()), 20, Bugs).

rpc(Module, Fun, Args) ->
    Local = rpc:call(node(), Module, Fun, Args),
    Remote = rpc:call(?REMOTE_NODE, Module, Fun, Args),
    eq_rpc(Local, Remote, false).

eq_rpc(Local, Remote, Unwrap) ->
    case Local == Remote of
        true  ->
            case Local of
                {ok, Res} when Unwrap -> Res;
                _ when Unwrap -> exit({unexpected_failure, Local});
                _ -> Local
            end;
        false ->
            case {Local, Remote} of
                {{badrpc, {'EXIT', {E1, _}}},{badrpc, {'EXIT', {E2, _}}}} when E1 == E2 ->
                    %% The stack traces are different...
                    if Unwrap -> exit({unexpected_failure, Local, Remote});
                       not Unwrap -> Local
                    end;
                _ -> exit({different, Local, Remote})
            end
    end.
    
%% -- Generators -------------------------------------------------------------

gen_account_pubkey() ->
    {binary(32), 0, 0}.

gen_account_pubkey(Accounts) ->
    oneof(Accounts ++ [gen_account_pubkey()]).


