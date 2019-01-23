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

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{}.

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
    [aec_trees:new(), aetx_env:tx_env(0, 1)].

init(_, _) ->
    ok.

init_next(S, _Value, [Trees, TxEnv]) ->
    S#{trees => Trees, tx_env => TxEnv}.

%% --- Operation: mine ---
mine_pre(S) ->
    maps:is_key(trees, S).

mine_args(#{trees := Trees, tx_env := TxEnv}) ->
    Height = aetx_env:height(TxEnv),
    {Local, Remote} = rpc(aec_trees, perform_pre_transformations, [Trees, Height + 1]),
    [Local, Remote, Height].

mine_pre(#{tx_env := TxEnv}, [_, _, H]) ->
    aetx_env:height(TxEnv) == H.

mine(Local, Remote, _Height) ->
    Local == Remote.

mine_next(#{tx_env := TxEnv} = S, _Value, [Local, _Remote, H]) ->
    S#{trees => Local, tx_env => aetx_env:set_height(TxEnv, H + 1)}.

mine_post(_S, [_, _, _], Bool) ->
    Bool.



%% --- ... more operations

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
    Remote =  rpc:call(?REMOTE_NODE, Module, Fun, Args),
    {Local, Remote}.
