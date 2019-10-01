%%% @author Thomas Arts <thomas@SpaceGrey.lan>
%%% @copyright (C) 2019, Thomas Arts
%%% @doc
%%%
%%% @end
%%% Created : 30 Sep 2019 by Thomas Arts <thomas@SpaceGrey.lan>

-module(aesc_fsm_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_component.hrl").

-compile([export_all, nowarn_export_all]).

%% -- State ------------------------------------------------------------------
initial_state() ->
    #{}.

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
    true.

precondition_common(_S, _Call) ->
    true.

%% postcondition_common(S, Call, Res) ->
%%     eq(Res, return_value(S, Call)). %% Check all return values

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
start_pre(_S) ->
    true.

start_args(_S) ->
    [#{}].

start(Arg) ->
    {ok, Pid} = aesc_fsm:start_link(Arg),
    unlink(Pid),
    register(sut, Pid),
    Pid.

start_callouts(_S, [Arg]) ->
    ?EMPTY.

start_next(S, _Value, _Args) ->
    S.

start_post(_S, _Args, Res) ->
    is_pid(Res).


%% --- ... more operations

%% -- Property ---------------------------------------------------------------
%% invariant(_S) ->
%% true.

weight(_S, start) -> 1;
weight(_S, _Cmd) -> 10.

prop_fsm() ->
    ?SETUP(
        fun() ->
                %% Setup mocking, etc.
                eqc_mocking:start_mocking(api_spec()),
                %% Return the teardwown function
                fun() -> ok end
        end,
    ?FORALL(Cmds, commands(?MODULE),
    begin
        %% stop the server if running
        {H, S, Res} = run_commands(Cmds),
        %% cleanup
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok)))
    end)).

%% -- API-spec ---------------------------------------------------------------
api_spec() ->
    #api_spec{ language = erlang, mocking = eqc_mocking,
               modules = [ lager_spec(), noise_layer_spec() ] }.

lager_spec() ->
    #api_module{ name = lager, fallback = lager_mock }.

noise_layer_spec() ->
    #api_module{
       name = aesc_session_noise,
       functions =
           [ #api_fun{ name = channel_open, arity = 2, matched = all, fallback = false}
           , #api_fun{ name = connect, arity = 3, matched = all, fallback = false}
           ] }.
