%%% @doc This module provides an in-memory store for Lager messages which can be
%%% used in place of the Lager application itself.
%%%
%%% By default all messages are ignored. If the OS environment variable
%%% `EQC_LAGER_MOCK` is set to `console` the logs will be printed to the console. If
%%% the OS environment variable `EQC_LAGER_MOCK` is set to `file` the logs will be
%%% printed to `eqc_lager_mock.log` by default, or the file configured by
%%% `EQC_LAGER_MOCK_FILE`.
%%%
%%% @end

-module(lager_mock).

-export([ start/0
        , debug/2
        , info/2
        , error/2
        , pr/2
        , print/0
        , init/0
        , stop/0
        ]).

%% ==================================================================
%% API

start() ->
    Pid = spawn(?MODULE, init, []),
    register(?MODULE, Pid),
    ok.

stop() ->
    ?MODULE ! stop,
    ok.

debug(Fmt, Args) ->
    log(debug, Fmt, Args).

info(Fmt, Args) ->
    log(info, Fmt, Args).

error(Fmt, Args) ->
    log(error, Fmt, Args).

pr(Term, _Mod) ->
    Term.

print() ->
    Me = self(),
    ?MODULE ! {print, Me},
    receive
        {print, Me, ok} ->
            ok
    after
        10000 ->
            io:format("lager mock print timeout~n")
    end,
    ok.

init() ->
    loop([]).

%% ==================================================================
%% Internal functions

loop(Logs) ->
    receive
        {log, Time, Level, Fmt, Args} ->
            Logs1 = [{Time, Level, Fmt, Args} | Logs],
            loop(Logs1);
        {print, Caller} ->
            case os:getenv("EQC_LAGER_MOCK") of
                "console" ->
                    print_to_console(Logs);
                "file" ->
                    File = os:getenv("EQC_LAGER_MOCK_FILE", "eqc_lager_mock.log"),
                    print_to_file(File, Logs);
                false ->
                    ok
            end,
            Caller ! {print, Caller, ok},
            loop(Logs);
        reset ->
            loop([]);
        stop ->
            ok
    end.

log(Level, Fmt, Args) ->
    Now = os:timestamp(),
    ?MODULE ! {log, Now, Level, Fmt, Args},
    ok.

print_to_console(Logs) ->
    print_logs(user, Logs).

print_to_file(File, Logs) ->
    % Ensure the file is empty when we write to it
    file:delete(File),
    {ok, Device} = file:open(File, [append]),
    print_logs(Device, Logs),
    ok = file:close(Device).

print_logs(Device, Logs) ->
    lists:map(
     fun({Time, Level, Fmt, Args}) ->
             Time1 = now_to_str(Time),
             io:format(Device, "~s lager_mock:~p - " ++ Fmt ++ "~n", [Time1, Level | Args])
     end, lists:reverse(Logs)),
    ok.

now_to_str(Time) ->
    {_, _, Ms} = Time,
    {{Y, M, D}, {H, Mi, S}} = calendar:now_to_local_time(Time),
    Args = [Y, M, D, H, Mi, S, Ms],
    lists:flatten(io_lib:format("~4..0w-~2..0w-~2..0wT~2..0w:~2..0w:~2..0w.~6..0w", Args)).
