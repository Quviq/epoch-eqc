%%% @doc This module provides an in-memory store for Lager messages which can be
%%% used in place of the Lager application itself.
%%%
%%% By default all messages are ignored. If the OS environment variable
%%% `LAGER_MOCK` is set to `console` the logs will be printed to the console. If
%%% the OS environment variable `LAGER_MOCK` is set to `file` the logs will be
%%% printed to `lager_mock.log` by default, or the file configured by
%%% `LAGER_MOCK_FILE`.
%%%
%%% @end

-module(lager_mock).

-export([ start/0
        , debug/2
        , info/2
        , error/2
        ]).

%% ==================================================================
%% API

start() ->
    ok.

debug(Fmt, Args) ->
    log(debug, Fmt, Args).

info(Fmt, Args) ->
    log(info, Fmt, Args).

error(Fmt, Args) ->
    log(error, Fmt, Args).

print() ->
    case os:getenv("LAGER_MOCK") of
        "console" ->
            print_console();
        "file" ->
            File = os:getenv("LAGER_MOCK_FILE", "lager_mock.log"),
            print_file(File)
    end.

%% ==================================================================
%% Internal functions

log(Level, Fmt, Args) ->
    ok.

print_console() ->
    ok.

print_file(File) ->
    ok.
