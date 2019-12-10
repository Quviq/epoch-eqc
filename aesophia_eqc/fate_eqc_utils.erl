%%% File        : fate_eqc_utils.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 11 Nov 2019 by Ulf Norell
-module(fate_eqc_utils).

-compile([export_all, nowarn_export_all]).

compile(File) ->
    compile(File, []).

compile(File, Options) ->
    Res = aeso_compiler:file(File, [{backend, fate} | Options]),
    ShortRes =
        case Res of
            {error, Errs} ->
                [io:format("~s\n", [aeso_errors:pp(Err)]) || Err <- Errs],
                error;
            {ok, #{ fate_code := FCode }} ->
                pp_fcode(FCode),
                ok
        end,
    case proplists:get_value(return_fcode, Options, false) of
        true -> Res;
        false -> ShortRes
    end.

pp_fcode(FCode) ->
  Sub    = aeb_fate_code:symbols(FCode),
  FCode1 = setelement(3, substitute(Sub, FCode), Sub),
  io:format("~s\n", [aeb_fate_asm:pp(FCode1)]).

substitute(Sub, X) ->
  NotFound = make_ref(),
  case maps:get(X, Sub, NotFound) of
    NotFound -> substitute1(Sub, X);
    Y        -> Y
  end.

substitute1(Sub, L) when is_list(L) -> [substitute(Sub, E) || E <- L];
substitute1(Sub, T) when is_tuple(T) ->
    list_to_tuple([ substitute(Sub, E) || E <- tuple_to_list(T) ]);
substitute1(Sub, M) when is_map(M) ->
    maps:from_list([ {substitute(Sub, K), substitute(Sub, V)}
                     || {K, V} <- maps:to_list(M) ]);
substitute1(_, X) -> X.

