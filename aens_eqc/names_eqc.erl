%%% @author Thomas Arts <thomas@SpaceGrey.local>
%%% @copyright (C) 2019, Thomas Arts
%%% @doc
%%%
%%% @end
%%% Created : 15 Aug 2019 by Thomas Arts <thomas@SpaceGrey.local>

-module(names_eqc).

-include_lib("eqc/include/eqc.hrl").

-compile([export_all, nowarn_export_all]).



%% old Fortuna code:

name_hash(NameAscii) ->
    Labels = binary:split(NameAscii, <<".">>, [global]),
    hash_labels(lists:reverse(Labels)).

hash_labels([]) ->
    empty_hash();
hash_labels([Label | Rest]) ->
    LabelHash = hash(Label),
    RestHash = hash_labels(Rest),
    hash(<<RestHash/binary, LabelHash/binary>>).

empty_hash() ->
    <<0:32/unit:8>>.

hash(Bin) ->
    aec_hash:hash(aens, Bin).

prop_legacy() ->
    ?FORALL(Strings, list(utf8()),
            begin
                Name = iolist_to_binary(lists:join(".", Strings)),
                OldHash = (catch {ok, name_hash(Name)}),
                NewHash = (catch {ok, aens_hash:name_hash(Name)}),
                ?WHENFAIL(eqc:format("old hash: ~p\nnew hash: ~p\n",
                                     [OldHash, NewHash]),
                          case {OldHash, NewHash} of
                              {{ok, H1}, {ok, H2}} -> collect(ok, true);
                              {{ok, _}, NewHash} -> false;
                              {_, {ok, _}} -> false;
                              _ -> collect(error, true) %% both raise exception
                          end)
            end).
