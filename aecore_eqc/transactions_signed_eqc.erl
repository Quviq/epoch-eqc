%%% @author Thomas Arts
%%% @doc Sign transactions for merge_statem
%%%
%%% @end
%%% Created : 2 Aug 2019 by Thomas Arts

-module(transactions_signed_eqc).

-include_lib("eqc/include/eqc.hrl").
%%-include_lib("eqc/include/eqc_merge_statem.hrl").
-import(eqc_statem, [more_commands/2, run_commands/1, check_command_names/2,
                     commands_length/1, call_features/1 ]).
-import(eqc_merge_statem, [ pretty_commands/4  %% Overwrite with specific pretty_commands
                    ]).

-compile([export_all, nowarn_export_all]).

models() ->
  [ txs_core_eqc, txs_oracles_eqc, txs_spend_eqc, txs_sign_eqc ].

call(S, {call, M, Cmd, Args}) ->
  CmdTx = list_to_atom(lists:concat([Cmd, "_tx"])),
  CmdCall = list_to_atom(lists:concat([Cmd, "_call"])),
  case lists:member({CmdTx, 2}, M:module_info(exports)) of
    true ->
      %% io:format("calling ~p ", [CmdTx]),
      case apply(M, CmdTx, [S, Args]) of
        {ok, Tx} ->
          %% io:format("-> ~p\n", [Tx]),
          case lists:member(txs_sign_eqc, models()) of
              false ->
                  apply_transaction(maps:get(height, S), Tx);
              true ->
                  %% io:format("Tx: ~p\n", [Tx]),
                  %% io:format("Accounts: ~p\n", [catch aetx:accounts(Tx)]),
                  %% io:format("Origin: ~p\n", [catch aetx:origin(Tx)]),
                  %% io:format("Signers: ~p\n", [catch aetx:signers(Tx, get(trees))]),
                  case aetx:signers(Tx, get(trees)) of
                      {ok, PubSigners} ->
                          PrivSigners = [ maps:get(Pub, maps:get(keys, S, #{}), <<"invalid">>) || Pub <- PubSigners],
                          Fault = maps:get(next_signing, S, correct),
                          Signers =
                              case Fault of
                                  correct -> PrivSigners;
                                  drop_first_signature -> tl(PrivSigners);
                                  drop_last_signature -> tl(lists:reverse(PrivSigners));
                                  replace_first ->
                                      ReplaceKey = lists:last(maps:values(maps:get(keys, S, #{})) -- [hd(PrivSigners)]),
                                      [ReplaceKey | tl(PrivSigners)];
                                  replace_last ->
                                      ReplaceKey = lists:last(maps:values(maps:get(keys, S, #{})) -- [hd(PrivSigners)]),
                                      [ReplaceKey | tl(lists:reverse(PrivSigners))]
                              end,
                          apply_transaction(Signers, maps:get(height, S), Tx);
                      AeTxErr ->
                          AeTxErr
                  end
          end;
        Error ->
          Error
      end;
    false ->
      case lists:member({CmdCall, 2}, M:module_info(exports)) of
        true ->
          %% io:format("calling ~p ", [CmdCall]),
          apply(M, CmdCall, [S, Args]);
        false ->
          %% io:format("calling ~p\n", [Cmd]),
          apply(M, Cmd, Args)
      end
  end.

%% -----

apply_transaction(Height, AeTx) ->
    %% io:format("Tx = ~p\n", [AeTx]),
    Env      = aetx_env:tx_env(Height),
    Trees    = get(trees),

    case aetx:process(AeTx, Trees, Env) of
        {ok, NewTrees, _NewEnv} ->
            put(trees, NewTrees),
            ok;
        Other ->
            Other
    end.

apply_transaction(Signers, Height, AeTx) ->
    Env      = aetx_env:tx_env(Height),
    Trees    = get(trees),
    %% io:format("Creating Binary Tx\n"),
    BinTx = aec_governance:add_network_id(aetx:serialize_to_binary(AeTx)),
    %% io:format("Creating Signatures ~p\n", [BinTx]),

    Signatures = [ enacl:sign_detached(BinTx, Signer) || Signer <- Signers ],
    io:format("Signatures: ~p\n", [Signers]),

    SignedTx = aetx_sign:new(AeTx, Signatures),
    %% When we use strict, we see errors returned, otherwise only invalid txs returned
    %% io:format("Created signed Tx"),
    case aec_trees:apply_txs_on_state_trees_strict([SignedTx], Trees, Env) of
        {ok, _ValidTxs, InvalidTxs, NewTrees, _} ->
            put(trees, NewTrees),
            case InvalidTxs of
                [] -> ok;
                _  -> {error, signatures}
            end;
        Other ->
            Other
    end.


%%% helper functions

%% Get this from the transction, such that it is model independent!
signers(F, Args) when F == extend_oracle ->
    [lists:nth(2, Args)];
signers(F, Args) when F == channel_create  ->
    [lists:nth(2, Args), lists:nth(3, Args)];
signers(response_oracle, Args) ->
    {_Sender, _Nonce, Oracle} = lists:nth(2, Args),
    [Oracle];
signers(F, Args) when F == channel_deposit; F == channel_withdraw;
                     F == channel_close_mutual; F == channel_close_solo;
                     F == channel_settle; F == channel_slash ->
    Party = lists:nth(3, Args),
    {Initiator, _, Responder} = lists:nth(2, Args),
    Sender = case Party of initiator -> Initiator; responder -> Responder end,
    case F of
        channel_close_solo -> [Sender];
        channel_slash -> [Sender];
        channel_settle -> [Sender];
        _ -> [Initiator, Responder]
    end;
signers(ns_update, Args) ->
    {_SenderTag, Sender} = lists:nth(3, Args),
    [Sender];
signers(_Kind, Args) ->
    io:format("Kind ~p ~p\n", [_Kind, Args]),
    {_SenderTag, Sender} = lists:nth(2, Args),
    [Sender].


signers(S, F, Args) ->
    %%TODO check that non of the signers is a GA account, because they need to sign differently
    [maps:get(Signer, maps:get(keys, S)) || Signer <- signers(F, Args) ].


%% -- Property ---------------------------------------------------------------

%% NOte that weight for sub model is still computed by that weight function.
%% weight for adding a new command should be organized in frequency in command generator

prop_txs() ->
    prop_txs(3).

prop_txs(Fork) ->
    propsetup(Fork,
    eqc:dont_print_counterexample(
    in_parallel(
    ?FORALL(Cmds, more_commands(5, eqc_merge_statem:merge_commands(?MODULE, models())),
    begin
        put(trees, undefined),
        {H, S, Res} = run_commands(Cmds),
        Height = maps:get(height, S, 0),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            features(call_features(H),
            stats(call_features(H),
                  pretty_commands(?MODULE, Cmds, {H, S, Res},
                                  Res == ok))))))
    end)))).



%% Terrrible. I need to know all Kinds before property runs to make this work: bleh.
stats(Features, Prop) ->
  {Atoms, Rest} = lists:partition(fun is_atom/1, Features),
  Kinds = lists:usort(lists:map(fun(T) -> element(1, T) end, Rest) ++ eqc_statem:apply({eqc_merge_statem, ?MODULE, models()}, all_command_names, [])),
  aggregate(with_title(atoms), Atoms,
     aggregate_feats(Kinds, Rest, Prop)).

aggregate_feats([], _, Prop) -> Prop;
aggregate_feats([Tag | Kinds], Features, Prop) ->
    {Tuples, Rest} = lists:partition(fun(X) -> element(1, X) == Tag end, Features),
    %% io:format("Tag ~p Tuples ~p\n",[Tag, Tuples]),
    aggregate(with_title(Tag), Tuples, aggregate_feats(Kinds, Rest, Prop)).

propsetup(Fork, Prop) ->
    ?SETUP(
    fun() ->
            _ = application:load(aecore),
            application:load(aesophia),  %% Since we do in_parallel, we may have a race in line 86 of aesophia_compiler
            %% compile_contracts(),
            HardForksTeardown = setup_hard_forks(#{<<"1">> => 0, <<"2">> => Fork, <<"3">> => 2*Fork, <<"4">> => 3*Fork}),
            DataDirTeardown = setup_data_dir(),
            fun() ->
                    DataDirTeardown(),
                    HardForksTeardown()
            end
    end, Prop).

setup_data_dir() ->
    %% make sure we can run in eqc/aecore_eqc
    {ok, Dir} = file:get_cwd(),
    %% Not asserting that configuration parameter is undefined so to ease experimenting in Erlang shell.
    case lists:reverse(filename:split(Dir)) of
        [_, "eqc" | _] ->
            application:set_env(setup, data_dir, "../../data");
        _ ->
            application:set_env(setup, data_dir, "data")
    end,
    fun() ->
            ok = application:unset_env(setup, data_dir)
    end.

setup_hard_forks(X) ->
    %% Not asserting that configuration parameter is undefined so to ease experimenting in Erlang shell.
    ok = application:set_env(aecore, hard_forks, X),
    fun() ->
            ok = application:unset_env(aecore, hard_forks)
    end.
