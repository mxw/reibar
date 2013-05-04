%
% ask.pl - Toplevel assertion and query loop.
%

:- use_module(dcg).
:- use_module(library(lists)).
:- ensure_loaded('evaluate.pl').
:- ensure_loaded('readLine.pl').
:- ensure_loaded('utils.pl').

%% input(-String)
%
% Get a string from the user, failing if it is empty.

input([H|T]) :- readLine([H|T]).

%% talk
%
% Prompts for a string and generates all interpretations for it.

talk :-
  input(String),
  sentence(String, _, Interp),
  format('Reduced:    ~p~n', [Interp]),
  notation(Interp, Simple),
  format('Simplified: ~p~n', [Simple]),
  talk.
