/* ------------------------------------------------------------------------
   Quantificational logic query evaluation

   Stuart Shieber
   CS187

   Evaluates queries in the quantificational logic notation generated
   by quantex-2part.pl.

   $Id: blocksqa.pl,v 1.1 2011/02/13 22:28:01 shieber Exp shieber $
   ------------------------------------------------------------------------ */

:- ensure_loaded('quantex-2part.pl').       % quantifer scoping

%%% eval(+Formula)
%%%
%%% Attempts to prove formula by extensionally evaluating qantifiers
%%% and using Prolog itself for atomic formulas.
%%%
%%% For example, consider: the(x^triangle(x), y^red(y)) (perhaps from
%%% "is the triangle red"). We take the restriction, replacing the
%%% object-level variable x with a fresh Prolog variable X, forming
%%% triangle(X). Then, find all X that satisfy triangle(X).  Verify
%%% that there is only one (because of the unqiueness  presupposition
%%% in "the"), say a. Then replace y with the found a forming
%%% red(a). Evaluate red(a).

eval(the(X^P, Y^Q)) :-
    !,
    simplesubst(P, X, Xvar, NewP),   % replace obj var with Prolog var
    findall(Xvar, eval(NewP), Xs),   % find all obj for restriction
    presuppose(Xs = [TheX], "uniqueness of 'the'"), % there should be only one
    simplesubst(Q, Y, TheX, NewQ),   % check that it matches the scope
    eval(NewQ).

eval(some(X^P, Y^Q)) :-
    !,
    simplesubst(P, X, Xvar, NewP),   % form restriction
    eval(NewP),                      % find something that satisfies
    simplesubst(Q, Y, Xvar, NewQ),   % check that it satisfies
    eval(NewQ).                      % the scope

eval(every(X^P, Y^Q)) :-
    !,
    simplesubst(P, X, Xvar, NewP),   % form restriction
    findall(Xvar, eval(NewP), Xs),   % find all that satisfy it
    simplesubst(Q, Y, Yvar, NewQ),   % check that they all satisfy
    all(Yvar, Xs, NewQ).             % the scope

eval(no(X^P, Y^Q)) :-
    !,
    simplesubst(P, X, Xvar, NewP),   % form restriction
    simplesubst(Q, Y, Xvar, NewQ),
    findall(Xvar, eval(and(NewP,NewQ)), []).   % find all that
                                     % satisfy it, checking
                                     % that there aren't any

eval(and(P, Q)) :-
    !,
    eval(P),                         % check that both branches
    eval(Q).                         % are satisfied

eval(Prop) :-
    call(Prop).                      % anything else, let
                                     % Prolog test it

%%% presuppose(+Goal, +Message)
%%%
%%% Goal holds or there is a presupposition failure, in which case
%%% fail reporting Message.

presuppose(Goal, _Msg) :-
    call(Goal),
    !.
presuppose(_Goal, Msg) :-
    format("Presupposition failure: ~s~n", [Msg]),
    fail.

%%% all(-Var, +Values, +Goal)
%%%
%%% Every instance of Goal (which is probably free in Var) generable
%%% by separately instantiating Var with one of the Values evaluates to
%%% true according to eval/1.

all(_Var, [], _Goal).
all(Var, [Val|Vals], Goal) :-
    \+ \+                   % without permanently instantiating
           (Var = Val,      % insert a val into Goal
        eval(Goal)),        % and check evaluation of the goal
    all(Var, Vals, Goal).   % check all other instantiations too

%%% simplesubst(Term, Var, SubTerm, New)
%%%
%%% New is Term with free occurrences of object variable Var (a Prolog
%%% constant) replaced by SubTerm.
%%%
%%% Should probably use subst/4 from betanf.pl for this.

simplesubst(PVar, _Var, _SubTerm, PVar) :-
    var(PVar),              % leave Prolog variables alone
    !.
simplesubst(Var, Var, SubTerm, SubTerm) :-  % replace occurrences of the variable
    !.

%% The rest go recursively through the terms, skipping bound
%% occurrences.

simplesubst([], _Var, _SubTerm, []) :-
    !.
simplesubst([First|Rest], Var, SubTerm, [NewFirst|NewRest]) :-
    !,
    simplesubst(First, Var, SubTerm, NewFirst),
    simplesubst(Rest,  Var, SubTerm, NewRest).
simplesubst(VarX^Scope, VarX, _, VarX^Scope) :- !.
simplesubst(VarX^Scope, Var, SubTerm, VarX^NewScope) :-
    !,
    simplesubst(Scope, Var, SubTerm, NewScope).
simplesubst(Term, Var, SubTerm, NewTerm) :-
    Term =.. [Functor | Args],
    Functor \== '^',            % not needed?
    simplesubst(Args, Var, SubTerm, NewArgs),
    NewTerm =.. [Functor|NewArgs].
