/* ------------------------------------------------------------------------
   Lambda calculus representation utilities

   Stuart Shieber
   CS187

   10/15/02
   revised 2/9/11

   $Id: blocksqa.pl,v 1.1 2011/02/13 22:28:01 shieber Exp shieber $
   ------------------------------------------------------------------------ */

:- module(utils, [notation/2]).
:- use_module(library(lists)).
:- use_module(betanf).

%%% notation(+Input, -Output)
%%%
%%% Output is simplified term representation for the lambda calculus
%%% term Input, which uses @ as the application operator.
%%% Applications in Output are absorbed into function symbols applied
%%% to arguments where possible, and uncurried.  For example:
%%%
%%%    f@a@b@c    ===>  f(a,b,c)
%%%    f@a@(b@c)  ===>  f(a, b(c))
%%%    x^f@(y^b)  ===>  x^f(y^b)
%%%    (x^x)@b    ===>  (x^x)@b

notation(X^Y, X^NewY) :-
	notation(Y, NewY), !.
notation((X^P)@Q, (X^NewP)@NewQ) :-
	notation(P, NewP),
	notation(Q, NewQ), !.
notation(X@Y, Term) :-
	notation(X, NewX),
	notation(Y, NewY),
	compose(NewX, Functor, Args),
	append(Args, [NewY], NewArgs),
	compose(Term, Functor, NewArgs), !.
notation(X,X).

%%% compose(?Term, ?Functor, ?Args)
%%%
%%% Term is a term whose functor is Functor and arguments are Args.
%%% Can be used in modes +,-,- or -,+,+.

compose(Term, Functor, Args) :-
	 Term =.. [Functor|Args].
