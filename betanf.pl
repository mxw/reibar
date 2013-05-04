%
% betanf.pl - Beta normal form reducer.
%
% Performs leftmost-outermost reduction to beta normal form of lambda terms
% represented as follows:
%
%   variables   represented as atoms or atom::index
%       x   x::1  x::2
%   application represented with infix @
%       p@x
%   abstraction represented with infix ^
%       x^x   x^(p@x)
%

:- module(betanf, [
     bnf/2,
     op(950,  yfx, @),    % application
     op(970,  xfy, ^),    % abstraction
     op(100,  xfx, ::)    % renamed variable
   ]).

:- use_module(library(lists)).


%------------------------------------------------------------------------------
%
%  Operator declarations.
%

%
% Representing terms.
%
:- op(950,  yfx, @).      % application
:- op(970,  xfy, ^).      % abstraction
:- op(100,  xfx, ::).     % renamed variable

%% is_var(+Var)
%
%  Holds if Var is a valid variable name, i.e., if it is an atom or atom::N.

is_var(X::_N) :- is_var(X).
is_var(X) :- atom(X).


%------------------------------------------------------------------------------
%
%  Reducer.
%

%% bnf(+Term, -ReducedTerm)
%
%  ReducedTerm is the beta normal form of Term.

bnf(E, T) :- reduce(E, T), E = T.
bnf(E, T) :- reduce(E, T_), E \= T_, bnf(T_, T).


%% reduce(+Term, -ReducedTerm)
%
%  Performs one reduction on a lambda term in normal order.

reduce(X, X) :- is_var(X).
reduce(X^E, X^E_) :- reduce(E, E_).
reduce((X^E1) @ E2, E) :- !, subst(E1, X, E2, E).

reduce(E1 @ E2, E1_ @ E2) :-
  reduce(E1, E1_),
  E1 \= E1_.

reduce(E1 @ E2, E1 @ E2_) :-
  reduce(E1, E1_),
  E1 = E1_,
  reduce(E2, E2_).


%% subst(+Term, +Var, +SubTerm, -NewTerm)
%
%  NewTerm is the result of substituting SubTerm for free instances of Var in
%  Term.  Renames variables as necessary.

subst(Y, Y, E, E).
subst(Y, X, _, Y) :- is_var(Y), Y \= X.

subst(E1 @ E2, X, E, T1 @ T2) :-
  subst(E1, X, E, T1),
  subst(E2, X, E, T2).

subst(Y^E_, Y, _, Y^E_).
subst(Y^E_, X, E, Y^T) :-
  Y \= X,
  freevars(E, FV),
  \+ member(Y, FV),
  subst(E_, X, E, T).

subst(Y^E_, X, E, Z^T) :-
  Y \= X,

  % Y is one of the subterm's free variables.
  freevars(E, FV_E),
  member(Y, FV_E),

  % Compute FV(E) + FV(E_) + {X}.
  freevars(E_, FV_E_),
  union(FV_E, FV_E_, FV_),
  union(FV_, [X], FV),

  % Take Z \notin FV to replace Y.
  variant(Y, FV, Z),
  subst(E_, Y, Z, T_),
  subst(T_, X, E, T).


%% freevars(+Term, -VarList)
%
%  VarList is a list of the free variables in a lambda term.

freevars(X, [X]) :- is_var(X).

freevars(X^E, FV) :-
  freevars(E, FV_),
  delete(FV_, X, FV).

freevars(E1 @ E2, FV) :-
  freevars(E1, FV1),
  freevars(E2, FV2),
  union(FV1, FV2, FV).


%------------------------------------------------------------------------------
%
%  Helper predicates.
%

%% variant(+Var, +VarList, -NewVar)
%
%  Generates a fresh variable name that does not appear in the VarList.

variant(X::N, L, NewX) :-
  member(X::N, L),
  N1 is N + 1,
  variant(X::N1, L, NewX).

variant(X, L, NewX) :-
  member(X, L),
  atom(X),
  variant(X::1, L, NewX).

variant(X, L, X) :- \+ member(X, L).


%------------------------------------------------------------------------------
%
%  Test cases.
%

%% test(?Name, ?Term)
%
%  :- test(X, Y), bnf(Y, Z).

test(top_level, (x^f@x)@a).       % top-level application
test(embedded, g@((x^f@x)@a)).    % embedded application
test(multiple_no_nest, g@((x^f@x)@a)@((x^f@x)@a)).  % multiple not nested
test(multiple_nest, g@((x^f@((y^h@y)@x))@a)).       % multiple nested
test(same_bound, g@((x^f@((x^h@x)@x))@a)).          % same bound variable
test(higher_order, (p^(p@(x^f@(x))))@(p^g@(p@a))).  % higher order

%
% Renaming.
%
test(renaming, (x^y^x)@y).
test(renaming, ((x::1)^(y::3)^x) @ (y::3)).
test(renaming, (y^f@((x^g@x@y)@a))@x).

%
% Combinator combinations (some from Barendregt).
%
test(skk, S@K@K) :-
  combinator(s, S), combinator(k, K).
test(b2_4_1_i, (y^y@y@y)@((a^b^a)@I@(S@S))) :-
  combinator(s, S), combinator(i, I).
test(ssz, CS@CS@CZ) :-
  combinator(cs, CS), combinator(cz, CZ).
test(yka, Y@K@a) :-
  combinator(y, Y), combinator(k, K).

%
% Combinators (some from Barendregt).
%
combinator(i, x^x).
combinator(k, x^y^x).
combinator(s, x^y^z^x@z@(y@z)).
combinator(y, f^(x^f@(x@x))@(x^f@(x@x))).
combinator(cs, a^b^c^b@(a@b@c)).
combinator(cz, x^x).
