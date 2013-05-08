%
% dcg.pl - A basic English DCG for generating syntax trees and predicate
% calculus semantics representations.
%

:- module(dcg, [sentence/3]).
:- use_module(library(lists)).
:- use_module(betanf).
:- use_module(utils).


%------------------------------------------------------------------------------
%
%  Toplevel and helpers.
%

%% sentence(+String, -Tree, -Interp)
%
% String is parsable, its parse is Tree, and its interpretation is Interp.

sentence(String, Tree, LF) :-
  s(Tree, Interp_, String, []),
  maplist(bnf, Interp_, Interp),
  maplist(notation, Interp, LF).


%% incr(+Counter, -N)
%
% Increment Counter with result N.

incr(Counter, N_) :-
  b_getval(Counter, N),
  N_ is N + 1,
  b_setval(Counter, N_).


%------------------------------------------------------------------------------
%
%  Semantics.
%
%  We employ a flat, reified logical form for our semantics, based on Hobbs's
%  "Ontological Promiscuity".  This is built up with nested lists of implicitly
%  conjuncted predicates, which we eventually flatten.
%

%% var_init
%
% Reset counter to 0.

var_init :- b_setval(event, 0), b_setval(entity, 0).

%% event(-E)
%
% Instantiate a new event variable.

event(e/E) --> {incr(event, E)}.

%% entity(-X)
%
% Instantiate a new entity variable.

entity(x/X) --> {incr(entity, X)}.


%------------------------------------------------------------------------------
%
%  Complementizer stack.
%
%  We use DCG rules for push and pop, and regular predicates elsewhere.
%

%% c_reset
%
% Reset counter to 0.

c_reset :- b_setval(counter, 0).

%% c_incr(-N)
%
% Increment counter with result N.

c_incr(N) :- incr(counter, N).

%% cstack_init
%
% Initialize the complementizer stack.

cstack_init :- c_reset, b_setval(cstack, []).

%% cstack_empty
%
% The cstack is empty.

cstack_empty :- b_getval(cstack, []).

%% cstack_depth(-N)
%
% N is the depth of the stack.

cstack_depth(N) :-
  b_getval(cstack, CStack),
  length(CStack, N).

%% cstack_push(+CType, +LF, -N, -Depth, +Data)
%
% Push a complementizer onto the stack, outputting its index and the stack
% depth before pushing.

cstack_push(CType, LF, N, Depth, Data) --> [],
  { c_incr(N),
    cstack_depth(Depth),
    b_getval(cstack, CStack),
    b_setval(cstack, [c(CType, LF, N, Data) | CStack])
  }.

%% cstack_pop(-CType, -LF, -N, -Data)
%
% Pop a complementizer off the stack.

cstack_pop(CType, LF, N, Data) --> [],
  { b_getval(cstack, [c(CType, LF, N, Data) | CStack]),
    b_setval(cstack, CStack)
  }.


%------------------------------------------------------------------------------
%
%  Complementizer grammar.
%

%% s(-T, -LF)
%
% Sentence.  Initialize the system and parse a CP.

s(CP, LF) -->
  {var_init}, {cstack_init},
  cp(CP, LF_), {flatten(LF_, LF)},
  {cstack_empty}.


%% cp(-T, -LF)
%
% Complementizer phrase.  We push specifiers and heads of CP's onto a
% sentence-local complementizer stack---this is used to pass them to their
% usual position in the sentence.

cp(cp(C_), LF) --> c_(C_, LF).

%cp(cp(dp(d_(np(n_(n(N/W))))), C_), C_i) -->
%  wp(W, _, WPi),
%  cstack_push(rel, WPi, N, Depth, W),
%  c_(C_, C_i),
%  { cstack_depth(Depth) }.

c_(c_(IP), LF) --> ip(IP, LF).

% Auxiliary complementizer.
c_(c_(c(N/Aux), IP), LF) -->
  aux(Agr, Tns, Gov, Aux, Lbd),
  { finite(Tns) },
  cstack_push(aux, Lbd, N, Depth, Tns/Gov),
  ip(Agr, _, Gov, IP, LF),
  { cstack_depth(Depth) }.

% Main verb complementizer (be/have).
c_(c_(c(N/V), IP), LF) -->
  v(Agr, Tns, Gov, Sub, v(V), Lbd),
  { finite(Tns), aspect(Gov) },
  cstack_push(verb, Lbd, N, Depth, Tns/Sub),
  ip(Agr, _, simp, IP, LF),
  { cstack_depth(Depth) }.


%% rp(+Agr, +Hum, +X, -T, -LF)
%
% Relative clause.  Functions syntactically as a complementizer phrase, but has
% distinct rules for construction.

rp(Agr, Hum, X, cp(Wh, c_(C, IP)), LF) -->
  rrel(X, Hum, Depth, Wh, C),
  ip(Agr, Tns, _, IP, LF),
  { finite(Tns) },
  { cstack_depth(Depth) }.


%% rel(+X, +Hum, -Depth, -Wh, -C)
%
% Relativizer.  Hum is the antecedent's humanity---personal or impersonal, and
% in the latter case, also location, time, etc.

% Subject.
rel(X, Hum, Depth, dp(N/Wh), c([])) -->
  whpro(Wh, nom, Hum, bound),
  cstack_push(nom, X, N, Depth, _).

% Object of verb or stranded preposition (detached).
rel(X, Hum, Depth, dp(N/Wh), c([])) -->
  whpro(Wh, obl, Hum, bound),
  cstack_push(obl, X, N, Depth, _).

% Object of fronted preposition (attached).
rel(X, Hum, Depth, pp(P, N/Wh), c([])) -->
  p(Prep, abstr, P, Lbd),
  whpro(Wh, obl, Hum, bound),
  cstack_push(pp, X:Lbd, N, Depth, Prep).

% Possessive.
%rel(X, Hum, Depth, Wh, c([])) -->
  % whose DP
  %cstack_push(gpn, X, N, Depth, Wh).


%% rrel(+X, +Hum, -Depth, -Wt, -C)
%
% Restrictive relativizer.  Additionally includes `that' and null relativizers.

rrel(X, Hum, Depth, Wh, C) --> rel(X, Hum, Depth, Wh, C).

rrel(X, _, Depth, dp(N/wh), c(that)) --> [that],
  cstack_push(nom, X, N, Depth, _).
rrel(X, _, Depth, dp(N/wh), c(that)) --> [that],
  cstack_push(obl, X, N, Depth, _).
rrel(X, _, Depth, dp(N/wh), c([])) -->
  cstack_push(obl, X, N, Depth, _).


%% nrel(+Hum, -Depth, -Wt, -C)
%
% Non-restrictive relativizer.  Additionally includes "D NP of which/whom".

nrel(X, Hum, Depth, Wh, C) --> rel(X, Hum, Depth, Wh, C).


%------------------------------------------------------------------------------
%
%  Inflection grammar.
%

%% Inflectional phrases.
%
% ip(-T, -LF)                     Null complementizer phrase.
% ip(+Agr, ?Tns, ?Gov, -T, -LF)   Nonzero complementizer phrase.

ip(ip(DP, I_), [Tns@E, Vld@X, LF2, LF1]) -->
  dp(Agr, DP, X:LF1),
  i_(Agr, Tns, _, Vld, I_, E:LF2),
  { finite(Tns) }.

ip(Agr, Tns, Gov, ip(DP, I_), [Tns@E, Vld@X, LF2, LF1]) -->
  dp(Agr, DP, X:LF1),
  i_(_, Tns, Gov, Vld, I_, E:LF2).

% Relative clause with subject gap.
ip(Agr, Tns, _, ip(dp(t/N), I_), [Tns@E, Vld@X, LF]) -->
  { case_role(Case, sbj) },
  cstack_pop(Case, X, N, _),
  i_(Agr, Tns, _, Vld, I_, E:LF).

i_(Agr, Tns, Gov, Vld, i_(i(Tns), II), LF) --> ii(Agr, Tns, Gov, Vld, II, LF).

ii(Agr, Tns, mod,  Vld, VP, LF) --> mp(Agr, Tns, Vld, VP, LF).
ii(Agr, Tns, perf, Vld, VP, LF) --> perfp(Agr, Tns, Vld, VP, LF).
ii(Agr, Tns, prog, Vld, VP, LF) --> progp(Agr, Tns, Vld, VP, LF).
ii(Agr, Tns, dsup, Vld, VP, LF) --> dsup(Agr, Tns, Vld, VP, LF).
ii(Agr, Tns, simp, Vld, VP, LF) --> vp(Agr, Tns, Vld, VP, LF).


%% Modality.
%
% mp(+Agr, -Tns, -Vld, -T, -LF)   Modal phrase.
% mc(-Vld, -T, -LF)               Modal complement.

mp(Agr, Tns, Vld, mp(m(Aux), MC), E:[Lbd@E@E_ | LF]) --> event(E),
  aux(Agr, Tns, mod, Aux, Lbd),
  mc(Vld, MC, E_:LF).

mp(_, Tns, Vld, mp(m(t/N), MC), E:[Lbd@E@E_ | LF]) --> event(E),
  cstack_pop(aux, Lbd, N, Tns/mod),
  mc(Vld, MC, E_:LF).

mc(Vld, PerfP, LF) --> perfp(_, infin, Vld, PerfP, LF).
mc(Vld, ProgP, LF) --> progp(_, infin, Vld, ProgP, LF).
mc(Vld, VP, LF) --> vp(_, infin, Vld, VP, LF).


%% Perfective aspect.
%
% perfp(+Agr, -Tns, -Vld, -T, -LF)  Perfective phrase.
% perfc(-T, -Vld, -LF)              Perfective complement.

perfp(Agr, Tns, Vld, perfp(perf(Aux), PerfC), E:[Lbd@E@E_ | LF]) --> event(E),
  aux(Agr, Tns, perf, Aux, Lbd),
  perfc(Vld, PerfC, E_:LF).

perfp(_, Tns, Vld, perfp(perf(t/N), PerfC), E:[Lbd@E@E_ | LF]) --> event(E),
  cstack_pop(aux, Lbd, N, Tns/perf),
  perfc(Vld, PerfC, E_:LF).

perfc(Vld, ProgP, LF) --> progp(_, pastp, Vld, ProgP, LF).
perfc(Vld, VP, LF) --> vp(_, pastp, Vld, VP, LF).


%% Progressive aspect.
%
% progp(+Agr, -Tns, -Vld, -T, -LF)  Progressive phrase.

progp(Agr, Tns, Vld, progp(prog(Aux), VP), E:[Lbd@E@E_ | LF]) --> event(E),
  aux(Agr, Tns, prog, Aux, Lbd),
  vp(_, presp, Vld, VP, E_:LF).

progp(_, Tns, Vld, progp(prog(t/N), VP), E:[Lbd@E@E_ | LF]) --> event(E),
  cstack_pop(aux, Lbd, N, Tns/prog),
  vp(_, presp, Vld, VP, E_:LF).


%% Do-support.
%
% dsup(+Agr, -Tns, -Vld, -T, -LF)   Fill `do' into Tns.

dsup(Agr, Do, Vld, VP, LF) -->
  aux(Agr, _, dsup, Do, _),
  vp(_, infin, Vld, VP, LF).

dsup(_, t/N, Vld, VP, LF) -->
  cstack_pop(aux, _, N, _/dsup),
  vp(_, infin, Vld, VP, LF).


%------------------------------------------------------------------------------
%
%  Verb grammar.
%

%% vopt(-Agr, -Tns, -Sub, -V, -LF)
%
% Parse a verb or pop one off the complementizer stack.

vopt(Agr, Tns, Sub, V, LF) --> v(Agr, Tns, Sub, V, LF).
vopt(_, Tns, Sub, v(t/N), LF) --> cstack_pop(verb, LF, N, Tns/Sub).


%% vp(+Agr, -Tns, -Vld, -T, -LF)
%
% Verb phrases.  We delegate verb subcategories with one or two theta roles to
% v_/4 and those with three theta roles to vc/5.

vp(Agr, Tns, Lbd, vp(V_), LF) --> v_(Agr, Tns, Lbd, V_, LF).

vp(Agr, Tns, Lbd@E@X, vp(v_(v(N/v), vp(Spec, V_))), E:[LF1, LF2]) --> event(E),
  { c_incr(N) },
  v(Agr, Tns, Sub, v(V), Lbd),
  vc(Sub, E, X, Spec, Comp, LF1),
  vv(v_(v(V/N), Comp), E, V_, LF2).


%% v_(+Agr, -Tns, -Vld, -T, -LF)
%
% Verb bars for the subcategories `nil', `np', and `a'.

v_(Agr, Tns, Lbd@E, V_, E:LF) --> event(E),
  vopt(Agr, Tns, nil, V, Lbd),
  vv(v_(V), E, V_, LF).

v_(Agr, Tns, Lbd@E@X, V_, E:[LF1 | LF2]) --> event(E),
  vopt(Agr, Tns, np, V, Lbd),
  dp(_, DP, X:LF1),
  vv(v_(V, DP), E, V_, LF2).

%v_(Agr, Tns, V_, V_i) --> event(E),
%  vopt(Agr, Tns, a, V, Lbd),
%  ap(AP, APi),
%  vv(v_(V, AP), Vi@APi, V_, V_i).

% Relative clause with object gap.
v_(Agr, Tns, Lbd@E@X, V_, E:LF) --> event(E),
  v(Agr, Tns, np, V, Lbd),
  cstack_pop(Case, X, N, _),
  { case_role(Case, obj) },
  vv(v_(V, dp(t/N)), E, V_, LF).


%% vc(+Sub, +E, -X, -Spec, -Comp, -LF)
%
% Verb complements.  Used for verbs with three theta roles in order to properly
% generate the syntax tree and handle synonymity.  Spec and Comp are the
% specifier and complement in the tree; E and X are the event of the verb and
% the entity of the object.

vc(np/pp, E, X, Spec, Comp, [LF1, LF2]) -->
  dp(_, Spec, X:LF1), pp(abstr, E, Comp, LF2).
vc(np/P,  E, X, Spec, Comp, [LF1, LF2]) -->
  dp(_, Spec, X:LF1), pp(abstr, P, E, Comp, LF2).
vc(np/np, E, X, Spec, Comp, [Lbd@Y@E, LF1, LF2]) -->
  dp(_, Spec, Y:LF1), dp(_, Comp, X:LF2),
  { p(to, abstr, _, Lbd, _, _) }.

% Relative clause with complement gap.
vc(np/np, E, X, Spec, dp(t/N), [Lbd@Y@E | LF]) -->
  { case_role(Case, obj) },
  dp(_, Spec, Y:LF), cstack_pop(Case, X, N, _),
  { p(to, abstr, _, Lbd, _, _) }.


%% vv(+V_, +E, -T, -LF)
%
% Verb adjuncts.  Adjoins prepositional phrases to verb bars.

vv(V_, _, V_, []) --> [].
vv(V_, E, VV, [Lbd@E, LF1, LF2]) -->
  pp(abstr, Lbd, PP, LF1),
  vv(v_(V_, PP), E, VV, LF2).


%------------------------------------------------------------------------------
%
%  Determiner and noun grammar.
%

%% dp(+Agr, -T, -LF)
%
% Determiner phrases.

dp(Agr, dp(D_), LF) --> d_(Agr, D_, LF).


%% d_(+Agr, -T, -LF)
%
% Determiner bars.

d_(Agr, d_(np(n_(PR))), X:[]) --> pr(Agr, PR, X).
d_(Agr, d_(D, NP), LF) --> d(Agr, D, _), np(Agr, NP, LF).


%% np(+Agr, -T, -LF)
%
% Noun phrases.

np(Agr, np(N_), LF) --> n_(Agr, N_, LF).


%% n_(+Agr, -T, -LF)
%
% Noun bars.

n_(Agr, N_, X:[Lbd@X | LF]) --> entity(X),
  n(Agr, N, Lbd),
  nn(Agr, n_(N), X, N_, LF).

%n_(Agr, N_, N_i) -->
%  ap(AP, APi),
%  n(Agr, N, Ni),
%  { and(Ni, APi, NA) },
%  nn(Agr, n_(AP, N), NA, N_, N_i).


%% nn(+Agr, +N_, +X, -T, -LF)
%
% Noun adjuncts.  Adjoins prepositional phrases and relative clauses to noun
% bars.

nn(_, N_, _, N_, []) --> [].
nn(_, N_, X, NN, [Lbd@X, LF1, LF2]) -->
  pp(abstr, Lbd, PP, LF1),
  nn(_, n_(N_, PP), X, NN, LF2).
nn(Agr, N_, X, n_(N_, CP), LF) --> rp(Agr, _, X, CP, LF).


%------------------------------------------------------------------------------
%
%  Preposition and adjective grammar.
%

%% Prepositional phrases.
%
% pp(+Reif, -Lbd, -T, -LF)          Prepositional phrase.
% pp(+Prep, +Reif, -Lbd, -T, -LF)   PP with pre-bound preposition.

pp(Reif, Lbd, PP, LF) --> pp(_, Reif, Lbd, PP, LF).
pp(Prep, abstr, Lbd@X, pp(P, DP), LF) -->
  p(Prep, abstr, P, Lbd),
  dp(_, DP, X:LF).
pp(Prep, reify, Lbd@E@X, pp(P, DP), E:LF) --> event(E),
  p(Prep, reify, P, Lbd),
  dp(_, DP, X:LF).


%% ap(-T, -LF)
%
% Adjective phrases.

ap(ap(a_(A)), Ai) --> a(A, Ai).


%------------------------------------------------------------------------------
%
%  Exported lexicons.
%

:- ensure_loaded('lex/pr.pl').
:- ensure_loaded('lex/noun.pl').
:- ensure_loaded('lex/adj.pl').
:- ensure_loaded('lex/verb.pl').

% Proper nouns.
pr(sg/3, n(PR), PR) --> {pr(X), atomic_list_concat(X, ' ', PR)}, X.

% Common nouns.
n(sg/3, n(Sg), x^Sg@x) --> [Sg], {noun(Sg, _Pl)}.
n(pl/3, n(Pl), x^Sg@x) --> [Pl], {noun(Sg, Pl)}.

% Adjectives.
a(a(A), x^A@x) --> [A], {adj(A)}.


%------------------------------------------------------------------------------
%
%  Verbs lexicon.
%

:- discontiguous(v/8).

%% finite(?Tns)
%
% Verb tense finiteness.

finite(pres).
finite(pret).
finite(Do) :- aux(_, Tns, dsup, Do, _, _, _), finite(Tns).

%% aspect(?Gov)
%
% Verb aspect government.

aspect(prog).
aspect(perf).

%% v_scf(+V, +Fs, ?Sub, -LF)
%
% Verb subcategorization frames.

v_scf(V, Fs, aux,   z^x^V@z@x)     :- member(aux, Fs).
v_scf(V, Fs, nil,   z^x^V@z@x)     :- member(nil, Fs).
v_scf(V, Fs, np,    z^y^x^V@z@x@y) :- member(np, Fs).
v_scf(V, Fs, np/X,  z^y^x^V@z@x@y) :- member(np/X, Fs).


%% Auxiliary verbs.
%
% aux(?Agr, ?Tns, ?Gov, -T, -LF)
% modal(-Pres, -Pret)
%
% We share the paradigm descriptions of `be' and `have' with the verb lexical
% predicate, and additionally define modal auxiliaries.

aux(Agr, Tns, prog, X, LF) --> v(Agr, Tns, prog, aux, v(X), LF).
aux(Agr, Tns, perf, X, LF) --> v(Agr, Tns, perf, aux, v(X), LF).
aux(Agr, Tns, dsup, X, LF) --> v(Agr, Tns, dsup, aux, v(X), LF).
aux(_/_, pres, mod, X, LF) --> [X], {modal(X, _), v_scf(X, [aux], aux, LF)}.
aux(_/_, pret, mod, X, LF) --> [X], {modal(_, X), v_scf(X, [aux], aux, LF)}.

  modal(can, could).
  modal(may, might).
  modal(shall, should).
  modal(will, would).


%% Copular verb `be'.
%
% b(-Agr, -Tns, -V)       Lexical paradigm for `be'.
% b_scf(+V, -Sub, -LF)    Special `invisible' logical forms for `be'.

v(Agr, Tns, prog, Sub, v(V), LF) --> [V], {b(Agr, Tns, V), b_scf(V, Sub, LF)}.

  b(_/_,  infin, be).
  b(_/_,  presp, being).
  b(_/_,  pastp, been).

  b(sg/1, pres,  am).
  b(sg/2, pres,  are).
  b(sg/3, pres,  is).
  b(pl/_, pres,  are).

  b(sg/1, pret,  was).
  b(sg/2, pret,  were).
  b(sg/3, pret,  was).
  b(pl/_, pret,  were).

b_scf(_, aux, _).
b_scf(_, nil, x^x).
b_scf(_, a,   x^y^x@y).
b_scf(_, pp,  x^y^x@y).
b_scf(V, np,  x^y^V@y@x).


%% v(?Agr, ?Tns, ?Gov, ?Sub, -T, -LF)
%
% Main verbs.  Features include agreement (number and person), tense,
% governance (modality, aspect, etc.), and subcategorization frame.

v(Agr, Tns, Sub, Vt, LF) --> v(Agr, Tns, _, Sub, Vt, LF).
v(_/_,  infin, Gov, Sub, v(V), LF) --> [V], {verb(V,_,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/1, pres,  Gov, Sub, v(V), LF) --> [V], {verb(V,_,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/2, pres,  Gov, Sub, v(V), LF) --> [V], {verb(V,_,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/3, pres,  Gov, Sub, v(V), LF) --> [V], {verb(X,V,_,_,_,Gov,Fs), v_scf(X,Fs,Sub,LF)}.
v(pl/_, pres,  Gov, Sub, v(V), LF) --> [V], {verb(V,_,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(_/_,  pret,  Gov, Sub, v(V), LF) --> [V], {verb(X,_,V,_,_,Gov,Fs), v_scf(X,Fs,Sub,LF)}.
v(_/_,  presp, Gov, Sub, v(V), LF) --> [V], {verb(X,_,_,V,_,Gov,Fs), v_scf(X,Fs,Sub,LF)}.
v(_/_,  pastp, Gov, Sub, v(V), LF) --> [V], {verb(X,_,_,_,V,Gov,Fs), v_scf(X,Fs,Sub,LF)}.

  verb(do, does, did, doing, done,  dsup, [aux, np]).
  verb(have, has, had, having, had, perf, [aux, np]).

% Lexicon shorthand.
verb(F1, F2, F3, F4, F5, simp, Fs) :- verb(F1, F2, F3, F4, F5, Fs).


%------------------------------------------------------------------------------
%
%  Particles lexicon.
%

%% d(?Agr, -T, -LF)
%
% Determiners.

d(Num/3, d(D), p^term@Q@(x^p@x)) --> [D], {det(D, Num, Q)}.

  det(a,     sg, some).
  det(the,   _,  the).
  det(some,  _,  some).
  det(every, sg, every).


%% p(?P, +Reif, -T, -LF)
%
% Prepositions.

p(P, reify, p(P), s^x^y^P@s@y@x) --> p(P).
p(P, abstr, p(P), x^y^P@y@x) --> p(P).

p(P) --> [P], {prep(P)}.
p(P) --> [P1, P2], {prep(P1, P2), atom_concat(P1, P2, P)}.

  prep(above).
  prep(at).
  prep(below).
  prep(by).
  prep(for).
  prep(from).
  prep(in).
  prep(of).
  prep(on).
  prep(to).
  prep(under).
  prep(with).
  prep(left, of).
  prep(right, of).


%------------------------------------------------------------------------------
%
%  Pro-forms lexicon.
%

%% case_role(?Case, ?Role)
%
% A noun inflected as Case can fill Role.

case_role(nom, sbj).
case_role(obl, obj).
case_role(gpn, _).


% pn(?Agr, ?Case, ?P)
%
% Personal pronouns.

pn(Agr, nom,  P) --> [P], {pro(Agr, P, _, _, _, _)}.
pn(Agr, obl,  P) --> [P], {pro(Agr, _, P, _, _, _)}.
pn(Agr, pos,  P) --> [P], {pro(Agr, _, _, P, _, _)}.
pn(Agr, gpn,  P) --> [P], {pro(Agr, _, _, _, P, _)}.
pn(Agr, refl, P) --> [P], {pro(Agr, _, _, _, _, P)}.

  pro(sg/1, i,    me,   my,     mine,   myself).
  pro(sg/2, you,  you,  your,   yours,  yourself).
  pro(sg/3, he,   him,  his,    his,    himself).
  pro(sg/3, she,  her,  her,    hers,   herself).
  pro(sg/3, it,   it,   its,    [],     itself).

  pro(pl/1, we,   us,   our,    ours,   ourselves).
  pro(pl/2, you,  you,  your,   yours,  yourselves).
  pro(pl/3, they, them, their,  theirs, themselves).


% whpro(?Wh, ?Case, ?Hum ?Rel)
%
% Wh- pronouns.  Features include case, relativizer function (bound/free), and
% humanity (personal/impersonal).
%
% Technically, relativizer function depends on case; for instance, we can't use
% the genitive pronoun form in bound clauses:
%
%     *The man whose they found.
%
% but this is dependent on the case/context pairing, not on the word itself;
% hence, we make this distinction in the rules and not in the lexical entry.

whpro(Wh, nom, Hum, Rel) --> [Wh], {whpro(Wh, _, _, Hum, Rs), member(Rel, Rs)}.
whpro(Wh, obl, Hum, Rel) --> [Wh], {whpro(_, Wh, _, Hum, Rs), member(Rel, Rs)}.
whpro(Wh, pos, Hum, Rel) --> [Wh], {whpro(_, _, Wh, Hum, Rs), member(Rel, Rs)}.
whpro(Wh, gpn, Hum, Rel) --> [Wh], {whpro(_, _, Wh, Hum, Rs), member(Rel, Rs)}.

  whpro(who,    whom,   whose,  pers,   [bound, free]).
  whpro(which,  which,  whose,  imprs,  [bound, free]).
  whpro(what,   what,   [],     imprs,  [free]).

% whdet(?Wh)
%
% Wh- determiners.  No features; all are humanity-blind and used in free
% contexts only.

whdet(Wh) --> [Wh], {whdet(Wh)}.

  whdet(what).
  whdet(which).

% whadv(?Wh, ?Fn, ?Rel)
%
% Wh- adverbs.  Features include function (time, location, etc.) and
% relativizer function (bound/free).

whadv(Wh, Fn, Rel) --> [Wh], {whadv(Wh, Fn, Rs), member(Rel, Rs)}.

  whadv(when,   time,   [bound, free]).
  whadv(where,  loc,    [bound, free]).
  whadv(why,    reas,   [bound, free]).
  whadv(how,    manner, [free]).
