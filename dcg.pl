%
% dcg.pl - A basic English DCG for generating syntax trees and predicate
% calculus semantics representations.
%

:- module(dcg, [sentence/3]).
:- use_module(betanf).
:- use_module(library(lists)).


%------------------------------------------------------------------------------
%
%  Toplevel and helpers.
%

%% sentence(+String, -Tree, -Interp)
%
% String is parsable, its parse is Tree, and its interpretation is Interp.

sentence(String, Tree, Interp) :-
  s(Tree, Interp_, String, []),
  bnf(Interp_, Interp).

%% and(+LF1, +LF2, -AndLF)
%
% Encoding of logical `and'.

and(X, Y, x^and@(X@x)@(Y@x)).


%------------------------------------------------------------------------------
%
%  Complementizer stack.
%

%% c_reset.
%
% Reset counter to 0.

c_reset :- b_setval(counter, 0).

%% c_incr(-N)
%
% Increment counter with result N.

c_incr(N1) :-
  b_getval(counter, N),
  N1 is N + 1,
  b_setval(counter, N1).

%% cstack_init
%
% Initialize the complementizer stack.

cstack_init :- c_reset, b_setval(cstack, []).

%% cstack_empty
%
% The cstack is empty.

cstack_empty :- b_getval(cstack, []).

%% cstack_push(+CType, +LF, -N, +Gov)
%
% Push a complementizer onto the stack.

cstack_push(CType, LF, N, Data) :-
  c_incr(N),
  b_getval(cstack, CStack),
  b_setval(cstack, [c(CType, LF, N, Data) | CStack]).

%% cstack_pop(-CType, -LF, -N, -Gov)
%
% Pop a complementizer off the stack.

cstack_pop(CType, LF, N, Data) :-
  b_getval(cstack, [c(CType, LF, N, Data) | CStack]),
  b_setval(cstack, CStack).


%------------------------------------------------------------------------------
%
%  Complementizer grammar.
%

%% Sentence.
%
% Initialize a new complementizer stack, parse a CP, then ensure that the stack
% is emptied.

s(CPt, CPi) --> {cstack_init}, cp(CPt, CPi), {cstack_empty}.


%% Complementizer phrases.
%
% We push specifiers and heads of CP's onto a sentence-local complementizer
% stack---this is used to pass them to their usual position in the sentence.

cp(cp(C_t), C_i) --> c_(C_t, C_i).

c_(c_(IPt), IPi) --> ip(IPt, IPi).

% Auxiliary complementizer.
c_(c_(c(N/Aux), IPt), IPi) -->
  aux(Agr, Tns, Gov, Aux, LF),
  { finite(Tns),
    cstack_push(aux, LF, N, Tns/Gov)
  },
  ip(Agr, Gov, IPt, IPi).

% Main verb complementizer (be/have).
c_(c_(c(N/V), IPt), IPi) -->
  v(Agr, Tns, Gov, Sub, v(V), LF),
  { finite(Tns), aspect(Gov),
    cstack_push(verb, LF, N, Tns/Sub)
  },
  ip(Agr, simp, IPt, IPi).


%------------------------------------------------------------------------------
%
%  Inflection grammar.
%

%% Inflectional phrases.
%
% ip(-T, -I)      Binds a DP to an I_ by number and person and forces the I_
%                 to be tense-finite.
% ip(+Agr, +Gov, -T, -I)    Enforces agreement Agr on DP without restricting I_.

ip(ip(DPt, I_t), I_i@DPi) -->
  dp(Agr, DPt, DPi),
  i_(Agr, Tns, _, I_t, I_i),
  {finite(Tns)}.

ip(Agr, Gov, ip(DPt, I_t), I_i@DPi) -->
  dp(Agr, DPt, DPi),
  i_(_, _, Gov, I_t, I_i).

i_(Agr, Tns, Gov, i_(i(Tns), IIt), IIi) --> ii(Agr, Tns, Gov, IIt, IIi).

ii(Agr, Tns, mod,  VPt, VPi) --> mp(Agr, Tns, VPt, VPi).
ii(Agr, Tns, perf, VPt, VPi) --> perfp(Agr, Tns, VPt, VPi).
ii(Agr, Tns, prog, VPt, VPi) --> progp(Agr, Tns, VPt, VPi).
ii(Agr, Tns, dsup, VPt, VPi) --> dsup(Agr, Tns, VPt, VPi).
ii(Agr, Tns, simp, VPt, VPi) --> vp(Agr, Tns, VPt, VPi).


%% Modality.
%
% mp(+Agr, -Tns, -T, -I)    Modal phrase.
% mc(-T, -I)                Modal complement.

mp(Agr, Tns, mp(m(Aux), MCt), MCi) -->
  aux(Agr, Tns, mod, Aux, _),
  {\+ cstack_pop(aux, _, _, _/mod)},
  mc(MCt, MCi).

mp(_, Tns, mp(m(t/N), MCt), MCi) -->
  {cstack_pop(aux, _, N, Tns/mod)},
  mc(MCt, MCi).

mc(PerfPt, PerfPi) --> perfp(_, infin, PerfPt, PerfPi).
mc(ProgPt, ProgPi) --> progp(_, infin, ProgPt, ProgPi).
mc(VPt, VPi) --> vp(_, infin, VPt, VPi).


%% Perfective aspect.
%
% perfp(+Agr, -Tns, -T, -I)   Perfective phrase.
% perfc(-T, -I)               Perfective complement.

perfp(Agr, Tns, perfp(perf(Aux), PerfCt), PerfCi) -->
  aux(Agr, Tns, perf, Aux, _),
  {\+ cstack_pop(aux, _, _, _/perf)},
  perfc(PerfCt, PerfCi).

perfp(_, Tns, perfp(perf(t/N), PerfCt), PerfCi) -->
  {cstack_pop(aux, _, N, Tns/perf)},
  perfc(PerfCt, PerfCi).

perfc(ProgPt, ProgPi) --> progp(_, pastp, ProgPt, ProgPi).
perfc(VPt, VPi) --> vp(_, pastp, VPt, VPi).


%% Progressive aspect.
%
% progp(+Agr, -Tns, -T, -I)   Progressive phrase.

progp(Agr, Tns, progp(prog(Aux), VPt), VPi) -->
  aux(Agr, Tns, prog, Aux, _),
  {\+ cstack_pop(aux, _, _, _/prog)},
  vp(_, presp, VPt, VPi).

progp(_, Tns, progp(prog(t/N), VPt), VPi) -->
  {cstack_pop(aux, _, N, Tns/prog)},
  vp(_, presp, VPt, VPi).


%% Do-support.
%
% dsup(+Agr, -Tns, -T, -I)    Fill `do' into Tns.

dsup(Agr, Do, VPt, VPi) -->
  aux(Agr, _, dsup, Do, _),
  {\+ cstack_pop(aux, _, _, _/dsup)},
  vp(_, infin, VPt, VPi).

dsup(_, t/N, VPt, VPi) -->
  {cstack_pop(aux, _, N, _/dsup)},
  vp(_, infin, VPt, VPi).


%------------------------------------------------------------------------------
%
%  Verb grammar.
%

%% vopt(-Agr, -Tns, -Sub, -Vt, -Vi)
%
% Parse a verb or pop one off the complementizer stack.

vopt(Agr, Tns, Sub, Vt, Vi) -->
  v(Agr, Tns, Sub, Vt, Vi),
  {\+ cstack_pop(verb, _, _, _)}.
vopt(_, Tns, Sub, v(t/N), Vi) -->
  {cstack_pop(verb, Vi, N, Tns/Sub)}.


%% vp(+Agr, -Tns, -T, -I)
%
% Verb phrases.  We delegate verb subcategories with one or two theta roles to
% v_/4 and those with three theta roles to vc/5.

vp(Agr, Tns, vp(V_t), V_i) --> v_(Agr, Tns, V_t, V_i).

vp(Agr, Tns, vp(v_(v(N/v), vp(Spec, V_t))), V_i) -->
  v(Agr, Tns, Sub, v(V), Vi),
  vc(Sub, Spec, Comp, DP, PP),
  {c_incr(N)},
  vv(v_(v(V/N), Comp), x^PP@(Vi@DP@x), V_t, V_i).


%% v_(+Agr, -Tns, -T, -I)
%
% Verb bars for the subcategories `nil', `np', and `a'.

v_(Agr, Tns, V_t, V_i) -->
  vopt(Agr, Tns, nil, Vt, Vi),
  vv(v_(Vt), Vi, V_t, V_i).
v_(Agr, Tns, V_t, V_i) -->
  vopt(Agr, Tns, np, Vt, Vi),
  dp(_, DPt, DPi),
  vv(v_(Vt, DPt), Vi@DPi, V_t, V_i).
v_(Agr, Tns, V_t, V_i) -->
  vopt(Agr, Tns, a, Vt, Vi),
  ap(APt, APi),
  vv(v_(Vt, APt), Vi@APi, V_t, V_i).


%% vc(+Sub, -Spec, -Comp, -DP, -PP)
%
% Verb complements.  Used for verbs with three theta roles in order to properly
% generate the syntax tree and handle synonymity.  Spec and Comp are the
% specifier and complement in the tree; DP and PP are the logical forms of the
% direct and indirect objects.

vc(np/np, Spec, Comp, DP, (x^y^to@y@x)@IO) -->
  dp(_, Spec, IO), dp(_, Comp, DP).
vc(np/pp, Spec, Comp, DP, PP) -->
  dp(_, Spec, DP), pp(Comp, PP).
vc(np/P, Spec, Comp, DP, PP) -->
  dp(_, Spec, DP), pp(P, Comp, PP).


%% vv(+V_t, +V_i, -T, -I)
%
% Verb adjuncts.  Adjoins prepositional phrases to verb bars.

vv(V_t, V_i, V_t, V_i) --> [].
vv(V_t, V_i, VVt, VVi) -->
  pp(PPt, PPi),
  vv(v_(V_t, PPt), x^PPi@(V_i@x), VVt, VVi).


%------------------------------------------------------------------------------
%
%  Determiner and noun grammar.
%

%% dp(+Agr, -T, -I)
%
% Determiner phrases.

dp(Agr, dp(D_t), D_i) --> d_(Agr, D_t, D_i).

%% d_(+Agr, -T, -I)
%
% Determiner bars.

d_(Agr, d_(np(PRt)), PRi) --> pr(Agr, PRt, PRi).
d_(Agr, d_(Dt, NPt), Di@NPi) --> d(Agr, Dt, Di), np(Agr, NPt, NPi).

%% np(+Agr, -T, -I)
%
% Noun phrases.

np(Agr, np(N_t), N_i) --> n_(Agr, N_t, N_i).

%% n_(+Agr, -T, -I)
%
% Noun bars.

n_(Agr, N_t, N_i) --> n(Agr, Nt, Ni), nn(n_(Nt), Ni, N_t, N_i).
n_(Agr, N_t, N_i) -->
  ap(APt, APi),
  n(Agr, Nt, Ni),
  {and(Ni, APi, NA)},
  nn(n_(APt, Nt), NA, N_t, N_i).

%% nn(+N_t, +N_i, -T, -I)
%
% Noun adjuncts.  Adjoins prepositional phrases to noun bars.

nn(N_t, N_i, N_t, N_i) --> [].
nn(N_t, N_i, NNt, NNi) -->
  pp(PPt, PPi),
  {and(N_i, PPi, And)},
  nn(n_(N_t, PPt), And, NNt, NNi).


%------------------------------------------------------------------------------
%
%  Preposition and adjective grammar.
%

%% Prepositional phrases.
%
% pp(-T, -I)          Prepositional phrase.
% pp(Prep, -T, -I)    PP with pre-bound preposition.

pp(PPt, PPi) --> pp(_, PPt, PPi).
pp(Prep, pp(Pt, DPt), Pi@DPi) --> p(Prep, Pt, Pi), dp(_, DPt, DPi).


%% ap(-T, -I)
%
% Adjective phrases.

ap(ap(a_(At)), Ai) --> a(At, Ai).


%------------------------------------------------------------------------------
%
%  Verbs lexicon.
%

:- discontiguous(v/8).

% Verb tense finiteness.
finite(pres).
finite(pret).
finite(Do) :- aux(_, Tns, dsup, Do, _, _, _), finite(Tns).

% Verb aspect government.
aspect(prog).
aspect(perf).

% Verb subcategorization frames.
v_scf(_, Fs, aux,   _)         :- member(aux, Fs).
v_scf(V, Fs, nil,   y^V@y)     :- member(nil, Fs).
v_scf(V, Fs, np,    x^y^V@y@x) :- member(np, Fs).
v_scf(V, Fs, np/X,  x^y^V@y@x) :- member(np/X, Fs).

%
% Auxiliary verbs.
%
% We share the paradigm descriptions of `be' and `have' with the verb lexical
% predicate, and additionally define modal auxiliaries.
%
aux(Agr, Tns, prog, X, _) --> v(Agr, Tns, prog, aux, v(X), _).
aux(Agr, Tns, perf, X, _) --> v(Agr, Tns, perf, aux, v(X), _).
aux(Agr, Tns, dsup, X, _) --> v(Agr, Tns, dsup, aux, v(X), _).
aux(_/_, pres, mod, X, _) --> [X], {modal(X, _)}.
aux(_/_, pret, mod, X, _) --> [X], {modal(_, X)}.

  modal(can, could).
  modal(may, might).
  modal(shall, should).
  modal(will, would).

%
% Copular verb `be'.
%
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

%
% Main verbs.
%
v(Agr, Tns, Sub, Vt, LF) --> v(Agr, Tns, _, Sub, Vt, LF).
v(_/_,  infin, Gov, Sub, v(V), LF) --> [V], {verb(V,_,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/1, pres,  Gov, Sub, v(V), LF) --> [V], {verb(V,_,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/2, pres,  Gov, Sub, v(V), LF) --> [V], {verb(V,_,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/3, pres,  Gov, Sub, v(V), LF) --> [V], {verb(_,V,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(pl/_, pres,  Gov, Sub, v(V), LF) --> [V], {verb(V,_,_,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(_/_,  pret,  Gov, Sub, v(V), LF) --> [V], {verb(_,_,V,_,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(_/_,  presp, Gov, Sub, v(V), LF) --> [V], {verb(_,_,_,V,_,Gov,Fs), v_scf(V,Fs,Sub,LF)}.
v(_/_,  pastp, Gov, Sub, v(V), LF) --> [V], {verb(_,_,_,_,V,Gov,Fs), v_scf(V,Fs,Sub,LF)}.

  verb(do, does, did, doing, done,  dsup, [aux, np]).
  verb(have, has, had, having, had, perf, [aux, np]).

%
% Main verb lexicon.
%
verb(F1, F2, F3, F4, F5, simp, Fs) :- verb(F1, F2, F3, F4, F5, Fs).


%------------------------------------------------------------------------------
%
%  Particles lexicon.
%

% Determiners.
d(Num/3, d(D), p^term@Q@(x^p@x)) --> [D], {det(D, Num, Q)}.

  det(a,     sg, some).
  det(the,   _,  the).
  det(some,  _,  some).
  det(every, sg, every).

% Prepositions.
p(P, p(P), x^y^P@y@x) --> [P], {prep(P)}.
p(P, p(P), x^y^P@y@x) --> [P1, P2], {prep(P1, P2), atom_concat(P1, P2, P)}.

  prep(above).
  prep(at).
  prep(below).
  prep(by).
  prep(of).
  prep(on).
  prep(to).
  prep(under).
  prep(with).
  prep(left, of).
  prep(right, of).


%------------------------------------------------------------------------------
%
%  Imported lexicons.
%

:- ensure_loaded('lex/pr.pl').
:- ensure_loaded('lex/noun.pl').
:- ensure_loaded('lex/verb.pl').
:- ensure_loaded('lex/adj.pl').

% Proper nouns.
pr(sg/3, n(PR), PR) --> {pr(X), atomic_list_concat(X, ' ', PR)}, X.

% Common nouns.
n(sg/3, n(Sg), x^Sg@x) --> [Sg], {noun(Sg, _Pl)}.
n(pl/3, n(Pl), x^Sg@x) --> [Pl], {noun(Sg, Pl)}.

% Adjectives.
a(a(A), x^A@x) --> [A], {adj(A)}.
