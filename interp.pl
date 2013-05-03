%
% interp.pl - A basic English DCG with lambda calculus-based semantics
% representation.
%

:- module(interp, [interpret/2]).
:- use_module(betanf).
:- use_module(library(lists)).


%------------------------------------------------------------------------------
%
%  Toplevel.
%

%% interpret(+String, -Interp)
%
% String is parsable and its interpretation is Interp.

interpret(String, Interp) :-
  s(Interp_, String, []),
  normal_form(Interp_, Interp).


%------------------------------------------------------------------------------
%
%  Grammar.
%

% Sentences.
s(CP) --> cp(CP).

% Complementizer phrases.
cp(C_) --> c_(C_).

c_(IP) --> ip(IP).
c_(IP) --> aux(Agr, Tns, Gov, _), ip(Gov, Agr, IP), {finite(Tns)}.
c_(IP) --> v(Agr, Tns, perf, Sub, V), ip(V, Sub, Agr, IP), {finite(Tns)}.
c_(IP) --> v(Agr, Tns, prog, Sub, V), ip(V, Sub, Agr, IP), {finite(Tns)}.

% Inflectional phrases.
ip(VP@DP) --> dp(Agr, DP), i_(Agr, VP).
ip(C, Agr, VP@DP) --> dp(Agr, DP), i_(C, VP).
ip(V, Sub, Agr, VP@DP) --> dp(Agr, DP), i_(V, Sub, VP).

i_(Agr, VP) --> vp(Agr, Tns, VP), {finite(Tns)}.
i_(Agr, VP) --> mp(Agr, Tns, VP), {finite(Tns)}.
i_(Agr, VP) --> perfp(Agr, Tns, VP), {finite(Tns)}.
i_(Agr, VP) --> progp(Agr, Tns, VP), {finite(Tns)}.

% TODO(mxw): Move this down into the modality/aspect predicates.
i_(mod,  VP) --> m_(VP).
i_(perf, VP) --> perf_(VP).
i_(prog, VP) --> prog_(VP).
i_(dsup, VP) --> dsup_(VP).

% TODO(mxw): Ew this is gross.
i_(V, Sub, VP) --> v_(V, Sub, _, VP).

/*
% Modality.
mp(Agr, Tns, VP) --> aux(Agr, Tns, mod, _), perfp(_, infin, VP).
mp(Agr, Tns, VP) --> aux(Agr, Tns, mod, _), progp(_, infin, VP).
mp(Agr, Tns, VP) --> aux(Agr, Tns, mod, _), vp(_, infin, VP).

% Aspect.
perfp(Agr, Tns, VP) --> aux(Agr, Tns, perf, _), progp(_, pastp, VP).
perfp(Agr, Tns, VP) --> aux(Agr, Tns, perf, _), vp(_, pastp, VP).
progp(Agr, Tns, VP) --> aux(Agr, Tns, prog, _), vp(_, presp, VP).
*/

% Modality.
mp(Agr, Tns, VP) --> aux(Agr, Tns, mod, _), m_(VP).

m_(VP) --> perfp(_, infin, VP).
m_(VP) --> progp(_, infin, VP).
m_(VP) --> vp(_, infin, VP).

% Perfective aspect.
perfp(Agr, Tns, VP) --> aux(Agr, Tns, perf, _), perf_(VP).

perf_(VP) --> progp(_, pastp, VP).
perf_(VP) --> vp(_, pastp, VP).

% Progressive aspect.
progp(Agr, Tns, VP) --> aux(Agr, Tns, prog, _), prog_(VP).

prog_(VP) --> vp(_, presp, VP).

% Do-support.
dsupp(Agr, Tns, VP) --> aux(Agr, Tns, dsup, _), dsup_(VP).

dsup_(VP) --> vp(_, infin, VP).

% Verb phrases.
%
% As in our syntax tree generator, we enforce objects for ditransitive verbs by
% inlining the relevant clasues of `v_' and calling `vv' directly.
vp(Agr, Tns, V_) --> v_(Agr, Tns, V_).
vp(Agr, Tns, VP) -->
  v(Agr, Tns, Sub, V),
  vc(Sub, DP, PP),
  vv(x^PP@(V@DP@x), VP).

v_(Agr, Tns, V_) --> v(Agr, Tns, nil, V), vv(V, V_).
v_(Agr, Tns, V_) --> v(Agr, Tns, np, V), dp(_, DP), vv(V@DP, V_).

v_(V, nil, _, V_) --> vv(V, V_).
v_(V, a,   _, V_) --> a(A), vv(V@A, V_).
v_(V, np,  _, V_) --> dp(_, DP), vv(V@DP, V_).

vv(V_, V_) --> [].
vv(V_, VV) --> pp(PP), vv(x^PP@(V_@x), VV).

vc(np/np, DP, (x^y^to@y@x)@IO) --> dp(_, IO), dp(_, DP).
vc(np/pp, DP, PP) --> dp(_, DP), pp(PP).
vc(np/P, DP, PP) --> dp(_, DP), pp(P, PP).

% Determiner phrases.
dp(Agr, D_) --> d_(Agr, D_).

d_(Agr, PN) --> pn(Agr, PN).
d_(Agr, D@NP) --> d(Agr, D), np(Agr, NP).

% Noun phrases.
np(Agr, N_) --> n_(Agr, N_).

n_(Agr, N_) --> n(Agr, N), nn(N, N_).
n_(Agr, N_) --> a(A), n(Agr, N), {and(N, A, NA)}, nn(NA, N_).

nn(N_, N_) --> [].
nn(N_, NN) --> pp(PP), {and(N_, PP, And)}, nn(And, NN).

% Prepositional phrases.
pp(PP) --> pp(_, PP).
pp(Prep, P@DP) --> p(Prep, P), dp(_, DP).

% Encoding for `and'.
and(X, Y, x^and@(X@x)@(Y@x)).


%------------------------------------------------------------------------------
%
%  Verbs lexicon.
%

:- discontiguous(v/7).

% Verb tense finiteness.
finite(pres).
finite(pret).

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
aux(Agr, Tns, prog, _) --> v(Agr, Tns, prog, aux, _).
aux(Agr, Tns, perf, _) --> v(Agr, Tns, perf, aux, _).
aux(Agr, Tns, dsup, _) --> v(Agr, Tns, dsup, aux, _).
aux(_/_, pres, mod, _) --> [X], {modal(X, _)}.
aux(_/_, pret, mod, _) --> [X], {modal(_, X)}.

  modal(can, could).
  modal(may, might).
  modal(shall, should).
  modal(will, would).

%
% Copular verb `be'.
%
v(Agr, Tns, prog, Sub, LF) --> [V], {b(Agr, Tns, V), b_scf(V, Sub, LF)}.

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
v(Agr, Tns, Sub, LF) --> v(Agr, Tns, _, Sub, LF).
v(_/_,  infin, Asp, Sub, LF) --> [V], {verb(V,_,_,_,_,Asp,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/1, pres,  Asp, Sub, LF) --> [V], {verb(V,_,_,_,_,Asp,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/2, pres,  Asp, Sub, LF) --> [V], {verb(V,_,_,_,_,Asp,Fs), v_scf(V,Fs,Sub,LF)}.
v(sg/3, pres,  Asp, Sub, LF) --> [V], {verb(_,V,_,_,_,Asp,Fs), v_scf(V,Fs,Sub,LF)}.
v(pl/_, pres,  Asp, Sub, LF) --> [V], {verb(V,_,_,_,_,Asp,Fs), v_scf(V,Fs,Sub,LF)}.
v(_/_,  pret,  Asp, Sub, LF) --> [V], {verb(_,_,V,_,_,Asp,Fs), v_scf(V,Fs,Sub,LF)}.
v(_/_,  presp, Asp, Sub, LF) --> [V], {verb(_,_,_,V,_,Asp,Fs), v_scf(V,Fs,Sub,LF)}.
v(_/_,  pastp, Asp, Sub, LF) --> [V], {verb(_,_,_,_,V,Asp,Fs), v_scf(V,Fs,Sub,LF)}.

  verb(do, does, did, doing, done,  dsup, [aux, np]).
  verb(have, has, had, having, had, perf, [aux, np]).

%
% Main verb lexicon.
%
verb(F1, F2, F3, F4, F5, simp, Fs) :- verb(F1, F2, F3, F4, F5, Fs).

  verb(bake, bakes, baked, baking, baked,   [nil, np, np/np]).
  verb(give, gives, gave, giving, given,    [np/np, np/to]).
  verb(go, goes, went, going, gone,         [nil]).
  verb(live, lives, lived, living, lived,   [nil]).
  verb(leave, leaves, left, leaving, left,  [nil, np]).
  verb(meet, meets, met, meeting, met,      [np]).
  verb(put, puts, put, putting, put,        [np/pp]).
  verb(see, sees, saw, seeing, seen,        [nil, np]).
  verb(support, supports, supported, supporting, supported, [np]).


%------------------------------------------------------------------------------
%
%  Particles lexicon.
%

% Determiners.
d(Num/3, p^term@Q@(x^p@x)) --> [D], {det(D, Num, Q)}.

  det(a,     sg, some).
  det(the,   _,  the).
  det(some,  _,  some).
  det(every, sg, every).

% Prepositions.
p(P, x^y^P@y@x) --> [P], {prep(P)}.
p(P, x^y^P@y@x) --> [P1, P2], {prep(P1, P2), atom_concat(P1, P2, P)}.

  prep(above).
  prep(below).
  prep(on).
  prep(under).
  prep(left, of).
  prep(right, of).


%------------------------------------------------------------------------------
%
%  Nouns lexicon.
%

% Proper nouns.
pn(sg/3, X) --> [X], {pn(X)}.

  pn(a).
  pn(b).
  pn(c).
  pn(d).
  pn(e).
  pn(f).

% Common nouns.
n(sg/3, x^Sg@x) --> [Sg], {noun(Sg, _Pl)}.
n(pl/3, x^Sg@x) --> [Pl], {noun(Sg, Pl)}.

  noun(table, tables).
  noun(block, blocks).
  noun(circle, circles).
  noun(square, squares).
  noun(parallelogram, parallelograms).
  noun(triangle, triangles).


%------------------------------------------------------------------------------
%
%  Adjectives lexicon.
%

a(x^A@x) --> [A], {adj(A)}.

  adj(blue).
  adj(circular).
  adj(green).
  adj(red).
  adj(square).
  adj(triangular).
  adj(yellow).
