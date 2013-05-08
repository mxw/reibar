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
%  We use DCG rules for push and pop, and regular predicates elsewhere.
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

%cp(cp(dp(d_(np(n_(n(N/W))))), C_t), C_i) -->
%  wp(W, _, WPi),
%  cstack_push(rel, WPi, N, Depth, W),
%  c_(C_t, C_i),
%  { cstack_depth(Depth) }.

c_(c_(IPt), IPi) --> ip(IPt, IPi).

% Auxiliary complementizer.
c_(c_(c(N/Aux), IPt), IPi) -->
  aux(Agr, Tns, Gov, Aux, LF),
  { finite(Tns) },
  cstack_push(aux, LF, N, Depth, Tns/Gov),
  ip(Agr, _, Gov, IPt, IPi),
  { cstack_depth(Depth) }.

% Main verb complementizer (be/have).
c_(c_(c(N/V), IPt), IPi) -->
  v(Agr, Tns, Gov, Sub, v(V), LF),
  { finite(Tns), aspect(Gov) },
  cstack_push(verb, LF, N, Depth, Tns/Sub),
  ip(Agr, _, simp, IPt, IPi),
  { cstack_depth(Depth) }.


%% rp(+Agr, +Hum, -T, -I)
%
% Relative clause.  Functions syntactically as a complementizer phrase, but has
% distinct rules for construction.

rp(Agr, Hum, cp(Wh, c_(C, IPt)), IPi) -->
  rrel(Hum, Depth, Wh, C, _),
  ip(Agr, Tns, _, IPt, IPi),
  { finite(Tns) },
  { cstack_depth(Depth) }.


%% rel(+Hum, -Depth, -Wt, -C, -I)
%
% Relativizer.  Hum is the antecedent's humanity---personal or impersonal, and
% in the latter case, also location, time, etc.

% Subject.
rel(Hum, Depth, dp(N/Wh), c([]), lf) -->
  whpro(Wh, nom, Hum, bound),
  cstack_push(nom, lf, N, Depth, _).

% Object of verb or stranded preposition (detached).
rel(Hum, Depth, dp(N/Wh), c([]), lf) -->
  whpro(Wh, obl, Hum, bound),
  cstack_push(obl, lf, N, Depth, _).

% Object of fronted preposition (attached).
rel(Hum, Depth, pp(Pt, N/Wh), c([]), lf) -->
  p(Prep, Pt, _),
  whpro(Wh, obl, Hum, bound),
  cstack_push(pp, lf, N, Depth, Prep).

% Possessive.
%rel(Hum, Depth, Wh, c([]), lf) -->
  % whose DP
  %cstack_push(gpn, lf, N, Depth, Wh).


%% rrel(+Hum, -Depth, -Wt, -C, -I)
%
% Restrictive relativizer.  Additionally includes `that' and null relativizers.

rrel(Hum, Depth, Wh, C, lf) --> rel(Hum, Depth, Wh, C, _).

rrel(_, Depth, dp(N/wh), c(that), lf) --> [that],
  cstack_push(nom, lf, N, Depth, _).
rrel(_, Depth, dp(N/wh), c(that), lf) --> [that],
  cstack_push(obl, lf, N, Depth, _).
rrel(_, Depth, dp(N/wh), c([]), lf) -->
  cstack_push(obl, lf, N, Depth, _).


%% nrel(+Hum, -Depth, -Wt, -C, -I)
%
% Non-restrictive relativizer.  Additionally includes "D NP of which/whom".

nrel(Hum, Depth, Wh, C, lf) --> rel(Hum, Depth, Wh, C, _).


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
  { finite(Tns) }.

ip(Agr, Tns, Gov, ip(DPt, I_t), I_i@DPi) -->
  dp(Agr, DPt, DPi),
  i_(_, Tns, Gov, I_t, I_i).

% Relative clause with subject gap.
ip(Agr, Tns, _, ip(dp(t/N), I_t), IPi) -->
  cstack_pop(Case, NPi, N, _),
  { case_role(Case, sbj) },
  i_(Agr, Tns, _, I_t, I_i),
  { and(NPi, I_i, IPi) }.

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
  \+ cstack_pop(aux, _, _, _/mod),
  mc(MCt, MCi).

mp(_, Tns, mp(m(t/N), MCt), MCi) -->
  cstack_pop(aux, _, N, Tns/mod),
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
  \+ cstack_pop(aux, _, _, _/perf),
  perfc(PerfCt, PerfCi).

perfp(_, Tns, perfp(perf(t/N), PerfCt), PerfCi) -->
  cstack_pop(aux, _, N, Tns/perf),
  perfc(PerfCt, PerfCi).

perfc(ProgPt, ProgPi) --> progp(_, pastp, ProgPt, ProgPi).
perfc(VPt, VPi) --> vp(_, pastp, VPt, VPi).


%% Progressive aspect.
%
% progp(+Agr, -Tns, -T, -I)   Progressive phrase.

progp(Agr, Tns, progp(prog(Aux), VPt), VPi) -->
  aux(Agr, Tns, prog, Aux, _),
  \+ cstack_pop(aux, _, _, _/prog),
  vp(_, presp, VPt, VPi).

progp(_, Tns, progp(prog(t/N), VPt), VPi) -->
  cstack_pop(aux, _, N, Tns/prog),
  vp(_, presp, VPt, VPi).


%% Do-support.
%
% dsup(+Agr, -Tns, -T, -I)    Fill `do' into Tns.

dsup(Agr, Do, VPt, VPi) -->
  aux(Agr, _, dsup, Do, _),
  \+ cstack_pop(aux, _, _, _/dsup),
  vp(_, infin, VPt, VPi).

dsup(_, t/N, VPt, VPi) -->
  cstack_pop(aux, _, N, _/dsup),
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
  \+ cstack_pop(verb, _, _, _).
vopt(_, Tns, Sub, v(t/N), Vi) -->
  cstack_pop(verb, Vi, N, Tns/Sub).


%% vp(+Agr, -Tns, -T, -I)
%
% Verb phrases.  We delegate verb subcategories with one or two theta roles to
% v_/4 and those with three theta roles to vc/5.

vp(Agr, Tns, vp(V_t), V_i) --> v_(Agr, Tns, V_t, V_i).

vp(Agr, Tns, vp(v_(v(N/v), vp(Spec, V_t))), V_i) -->
  v(Agr, Tns, Sub, v(V), Vi),
  vc(Sub, Vi, Spec, Comp, VCi),
  { c_incr(N) },
  vv(v_(v(V/N), Comp), VCi, V_t, V_i).


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

% Relative clause with object gap.
v_(Agr, Tns, VVt, VVi) -->
  v(Agr, Tns, np, Vt, Vi),
  cstack_pop(Case, NPi, N, _),
  { case_role(Case, obj) },
  { and(NPi, Vi, V_i) },
  vv(v_(Vt, dp(t/N)), V_i, VVt, VVi).


%% vc(+Sub, -Spec, -Comp, -DP, -PP)
%
% Verb complements.  Used for verbs with three theta roles in order to properly
% generate the syntax tree and handle synonymity.  Spec and Comp are the
% specifier and complement in the tree; VC is the logical form of the phrase.

vc(np/pp, V, Spec, Comp, VC) -->
  dp(_, Spec, DP), pp(Comp, PP),
  { vclf(V, DP, PP, VC) }.
vc(np/P, V, Spec, Comp, VC) -->
  dp(_, Spec, DP), pp(P, Comp, PP),
  { vclf(V, DP, PP, VC) }.
vc(np/np, V, Spec, Comp, VC) -->
  dp(_, Spec, IO), dp(_, Comp, DP),
  { p(to, _, P, _, _) },
  { vclf(V, DP, P@IO, VC) }.

% Relative clause with complement gap.
vc(np/np, V, Spec, dp(t/N), (P@IO)@VPi) -->
  dp(_, Spec, IO),
  cstack_pop(Case, NPi, N, _),
  { case_role(Case, obj) },
  { p(to, _, P, _, _) },
  { and(V, NPi, VPi) }.

% Logical form for verb complements.
vclf(V, DP, PP, x^PP@(V@DP@x)).


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

d_(Agr, d_(np(n_(PRt))), PRi) --> pr(Agr, PRt, PRi).
d_(Agr, d_(Dt, NPt), Di@NPi) --> d(Agr, Dt, Di), np(Agr, NPt, NPi).


%% np(+Agr, -T, -I)
%
% Noun phrases.

np(Agr, np(N_t), N_i) --> n_(Agr, N_t, N_i).


%% n_(+Agr, -T, -I)
%
% Noun bars.

n_(Agr, N_t, N_i) --> n(Agr, Nt, Ni), nn(Agr, n_(Nt), Ni, N_t, N_i).
n_(Agr, N_t, N_i) -->
  ap(APt, APi),
  n(Agr, Nt, Ni),
  { and(Ni, APi, NA) },
  nn(Agr, n_(APt, Nt), NA, N_t, N_i).


%% nn(+Agr, +N_t, +N_i, -T, -I)
%
% Noun adjuncts.  Adjoins prepositional phrases and relative clauses to noun
% bars.

nn(_, N_t, N_i, N_t, N_i) --> [].
nn(_, N_t, N_i, NNt, NNi) -->
  pp(PPt, PPi),
  { and(N_i, PPi, And) },
  nn(_, n_(N_t, PPt), And, NNt, NNi).
nn(Agr, N_t, N_i, n_(N_t, CPt), CPi) --> rp(Agr, _, CPt, CPi).


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

v_scf(_, Fs, aux,   _)         :- member(aux, Fs).
v_scf(V, Fs, nil,   y^V@y)     :- member(nil, Fs).
v_scf(V, Fs, np,    x^y^V@y@x) :- member(np, Fs).
v_scf(V, Fs, np/X,  x^y^V@y@x) :- member(np/X, Fs).


%% Auxiliary verbs.
%
% aux(?Agr, ?Tns, ?Gov, -T, -I)
% modal(-Pres, -Pret)
%
% We share the paradigm descriptions of `be' and `have' with the verb lexical
% predicate, and additionally define modal auxiliaries.

aux(Agr, Tns, prog, X, _) --> v(Agr, Tns, prog, aux, v(X), _).
aux(Agr, Tns, perf, X, _) --> v(Agr, Tns, perf, aux, v(X), _).
aux(Agr, Tns, dsup, X, _) --> v(Agr, Tns, dsup, aux, v(X), _).
aux(_/_, pres, mod, X, _) --> [X], {modal(X, _)}.
aux(_/_, pret, mod, X, _) --> [X], {modal(_, X)}.

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


%% v(?Agr, ?Tns, ?Gov, ?Sub, -T, -I)
%
% Main verbs.  Features include agreement (number and person), tense,
% governance (modality, aspect, etc.), and subcategorization frame.

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

% Lexicon shorthand.
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
