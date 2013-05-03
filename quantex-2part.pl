/*****************************************************************************

             Prolog Implementation of Scope Generation Algorithm

*****************************************************************************/


/*----------------------------------------------------------------------------
                           Representation of wffs:

A wff of the form 'p(arg1,...,argn)' is represented as the Prolog term
p(arg1',...,argn') where argi' is the encoding of the
subexpression argi.

A constant term is represented by the homonymous Prolog constant.

A variable term is represented either as a Prolog constant or a term of
the form x!n, where x is a constant and n is an integer.  This representation
is consistent with that used in reducer.pl.

A complex term is represented by the Prolog term term(quant,restrict')
where restrict' is the encoding of the property that forms the
restriction of the quantifier.  In particular, restrict' must be an
abstraction of the form x^wff.

This representation differs from (and generalizes and simplifies) that
in the original paper by Hobbs and Shieber.
----------------------------------------------------------------------------*/

:- use_module(library(lists)).
:- use_module('betanf').


/*----------------------------------------------------------------------------
                          Scope Generation Routines
----------------------------------------------------------------------------*/


% gen(Form,ScopedForm)
% ====================
%
%   Form       ==> a wff with in-place complex terms
%   ScopedForm <== a full scoping of Form

gen(Form, ScopedForm) :-
    pull(Form, true, ScopedForm).


% pull(Form, Complete?, ScopedForm)
% =================================
%
%   Form         ==> a wff with in-place complex terms
%   Complete?    ==> true iff only full scopings are allowed
%   ScopedForm   <== a full or partial scoping of Form
%
%   Applies terms at various level of embedding in Form, including
%   applying to the entire Form, and to opaque argument positions
%   inside Form.

pull(Form, Complete, ScopedForm) :-
    pull_opaque_args(Form, PulledOpaque),
    apply_terms(PulledOpaque, Complete, ScopedForm).


% pull_opaque_args(Form, ScopedForm)
% ================================
%
%   Form       ==> a term or a wff with in-place complex terms
%   ScopedForm <== Form with opaque argument positions recursively scoped
%
%   Scopes arguments of the given Form recursively.

pull_opaque_args(WffIn, WffOut) :-
    is_wff(WffIn),
    !,
    wff(WffIn, Pred, Args),
    pull_opaque_args(Pred, 1, Args, ScopedArgs),
    wff(WffOut, Pred, ScopedArgs).

pull_opaque_args(Term, Term).


% pull_opaque_args(Pred, ArgIndex, Args, ScopedArgs)
% ==================================================
%
%   Pred       ==> the predicate of the wff whose args are being scoped
%   ArgIndex   ==> the nindex of the argument currently being scoped
%   Args       ==> list of args from ArgIndex on
%   ScopedArgs <== Args with opaque argument positions recursively scoped
%
%   Scopes a given argument if opaque; otherwise, scopes its
%   subparts recursively.

% No more arguments.
pull_opaque_args(_Pred,_ArgIndex,[],[]) :- !.

% Current argument position is opaque; scope it.
pull_opaque_args(Pred, ArgIndex,
      [FirstArg|RestArgs],
      [ScopedFirstArg|ScopedRestArgs]) :-
    opaque(Pred,ArgIndex), !,
    pull(FirstArg,false,ScopedFirstArg),
    NextIndex is ArgIndex+1,
    pull_opaque_args(Pred, NextIndex, RestArgs, ScopedRestArgs).

% Current argument is not opaque; don't scope it.
pull_opaque_args(Pred, ArgIndex,
      [FirstArg|RestArgs],
      [ScopedFirstArg|ScopedRestArgs]) :-
    pull_opaque_args(FirstArg,ScopedFirstArg),
    NextIndex is ArgIndex+1,
    pull_opaque_args(Pred, NextIndex, RestArgs, ScopedRestArgs).


% apply_terms(Form, Complete?, ScopedForm)
% ========================================
%
%   Form         ==> a wff with in-place complex terms
%   Complete?    ==> true iff only full scopings are allowed
%   ScopedForm   <== a full or partial scoping of Form
%
%   Applies one or more terms to the Form alone (not to any embedded
%   forms.

apply_terms(Form, _Complete, Form) :-
    not(term(Form,_Term)),
    !.

apply_terms(Form, false, Form).

apply_terms(Form, Complete, ScopedForm) :-
    applicable_term(Form, Term),
    apply_term(Term, Form, AppliedForm),
    apply_terms(AppliedForm, Complete, ScopedForm).


% apply_term(Term,Form,NewForm)
% ==============================
%
%   Term      ==> a complex term
%   Form      ==> the wff to apply Term to
%   NewForm   <== Form with the quantifer wrapped around it

apply_term(term(Quant,X^Restrict), Body, Wff) :-
    % scope the restriction of the term
    pull(Restrict, false, PulledRestrict),
    % replace the inplace term with the variable
    betanf:is_variable(X, Name, Color),
    betanf:fresh(Name,Color,Body,Color,MaxColor),
    NewColor is MaxColor+1,
    betanf:is_variable(Var, X, NewColor),
    subst(Var,term(Quant,X^Restrict), Body, BodyOut),
    wff(Wff, Quant, [X^PulledRestrict, Var^BodyOut]).


% applicable_term(Form, Term)
% ===========================
%
%   Form ==> an expression in the logical form language
%   Term <== a top-level term in Form (that is, a term embedded in
%        no other term) which is not free in any variable bound
%        along the path from Form to the Term.

applicable_term(Form, Term) :-
    applicable_term(Form, Term, []).


% applicable_term(Form,Term,BlockingVars)
% =======================================
%
%   Form ==> an expression in the logical form language
%   Term <== a top-level term in Form (that is, a term embedded in
%        no other term) which is not free in any variable bound
%        along the path from Form to the Term.
%   BlockingVars ==>
%        a list of variables bound along the path so far

% A variable is not an applicable top-level term...
applicable_term(Term, _, _) :-
    var(Term),
    !,
    fail.

% A term is an applicable top-level term...
applicable_term(term(Q,R),term(Q,R), BVs) :-
    % if it meets the definition.
    absent_list(BVs, R).

% An applicable term of the restriction or body of a quantifier is applicable
% only if the variable bound by the quantifier is not free in the term.
applicable_term(Wff ,Term, BVs) :-
    is_wff(Wff),
    wff(Wff, Quant,[X^Restrict,Y^Body]),
    quantifier(Quant), !,
    (applicable_term(Restrict,Term,[X|BVs]);
     applicable_term(Body,Term,[Y|BVs])).

% An applicable term of an argument list is an applicable term of the wff.
applicable_term(Wff, Term, BVs) :-
    is_wff(Wff),
    wff(Wff, _Pred, Args),
    applicable_term(Args, Term, BVs).

% An applicable term of any argument is an applicable term of the whole
% list.
applicable_term([F|R],Res, BVs) :-
    applicable_term(F,Res,BVs) ;
    applicable_term(R,Res,BVs).

% Note the absence of a rule looking for applicable terms inside of
% complex terms.  This limits applicable terms to be top-level.


/*----------------------------------------------------------------------------
                      Scope Generation Utility Routines
----------------------------------------------------------------------------*/


% term(Form, Term)
% ================
%
%   Form ==> an expression in the logical form language
%   Term <== a top-level term in Form (that is, a term embedded in
%        no other term)

term(X, _) :-
    var(X),
    !,
    fail.

term(term(Q,R),term(Q,R)).

term(Wff,Term) :-
    is_wff(Wff),
    wff(Wff, _Pred, Args),
    term(Args,Term).

term([F|R],Res) :-
    term(F,Res) ; term(R,Res).

% Note the absence of a rule looking for top_level terms inside of
% complex terms.  This is acceptable since we only use term as a
% predicate checking if any terms exist and don't rely on a complete
% coverage.


% free_in(Variables,Form)
% =======================

absent_list([], _Form).

absent_list([Var|Vars], Form) :-
    betanf:absent(Var, Form),
    absent_list(Vars, Form).


% wff(Wff, Pred, Args)
% ====================
%
% Holds if the Wff consists of the predicate Pred applied to the
% arguments listed in Args.
%
%   Wff  ==> representation of a wff
%   Pred <== the predicate symbol in Wff
%   Args <== list of the args in Wff

wff(Wff, Pred, Args) :-
    Wff =.. [Pred|Args].

is_wff(Wff) :-
    not(is_term(Wff)),
    not(is_list(Wff)).

is_term(term(_,_)).


/*----------------------------------------------------------------------------
                           Generic Prolog Utilities
----------------------------------------------------------------------------*/


% rec_member(Element,Term)
% ========================

rec_member(Element1,Element2) :- Element1 == Element2, !.
rec_member(_Element,Other) :- atomic(Other), !, fail.
rec_member(_Element,Other) :- var(Other), !, fail.
rec_member(Element,[First|Rest]) :- !,
    (rec_member(Element,First) ;
     rec_member(Element,Rest)).
rec_member(Element,Term) :-
    Term =.. List,
    rec_member(Element,List).


% subst(New,Old,In,Out)
% =====================
%
%   Substitutes the term New for all occurrences of the term Old in
%   the term In yielding the term Out.

subst(New,Old,Old,New) :- !.
subst(_New,_Old,[],[]) :- !.
subst(_New,_Old,Atom,Atom) :- atomic(Atom), !.
subst(New,Old,[First|Rest],[OutFirst|OutRest]) :- !,
    subst(New,Old,First,OutFirst),
    subst(New,Old,Rest,OutRest).
subst(New,Old,In,Out) :-
    In =.. List,
    subst(New,Old,List,OutList),
    Out =.. OutList.


% not(P)
% ======
%
%   Fails iff P succeeds.

not(F) :- F, !, fail.
not(_F).


% remove(Element,List, NewList)
% =============================

remove(_Element,[],[]).

remove(Element,[Element|List],NewList) :- !,
    remove(Element,List,NewList).

remove(Element,[Other|List],[Other|NewList]) :-
    remove(Element,List,NewList).


/*----------------------------------------------------------------------------
                 Test Formulas
----------------------------------------------------------------------------*/


% quantifier(Quant)
% =================

quantifier(every).
quantifier(some).
quantifier(most).
quantifier(a).
quantifier(few).
quantifier(many).


test(Id) :-
    test(Id,W),
    bagof(R,gen(W,R),B),
    print('Unscoped: '), write(W), nl,
    print('Scoped: '), nl,
    print_bag(B).

print_bag([]).
print_bag([Sol|Rest]) :-
    write(Sol), nl,
    print_bag(Rest).

% "Every man sleeps."
% One complex term.  One reading.
test(1, sleeps(term(every,m^man(m)))).

% "Every man loves some woman."
% Two sibling complex terms.  Two readings.
test(2, loves(term(every,m^man(m)),
              term(some,w^woman(w)))).

% "Every department in most companies folds."
% Two complex terms, one embedded.  Two readings.
test(3, folds(term(every,
                   d^and(department(d),
                         in(d, term(most, c^company(c))))))).

% Should be 1 reading (blocking variable).
test('3a', foo(term(every, d^and(department(d),
                                 in(d, term(most, c^company(c,d))))))).

% "Every representative of a company saw most samples."
% 5 readings.
test(4, saw(term(every, r^and(representative(r),
                              of(r, term(a, c^company(c))))),
            term(most,s^sample(s)))).

% "Some representative of every department in most companies
%   sees few samples."
% 14 readings.
test(5, see(term(some, r^and(representative(r),
                             of(r, term(every, d^and(department(d),
                                                     in(d, term(most,c^company(c)))))))),
            term(few,s^sample(s)))).

% "Some of every of most companies saw few of many companies."
% 42 readings.
test(6, saw(term(some, r^of(r, term(every, d^in(d,term(most,c^company(c)))))),
            term(few, f^in(f,term(many,e^company(e)))))).

% Every man seems to love some woman."
% "seem" is opaque in its first argument.
% 6 readings.
opaque(seem,1).
test(7, seem(loves(term(every,m^man(m)),
                   term(some,w^woman(w))))).

% Test of blocking variables.
% 1 reading.
test(8, foo(term(every, d^and(department(d),
                              in(d, term(most, c^ company(c, d))))))).

% Test of blocking variables
% 2 readings.
test(9, foo(term(every, d^and(department(d),
                              in(d, term(most, c^ company(c,d))))),
            term(some, y^ p(y)))).

% Same as 9 but no free variable in embedded term (for comparison).
% 5 readings.
test(10, foo(term(every, d^and(department(d),
                               in(d, term(most, c^ company(c))))),
             term(some, y^ p(y)))).

% Test of blocking variable within opaque position
% 2 readings.
test(11, f(term(every, x^seem( p(term(some, y^ g(x, y))))))).

% Test of opaque within transparent position
% 2 readings.
test(12, f(seem(p(term(some, y^ g(y)))))).

% Test of blocking variable within opaque position.
% 2 readings.
test(13, seem(p(term(every, x^f(term(some, y^ g(x, y) )))))).

% Same as 13 but no free variable in embedded term (for comparison).
% 5 readings.
test(14, seem(p(term(every, x^f(term(some, y^ g(y))))))).
