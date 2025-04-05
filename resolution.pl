/*
    YES
    YES
    YES
    NO
    YES
    YES
    YES
    NO
    NO
    YES
*/

:- op(140, fy, neg).
:- op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

member(X, [X|_]).
member(X, [_|Tail]) :- member(X, Tail).

remove(_, [], []).
remove(X, [X|Tail], NewTail) :- remove(X, Tail, NewTail).
remove(X, [Head|Tail], [Head|NewTail]) :- \+ X = Head, remove(X, Tail, NewTail).

/*
    ELIMINATE EQUIVALENCES

    elim_equiv(+Formula, -NewFormula)
    This predicate eliminates equivalences and non-equivalences from a formula.
    It replaces 'equiv' with the conjunction of two implications and 'notequiv' with the disjunction of two negated literals.
    equiv 'A equiv B' is replaced with '(A imp B) and (B imp A)'.
    notequiv 'A notequiv B' is replaced with '(A and neg B) or (B and neg A)'.
    The predicate is recursive and works on the structure of the formula.
*/
elim_equiv(X, X) :- atomic(X), !.
elim_equiv(true, true).
elim_equiv(false, false).
elim_equiv(neg F, neg F1) :-
    elim_equiv(F, F1).
elim_equiv(F1 and F2, E1 and E2) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 or F2, E1 or E2) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 imp F2, E1 imp E2) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 revimp F2, E1 revimp E2) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 uparrow F2, E1 uparrow E2) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 downarrow F2, E1 downarrow E2) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 notimp F2, E1 notimp E2) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 notrevimp F2, E1 notrevimp E2) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 equiv F2, (E1 imp E2) and (E2 imp E1)) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).
elim_equiv(F1 notequiv F2, ((E1 and neg E2) or (E2 and neg E1))) :-
    elim_equiv(F1, E1), elim_equiv(F2, E2).

% Conjunctive and Disjunctive Definitions
conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

% Unary Definitions
unary(neg(neg(_))).
unary(neg(true)).
unary(neg(false)).

component(neg(neg(X)), X).
component(neg(true), false).
component(neg(false), true).

% Break down complex formulas into components
components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).

% Single-Step Expansion for Clauseform Conversion
singleStep([Disjunction|Rest], New) :-
    member(Formula, Disjunction),
    unary(Formula),
    component(Formula, NewFormula),
    remove(Formula, Disjunction, Temporary),
    NewDisjunction = [NewFormula|Temporary],
    New = [NewDisjunction|Rest].

singleStep([Disjunction|Rest], New) :-
    member(Beta, Disjunction),
    disjunctive(Beta),
    components(Beta, BetaOne, BetaTwo),
    remove(Beta, Disjunction, Temporary),
    NewDis = [BetaOne, BetaTwo|Temporary],
    New = [NewDis|Rest].

singleStep([Disjunction|Rest], New) :-
    member(Alpha, Disjunction),
    conjunctive(Alpha),
    components(Alpha, AlphaOne, AlphaTwo),
    remove(Alpha, Disjunction, Temporary),
    NewDisOne = [AlphaOne|Temporary],
    NewDisTwo = [AlphaTwo|Temporary],
    New = [NewDisOne, NewDisTwo|Rest].

singleStep([Disjunction|Rest], [Disjunction|NewRest]) :-
    singleStep(Rest, NewRest).

expand(Con, NewCon) :-
    (   singleStep(Con, Temp)
    ->  expand(Temp, NewCon)
    ;   NewCon = Con
    ).

clauseform(X, Y) :- expand([[X]], Y).

% Dual Clauseform
singleStepDual([Conjunction|Rest], New) :-
    member(Formula, Conjunction),
    unary(Formula),
    component(Formula, NewFormula),
    remove(Formula, Conjunction, Temporary),
    NewConjunction = [NewFormula|Temporary],
    New = [NewConjunction|Rest].

singleStepDual([Conjunction|Rest], New) :-
    member(Alpha, Conjunction),
    conjunctive(Alpha),
    components(Alpha, AlphaOne, AlphaTwo),
    remove(Alpha, Conjunction, Temporary),
    NewCon = [AlphaOne, AlphaTwo|Temporary],
    New = [NewCon|Rest].

singleStepDual([Conjunction|Rest], New) :-
    member(Beta, Conjunction),
    disjunctive(Beta),
    components(Beta, BetaOne, BetaTwo),
    remove(Beta, Conjunction, Temporary),
    NewConOne = [BetaOne|Temporary],
    NewConTwo = [BetaTwo|Temporary],
    New = [NewConOne, NewConTwo|Rest].

singleStepDual([Conjunction|Rest], [Conjunction|NewRest]) :-
    singleStepDual(Rest, NewRest).

expandDual(Dis, NewDis) :-
    (   singleStepDual(Dis, Temp)
    ->  expandDual(Temp, NewDis)
    ;   NewDis = Dis
    ).

dualclauseform(X, Y) :- expandDual([[X]], Y).

% Resolution Rules
complement(neg(X), X) :- !.
complement(X, neg(X)) :- atomic(X).

resolve(C1, C2, Resolvent) :-
    member(Lit, C1),
    complement(Lit, CompLit),
    member(CompLit, C2),
    delete(C1, Lit, R1),
    delete(C2, CompLit, R2),
    append(R1, R2, Temp),
    sort(Temp, Resolvent).

resolution(ClauseSet, NewClauseSet) :-
    findall(Resolvent,
        ( member(C1, ClauseSet),
          member(C2, ClauseSet),
          resolve(C1, C2, Resolvent),
          \+ member(Resolvent, ClauseSet)
        ),
        Resolvents),
    Resolvents \= [],
    append(ClauseSet, Resolvents, TempClauseSet),
    sort(TempClauseSet, UpdatedClauseSet),
    ( member([], UpdatedClauseSet) ->
          NewClauseSet = UpdatedClauseSet
      ; resolution(UpdatedClauseSet, NewClauseSet)
    ).
resolution(ClauseSet, ClauseSet).

% Combining Premises 
and_list([], true).  % no premises => true
and_list([F], F).
and_list([F|Fs], and(F, Rest)) :-
    and_list(Fs, Rest).

% Test Predicate
% test(Premises, Consequence) prints 'YES' if Consequence is a logical consequence of Premises, and 'NO' otherwise.
test(Premises, Consequence) :-
    % First, eliminate equiv and notequiv from premises and consequence.
    maplist(elim_equiv, Premises, PremisesNoEquiv),
    elim_equiv(neg(Consequence), NegConseq),
    and_list(PremisesNoEquiv, PremisesConj),
    Overall = and(PremisesConj, NegConseq),
    clauseform(Overall, CNF),
    resolution(CNF, Result),
    ( member([], Result) ->
          write('YES'), nl
      ; write('NO'), nl
    ).
