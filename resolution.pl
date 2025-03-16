#Binary connectives
neg(X) :- \+ X.
X and Y :- X, Y.
X or Y :- X; Y.
X imp Y :- neg(X); Y.
X revimp Y:- X; neg(Y).
X uparrow Y :- neg(X and Y).
X downarrow Y :- neg(X or Y).
X notimp Y :- neg(X imp Y).
X notrevimp Y:- neg(X revimp Y).

# Equivalence connectives
X equiv Y :- X imp Y, Y imp X.
X notequiv Y :- neg(X equiv Y).

/** member(Item, List) :- Item occurs in List
*/

member(X, [X | _]).
member(X, [_ | Tail]) :- member(X, Tail).

/** remove(Item, List, Newlist) :- Newlist is the result of removing all occurrences of Item from List.
*/

remove(_, [], []).
remove(X, [X | Tail], Newtail) :- remove(X, Tail, Newtail).
remove(X, [Head | Tail], [Head | Newtail]) :- not(X=Head), remove(X, Tail, Newtail).

/** unary(X) :- X is a double negation or a negated constant.
*/

unary(neg neg _).
unary(neg true).
unary(neg false).

# Conjunctive and disjunctive connectives
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
disjunction(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

#Alpha and Beta formulas
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

component(neg neg X, X).
component(neg true, false).
component(neg false, true).

#Clause form
clauseform(X, Y) :- component(X, X1), clauseform(X1, Y).
clauseform(X and Y, CNF1) :- clauseform(X, CNF1), clauseform(Y, CNF2), append(CNF1, CNF2, CNF).
clauseform(X or Y, CNF) :- clauseform(X, CNF1), clauseform(Y, CNF2), findall(Disjunction, (member(A, CNF1), member(B, CNF2), append(A, B, Disjunction)), CNF).
clauseform(X imp Y, CNF) :- clauseform(or(neg(X), Y), CNF).
clauseform(X revimp Y, CNF) :- clauseform(or(X, neg(Y)), CNF).
clauseform(X uparrow Y, CNF) :- clauseform(neg(and(X, Y)), CNF).
clauseform(X downarrow Y, CNF) :- clauseform(neg(or(X, Y)), CNF).
clauseform(X notimp Y, CNF) :- clauseform(neg(imp(X, Y)), CNF).
clauseform(X notrevimp Y, CNF) :- clauseform(neg(revimp(X, Y)), CNF).
cluseform(X equiv Y, CNF) :- clauseform(and(imp(X, Y), imp(Y, X)), CNF).
clauseform(X notequiv Y, CNF) :- clauseform(neg(equiv(X, Y)), CNF).
clauseform(X, [[X]]).

/** singleStep(Old, New) :- New is the result of applying a single step of the expansion to Old, which is a generalized
conjunction of generalized disjunctions.
*/
singleStep([Disjunction | Rest], New) :-
    member(Formula, Disjunction),
    unary(Formula),
    component(Formula, Newformula),
    remove(Formula, Disjunction, Temporary),
    Newdisjunction = [Newformula | Temporary],
    New = [Newdisjunction | Rest].

singleStep([Disjunction | Rest], New) :-
    member(Beta, Disjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo),
    remove(Beta, Disjunction, Temporary),
    Newdis = [Betaone, Betatwo | Temporary],
    New = [Newdis | Rest].

singleStep([Disjunction | Rest], New) :-
    member(Alpha, Disjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo),
    remove(Alpha, Disjunction, Temporary),
    Newdisone = [Alphaone | Temporary],
    Newdistwo = [Alphatwo | Temporary],
    New = [Newdisone, Newdistwo | Rest].

singleStep([Disjunction | Rest], [Disjunction | Newrest]) :-
    singleStep(Rest, Newrest).

/** expand(Old, New) :- New is the result of applying singleStep as many times as possible, starting with Old.
*/

expand(Con, Newcon) :-
    singleStep(Con, Temp),
    expand(Temp, Newcon).

expand(Con, Con).

clauseform(X, Y) :- expand([[X]], Y).

/** singleStepDual(Old, New) :- New is the result of applying a single step of the expansion to Old, which is a generalized
disjunction of generalized conjunctions.
*/

singleStepDual([Conjunction | Rest], New) :-
    member(Formula, Conjunction),
    unary(Formula),
    component(Formula, Newformula),
    remove(Formula, Conjunction, Temporary),
    New = [Newconjunction | Rest],
    Newconjunction = [Newformula | Temporary].

singleStepDual([Conjunction | Rest], New) :-
    member(Alpha, Conjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo),
    remove(Alpha, Conjunction, Temporary),
    Newcon = [Alphaone, Alphatwo | Temporary],
    New = [Newcon | Rest].

singleStepDual([Conjunction | Rest], New) :-
    member(Beta, Conjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo),
    remove(Beta, Conjunction, Temporary),
    Newconone = [Betaone | Temporary],
    Newcontwo = [Betatwo | Temporary],
    New = [Newconone, Newcontwo | Rest].

singleStepDual([Conjunction | Rest], [Conjunction | Newrest]) :-
    singleStepDual(Rest, Newrest).

/** expandDual(Old, New) :- New is the result of applying singleStepDual as many times as possible, starting with Old.
*/

expandDual(Dis, Newdis) :-
    singleStepDual(Dis, Temp),
    expandDual(Temp, Newdis).

expandDual(Dis, Dis).

dualclauseform(X, Y) :- expandDual([[X]], Y).