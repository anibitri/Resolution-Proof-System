% Binary connectives
neg(X) :- \+ X.
and(X,Y) :- X, Y.
or(X,Y) :- X; Y.
imp(X,Y) :- \+ X; Y.
revimp(X,Y) :- X; \+ Y.
uparrow(X,Y) :- \+ and(X,Y).
downarrow(X,Y) :- \+ or(X,Y).
notimp(X,Y) :- \+ imp(X,Y).
notrevimp(X,Y) :- \+ revimp(X,Y).

% Equivalence connectives
equiv(X,Y) :- X=Y.
notequiv(X,Y) :- \+ equiv(X,Y).

% Conjunctive and disjunctive connectives
conjunctive(and(_, _)).
conjunctive(neg(or(_, _))).
conjunctive(neg(imp(_, _))).
conjunctive(neg(revimp(_, _))).
conjunctive(neg(uparrow(_, _))).
conjunctive(downarrow(_, _)).
conjunctive(notimp(_, _)).
conjunctive(notrevimp(_, _)).

disjunctive(neg(and(_, _))).
disjunctive(or(_, _)).
disjunctive(imp(_, _)).
disjunction(revimp(_, _)).
disjunctive(uparrow(_, _)).
disjunctive(neg(downarrow(_, _))).
disjunctive(neg(notimp(_, _))).
disjunctive(neg(notrevimp(_, _))).

% Alpha and Beta formulas
components(and(X, Y), X, Y).
components(neg(and(X, Y)), neg(X), neg(Y)).
components(or(X, Y), X, Y).
components(neg(or(X, Y)), neg(X), neg(Y)).
components(imp(X, Y), neg(X), Y).
components(neg(imp(X, Y)), X, neg(Y)).
components(revimp(X, Y), X, neg(Y)).
components(neg(revimp(X, Y)), neg(X), Y).
components(uparrow(X, Y), neg(X), neg(Y)).
components(neg(uparrow(X, Y)), X, Y).
components(downarrow(X, Y), neg(X), neg(Y)).
components(neg(downarrow(X, Y)), X, Y).
components(notimp(X, Y), X, neg(Y)).
components(neg(notimp(X, Y)), neg(X), Y).
components(notrevimp(X, Y), neg(X), Y).
components(neg(notrevimp(X, Y)), X, neg(Y)).

component(neg(neg(X)), X).
component(neg(true), false).
component(neg(false), true).

% Clause form
clauseform(X, Y) :- component(X, X1), clauseform(X1, Y).
clauseform(and(X, Y), CNF1) :- clauseform(X, CNF1), clauseform(Y, CNF2), append(CNF1, CNF2, CNF).
clauseform(or(X, Y), CNF) :- clauseform(X, CNF1), clauseform(Y, CNF2), findall(Disjunction, (member(A, CNF1), member(B, CNF2), append(A, B, Disjunction)), CNF).
clauseform(imp(X, Y), CNF) :- clauseform(or(neg(X), Y), CNF).
clauseform(revimp(X, Y), CNF) :- clauseform(or(X, neg(Y)), CNF).
clauseform(uparrow(X, Y), CNF) :- clauseform(neg(and(X, Y)), CNF).
clauseform(downarrow(X, Y), CNF) :- clauseform(neg(or(X, Y)), CNF).
clauseform(notimp(X, Y), CNF) :- clauseform(neg(imp(X, Y)), CNF).
clauseform(notrevimp(X, Y), CNF) :- clauseform(neg(revimp(X, Y)), CNF).
cluseform(equiv(X, Y), CNF) :- clauseform(and(imp(X, Y), imp(Y, X)), CNF).
clauseform(notequiv(X, Y), CNF) :- clauseform(neg(equiv(X, Y)), CNF).
clauseform(X, [[X]]).
