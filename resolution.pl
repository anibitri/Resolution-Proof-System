?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp ]).



member(X, [X | _]).
member(X, [_ | Tail]) :- member(X, Tail).



remove(_, [], []).
remove(X, [X | Tail], Newtail) :- remove(X, Tail, Newtail).
remove(X, [Head | Tail], [Head | Newtail]) :- not(X=Head), remove(X, Tail, Newtail).



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



unary(neg neg _).
unary(neg true).
unary(neg false).



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



expand(Con, Newcon) :-
    singleStep(Con, Temp),
    expand(Temp, Newcon).

expand(Con, Con).

clauseform(X, Y) :- expand([[X]], Y).



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



expandDual(Dis, Newdis) :-
    singleStepDual(Dis, Temp),
    expandDual(Temp, Newdis).

expandDual(Dis, Dis).

dualclauseform(X, Y) :- expandDual([[X]], Y).

% Equivalence connectives
equiv(X,Y) :- X = Y.
notequiv(X,Y) :- \+ equiv(X,Y).



% In this new version we use the clauseform predicate from normalForm.pl.
% It converts a formula into its clausal form.

% Resolution rule implementation
resolve(C1, C2, Resolvent) :-
    member(Lit, C1),
    complement(Lit, CompLit),
    member(CompLit, C2),
    delete(C1, Lit, R1),
    delete(C2, CompLit, R2),
    append(R1, R2, Temp),
    sort(Temp, Resolvent).

% Complement of a literal
complement(neg(X), X) :- !.
complement(X, neg(X)) :- atomic(X).

% Resolution loop
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

% Helper to combine multiple premises with AND
and_list([], true).  % Base case: no premises means "true"
and_list([F], F).    
and_list([F|Fs], and(F, Rest)) :-
    and_list(Fs, Rest).

% Test predicate - invoked from check.py
test(Premises, Consequence) :-
    and_list(Premises, PremisesConj),
    Overall = and(PremisesConj, neg(Consequence)),
    clauseform(Overall, CNF),
    resolution(CNF, Result),
    ( member([], Result) ->
          write('YES'), nl
      ; write('NO'), nl
    ).

