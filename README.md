# Resolution-Proof-System

This is an implementation of a resolution theorem prover in Prolog. The prover tests whether a given propositional formula (the consequence) is a logical consequence of a set of propositional formulas (the premises). 

The system first transforms formulas into clause form (conjunctive normal form) and then applies resolution rules to determine logical consequence. The outermost interface predicate is:

- `test(Premises, Consequence)`

- Premises is a list of propositional formulas.
- Consequence is a single propositional formula.

# Running the program

- cd into the direcory where resolution.pl is
- Run `swipl resolution.pl`
- To exit the Prolog environment, run `halt.`

## Test Cases

- `test([x imp y, x], y).`
- `test([neg x imp y], neg (x notimp y) imp y).`
- `test([x imp y, y imp z], neg neg z or neg x).`
- `test([], (x imp (y imp z)) equiv ((x imp y) imp z)).`
- `test([x notequiv y], y notequiv x).`
- `test([], (x notequiv (y notequiv z)) equiv ((x notequiv y) notequiv z)).`
- `test([neg (x uparrow y)], neg x downarrow neg y).`
- `test([(z notrevimp u) or (u uparrow neg v)], neg (neg x revimp neg y)).`
- `test([x or y, neg (neg y notrevimp z)], neg neg (z equiv x) notrevimp y).`
- `test([neg (z notrevimp y) revimp x], (x or w) imp ((y imp z) or w)).`

The outputs for the test cases above are commented in the beginning of the file. For reference:

- /*
-    YES
-    YES
-    YES
-    NO
-    YES
-    YES
-    YES
-    NO
-    NO
-    YES
- */