# Resolution-Theorem-Prover
A program which proves a theorem as correct or incorrect given a knowledge base. 

# Summary
The resolution theorem prover takes a series of statements as axioms, matches those axioms to literals in the theorem, then resolves those statements to nil if possible. The main function rtp determines success or failure based upon whether the theorem was resolved to nil or was repeatedly passed into the function respectively.
# Running the Program
1. Open Lisp.
2. (load “rtp.lisp”)
3. File is now loaded and can be run and tested. Test cases are appended at the bottom of the file.
# How it Works
Two major components of the program provide an ability to resolve a theorem from an axiom set. The first component, a pattern matcher, uses the unify.lisp file to check if two literals can be matched together. If the literals can in fact be unified, the program returns bindings necessary to ensure the program continues to hold variables to the values they were originally assigned.
The second component is the resolution control structure. When the rtp function is called, each axiom compares each literal in the axiom to a literal in the theorem. If they’re negative of one another (one has a not as its first element and the other doesn’t, i.e. car = not or car != not, then they potentially resolve. The function then takes the not away from one of the literals, (cadr of the list), and those two things are unified. If they unify, then those two things resolve. Then the resolvent is evaluated, (eliminate negated clauses). Then rtp is called again passing in the bindings that you got from unify along with each theorem so that the program may know when it cannot proceed.
# Problems Encountered
Attempting to evaluate computable predicates took some time, but was eventually fixed by attempting to evaluate each literal and then by suppressing errors. I am not sure if this is the most efficient way to operate, but I was unsure of how to use marcos similar to the variable notation in the unify function (?x1).
Determining when the theorem prover failed was challenging, but I resolved this by comparing each theorem to previous theorems seen before in the function. It works in most respects, but I was attempting to use a local scope with let, but the recursive calls did not treat the local variable correctly. To remedy this, I passed in a list of theorems as a parameter.
