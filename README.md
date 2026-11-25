# predtree

find predicates across your repos that are the same or nearly the same, and build their family tree. Clauses are compared after renaming variables to a canonical form, so p(X) :- q(X) and p(Y) :- q(Y) are the same clause. Similarity is the Jaccard index of the clause sets; families are joined by single linkage above a threshold. For near duplicates, near_similarity/3 compares the goals inside clauses, with the predicate's own name replaced by self, so a clause edited in one goal, or a copy under another name, still counts as close; families_near/3 groups by it. A predicate is Name-Clauses (a list of clause terms).

## Use

```prolog
?- use_module(prolog/predtree).
?- similarity([(p(X) :- q(X)), p(a)], [p(b), (p(Y) :- q(Y))], S).        % S = 1/3
?- families([a-[p(1)], b-[p(1)], c-[r(2)]], 1/2, F).                      % F = [[a,b],[c]]
?- near_similarity([(p(X) :- q(X), r(X))], [(p(Y) :- q(Y), s(Y))], S).   % S = 1/2 (similarity/3 gives 0/1)
?- canonical((f(X, Y) :- g(Y, X)), C).                                    % C = (f(A,B) :- g(B,A)) numbered
```

## Proofs

`proofs/theorems.pl` proves 6 theorems by exhaustion: each one is checked for every case in a finite domain that covers every branch of the definitions. every predicate whose clauses are a subset of a pool of four clauses (two of them

1. Similarity is symmetric, between 0 and 1, and 1 exactly when the clause sets are the same up to variable names.
2. Renaming variables never changes anything.
3. Families partition the predicates: each one is in exactly one family.
4. At threshold 1, families are exactly the groups of duplicates (and the singletons).
5. The tree contains every predicate exactly once.
6. near_similarity/3 is a proper measure that ignores variable and predicate names and credits shared goals: clauses that differ in one of three goals are 1/2 similar, and len and length_of written the same way are 1/1.

```sh
swipl -g main -t halt proofs/theorems.pl
```

## 200 inputs and outputs

`io/ios.txt` lists 200 inputs and outputs from real runs, and `io/ios.pl` has the same as Prolog facts. The inputs come from a fixed seed (`io/cases.pl`). `swipl -g check -t halt io/run.pl` runs them again. It fails if any output changes, or if a predicate doesn't confirm its own recorded output, which checks steadfastness. GitHub Actions runs the proofs and the examples on every push, and records the examples on the first push.

Licence: BSD-3-Clause.
