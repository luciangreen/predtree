% Theorems about predtree, proved by exhaustion. Run: swipl -g main -t halt proofs/theorems.pl
:- module(theorems, [main/0]).
:- use_module('../prolog/predtree').
:- use_module(prove).
:- discontiguous theorem/1.
:- use_module(library(lists)).
:- use_module(library(apply)).
main :- prove_all(theorems).

% Domain: every predicate whose clauses are a subset of a pool of four clauses (two of them
% the same up to variable names), and every set of up to 3 such named predicates.
pool([(p(X) :- q(X)), (p(Y) :- q(Y)), p(a), (p(Z) :- r(Z, Z))]).
pred(Cs) :- pool(P), subset_of(P, Cs).
subset_of([], []).
subset_of([X|Xs], [X|Ys]) :- subset_of(Xs, Ys).
subset_of([_|Xs], Ys) :- subset_of(Xs, Ys).
named(Ps) :- between(1, 3, N), length(Cs, N), maplist(pred, Cs), numlist(1, N, Is), maplist([I, C, I-C]>>true, Is, Cs, Ps).

% 1. Similarity is symmetric, between 0 and 1, and 1 exactly when the clause sets are the same up to variable names.
theorem(similarity_is_a_proper_measure) :-
    forall(( pred(A), pred(B) ), ( similarity(A, B, S1), similarity(B, A, S2), S1 == S2, S1 = N/D, N >= 0, N =< D,
                                   clause_set(A, SA), clause_set(B, SB), iff(N =:= D, SA == SB) )).

% 2. Renaming variables never changes anything.
theorem(variable_names_do_not_matter) :- forall(pred(A), ( copy_term(A, B), similarity(A, B, 1/1) )).

% 3. Families partition the predicates: each one is in exactly one family.
theorem(families_partition) :-
    forall(( named(Ps), member(T, [0/1, 1/2, 1/1]) ), ( families(Ps, T, Fs), append(Fs, All), msort(All, S), pairs_keys(Ps, Ns), msort(Ns, S) )).

% 4. At threshold 1, families are exactly the groups of duplicates (and the singletons).
theorem(threshold_one_is_duplicates) :-
    forall(named(Ps), ( families(Ps, 1/1, Fs), duplicates(Ps, Ds), include([F]>>(F = [_, _|_]), Fs, Big), msort(Ds, D1), maplist(msort, D1, D2), msort(D2, D3), Big == D3 )).

% 5. The tree contains every predicate exactly once.
theorem(tree_has_every_leaf_once) :-
    forall(named(Ps), ( tree(Ps, T), predtree:leaves(T, L), msort(L, S), pairs_keys(Ps, Ns), msort(Ns, S) )).
