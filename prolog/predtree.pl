% predtree: find predicates across your repos that are the same or nearly the same, and build
% their family tree. Clauses are compared after renaming variables to a canonical form, so
% p(X) :- q(X) and p(Y) :- q(Y) are the same clause. Similarity is the Jaccard index of the
% clause sets; families are joined by single linkage above a threshold.
% A predicate is Name-Clauses (a list of clause terms).
%?- similarity([(p(X) :- q(X)), p(a)], [p(b), (p(Y) :- q(Y))], S).        % S = 1/3
%?- families([a-[p(1)], b-[p(1)], c-[r(2)]], 1/2, F).                      % F = [[a,b],[c]]
%?- canonical((f(X, Y) :- g(Y, X)), C).                                    % C = (f(A,B) :- g(B,A)) numbered
:- module(predtree, [canonical/2, clause_set/2, similarity/3, duplicates/2, families/3, tree/2]).
:- use_module(library(lists)).
:- use_module(library(apply)).

canonical(C, K) :- copy_term(C, K0), numbervars(K0, 0, _), K = K0.
clause_set(Cs, S) :- maplist(canonical, Cs, Ks), sort(Ks, S).

% similarity(+Clauses1, +Clauses2, -S): |shared| / |either| as a fraction N/D (1/1 when both are empty).
similarity(A, B, S) :- clause_set(A, SA), clause_set(B, SB), ord_intersection(SA, SB, I), ord_union(SA, SB, U),
    length(I, NI), length(U, NU), ( NU =:= 0 -> S = 1/1 ; G is gcd(NI, NU), ( NI =:= 0 -> S = 0/1 ; N is NI // G, D is NU // G, S = N/D ) ).
frac_ge(N1/D1, N2/D2) :- N1 * D2 >= N2 * D1.

% duplicates(+Preds, -Groups): names whose clause sets are identical (up to variable names), groups of 2+.
duplicates(Ps, Gs) :- maplist([N-Cs, S-N]>>clause_set(Cs, S), Ps, Ks), msort(Ks, Sorted), group_keys(Sorted, All), include([G]>>(G = [_, _|_]), All, Gs).
group_keys([], []).
group_keys([K-V|R], [[V|Vs]|Gs]) :- same_key(K, R, Vs, R1), group_keys(R1, Gs).
same_key(K, [K2-V|R], [V|Vs], R1) :- K == K2, !, same_key(K, R, Vs, R1).
same_key(_, R, [], R).

% families(+Preds, +Threshold, -Families): connected groups, joining any two at least Threshold similar.
families(Ps, T, Fs) :- pairs_keys(Ps, Ns), components(Ns, Ps, T, Fs0), maplist(msort, Fs0, Fs1), msort(Fs1, Fs).
components([], _, _, []).
components([N|Ns], Ps, T, [C|Cs]) :- reach([N], Ps, T, [N], C), subtract(Ns, C, Rest), components(Rest, Ps, T, Cs).
reach([], _, _, Seen, Seen).
reach([N|Q], Ps, T, Seen, C) :- memberchk(N-A, Ps),
    findall(M, ( member(M-B, Ps), \+ memberchk(M, Seen), similarity(A, B, S), frac_ge(S, T) ), New0), sort(New0, New),
    append(Seen, New, Seen1), append(Q, New, Q1), reach(Q1, Ps, T, Seen1, C).

% tree(+Preds, -Tree): single-linkage merge order, most similar first: merges as join(S, A, B).
tree(Ps, Tree) :- pairs_keys(Ps, Ns), maplist([N, leaf(N)]>>true, Ns, Ls), merge_all(Ls, Ps, Tree).
merge_all([T], _, T) :- !.
merge_all(Ts, Ps, Tree) :- findall(S-(A+B), ( select(A, Ts, R), member(B, R), A @< B, link(A, B, Ps, S) ), Cands),
    best(Cands, S-(A+B)), subtract(Ts, [A, B], Rest), merge_all([join(S, A, B)|Rest], Ps, Tree).
best([C|Cs], B) :- foldl([X, Y, Z]>>( X = S1-_, Y = S2-_, ( frac_ge(S1, S2), \+ frac_ge(S2, S1) -> Z = X ; Z = Y ) ), Cs, C, B).
link(A, B, Ps, S) :- leaves(A, La), leaves(B, Lb), findall(X, ( member(Na, La), member(Nb, Lb), memberchk(Na-Ca, Ps), memberchk(Nb-Cb, Ps), similarity(Ca, Cb, X) ), Xs), max_frac(Xs, S).
max_frac([X|Xs], M) :- foldl([A, B, C]>>(frac_ge(A, B) -> C = A ; C = B), Xs, X, M).
leaves(leaf(N), [N]).
leaves(join(_, A, B), L) :- leaves(A, La), leaves(B, Lb), append(La, Lb, L).
