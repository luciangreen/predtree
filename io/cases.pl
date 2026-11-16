:- module(cases, [title/1, case/3]).
:- use_module('../prolog/predtree').
:- use_module(engine).
title('predtree').
clause_g(C) :- rnd_pick([(f(X) :- g(X)), (f(Y) :- g(Y)), f(1), f(2), (f(Z) :- h(Z, Z)), (f([H|T]) :- f(T), g(H)), (f(A) :- g(A), h(A, A))], C).
pred_g(Cs) :- rnd_int(1, 4, N), length(Cs, N), maplist(clause_g, Cs).
preds_g(Ps) :- rnd_int(2, 5, N), numlist(1, N, Is), maplist([I, Name-Cs]>>( atom_concat(p, I, Name), pred_g(Cs) ), Is, Ps).
case(similarity, [A, B], similarity) :- pred_g(A), pred_g(B).
case(duplicates, [Ps], duplicates) :- preds_g(Ps).
case(families, [Ps, T], families) :- preds_g(Ps), rnd_pick([1/3, 1/2, 1/1], T).
case(tree, [Ps], tree) :- preds_g(Ps).
case(canonical, [C], canonical) :- clause_g(C).
