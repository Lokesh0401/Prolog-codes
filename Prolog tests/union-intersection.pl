member(X, []) :- fail.
member(X, [X|Xs]) :- !.
member(X, [Y|Ys]) :- member(X, Ys).

union(X, [], X).
union(X, [Y|Ys], Z) :- union(X, Ys, Z), member(Y, X).
union(X, [Y|Ys], Z) :- union([Y|X], Ys, Z), \+ member(Y, X).

intersection(X, [], []).
intersection(X, [Y|Ys], Z) :- intersection(X, Ys, W), member(Y, X), union(W, [Y], Z).
intersection(X, [Y|Ys], Z) :- intersection(X, Ys, Z), \+ member(Y, X).
