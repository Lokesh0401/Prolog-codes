hastype(Gamma, const(N), intT).
hastype(Gamma, bool(true), boolT).
hastype(Gamma, bool(false), boolT).
hastype(Gamma, unit, unitT).

hastype(Gamma, neg(E), intT) :- hastype(Gamma, E, intT).
hastype(Gamma, abs(E), intT) :- hastype(Gamma, E, intT).
hastype(Gamma, plus(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, sub(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, mul(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, div(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, mod(E1, E2), intT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.

hastype(Gamma, not(E), boolT) :- hastype(Gamma, E, boolT), !.
hastype(Gamma, and(E1, E2), boolT) :- hastype(Gamma, E1, boolT), hastype(Gamma, E2, boolT), !.
hastype(Gamma, or(E1, E2), boolT) :- hastype(Gamma, E1, boolT), hastype(Gamma, E2, boolT), !.
hastype(Gamma, implies(E1, E2), boolT) :- hastype(Gamma, E1, boolT), hastype(Gamma, E2, boolT), !.

hastype(Gamma, gt(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, lt(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, gte(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, lte(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, eq(E1, E2), boolT) :- hastype(Gamma, E1, intT), hastype(Gamma, E2, intT), !.
hastype(Gamma, eq(E1, E2), boolT) :- hastype(Gamma, E1, boolT), hastype(Gamma, E2, boolT), !.

hastype(Gamma, pair(E1, E2), cartesianT([T1, T2])) :- hastype(Gamma, E1, T1), hastype(Gamma, E2, T2).
hastype(Gamma, first(E), T1) :- hastype(Gamma, E, cartesianT(T1, T2)).
hastype(Gamma, second(E), T2) :- hastype(Gamma, E, cartesianT(T1, T2)).

hastype(Gamma, if_then_else(E0, E1, E2), T) :- hastype(Gamma, E0, boolT), hastype(Gamma, E1, T), hastype(Gamma, E2, T).

hastype(Gamma, abs(variable(X), E1), arrowT(T1, T2)) :- hastype(Gamma, variable(X), T1), hastype([p(variable(X), T1)|Gamma], E1, T2).
hastype(Gamma, call(E1, E2), T2) :- hastype(Gamma, E1, arrowT(T1, T2)), hastype(Gamma, E2, T1).

member(X, []) :- fail.
member(X, [X|Xs]) :- !.
member(X, [Y|Ys]) :- member(X, Ys).
union(X, [], X).
union(X, [Y|Ys], Z) :- union(X, Ys, Z), member(Y, X).
union(X, [Y|Ys], Z) :- union([Y|X], Ys, Z), \+ member(Y, X).

lookup(Xs, variable(X), T) :- member((X, T), Xs).

hastype(Gamma, variable(X), T) :- lookup(Gamma, variable(X), T).

typeElaborates(Gamma, x_is_e(variable(X), E), [(X, T)]) :- hastype(Gamma, E, T).
typeElaborates(Gamma, seq(E1, E2), Gamma3) :- typeElaborates(Gamma, E1, Gamma1), typeElaborates(Gamma11, E2, Gamma2), union(Gamma, Gamma1, Gamma11), union(Gamma1, Gamma2, Gamma3).
typeElaborates(Gamma, par(E1, E2), Gamma3) :- typeElaborates(Gamma, E1, Gamma1), typeElaborates(Gamma, E2, Gamma2), union(Gamma1, Gamma2, Gamma3).
typeElaborates(Gamma, d1_in_d2(E1, E2), Gamma2) :- typeElaborates(Gamma, E1, Gamma1), typeElaborates(Gamma11, E2, Gamma2), union(Gamma, Gamma1, Gamma11).

hastype(Gamma, let_d_in_e(E1, E2), T) :- typeElaborates(Gamma, E1, Gamma1), hastype(Gamma11, E2, T), union(Gamma, Gamma1, Gamma11).
hastype(Gamma, let_x_in_e(variable(X), E1, E2), T) :- hastype(Gamma, E1, T1), hastype([(X,T1)|Gamma], E2, T).

hastype(Gamma, nTuple([]), nTupleT([])) :- !.
hastype(Gamma, nTuple([E1|Es]), nTupleT([T1|Ts])) :- hastype(Gamma, E1, T1), hastype(Gamma, nTuple(Es), nTupleT(Ts)).

hastype(Gamma, proj(0, nTuple([E1|Es])), T) :- hastype(Gamma, E1, T).
hastype(Gamma, proj(N, nTuple([E1|Es])), T) :- hastype(Gamma, proj(N1, nTuple(Es)), T), N is N1 + 1.


/** primtives */
?- hastype([], unit, W).
?- hastype([], bool(true), W).
?- hastype([], const(2), W).

/** expressions without variables */
?- hastype([], plus(sub(const(3), const(1)), const(1)), W).
?- hastype([], div(mod(const(3), const(2)), const(7)), W).
?- hastype([], plus(const(2), not(bool(true))), W). /* false */
?- hastype([], or(bool(true), and(bool(true), bool(false))), W).
?- hastype([], or(bool(true)), W). /* false */
?- hastype([], and(eq(const(2), const(4)), gte(const(2), const(3))), W).
?- hastype([], and(plus(const(2), const(4)), gte(const(2), const(3))), W). /* false */

/** expressions with variables */
?- lookup([(x, intT)], variable(x), W).
?- lookup([(x, boolT), (y, unitT)], variable(y), W).
?- hastype([(x, intT)], plus(variable(x), const(3)), W).
?- hastype([(x, intT), (y, boolT)], and(eq(plus(variable(x), const(1)), const(2)), variable(y)), W).
?- hastype([(x, boolT), (y, boolT)], and(eq(plus(variable(x), const(1)), const(2)), variable(y)), W).
?- hastype([(y, boolT), (x, intT)], abs(variable(x)), W).
?- hastype([(y, boolT), (x, intT)], lt(variable(x), const(23)), W).
?- hastype([(y, boolT), (x, intT)], eq(variable(x), const(23)), W).
?- hastype([(y, boolT), (x, intT)], eq(bool(true), bool(false)), W). /* false */
?- hastype([(y, boolT), (x, intT)], and(bool(true), bool(false)), W).
?- hastype([(y, boolT), (x, intT)], if_then_else(bool(true), const(23), variable(y)), W). /* false */
?- hastype([(y, intT), (x, intT)], if_then_else(bool(true), const(23), variable(y)), W).
?- hastype([(y, boolT), (x, intT)], nTuple([bool(true), bool(false), const(23), variable(y), variable(x)]), W).
?- hastype([(y, boolT), (x, intT)], proj(0, nTuple([bool(true), bool(false), const(23), variable(y), variable(x)])), W).
?- hastype([(y, boolT), (x, intT)], proj(3, nTuple([bool(true), bool(false), const(23), variable(y), variable(x)])), W).

/** Abstractions */
?- hastype([(y, boolT), (x, intT)], abs(variable(x), plus(variable(x), const(32))), W).
?- hastype([(y, boolT), (x, intT)], call(abs(variable(x), plus(variable(x), const(32))), const(23)), W).
?- hastype([(y, boolT), (x, intT)], call(abs(variable(y), and(variable(y), bool(false))), const(23)), W). /* false */
?- hastype([(y, boolT), (x, intT)], call(abs(variable(y), and(variable(y), bool(false))), bool(true)), W).

/* Local Definitions */
?- typeElaborates([(y, boolT), (x, intT)], x_is_e(variable(y), bool(true)), W).
?- typeElaborates([(y, boolT), (x, intT)], par(x_is_e(variable(y), const(23)), x_is_e(variable(x), bool(true))), W).
?- typeElaborates([(y, boolT), (x, intT)], seq(x_is_e(variable(y), const(23)), x_is_e(variable(x), eq(const(6), variable(y)))), W).
?- typeElaborates([(y, boolT), (x, intT)], par(x_is_e(variable(y), const(23)), x_is_e(variable(x), eq(const(6), variable(y)))), W). /* false */
?- typeElaborates([(y, boolT), (x, intT)], d1_in_d2(x_is_e(variable(z), const(23)) , x_is_e(variable(x), lte(variable(z),const(45)) ) ), W).
?- hastype([(y, boolT), (x, intT)], let_x_in_e(variable(y), bool(true), and(variable(y), bool(false))), W).
?- hastype([], let_x_in_e(variable(y), bool(true), and(variable(y), bool(false))), W).
?- hastype([], let_d_in_e(seq(x_is_e(variable(y), bool(true)), x_is_e(variable(x), bool(false))), and(variable(y),variable(x))), W).
?- hastype([], let_d_in_e(par(x_is_e(variable(y), bool(true)), x_is_e(variable(x), bool(false))), and(variable(y),variable(x))), W).
?- hastype([], let_d_in_e( d1_in_d2( x_is_e(variable(y), bool(true)), x_is_e(variable(x), and(variable(y),bool(false))) ),and(variable(x),variable(x))),W).

/* Ambiguous expressions */
?- hastype([], eq(plus(A, B), sub(C, D)), T).
?- hastype([], and(E1, E2), T).
?- hastype(Gamma, eq(and(X,Y),plus(A,B)), T).