edge(a,b).
edge(b,e).
edge(c,e).
edge(a,c).
edge(i,c).

path(X, X).
path(X, Y) :- edge(X, Y).
path(X, Y) :- edge(X, Z), path(Z, Y).

/** <examples>
?- path(a, a).
?- path(a, b).
?- path(a, c).
?- path(i,c).
?- path(a, W).
*/
