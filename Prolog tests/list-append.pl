append([], L2, L2).
append([X|Xs], L2, [X|L3]) :- append(Xs, L2, L3).

/** <examples>
?- append([1,2,3], [2,3,4], W).

*/
