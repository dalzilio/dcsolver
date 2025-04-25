# DCSolver

A simple API for checking the satisfiability of difference constraints systems,
meaning conjunction of linear inequalities of the form `x - y ≤ c` or `x - y <
c`, where `x` and `y` are real-valued variables and `c`is an integer constant.

We follow an approach described by Pratt, where satisfiability is reduced to the
problem of checking the absence of negative cycles in a graph where variables
are node, and there is an edge from `y` to `x` of length `c`to represent the
constraint `x - y < c`.

We consider a special vertex for the starting date (0). Hence, we can encode
constraints of the form `x ≤ b` or `x > a`, using relations of the form `x - 0 ≤
b` and `0 - x < a`, respectively.

For a more formal approach, and an incremental method, see:

* Ramalingam, G., Song, J., Joskowicz, L. et al. [Solving Systems of Difference
Constraints Incrementally](https://doi.org/10.1007/PL00009261). Algorithmica 23, 261–275 (1999).

Supporting strict constraints (meaning answering if the system is SAT for
rational/real values) is more difficult. Some solution is given in:

* Armando, A., Castellini, C., Giunchiglia, E., Maratea, M. (2005). [A SAT-Based
Decision Procedure for the Boolean Combination of Difference
Constraints](https://doi.org/10.1007/11527695_2). In Proc. of Theory and
Applications of Satisfiability Testing. SAT 2004. Lecture Notes in Computer
Science, vol 3542.

We want to support an incremental approach and take into account "stratified"
constraints systems, with blocks of consecutive variables that we know will
always be ``disconnected'' from each others.

TODO:

* At the moment we use a simplified version with Bellman-Ford algorithm.
