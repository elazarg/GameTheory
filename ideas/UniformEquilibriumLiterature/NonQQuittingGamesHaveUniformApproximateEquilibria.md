# Non-Q quitting games have ordinary uniform approximate equilibria

| Field | Value |
| --- | --- |
| Citation of record | Solan--Solan, *Quitting Games and Linear Complementarity Problems*, MOR 45(2) (2020) |
| Source confidence | `PRIMARY_ABSTRACT`; full matrix adapter unaudited |
| Mathematical status | `PROVED` externally |
| Repository / Lean status | `RECORDED / NONE` |
| Objective priority | `P1` |
| Exact scope and quantifiers | Every multiplayer quitting game has sunspot approximate equilibria; if the source's derived payoff matrix is not a Q-matrix, the game has ordinary uniform approximate equilibria for every positive accuracy. |
| Adapter | Reconstruct the paper's normalization, complementarity problem, Q-matrix convention, and uniform evaluation before importing the theorem. |
| Consumer | Preprocessing split for the finite-quitting P0 and a solved oracle for the positive-debt producer. |

The direction matters.  The externally closed ordinary-profile class is the
**non-Q** side.  The Q-matrix side is not thereby an ordinary-Nash existence
theorem; the general theorem there uses a sunspot device and belongs to a
strictly richer strategy model.

This result can narrow the quitting search only after an exact adapter maps a
repository payoff table to the paper's derived matrix.  It does not by itself
show that a positive optimized-debt plateau forces the Q-matrix condition, nor
that the complementarity pivot structure supplies the marked packet or
bounded repair required by the current P0.

**Citation.** E. Solan and O. N. Solan, *Quitting Games and Linear
Complementarity Problems*, Mathematics of Operations Research **45**(2),
626--651 (2020), DOI
[`10.1287/moor.2019.0996`](https://doi.org/10.1287/moor.2019.0996).
