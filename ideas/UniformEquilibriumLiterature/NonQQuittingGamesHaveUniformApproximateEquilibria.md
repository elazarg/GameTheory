# Non-Q quitting games have ordinary uniform approximate equilibria

| Field | Value |
| --- | --- |
| Citation of record | Solan--Solan, *Quitting Games and Linear Complementarity Problems*, MOR 45(2) (2020) |
| Source confidence | `PRIMARY_FULLTEXT` on the arXiv preprint (arXiv:1707.02598); published MOR numbering not cross-checked |
| Mathematical status | `PROVED` externally, at the corrected scope below |
| Repository / Lean status | `RECORDED / NONE` |
| Objective priority | `P1` |
| Exact scope and quantifiers | Every multiplayer quitting game has sunspot approximate equilibria. The non-Q conclusion is **not** a single numbered theorem: see the scope correction below. |
| Adapter | The matrix normalization and Q-matrix convention are now audited (below). The remaining adapter work is the evaluation notion, not the matrix. |
| Consumer | Preprocessing split for the finite-quitting P0 and a solved oracle for the positive-debt producer. |

## Scope correction (2026-08-03 source audit)

The previous unconditional reading of this file's own title was overstated
against the source text. Full audit with verbatim quotes and page locators:
[`LIT-P1-3-SolanSolanSourceAudit.md`](../../ephemeral/LIT-P1-3-SolanSolanSourceAudit.md).

Two corrections matter for any import.

**1. The literal theorem carries two extra hypotheses.** Theorem 2.11 assumes
`I* ≠ ∅` and that `LCP(R̂,0̄)` has no nontrivial solution. Under those
hypotheses, part (1) gives a stationary approximate equilibrium when `R̂` is
not a `Q`-matrix, and part (2) gives only a *sunspot* equilibrium when it is.
The unconditional "not a `Q`-matrix implies ordinary existence" is
reconstructible — Lemma 2.6 covers `I* = ∅` and Lemma 2.10 covers a
nontrivial `LCP(R̂,0̄)` solution, both yielding stationary approximate
equilibria outright — but it is a synthesis of three results, not a citation.
Any repository theorem must discharge all three cases explicitly.

**2. The conclusion is stationary and undiscounted, not stated as uniform.**
The paper's numbered results deliver a *stationary ε-equilibrium* in the
undiscounted notion of its Section 2.1. The "uniform" upgrade appears only in
Introduction prose citing Solan--Vieille (2001) and was not found re-invoked
adjacent to Theorem 2.11 or its proof. This file's name therefore overstates
what is quoted; the name is retained only because inbound links depend on it.
Importing this as a *uniform* result requires the separate Solan--Vieille
upgrade, audited on its own terms.

**Audited derived matrix.** Normality is recursive: `I_0 = I`,
`I_{l+1} = {i ∈ I_l : ∃ j ∈ I_l, r^j_i ≤ 0}`, and `I* = ⋂_l I_l`. Column `i`
of `R̂` is `r^i` restricted to normal-player rows; the diagonal is zero by
the source's Assumption 2.1 (`r^i_i = 0`), and no rescaling or sign flip is
applied. `Q`-matrix is the standard notion: `LCP(R̂,q)` solvable for every
`q`. This resolves the matrix half of the adapter.

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
