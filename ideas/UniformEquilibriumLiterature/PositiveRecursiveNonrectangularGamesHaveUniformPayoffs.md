# Positive-recursive nonrectangular absorbing existence

| Field | Value |
| --- | --- |
| Citation of record | Solan--Vieille, arXiv:2512.04306v1 (3 Dec 2025), Theorem 2.8 and Remark 2.9 |
| Source confidence | `PRIMARY_VERIFIED`; unrefereed preprint |
| Mathematical status | `PROVED` in the cited preprint |
| Repository status | `RECORDED` |
| Lean status | `NONE` |
| Objective priority | `P2` |
| Exact scope and quantifiers | Finite-player, one-live-state positive recursive absorbing games whose zero-absorption set has no rectangular connected component admit an undiscounted equilibrium payoff; positivity/monotonicity supplies the uniform upgrade. |
| Source alignment | No adapter or formalization yet. |
| Lean destination | `PositiveRecursiveAbsorbing.lean` and `NonrectangularPositiveRecursiveAbsorbing.lean` |
| Acceptance and consumer | Define the source graph and rectangular-component predicate exactly; test the theorem on quitting examples and expose the construction as a possible boundary-repair consumer. |
| Discrepancies | The theorem number is 2.8 in the checked version; do not import numbering from Q100 or the separate unpublished correlated manuscript. |

See [`20-nonzero-sum-equilibrium.md`](../../docs/uniform-equilibrium/references/20-nonzero-sum-equilibrium.md).
The result is recorded but not operationally consumed. It does not cover
non-positive, non-recursive, multi-live-state, or rectangular-component cases.
