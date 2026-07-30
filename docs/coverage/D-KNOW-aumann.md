# D-KNOW: finite epistemic partitions and Aumann agreement

Title: Finite epistemic partitions and Aumann agreement
Family ID: D-KNOW
Pinned roots: `GameTheory/Concepts/Knowledge/CommonKnowledge.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: working tree based on `c011ddd`
Canonical destination: `GameTheory.Epistemic`
Domain contract / decision: D16, EXP-043
Owner: Wave 1 / knowledge ownership
Status: partial
Last verified: 2026-07-30

This bounded ledger accounts for the promoted Aumann slice only. The remaining
common-knowledge and approximate-common-knowledge declarations stay
unaccounted until their full family inventory is reviewed; generated index
rows are not classifications.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Concepts/Knowledge/CommonKnowledge.lean` | `InfoPartition` | structure | adapt | `GameTheory.Epistemic.InfoPartition` | EXP-043/D16; focused build | Keeps finite cells and their partition laws without storing carrier finiteness or decidability. |
| same | `posterior` | definition | adapt | `GameTheory.Epistemic.posterior` | EXP-043/D16 | Uses the canonical `FinDist` prior instead of a second real-weight probability representation. |
| same | `posterior_eq_of_same_cell` | theorem | adapt | `GameTheory.Epistemic.posterior_eq_of_mem_cell` | focused build | The membership premise exposes exactly how cell coherence yields equal posteriors. |
| same | `IsSelfEvident` | definition | adapt | `GameTheory.Epistemic.IsSelfEvident` | EXP-043/D16 | State-event semantics remain independent of Protocol histories. |
| same | `cells_disjoint` | theorem | adapt | `GameTheory.Epistemic.cells_disjoint` | focused build | Derived from the partition laws. |
| same | `selfEvident_eq_biUnion_cells` | theorem | adapt | `GameTheory.Epistemic.selfEvident_eq_biUnion_cells` | focused build | Uses distinct finite cells. |
| same | `selfEvident_sum_decomp` | theorem | adapt | `GameTheory.Epistemic.selfEvident_sum_decomp` | focused build | Finite sums require decidable equality only at the theorem. |
| same | `aumann_full_agreement` | theorem | adapt | `GameTheory.Epistemic.aumann_full_agreement` | EXP-043/D16; axiom audit | Full support is operation-local; no action profile, Protocol, or topology premise appears. |

Attribution: the pinned theorem supplies the finite-cell decomposition and
agreement proof plan. The successor adapts its probability representation and
separates it from history-local Protocol information after EXP-043's merging
counterexample.

Validation:

```text
lake build GameTheory.Epistemic
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The focused build completes in 1,715 jobs and the full build in 3,345. The
stable root has 174 nonblank lines, zero forbidden source/import tokens, and
only the standard `propext`, `Classical.choice`, and `Quot.sound` axiom
profile. Boundary probes reach all three intended inputs, reject five
static/sequential/analytic dependencies, and confirm that Protocol cannot
reach the epistemic declarations.
