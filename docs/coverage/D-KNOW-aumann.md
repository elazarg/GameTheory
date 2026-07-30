# D-KNOW: finite common knowledge and Aumann agreement

Title: Finite S5/common knowledge and Aumann agreement
Family ID: D-KNOW
Pinned roots: `GameTheory/Concepts/Knowledge/CommonKnowledge.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: working tree based on `c011ddd`
Canonical destination: `GameTheory.Epistemic`
Domain contract / decision: D16, EXP-043
Owner: Wave 1 / knowledge ownership
Status: partial
Last verified: 2026-07-30

This ledger accounts for every declaration in the pinned
`CommonKnowledge.lean` file. The 32 declarations in
`ApproximateCommonKnowledge.lean` remain unaccounted until their separate
threshold-belief batch is reviewed; generated index rows are not
classifications.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Concepts/Knowledge/CommonKnowledge.lean` | `InfoPartition` | structure | adapt | `GameTheory.Epistemic.InfoPartition` | EXP-043/D16; focused build | Keeps finite cells and their partition laws without storing carrier finiteness or decidability. |
| same | `posterior` | definition | adapt | `GameTheory.Epistemic.posterior` | EXP-043/D16 | Uses the canonical `FinDist` prior instead of a second real-weight probability representation. |
| same | `posterior_eq_of_same_cell` | theorem | adapt | `GameTheory.Epistemic.posterior_eq_of_mem_cell` | focused build | The membership premise exposes exactly how cell coherence yields equal posteriors. |
| same | `agree_to_disagree` | theorem | adapt | `GameTheory.Epistemic.posterior_eq_of_cell_eq` | focused build | The source theorem is equality under a shared current cell, not full public-event agreement. |
| same | `IsSelfEvident` | definition | adapt | `GameTheory.Epistemic.IsSelfEvident` | EXP-043/D16 | State-event semantics remain independent of Protocol histories. |
| same | `posterior_self_evident` | theorem | adapt | `GameTheory.Epistemic.posterior_eq_one_of_selfEvident` | focused build; axiom audit | The arbitrary positive weight premise becomes full support of the canonical prior. |
| same | `cell_disjoint_of_not_in_self_evident` | theorem | adapt | `GameTheory.Epistemic.cell_inter_eq_empty_of_not_mem_selfEvident` | focused build | Records the exact empty-intersection conclusion. |
| same | `posterior_zero_outside_self_evident` | theorem | adapt | `GameTheory.Epistemic.posterior_eq_zero_of_not_mem_selfEvident` | focused build | Drops the source's unused positivity premise. |
| same | `Knows` | definition | adapt | `GameTheory.Epistemic.Knows` | focused build | Whole-state enumeration requests `Fintype Ω` only at the operator layer. |
| same | `mem_Knows_iff` | theorem | adapt | `GameTheory.Epistemic.mem_Knows_iff` | focused build | Cell-containment characterization. |
| same | `Knows_subset` | theorem | adapt | `GameTheory.Epistemic.Knows_subset` | focused build | S5 axiom T. |
| same | `Knows_idem` | theorem | adapt | `GameTheory.Epistemic.Knows_idem` | focused build | S5 axiom 4 in fixed-point form. |
| same | `Knows_not_Knows` | theorem | adapt | `GameTheory.Epistemic.Knows_not_Knows` | focused build; axiom audit | S5 axiom 5 in fixed-point form. |
| same | `Knows_mono` | theorem | adapt | `GameTheory.Epistemic.Knows_mono` | focused build | Monotonicity. |
| same | `Knows_inter` | theorem | adapt | `GameTheory.Epistemic.Knows_inter` | focused build | Knowledge distributes over event conjunction. |
| same | `isSelfEvident_iff_subset_Knows` | theorem | adapt | `GameTheory.Epistemic.isSelfEvident_iff_subset_Knows` | focused build | Truth of a self-evident event implies knowledge. |
| same | `isSelfEvident_iff_Knows_eq` | theorem | adapt | `GameTheory.Epistemic.isSelfEvident_iff_Knows_eq` | focused build | Fixed-point characterization. |
| same | `mutualKnowledge` | definition | adapt | `GameTheory.Epistemic.mutualKnowledge` | focused build | Enumerates agents and states only at this operation. |
| same | `mem_mutualKnowledge_iff` | theorem | adapt | `GameTheory.Epistemic.mem_mutualKnowledge_iff` | focused build | Pointwise family characterization. |
| same | `mutualKnowledge_subset` | theorem | adapt | `GameTheory.Epistemic.mutualKnowledge_subset` | focused build | Requests a nonempty agent family only for veridicality. |
| same | `CommonKnowledgeAt` | definition | adapt | `GameTheory.Epistemic.CommonKnowledgeAt` | D16; focused build | Uses the public self-evident-event characterization. |
| same | `CommonKnowledge` | definition | adapt | `GameTheory.Epistemic.CommonKnowledge` | focused build | Enumerates the finite state space; no Protocol state is involved. |
| same | `mem_CommonKnowledge_iff` | theorem | adapt | `GameTheory.Epistemic.mem_CommonKnowledge_iff` | focused build | Membership characterization. |
| same | `CommonKnowledgeAt.implies_mem` | theorem | adapt | `GameTheory.Epistemic.CommonKnowledgeAt.implies_mem` | focused build | Common knowledge is truthful. |
| same | `CommonKnowledgeAt.implies_Knows` | theorem | adapt | `GameTheory.Epistemic.CommonKnowledgeAt.implies_Knows` | focused build | Common knowledge implies every agent knows. |
| same | `CommonKnowledgeAt.idem` | theorem | adapt | `GameTheory.Epistemic.CommonKnowledgeAt.idem` | focused build; axiom audit | Positive introspection at the group level. |
| same | `cells_disjoint` | theorem | adapt | `GameTheory.Epistemic.cells_disjoint` | focused build | Derived from the partition laws. |
| same | `selfEvident_eq_biUnion_cells` | theorem | adapt | `GameTheory.Epistemic.selfEvident_eq_biUnion_cells` | focused build | Uses distinct finite cells. |
| same | `selfEvident_sum_decomp` | theorem | adapt | `GameTheory.Epistemic.selfEvident_sum_decomp` | focused build | Finite sums require decidable equality only at the theorem. |
| same | `aumann_full_agreement` | theorem | adapt | `GameTheory.Epistemic.aumann_full_agreement` | EXP-043/D16; axiom audit | Full support is operation-local; no action profile, Protocol, or topology premise appears. |

Attribution: the pinned file supplies the finite S5 operators, public-event
common-knowledge characterization, cell decomposition, and agreement proof
plan. The successor adapts its probability representation and separates it
from history-local Protocol information after EXP-043's merging counterexample.

Validation:

```text
lake build GameTheory.Epistemic
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The original Aumann promotion focused build completed in 1,715 jobs and its
full build in 3,345. The expanded S5 batch builds in 1,716 focused / 3,350 full
jobs and brings the Epistemic root to 370 nonblank lines. Source and axiom
audits remain at zero forbidden tokens and the standard `propext`,
`Classical.choice`, and `Quot.sound` profile. Boundary probes positively reach
all four finite-law/epistemic/common-knowledge inputs and reject the same five
static, sequential, and analytic dependencies.
