# M-FAIR: finite indivisible foundations

Title: Additive values and fairness over canonical allocations
Family ID: M-FAIR
Pinned root: `GameTheory/Mechanism/FairDivision/Indivisible/Basic.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `e1e5052`
Canonical destination: `GameTheory.Mechanism.FairDivision.Basic`
Domain contract / decision: D9, D11, EXP-067
Owner: Wave 4 / finite fair division
Status: complete; 40/40 declarations recovered or subsumed, with no deferred rows
Last verified: 2026-08-09

The successor reuses `Mechanism.Combinatorial.Allocation`, where pairwise
disjointness is already certified, and states completeness separately.  It
does not recreate v1's raw function-valued public allocation.  Additive
fairness is finite and probability-free; divisible cake theory remains M-CAKE.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/FairDivision/Indivisible/Basic.lean` | `Bundle` | abbrev | adapt | `GameTheory.Mechanism.FairDivision.Bundle` | focused Basic build | Transparent finite bundle. |
| same | `Allocation` | abbrev | subsumed | `GameTheory.Mechanism.Combinatorial.Allocation` | EXP-067 owner comparison | One canonical disjoint allocation; the fair-division name is a transparent specialization. |
| same | `AdditiveValuation` | abbrev | adapt | same name under `GameTheory.Mechanism.FairDivision` | hostile value profile | Item values remain capability-free. |
| same | `value` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | hostile arithmetic | Finite additive sum. |
| same | `Nonnegative` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | hostile profile proof | No assumption stored in valuation data. |
| same | `IsAllocation` | def | adapt | `GameTheory.Mechanism.FairDivision.IsComplete` | canonical allocation + completeness fixture | Disjointness moved into the type; only coverage remains a predicate. |
| same | `IsEnvyFree` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | strict-envy negative control | Canonical allocation input. |
| same | `IsEF1` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | genuine removal witness | Canonical allocation input. |
| same | `IsEFX` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Lowest finite semantic layer. |
| same | `IsProportional` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Finiteness only where the full universe is summed. |
| same | `IsAlphaMMS` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Benchmark remains theorem input. |
| same | `isEnvyFree_iff` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Transparent statement. |
| same | `isEF1_iff` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Transparent statement. |
| same | `isEFX_iff` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Transparent statement. |
| same | `isProportional_iff` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Transparent statement. |
| same | `value_empty` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Additive identity. |
| same | `value_mono` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | round-robin proof | Nonnegative additive monotonicity. |
| same | `value_erase_le` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Sub-bundle monotonicity. |
| same | `value_insert_of_notMem` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Additive insertion. |
| same | `value_erase_add` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Additive erasure. |
| same | `value_nonneg` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | round-robin endpoint | Empty-envied-bundle branch. |
| same | `value_eq_zero_of_forall_eq_zero` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Support-free finite sum fact. |
| same | `IsEnvyFree.isEFX_of_nonnegative` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Direct hierarchy. |
| same | `IsEnvyFree.isEF1` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Direct hierarchy. |
| same | `IsEFX.isEF1_of_nonnegative` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Positive-good witness. |
| same | `value_univ_eq_sum_allocation` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Uses typed disjointness plus explicit completeness. |
| same | `IsEnvyFree.isProportional` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused Basic build | Complete additive decomposition. |
| same | `twoAgentAllocation` | def | adapt | `GameTheory.Mechanism.FairDivision.twoAgentAllocation` | canonical constructor fixture | Disjointness is an explicit constructor premise and enters the canonical allocation type. |
| same | `twoAgentAllocation_zero` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused build | Exact first-bundle projection. |
| same | `twoAgentAllocation_one` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused build | Exact second-bundle projection. |
| same | `twoAgentAllocation_isAllocation` | theorem | adapt | `GameTheory.Mechanism.FairDivision.twoAgentAllocation_isComplete` | hostile completeness fixture | Only coverage remains propositional because disjointness is already typed. |
| same | `ef_impossible_two_agents_one_good` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | strict separation fixture; axiom audit | A single positively valued good refutes envy-free existence while the EFX theorem remains available. |
| same | `cutScore` | private def | adapt | private `cutScore` | focused build | Cut-and-choose proof machinery remains private. |
| same | `cutScore_compl` | private theorem | adapt | private `cutScore_compl` | focused build | Complement symmetry for the private cut score. |
| same | `maximin_cut_no_envy_after_erase_right` | private theorem | adapt | private same name | focused build | Positive-good transfer contradiction for the right side. |
| same | `maximin_cut_no_envy_after_erase_left` | private theorem | adapt | private same name | focused build | Derived by complement symmetry. |
| same | `maximin_cut_partition_efx_for_zero` | private theorem | adapt | private same name | hostile EFX fixture | First orientation over the canonical allocation constructor. |
| same | `maximin_cut_partition_efx_for_zero_swapped` | private theorem | adapt | private same name | hostile EFX fixture | Swapped orientation over the canonical allocation constructor. |
| same | `exists_efx_two_agents` | theorem | adapt | `GameTheory.Mechanism.FairDivision.exists_efx_two_agents` | focused root/test build; axiom audit | General finite two-agent EFX existence with theorem-local finiteness and nonnegativity. |
| same | `efx_two_agents_two_goods` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused build | Transparent textbook specialization of the general theorem. |

Attribution: v1 supplies the additive fairness hierarchy and finite-sum proofs.
EXP-067 changes ownership, not the mathematics: disjointness is now carried by
the existing combinatorial allocation, and completeness is the only additional
certificate.  The cut-and-choose recovery completes the ledger at 39 adapted
rows and one subsumed carrier row.

Validation: the focused `TwoAgentEFX`, fair-division root, hostile test, and
mechanism-root build completed 1,756 jobs warning-free.  The hostile
three-good allocation is strictly not envy-free but is EFX, while the
one-good theorem supplies the negative control.  The existence theorem,
negative control, and explicit EFX fixture depend only on `propext`,
`Classical.choice`, and `Quot.sound`.
The full Phase 2 audit returned `VERIFIED=1`, with all six intended
fair-division inputs reached and all four game/probability/Protocol/measure
boundaries rejected.  Exact coverage returned `VERIFIED=1`, and the
warning-clean default build completed all 3,526 jobs.
