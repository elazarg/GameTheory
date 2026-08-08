# M-FAIR: finite indivisible foundations

Title: Additive values and fairness over canonical allocations
Family ID: M-FAIR
Pinned root: `GameTheory/Mechanism/FairDivision/Indivisible/Basic.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `e1e5052`
Canonical destination: `GameTheory.Mechanism.FairDivision.Basic`
Domain contract / decision: D9, D11, EXP-067
Owner: Wave 4 / finite fair division
Status: partial; all 40 declarations classified, 27 recovered or subsumed and 13 deferred to the two-agent EFX gate
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
| same | `twoAgentAllocation` | def | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Canonical constructor must expose disjointness rather than accept arbitrary bundles. |
| same | `twoAgentAllocation_zero` | theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Follows the redesigned constructor. |
| same | `twoAgentAllocation_one` | theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Follows the redesigned constructor. |
| same | `twoAgentAllocation_isAllocation` | theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Will state completeness; disjointness is typed. |
| same | `ef_impossible_two_agents_one_good` | theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Useful separation result, not required by the round-robin gate. |
| same | `cutScore` | private def | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Private cut-and-choose machinery. |
| same | `cutScore_compl` | private theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Private cut-and-choose machinery. |
| same | `maximin_cut_no_envy_after_erase_right` | private theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Private cut-and-choose machinery. |
| same | `maximin_cut_no_envy_after_erase_left` | private theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Private cut-and-choose machinery. |
| same | `maximin_cut_partition_efx_for_zero` | private theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Private cut-and-choose machinery. |
| same | `maximin_cut_partition_efx_for_zero_swapped` | private theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Private cut-and-choose machinery. |
| same | `exists_efx_two_agents` | theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Next finite-existence consumer after release parity. |
| same | `efx_two_agents_two_goods` | theorem | deferred | M-FAIR two-agent EFX recovery gate | inventory classification | Finite specialization follows the general theorem. |

Attribution: v1 supplies the additive fairness hierarchy and finite-sum proofs.
EXP-067 changes ownership, not the mathematics: disjointness is now carried by
the existing combinatorial allocation, and completeness is the only additional
certificate.

