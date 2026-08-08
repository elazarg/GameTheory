# M-FAIR: choice round-robin

Title: Complete canonical round-robin allocations are EF1
Family ID: M-FAIR
Pinned root: `GameTheory/Mechanism/FairDivision/Indivisible/RoundRobin.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `e1e5052`
Canonical destination: `GameTheory.Mechanism.FairDivision.RoundRobin`
Domain contract / decision: D9, D11, EXP-067
Owner: Wave 4 / finite fair division
Status: complete; 27/27 declarations classified, no deferred rows
Last verified: 2026-08-09

Private recursion may use a function-valued bundle map, but the public
algorithm returns `Combinatorial.Allocation` and a separate completeness
certificate.  The predecessor's public raw recursive core is retired.  Every
update in the proof is a local `if`-based helper; no raw profile or function
update primitive enters the source or API.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/FairDivision/Indivisible/RoundRobin.lean` | `IsAllocationOn` | private def | adapt | private `IsAllocationOn` | focused build | Raw recursion invariant only. |
| same | `IsEF1OnNonempty` | private def | adapt | private `IsEF1OnNonempty` | focused build | Strong induction invariant only. |
| same | `rawBestGood` | private def | adapt | private `rawBestGood` | focused build | Classical proof selector. |
| same | `rawBestGood_mem` | private lemma | adapt | private `rawBestGood_mem` | focused build | Selection membership. |
| same | `rawBestGood_le` | private lemma | adapt | private `rawBestGood_le` | hostile strict rankings | Selection maximality. |
| same | `rawRoundRobinAux` | private def | adapt | private `rawRoundRobinAux` | focused build | Private function-valued recursion state. |
| same | `rawRoundRobinAlloc` | private def | adapt | private `rawRoundRobinAlloc` | focused build | Private bundle map before certification. |
| same | `roundRobinAux_empty` | private lemma | adapt | private `roundRobinAux_empty` | focused build | Base equation. |
| same | `roundRobinAux_step` | private lemma | adapt | private `roundRobinAux_step` | focused build | Successor equation. |
| same | `roundRobinAux_mono` | private lemma | adapt | private `roundRobinAux_mono` | focused build | Bundle monotonicity. |
| same | `roundRobinAux_disjoint` | private lemma | adapt | private `roundRobinAux_disjoint` | source-transport audit | Uses named equality reasoning, not transport syntax. |
| same | `roundRobinAux_biUnion` | private lemma | adapt | private `roundRobinAux_biUnion` | focused build | Coverage invariant. |
| same | `rawRoundRobinAlloc_isAllocation` | private theorem | adapt | private same name | focused build | Produces disjointness and explicit-set coverage. |
| same | `roundRobin_noEnvy_of_earlier` | private lemma | adapt | private same name | focused build | Earlier-picker inequality. |
| same | `roundRobin_ef1_of_later` | private lemma | adapt | private same name | focused build | Later-picker removal witness. |
| same | `rawRoundRobinAlloc_isEF1` | private theorem | adapt | private same name | focused build | Combines order cases. |
| same | `bestGood` | def | adapt | `GameTheory.Mechanism.FairDivision.bestGood` | hostile strict rankings | Public proof-semantic selector. |
| same | `bestGood_mem` | lemma | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused build | Candidate membership. |
| same | `bestGood_le` | lemma | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused build | Candidate maximality. |
| same | `roundRobinAux` | def | retired | private `rawRoundRobinAux` only | EXP-067 owner comparison | Public raw bundle recursion would recreate a second allocation surface. |
| same | `roundRobinAllocation` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | canonical type inspection | Returns `Combinatorial.Allocation`. |
| same | `isAllocation_of_isAllocationOn_univ` | private theorem | adapt | private `isComplete_of_isAllocationOn_univ` | focused build | Disjointness is already typed. |
| same | `roundRobinRule` | def | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused root build | Subtype carries completeness only. |
| same | `roundRobinAllocation_isAllocation` | theorem | adapt | `GameTheory.Mechanism.FairDivision.roundRobinAllocation_isComplete` | hostile specialization | Exact cover; typed disjointness. |
| same | `isEF1_of_isEF1OnNonempty` | private theorem | adapt | private `raw_isEF1_of_isEF1OnNonempty` | focused build | Converts the strong invariant before canonical packaging. |
| same | `roundRobinAllocation_isEF1` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | hostile specialization | General finite release flagship. |
| same | `roundRobinRule_isEF1` | theorem | adapt | same name under `GameTheory.Mechanism.FairDivision` | focused root build | Certified-rule corollary. |

Attribution: the pinned proof supplies the best-item selection, partition
invariants, earlier/later picker split, and strong-induction EF1 argument.  The
successor keeps that proof while replacing the public raw allocation and all
explicit equality transports.

Validation:

```text
lake build GameTheory.Mechanism.FairDivision GameTheory.Tests.FairDivision GameTheory.Mechanism
git diff --check
```

The hostile fixture has conflicting strict rankings over three goods, a
complete canonical allocation with a two-good bundle, strict envy, a positive
removal witness, and specializations of both general round-robin theorems.
