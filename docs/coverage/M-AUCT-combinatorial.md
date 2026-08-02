# M-AUCT: combinatorial-auction recovery

Title: Combinatorial valuations, allocations, surplus, and quasi-fields
Family ID: M-AUCT
Pinned root: `GameTheory/Auctions/Combinatorial.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `8239c18`
Canonical destination: `GameTheory.Mechanism.Combinatorial`
Domain contract / decision: D4-D5; opt-in mature mechanism-design domain
Owner: post-architecture breadth wave
Status: complete; 54/54 declarations adapted
Last verified: 2026-08-02

This ledger recovers the pinned combinatorial-auction vocabulary into the
opt-in mechanism namespace without preserving its old compatibility surface.
The successor uses declaration-local `[Fintype A]` at selectors and existence
theorems that enumerate allocations, rather than the predecessor's `[Finite A]`
plus `Fintype.ofFinite` and transport tactics.  Other semantic operations do
not acquire the enumeration assumption.  No compatibility layer is planned.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Auctions/Combinatorial.lean` | `Valuation` | structure | adapt | `GameTheory.Mechanism.Combinatorial.Valuation` | current `Mechanism/Combinatorial/Basic.lean` | Normalized monotone finite-bundle valuation. |
| same | `<anonymous@44>` | instance | adapt | canonical `Valuation` function-coercion instance | current Basic source | Anonymous predecessor instance receives the canonical instance. |
| same | `empty` | theorem | adapt | `Valuation.empty` | current Basic source | Empty-bundle normalization. |
| same | `ext` | theorem | adapt | `Valuation.ext` | current Basic source | Extensionality for valuations. |
| same | `mono` | theorem | adapt | `Valuation.mono` | current Basic source | Monotonicity projection. |
| same | `nonneg` | theorem | adapt | `Valuation.nonneg` | current Basic source | Nonnegative values follow from normalization and monotonicity. |
| same | `thresholdBundle` | def | adapt | `Valuation.thresholdBundle` | current Basic source | Threshold valuation on a nonempty required bundle. |
| same | `thresholdBundle_apply_of_subset` | theorem | adapt | `Valuation.thresholdBundle_apply_of_subset` | current Basic source | Positive threshold branch. |
| same | `thresholdBundle_apply_of_not_subset` | theorem | adapt | `Valuation.thresholdBundle_apply_of_not_subset` | current Basic source | Zero threshold branch. |
| same | `<anonymous@96>` | instance | adapt | canonical `Valuation` inhabited instance | current Basic source | Anonymous predecessor instance receives the canonical instance. |
| same | `feasibleBundles` | def | adapt | `Valuation.feasibleBundles` | current Basic source | Quasi-field bundles feasible inside a bundle. |
| same | `empty_mem_feasibleBundles` | theorem | adapt | `Valuation.empty_mem_feasibleBundles` | current Basic source | Empty bundle feasibility. |
| same | `feasibleBundles_nonempty` | theorem | adapt | `Valuation.feasibleBundles_nonempty` | current Basic source | Feasible-bundle nonemptiness. |
| same | `feasibleBundles_mono` | theorem | adapt | `Valuation.feasibleBundles_mono` | current Basic source | Feasible bundles grow monotonically. |
| same | `bundling` | def | adapt | `Valuation.bundling` | current Basic source | Best feasible bundled valuation. |
| same | `bundling_value_eq_sup` | theorem | adapt | `Valuation.bundling_value_eq_sup` | current Basic source | Definition-facing supremum identity. |
| same | `bundling_le_original` | theorem | adapt | `Valuation.bundling_le_original` | current Basic source | Bundling cannot increase value. |
| same | `le_bundling_of_mem` | theorem | adapt | `Valuation.le_bundling_of_mem` | current Basic source | A feasible member lower-bounds bundled value. |
| same | `bundling_eq_original_of_mem` | theorem | adapt | `Valuation.bundling_eq_original_of_mem` | current Basic source | Exactness on a quasi-field bundle. |
| same | `IsBasedOn` | def | adapt | `Valuation.IsBasedOn` | current Basic source | Bundling-fixed valuation predicate. |
| same | `bundling_isBasedOn` | theorem | adapt | `Valuation.bundling_isBasedOn` | current Basic source | Bundling idempotence. |
| same | `Allocation` | structure | adapt | `GameTheory.Mechanism.Combinatorial.Allocation` | current Basic source | Pairwise-disjoint allocation. |
| same | `shrink` | def | adapt | `Allocation.shrink` | current Basic source | Shrink one allocated bundle. |
| same | `shrink_bundle_self` | theorem | adapt | `Allocation.shrink_bundle_self` | current Basic source | Selected bundle after shrink. |
| same | `shrink_bundle_ne` | theorem | adapt | `Allocation.shrink_bundle_ne` | current Basic source | Other bundles after shrink. |
| same | `residualAfterOpponents` | def | adapt | `Allocation.residualAfterOpponents` | current Basic source | Residual goods with operation-local `[Fintype]`. |
| same | `giveResidualTo` | def | adapt | `Allocation.giveResidualTo` | current Basic source | Give residual goods to one buyer. |
| same | `giveResidualTo_bundle_self` | theorem | adapt | `Allocation.giveResidualTo_bundle_self` | current Basic source | Selected residual assignment. |
| same | `giveResidualTo_bundle_ne` | theorem | adapt | `Allocation.giveResidualTo_bundle_ne` | current Basic source | Other assignments unchanged. |
| same | `bundle_subset_residualAfterOpponents` | theorem | adapt | `Allocation.bundle_subset_residualAfterOpponents` | current Basic source | Original bundle lies in its residual. |
| same | `emptyAllocation` | def | adapt | `emptyAllocation` | current Basic source | Empty allocation. |
| same | `allocationInhabited` | instance | adapt | `allocationInhabited` | current Basic source | Canonical allocation inhabitance. |
| same | `allocationFintype` | instance | adapt | `allocationFintype` | current Basic source | Canonical finite allocation enumeration. |
| same | `surplus` | def | adapt | `GameTheory.Mechanism.Combinatorial.surplus` | current Surplus source; focused build | Allocation surplus. |
| same | `IsSurplusMaximizer` | def | adapt | `IsSurplusMaximizer` | current Surplus source; focused build | Surplus-maximizing predicate. |
| same | `allocationSize` | def | adapt | `allocationSize` | current Surplus source; focused build | Allocation tie-break size. |
| same | `exists_surplus_maximizing_allocation` | theorem | adapt | `exists_surplus_maximizing_allocation` | current Surplus source; focused build | Finite maximizer existence with theorem-local enumeration. |
| same | `surplusMaximizingAllocation` | def | adapt | `surplusMaximizingAllocation` | current Surplus source; focused build | Chosen surplus maximizer. |
| same | `surplusMaximizingAllocation_isSurplusMaximizer` | theorem | adapt | `surplusMaximizingAllocation_isSurplusMaximizer` | current Surplus source; focused build | Chosen allocation maximizes surplus. |
| same | `surplus_shrink_eq_of_value_eq` | theorem | adapt | `surplus_shrink_eq_of_value_eq` | current Surplus source; focused build | Surplus survives value-preserving shrink. |
| same | `allocationSize_shrink_lt` | theorem | adapt | `allocationSize_shrink_lt` | current Surplus source; focused build | Proper shrink reduces allocation size. |
| same | `surplusMaximizers` | def | adapt | `surplusMaximizers` | current Surplus source; focused build | Predicate-defined set of surplus maximizers. |
| same | `surplusMaximizers_nonempty` | theorem | adapt | `surplusMaximizers_nonempty` | current Surplus source; focused build | Nonempty maximizer set. |
| same | `frugalSurplusMaximizingAllocation` | def | adapt | `frugalSurplusMaximizingAllocation` | current Surplus source; focused build | Frugal selected maximizer. |
| same | `frugalSurplusMaximizingAllocation_isSurplusMaximizer` | theorem | adapt | `frugalSurplusMaximizingAllocation_isSurplusMaximizer` | current Surplus source; focused build | Frugal choice still maximizes surplus. |
| same | `IsFrugal` | def | adapt | `IsFrugal` | current Surplus source; focused build | No value-preserving removable allocation. |
| same | `frugalSurplusMaximizingAllocation_isFrugal` | theorem | adapt | `frugalSurplusMaximizingAllocation_isFrugal` | current Surplus source; focused build | Chosen maximizer is frugal. |
| same | `IsFrugal.allocated_bundle_mem_of_based` | theorem | adapt | `IsFrugal.allocated_bundle_mem_of_based` | current Surplus source; focused build | Frugality forces allocated bundles into a based quasi-field. |
| same | `IsQuasiField` | def | adapt | `GameTheory.Mechanism.Combinatorial.IsQuasiField` | current QuasiField source; focused build | Empty, complement, and disjoint-union closure. |
| same | `IsQuasiField.empty_mem` | theorem | adapt | `IsQuasiField.empty_mem` | current QuasiField source; focused build | Empty-bundle closure. |
| same | `IsQuasiField.compl_mem` | theorem | adapt | `IsQuasiField.compl_mem` | current QuasiField source; focused build | Complement closure. |
| same | `IsQuasiField.disjoint_union_mem` | theorem | adapt | `IsQuasiField.disjoint_union_mem` | current QuasiField source; focused build | Binary disjoint-union closure. |
| same | `IsQuasiField.biUnion_mem_of_pairwise_disjoint` | theorem | adapt | `IsQuasiField.biUnion_mem_of_pairwise_disjoint` | current QuasiField source; focused build | Finite pairwise-disjoint union closure. |
| same | `IsQuasiField.residualAfterOpponents_mem` | theorem | adapt | `IsQuasiField.residualAfterOpponents_mem` | current QuasiField source; focused build | Residual allocation bundle remains in the quasi-field. |

Disposition count: 54 adapt.

Attribution: the declaration inventory, valuation and allocation semantics,
surplus-maximization construction, frugal tie-break, and quasi-field closure
arguments are recovered from the pinned source.  The successor retains the
mathematics while replacing global finite-type recovery and dependent
transport plumbing with explicit local enumeration only at declarations that
enumerate goods, buyers, or allocations.

Validation:

```text
lake build GameTheory.Mechanism.Combinatorial.Basic GameTheory.Mechanism.Combinatorial.Surplus GameTheory.Mechanism.Combinatorial.QuasiField
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
