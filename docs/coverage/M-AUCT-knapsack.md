# M-AUCT: knapsack recovery

Title: Knapsack allocation, exact search, and approximation recovery
Family ID: M-AUCT
Pinned root: `GameTheory/Auctions/Knapsack/Basic.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `d595d17`
Canonical destination: `GameTheory.Mechanism.Knapsack`
Domain contract / decision: EXP-054 / D25; EXP-055 / D26; EXP-056 / D27
Owner: post-architecture breadth wave
Status: partial; 71 reviewed, 33 adapt, 35 retired, 2 subsumed, 1 deferred; EXP-056 / D27 complete
Last verified: 2026-08-02

This ledger records the pinned knapsack module without importing its obsolete
`Function.update` representation or its noncomputable wrappers into the
successor. Stable `Aggregate`, `Basic`, and `Mechanism` APIs recover the real
finite-allocation, welfare-maximization, monotonicity, and canonical
pivot-normalized VCG truthfulness slice; stable `Algorithm` and `Correctness`
APIs recover the explicit natural-number exact skip/take cluster. The repaired
executable approximation cluster is validated under EXP-056 / D27. The
historical fractional layer is retired rather
than reproduced: its pinned "optimality" comparison assumed the very
fractional-optimality fact it needed. Exact payment identity remains explicitly
deferred behind D11.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Auctions/Knapsack/Basic.lean` | `Data` | structure | adapt | `GameTheory.Mechanism.Knapsack.Data` | EXP-055 / D26 | Real weights and capacity are recovered as public finite-set data. |
| same | `BinaryAllocation` | abbrev | retired | finite-set allocation representation | EXP-055 / D26 | The Boolean-function representation is deliberately not retained. |
| same | `binaryToAllocation` | def | adapt | `GameTheory.Mechanism.Knapsack.indicator` | EXP-055 / D26 | Finite-set membership supplies the real zero/one coordinate. |
| same | `binaryLoad` | def | adapt | `GameTheory.Mechanism.Knapsack.load` | EXP-055 / D26 | Shared scalar-polymorphic finite-set aggregate specialized to real weights. |
| same | `binaryRespectsCapacity` | def | adapt | `GameTheory.Mechanism.Knapsack.Feasible` | EXP-055 / D26 | Capacity feasibility is stated directly on a finite-set allocation. |
| same | `feasibleBinaryAllocations` | def | adapt | `GameTheory.Mechanism.Knapsack.feasibleAllocations` | EXP-055 / D26 | Supported feasible allocations use an explicit finite universe. |
| same | `binarySocialWelfare` | def | adapt | `GameTheory.Mechanism.Knapsack.welfare` | EXP-055 / D26 | Shared scalar-polymorphic finite-set welfare specialized to real bids. |
| same | `zeroBinaryRespectsCapacity` | theorem | adapt | `GameTheory.Mechanism.Knapsack.empty_feasible` | EXP-055 / D26 | Empty feasibility correctly makes nonnegative capacity explicit. |
| same | `feasibleBinaryAllocations_nonempty` | theorem | adapt | `GameTheory.Mechanism.Knapsack.feasibleAllocations_nonempty` | EXP-055 / D26 | Nonemptiness follows from the explicit empty allocation witness. |
| same | `exists_welfareMaximizer` | theorem | adapt | `GameTheory.Mechanism.Knapsack.exists_welfareMaximizer` | EXP-055 / D26 | Finite supported welfare maximization is recovered. |
| same | `welfareMaximizer` | def | adapt | `GameTheory.Mechanism.Knapsack.welfareMaximizer` | EXP-055 / D26 | Noncomputable choice is confined to real semantic selection, not execution. |
| same | `welfareMaximizer_mem_feasibleBinaryAllocations` | theorem | adapt | `GameTheory.Mechanism.Knapsack.welfareMaximizer_mem` | EXP-055 / D26 | The selected maximizer has a feasible-set membership certificate. |
| same | `welfareMaximizer_ge` | theorem | adapt | `GameTheory.Mechanism.Knapsack.welfareMaximizer_ge` | EXP-055 / D26 | The selected allocation dominates every feasible alternative. |
| same | `maximalSocialWelfare` | def | adapt | `GameTheory.Mechanism.Knapsack.maximalWelfare` | EXP-055 / D26 | The maximum value is defined through the recovered selector. |
| same | `welfareMaximizer_respectsCapacity` | theorem | adapt | `GameTheory.Mechanism.Knapsack.welfareMaximizer_feasible` | EXP-055 / D26 | Feasibility is recovered directly from selector membership. |
| same | `binaryRespectsCapacity_of_mem_feasibleBinaryAllocations` | theorem | adapt | `GameTheory.Mechanism.Knapsack.feasible_of_mem_feasibleAllocations` | EXP-055 / D26 | Feasible-set membership eliminates to the capacity predicate. |
| same | `fractionalSocialWelfare` | def | retired | direct natural `welfare` comparison | EXP-056 / D27 | The repaired proof is division-free and never exposes a fractional allocation API. |
| same | `fractionalFeasible` | def | retired | direct natural feasible-allocation comparison | EXP-056 / D27 | Ambient fractional feasibility is unsound after filtering overweight items, so it is not retained. |
| same | `ratio` | def | adapt | `GameTheory.Mechanism.Knapsack.densityLE` | EXP-056 / D27 | Checked cross-multiplication replaces division. |
| same | `ratioTieKey` | def | retired | `densityLE` total preorder | EXP-056 / D27 | No semantic tie key is needed for the returned-allocation guarantee. |
| same | `sortedAgentsByRatio` | def | adapt | `GameTheory.Mechanism.Knapsack.sortByDensity` | EXP-056 / D27 | Explicit checked density sorting replaces the noncomputable ratio order. |
| same | `fractionalGreedyList` | def | retired | division-free prefix/exchange proof | EXP-056 / D27 | The old fractional program is not an executable guarantee. |
| same | `fractionalGreedyAllocation` | def | retired | `approximate` returned feasible allocation | EXP-056 / D27 | The successor returns an actual integral allocation. |
| same | `binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity` | theorem | retired | direct natural feasibility theorem | EXP-056 / D27 | The fractional bridge is unnecessary and invalid as an overweight-filtering invariant. |
| same | `fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal` | theorem | retired | `welfare_le_two_mul_approximate` | EXP-056 / D27 | The pinned theorem assumed fractional optimality; the successor proves the integral bound directly. |
| same | `binarySocialWelfare_update_eq_add` | theorem | adapt | `GameTheory.Mechanism.Knapsack.welfare_update` | EXP-055 / D26 | Canonical `Profile.update` gives the finite-set welfare-coordinate identity. |
| same | `welfareMaximizingAllocationRule` | def | adapt | `GameTheory.Mechanism.Knapsack.allocationRule` | EXP-055 / D26 | Full finite-universe welfare maximization is the canonical allocation rule. |
| same | `welfareMaximizingPaymentRule` | def | deferred | M-BAYES / D11 envelope gate | M-BAYES / D11 | Payment recovery waits for the envelope gate. |
| same | `welfareMaximizingMechanism` | def | adapt | `GameTheory.Mechanism.Knapsack.vcgSetup` | EXP-055 / D26 | Canonical finite VCG setup uses a pivot-normalized own-report-independent offset. |
| same | `welfareMaximizingAllocationRule_isMonotone` | theorem | adapt | `GameTheory.Mechanism.Knapsack.allocationRule_monotone` | EXP-055 / D26 | Monotonicity is proved for finite-set indicator allocation coordinates. |
| same | `welfareMaximizingMechanism_isDSIC` | theorem | adapt | `GameTheory.Mechanism.Knapsack.vcgSetup_truthful_isExPostNash` | EXP-055 / D26 | The canonical topology-free VCG theorem establishes truthful ex-post Nash. |
| same | `natBinarySocialWelfare` | def | adapt | `GameTheory.Mechanism.Knapsack.welfare` | Algorithm API | Executable natural-number welfare over a finite-set allocation. |
| same | `natBinaryLoad` | def | adapt | `GameTheory.Mechanism.Knapsack.load` | Algorithm API | Executable natural-number load over a finite-set allocation. |
| same | `supportedOn` | def | retired | `Algorithm` Finset-supported allocation representation | Finset representation review | Function-update support predicate is an obsolete implementation detail. |
| same | `eq_false_of_supportedOn_of_not_mem` | theorem | retired | `Algorithm` Finset membership elimination | Finset representation review | Private Function-update helper is not mathematical payload. |
| same | `supportedOn_nil_iff` | theorem | retired | `Algorithm` empty Finset representation | Finset representation review | Private implementation lemma; empty support is definitional. |
| same | `supportedOn_tail_of_eq_false` | theorem | retired | `Algorithm` Finset erasure representation | Finset representation review | Private list-tail update helper is not retained. |
| same | `supportedOn_update_false` | theorem | retired | `Algorithm` Finset erase/insert representation | Finset representation review | Private Function-update helper is eliminated. |
| same | `natBinarySocialWelfare_eq_add_of_true` | theorem | retired | `Correctness` direct Finset-sum proof | Finset representation review | Private update arithmetic helper is not mathematical payload. |
| same | `natBinaryLoad_eq_add_of_true` | theorem | retired | `Correctness` direct Finset-sum proof | Finset representation review | Private update arithmetic helper is not mathematical payload. |
| same | `natBinarySocialWelfare_update_true_of_false` | theorem | retired | `Correctness` direct Finset-sum proof | Finset representation review | Private Function-update helper is eliminated. |
| same | `natBinaryLoad_update_true_of_false` | theorem | retired | `Correctness` direct Finset-sum proof | Finset representation review | Private Function-update helper is eliminated. |
| same | `dpSolveList` | def | adapt | `GameTheory.Mechanism.Knapsack.solveList` | Algorithm API | Stable exact skip/take recurrence; no memoization or complexity claim. |
| same | `dpSolveList_supportedOn` | theorem | adapt | `GameTheory.Mechanism.Knapsack.solveList_subset_toFinset` | Correctness API | Public successor support theorem. |
| same | `dpSolveList_feasible` | theorem | adapt | `GameTheory.Mechanism.Knapsack.solveList_feasible` | Correctness API | Public successor feasibility theorem. |
| same | `dpSolveList_optimal` | theorem | adapt | `GameTheory.Mechanism.Knapsack.solveList_optimal` | Correctness API | Public successor optimality theorem. |
| same | `dynamicProgrammingOptimalAllocation` | def | retired | `GameTheory.Mechanism.Knapsack.solveList` | Algorithm API review | Misleading noncomputable wrapper; the explicit-list API is canonical. |
| same | `dynamicProgrammingOptimalValue` | def | retired | `GameTheory.Mechanism.Knapsack.solveList` plus `welfare` | Algorithm API review | Misleading noncomputable wrapper; the explicit-list API is canonical. |
| same | `dynamicProgrammingOptimalAllocation_feasible` | theorem | subsumed | `GameTheory.Mechanism.Knapsack.solveList_feasible` | Correctness direct proof chain | Direct explicit-list feasibility theorem subsumes wrapper correctness. |
| same | `dynamicProgrammingOptimalAllocation_optimal` | theorem | subsumed | `GameTheory.Mechanism.Knapsack.solveList_optimal` | Correctness direct proof chain | Direct explicit-list optimality theorem subsumes wrapper correctness. |
| same | `natAuctionData` | def | retired | explicit `(weight value : Agent → Nat)` arguments | EXP-056 / D27 | A wrapper record adds no invariant to the executable API. |
| same | `realBidOfNat` | def | retired | natural executable welfare | EXP-056 / D27 | No coercion to reals is needed for the discrete guarantee. |
| same | `integralGreedyList` | def | adapt | `GameTheory.Mechanism.Knapsack.greedySplit` and `greedyPrefix` | EXP-056 / D27 | The stop-at-first-failure scan is recovered with named trace data and an actual finite-set allocation. |
| same | `integralGreedyAllocation` | def | adapt | `GameTheory.Mechanism.Knapsack.greedyPrefix` | EXP-056 / D27 | The integral density prefix is returned as a feasible finite-set allocation. |
| same | `integralGreedyValue` | def | adapt | `GameTheory.Mechanism.Knapsack.welfare` of `greedyPrefix` | EXP-056 / D27 | Shared welfare measures the recovered prefix allocation. |
| same | `highestBidValue` | def | retired | `GameTheory.Mechanism.Knapsack.bestItem?` over `feasibleItems` | EXP-056 / D27 | The ambient maximum is the source of the overweight-singleton defect; the repaired candidate is deliberately feasibility-relative and attained. |
| same | `le_highestBidValue` | theorem | retired | `GameTheory.Mechanism.Knapsack.le_bestItem?` on the eligible list | EXP-056 / D27 | Ambient domination is not the needed invariant; only supported feasible singleton domination survives. |
| same | `fractionalSocialWelfare_realBidOfNat_binaryToAllocation` | theorem | retired | natural `welfare` | EXP-056 / D27 | Coercion-only bridge is absent from the natural proof. |
| same | `natFractionalGreedyList` | def | retired | division-free prefix/exchange proof | EXP-056 / D27 | No fractional greedy list is constructed. |
| same | `natFractionalGreedyAllocation` | def | retired | `approximate` integral allocation | EXP-056 / D27 | The successor returns only a checked integral allocation. |
| same | `natFractionalGreedyValue` | def | retired | direct natural welfare bound | EXP-056 / D27 | No fractional value is a public intermediate. |
| same | `fractionalSupportedOn` | def | retired | Finset allocation representation | EXP-056 / D27 | Function-valued support is obsolete. |
| same | `eq_zero_of_fractionalSupportedOn_of_not_mem` | theorem | retired | Finset membership | EXP-056 / D27 | Obsolete function-support elimination. |
| same | `integralGreedyList_supportedOn` | theorem | adapt | `GameTheory.Mechanism.Knapsack.greedyPrefix_subset` | EXP-056 / D27 | Function support is repaired to finite-set inclusion for the actual prefix allocation. |
| same | `natFractionalGreedyList_supportedOn` | theorem | retired | `approximate_subset` | EXP-056 / D27 | The fractional list is not retained. |
| same | `fractionalSocialWelfare_update_one_of_zero` | theorem | retired | Finset-sum welfare algebra | EXP-056 / D27 | Update arithmetic is neither a public API nor needed by the proof. |
| same | `fractionalSocialWelfare_singleton` | theorem | retired | `singletonAllocation` plus `welfare` | EXP-056 / D27 | Singleton welfare is used directly in the integral branch. |
| same | `natFractionalGreedyList_le_integralGreedyList_plus_highest` | theorem | retired | direct density-exchange bound | EXP-056 / D27 | The repaired proof does not pass through a fractional list. |
| same | `natFractionalGreedyValue_le_integralGreedyValue_plus_highest` | theorem | retired | direct density-exchange bound | EXP-056 / D27 | The repaired proof eliminates the historical intermediate inequality. |
| same | `dynamicProgrammingOptimalAllocation_fractionalFeasible` | theorem | retired | `solveList_welfare_le_two_mul_approximate?` | EXP-056 / D27 | Exact optimality compares directly with the returned approximate allocation. |
| same | `integralGreedy_halfApprox_dpOptimal` | theorem | adapt | `GameTheory.Mechanism.Knapsack.solveList_welfare_le_two_mul_approximate?` | EXP-056 / D27 | Prefilters infeasible items, certifies density order, compares the actual greedy and feasible-singleton allocations, and returns the better allocation. |

Disposition count: 33 adapt, 35 retired, 2 subsumed, 1 deferred; 71 reviewed.

Findings: the pinned source contains 45 raw `Function.update` occurrences,
including proof-facing update helpers; it also exposes 19 noncomputable public
definitions.  Its skip/take recurrence is uncached and makes
`2^(n + 1) - 1` solver calls when every item fits; it is also wrapped by
noncomputable public selectors.  The successor therefore retains a direct
Finset-based exact recurrence and proves correctness without reproducing those
wrappers or claiming dynamic-programming complexity.

Attribution: declaration names, kinds, visibility, and the DP/greedy/
mechanism theorem inventory are from
`reference/GameTheory-v1/GameTheory/Auctions/Knapsack/Basic.lean` at pinned
commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`. The recovery classification
follows EXP-054 / D25, EXP-055 / D26, and EXP-056 / D27.
It preserves the natural-number exact-search payload and recovers the finite
real semantics, VCG truthfulness, and repaired executable approximation slice,
while deliberately retiring the unsound/conditional fractional intermediates
and withholding exact payment identity until M-BAYES/D11.

Validation:

```text
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
