# M-AUCT: knapsack recovery

Title: Knapsack allocation, exact search, and approximation recovery
Family ID: M-AUCT
Pinned root: `GameTheory/Auctions/Knapsack/Basic.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `d595d17`
Canonical destination: `GameTheory.Mechanism.Knapsack`
Domain contract / decision: EXP-054 / D25
Owner: post-architecture breadth wave
Status: partial; 71 reviewed, 6 adapt, 11 retired, 2 subsumed, 52 deferred
Last verified: 2026-08-02

This ledger records the pinned knapsack module without importing its obsolete
`Function.update` representation or its noncomputable wrappers into the
successor.  The executable recovery is limited to the natural-number exact
skip/take cluster: stable `Algorithm` APIs provide the computation and stable
`Correctness` APIs provide its support, feasibility, and optimality results.
All other mathematical recovery remains gated by the explicit experiments and
domain decisions named below; no deferred item is credited as recovered.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Auctions/Knapsack/Basic.lean` | `Data` | structure | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real semantic data awaits the canonical slice. |
| same | `BinaryAllocation` | abbrev | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real semantic vocabulary. |
| same | `binaryToAllocation` | def | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real semantic conversion. |
| same | `binaryLoad` | def | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real semantic load. |
| same | `binaryRespectsCapacity` | def | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real feasibility predicate. |
| same | `feasibleBinaryAllocations` | def | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real feasible-allocation set. |
| same | `binarySocialWelfare` | def | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real welfare. |
| same | `zeroBinaryRespectsCapacity` | theorem | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real semantic theorem. |
| same | `feasibleBinaryAllocations_nonempty` | theorem | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real semantic theorem. |
| same | `exists_welfareMaximizer` | theorem | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real maximization theorem. |
| same | `welfareMaximizer` | def | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Noncomputable real selector awaits the slice. |
| same | `welfareMaximizer_mem_feasibleBinaryAllocations` | theorem | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real selector correctness. |
| same | `welfareMaximizer_ge` | theorem | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real selector optimality. |
| same | `maximalSocialWelfare` | def | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real optimum value. |
| same | `welfareMaximizer_respectsCapacity` | theorem | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real selector feasibility. |
| same | `binaryRespectsCapacity_of_mem_feasibleBinaryAllocations` | theorem | deferred | next real finite-allocation/mechanism experiment | EXP-054 / D25 | Base real membership elimination. |
| same | `fractionalSocialWelfare` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Fractional approximation slice. |
| same | `fractionalFeasible` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Fractional approximation slice. |
| same | `ratio` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Ratio ordering is experiment-gated. |
| same | `ratioTieKey` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Ratio tie-breaking is experiment-gated. |
| same | `sortedAgentsByRatio` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Ratio sorting is experiment-gated. |
| same | `fractionalGreedyList` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Fractional greedy computation awaits optimality experiment. |
| same | `fractionalGreedyAllocation` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Fractional greedy allocation awaits optimality experiment. |
| same | `binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Fractional feasibility bridge. |
| same | `fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Fractional optimality comparison. |
| same | `binarySocialWelfare_update_eq_add` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Update-based welfare identity is part of the approximation proof route. |
| same | `welfareMaximizingAllocationRule` | def | deferred | next real semantic experiment | EXP-054 / D25 | Allocation-rule recovery awaits the next real semantic slice. |
| same | `welfareMaximizingPaymentRule` | def | deferred | M-BAYES / D11 envelope gate | M-BAYES / D11 | Payment recovery waits for the envelope gate. |
| same | `welfareMaximizingMechanism` | def | deferred | canonical finite VCGSetup knapsack bridge | D25; existing topology-free VCG truthfulness | Mechanism wrapper awaits the finite VCGSetup bridge, not an envelope identity. |
| same | `welfareMaximizingAllocationRule_isMonotone` | theorem | deferred | next real semantic experiment | EXP-054 / D25 | Allocation-rule monotonicity awaits the next real semantic slice. |
| same | `welfareMaximizingMechanism_isDSIC` | theorem | deferred | canonical finite VCGSetup knapsack bridge | D25; existing topology-free VCG truthfulness | DSIC recovery preserves the mature topology-free VCG truthfulness route. |
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
| same | `natAuctionData` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `realBidOfNat` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `integralGreedyList` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `integralGreedyAllocation` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `integralGreedyValue` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `highestBidValue` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `le_highestBidValue` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `fractionalSocialWelfare_realBidOfNat_binaryToAllocation` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `natFractionalGreedyList` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `natFractionalGreedyAllocation` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `natFractionalGreedyValue` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `fractionalSupportedOn` | def | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `eq_zero_of_fractionalSupportedOn_of_not_mem` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `integralGreedyList_supportedOn` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `natFractionalGreedyList_supportedOn` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `fractionalSocialWelfare_update_one_of_zero` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `fractionalSocialWelfare_singleton` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation recovery awaits the experiment. |
| same | `natFractionalGreedyList_le_integralGreedyList_plus_highest` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation comparison. |
| same | `natFractionalGreedyValue_le_integralGreedyValue_plus_highest` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Greedy/approximation comparison. |
| same | `dynamicProgrammingOptimalAllocation_fractionalFeasible` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Fractional bridge for the approximation proof. |
| same | `integralGreedy_halfApprox_dpOptimal` | theorem | deferred | next ratio-order/fractional-optimality approximation experiment | EXP-054 / D25 | Repair must prefilter infeasible items, use the highest feasible singleton, certify ratio order, and return the better feasible allocation; the pinned conditional maximum-of-values statement is not an algorithmic guarantee. |

Disposition count: 6 adapt, 11 retired, 2 subsumed, 52 deferred; 71 reviewed.

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
commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.  The recovery classification
follows EXP-054 / D25; it preserves the natural-number exact-search payload
while deliberately withholding the real, fractional, approximation, payment,
and DSIC families until their stated gates pass.

Validation:

```text
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
