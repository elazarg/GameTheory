# Audit, 2026-08-04 — mechanical census of the quitting/uniform Lean tree

> **Standing.** Dated audit record. Scope: the 149 modules under
> `GameTheory/Concepts/Stochastic/` (of 421) whose names match
> `quitting|uniform|absorb|cycl|complementar|debt|conjecture`. Mechanical, with
> file:line evidence; the interpretation is minimal by design.

## Placeholders

Two `sorry`s, both deliberate: `quittingGame_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`) and `exists_uniformDeviationCapConstructor`
(`UniformExistenceConjecture.lean`). **Zero** occurrences of `sorryAx`,
`native_decide`, `axiom`, `opaque`, `@[implemented_by]`, or `partial` in scope.

The only `native_decide`/`opaque` in the whole directory are four numeric
constants in the `BlockPairK11Dyadic*` family — a self-contained, mutually
importing island of 12 files that **nothing in scope imports**, so the
`Lean.ofReduceBool` axiom it introduces cannot reach the quitting chain.

## The 19 `HEADLINE` results

All 19 in the tree fall inside scope. **11 mention
`IsUniformEquilibriumPayoff`** — i.e. reach the actual target — and **8 are
intermediate certificates or fences** about arrays of reals, Prop-level
disjunctions, or refuted routes. Notably, the three-branch disjunction
`quittingCycle_zeroSolo_or_admissible_or_isolatedNegative` is in the second
group: it contains no `IsUniformEquilibriumPayoff` term at all.

## Reachability toward the conjecture

**Two base bridges** carry everything:
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean:53`) and
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean:161`).

Above them sit roughly **twenty-five sufficient-condition theorems** whose
conclusion is `IsUniformEquilibriumPayoff`: the zero-solo/admissible-cycle
disjunction; two parallel debt families (exact-debt and dynamic-debt, each with
chain, budget, and infimum forms); the periodic/cyclic certificate family; the
cutoff/root/pair constructions; a clock dichotomy; trivial dispatch for
absorbing or subsingleton states; and concrete-table capstones.

**Exactly one theorem has `IsUniformEquilibriumPayoff` only in a hypothesis**:
`uniformEquilibriumPayoff_weighted_eq_two_of_bottomRightOccupation_vanishing`
(`UniformEquilibrium/Examples/Sorin/UniformSeparation.lean:153`).

### The gap, stated plainly

**No general hypothesis above is supplied for an arbitrary weight.** Checked
one by one:

- `IsQuittingZeroSolo ∨ HasAdmissibleAbsorbingQuittingCycle` — **actively
  refuted** (`UniformEquilibrium/Quitting/Boundary/Repair/DisjunctionCounterexample.lean:676`).
- `QuittingOwnJoinMonotone` / `QuittingPositiveSoloOwnJoinMonotone` — defined
  and consumed only inside `UniformEquilibrium/Quitting/Cycles/JoinMonotoneUniform.lean`; nothing proves
  either holds generally.
- The debt-vanishing infima — `UniformEquilibrium/Quitting/Debt/Dynamic/ExactDynamicDebtVanishingCounterexample.lean`
  exhibits a table where the exact-debt infimum is **positive** yet the game
  still has a uniform equilibrium payoff by an unrelated argument. So the
  criterion is **neither necessary** nor known to hold generally.
- "Every opponent clock diverges" — the wrapping theorem shows this is a
  genuine either/or, not a forced outcome.

That is the reach problem, in one place: many rungs, none of them anchored to
an arbitrary weight.

## Orphans

Three modules in scope are imported by **nothing**, including `GameTheory.lean`,
so the full-tree build does not compile them and they can rot silently:

- `UniformEquilibrium/Quitting/Debt/Dynamic/DebtClockDischarge.lean` — divergent-clock debt discharge.
- `UniformEquilibrium/Quitting/Debt/Marked/StrictTimeClosing.lean` — finite scalar contraction for
  closing a marked cycle.
- `UniformEquilibrium/Quitting/Debt/Ledger/VanishingChargeRecurrenceNoGo.lean` — `no_quarter_relativeReturn`:
  compact recurrence need not beat a vanishing contraction charge.

No `private` declaration looks like an accidentally-hidden export; all are
ordinary internal helpers.

## The one unused `Prop` placeholder

`NoBoundedCompletelyAbsorbingInverseIterate`
(`UniformEquilibrium/Quitting/Boundary/Analytic/UnboundedInverseIterate.lean:213`) — never established, never
consumed as a hypothesis, exactly as its docstring says. Its antecedent in
`noBounded_of_noCompletelyAbsorbingInverseIterate` is itself proved false in
the same file. Every other `Has…`/`Is…` Prop in scope has a genuine use.

## The fences

Thirteen counterexample/no-go/regression modules, plus five negation-conclusion
theorems outside the naming convention. Knowing the full set matters, because
each one forecloses a route:

`not_forall_isQuittingZeroSolo_or_hasAdmissibleAbsorbingQuittingCycle` ·
`not_isεAsymptoticNash_localGlobalCounterexampleProfile` ·
`no_sureSetSmallOwnerLimitCertificate` · six `not_isεAsymptoticNash_*` in
`QuittingSureSetRepairFullIntervalCounterexample` ·
`atomwise_regret_does_not_transfer_dynamicDebt` ·
`not_exists_obstacle_as_function_of_accumulatedMass` ·
`not_stationaryGainComplementary_of_false_positive` ·
`liftedFlag_residualDepth_not_tendsto_atTop` · `successorImage_not_convex` ·
`quittingTwoPhaseClosure_not_both_pos` · `no_quarter_relativeReturn` ·
`not_noCompletelyAbsorbingInverseIterate` ·
`not_isQuittingCyclicContinuation_zero` ·
`not_exists_uniformEquilibriumPayoff_of_arbitrarilyLateExploitabilityGap` ·
`quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap` ·
`privateRecommendationTarget_not_isUniformEquilibriumPayoff` ·
`discountedEndpoint_not_isUniformEquilibriumPayoff_of_bottomRightOccupation_vanishing`.

Three modules named "counterexample" contain no literal negation and instead
demonstrate a positive construction outside a template's hypothesis
(`QuittingBoundedSurgeryDescentCounterexample`,
`QuittingExactDynamicDebtVanishingCounterexample`,
`QuittingNegativeSingletonChargeRegression`).

## Duplication

- **Exact-debt versus dynamic-debt infrastructures.** Two parallel families
  with identical theorem shapes — chain compiler, infimum criterion — differing
  only in which debt functional bounds the terminal solo reward
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/FiniteChainTerminalCompiler.lean:453` ↔
  `UniformEquilibrium/Quitting/Debt/Dynamic/FiniteDynamicDebtCompiler.lean:167`;
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanMinimizer.lean:654` ↔
  `UniformEquilibrium/Quitting/Debt/Dynamic/FiniteDynamicDebtOptimizer.lean:454`). The largest duplication in
  the tree.
- Pair-repair versus mirror-pair-repair (`UniformEquilibrium/Quitting/Classification/TwoPlayer/PairRepair.lean:367`
  ↔ `:675`), with ~14 `mirror_*` helpers duplicating the primary computation.
  By design, role-reversal; acknowledged.
- `isUniformEquilibriumPayoff_zero` ↔ `_one` (`UniformEquilibrium/Examples/PureExternality/Cycle.lean:376`,
  `:430`) — one proof template, two constants.
- Periodic-compiler certificate versus singleton-arc-cycle certificate:
  **unsure, likely not duplication** — different contraction notions, and the
  latter's docstring explicitly states its quantifier pattern is distinct.
