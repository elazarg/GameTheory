# Uniform-equilibrium toolkit

This page organizes the production library by mathematical job.  It is a
stable entry map, not a progress report: current priorities and open work live
in [`PIPELINE.md`](PIPELINE.md), while [`FRONTIER.md`](FRONTIER.md) states the
current mathematical boundary.

The central distinction is between a **compiler**, which turns a supplied
certificate into a uniform payoff, and a **producer**, which constructs that
certificate from more primitive game data.  A verifier, compactness theorem,
or counterexample restriction is not silently counted as either one.

## Dependency shape

```text
game or analytic data
        |
        v
producer / selector -----> certificate or executable path
                                  |
                                  v
                         verifier / compiler
                                  |
                                  v
                   IsUniformEquilibriumPayoff

closure and transfer tools move proved results between nearby games or
payoff descriptions; diagnostics and no-go results constrain every branch
without producing a witness.
```

## Canonical public entry points

| Family | Canonical import | What it exports |
| --- | --- | --- |
| Uniform-payoff consequences | `UniformConsequences.lean` | Semantic waist dependencies, target equivalence under vanishing payoff gaps, potential shaping, tail-width and bounded-work characterizations, and transition discontinuity. |
| Adaptive-potential systems | `AdaptivePotentialSystemTools.lean` | The single `AdaptivePotentialSystemAt` structure together with retargeting, profile transport, ledger conversion, finite-time bounds, and owner-separated assembly. |
| Quitting terminal selection | `QuittingTerminalUniformPayoffSelection.lean` | The equivalence between terminal approximate Nash existence at every accuracy and uniform-payoff existence for finite quitting games. |
| Diagonal target tails | `QuittingDiagonalTargetTail.lean` | Exact-prefix plus player-indexed closed-tail compilation and its counterexample restriction. |
| Support-retaining paths | `QuittingSupportWitnessUniform.lean` | Infinite support-rational path and finite periodic-cycle compilers. |
| Essential APS | `QuittingEssentialAPSAll.lean` | The complete singleton-flow APS layer, including the adaptive-mesh capstone. |
| Face circulations | `QuittingFaceCirculationAll.lean` | Certificate/orbit/path production, concrete payoff examples, and the two-coordinate boundary analyses. Use `MultiOwnerFaceCirculationCompactPath.lean` for the narrow generic compiler. |
| Boundary holonomy | `QuittingBoundaryHolonomyAll.lean` | Source-retaining fixed-cutoff compactness together with residual, self-similar, tangent, and realized-coordinate analysis. |
| Reward closure | `QuittingUniformPayoffExistenceClosure.lean` | Fixed-skeleton quitting-game existence under uniform reward limits and dense solved approximants. |
| Nonexistence certificates | `UniformNonexistenceCertificate.lean` | Late-horizon exploitability and quitting-terminal gaps that rule out every uniform payoff. |

Import an internal file directly when its narrower interface is the point of
the proof.  The umbrellas are navigation and downstream entry points, not a
ban on precise dependencies.

## Semantic waist and terminal bridge

`Uniform.lean` owns `StochasticGame.IsUniformEquilibriumPayoff` and
`HasUniformDeviationCapConstructor`.  Their exact equivalence is the
construction waist: a candidate mechanism is complete only after it supplies
the uniform finite-horizon delivery and unilateral-deviation bounds encoded by
that constructor.

For finite quitting games, the preferred higher-level waist is
`QuittingTerminalUniformPayoffSelection.lean`.  It selects one bounded target
from terminal approximate equilibria available at every positive accuracy and
then invokes the terminal-to-uniform bridge.  Terminal verification,
target selection, and uniformization remain separate steps in lower-level
proofs.

`AdaptivePotentialSystemTools.lean` is the transformation facade for the
proof-facing adaptive-potential waist. It deliberately reuses the one
`AdaptivePotentialSystemAt` definition: consolidation here means a canonical
API surface, not a second structure. Public stopping and response compilers
remain separate because they add causal-law realization and credibility
obligations.

## Positive construction families

| Family | Required input | Production output | Remaining nonclaim |
| --- | --- | --- | --- |
| Diagonal target tail | Accuracy-indexed exact Nash--Bellman prefixes with small joint survival and player-indexed target-closed tails | Terminal approximate equilibria and hence a uniform payoff | Does not construct the prefixes or prove their survival certificate. |
| Support witness | At every tolerance, a support-wise approximately optimal root path, divergent absorption, and continuation-by-continuation individual rationality; alternatively a finite periodic witness with one absorbing phase | A terminal `3ε` profile and target-free uniform-payoff existence | Does not produce the paths or cycles for arbitrary games. |
| Essential APS | A compact convex functional unique-live component with finite-window face avoidance, terminal-freeness, and bounds | A coherent executable path, qualitative deleted-player survival, adaptive finite meshes, and a uniform payoff for every initial component value | Does not prove that an arbitrary game has a nonempty component; pointwise full jumps remain outside the adaptive logarithmic mesh. |
| Multi-owner face circulation | A bounded balanced circulation with a uniform positive phase-ratio floor and a payoff floor above the quitting punishment value | A chronological support-rational path selected by compact finite-prefix reversal, then a uniform payoff | Does not construct such a circulation for every game or identify the selected target with a named certificate vertex. |
| Finite admissible cycle | A realized admissible absorbing cyclic continuation block | A terminal equilibrium and uniform payoff | The cycle disjunct is not exhaustive for all quitting games. |
| Two-player closure | An arbitrary finite two-player quitting game | Unconditional uniform-payoff existence | Does not extend the pair-repair classification to three or more players. |

The essential-APS and circulation families contain genuine producers relative
to their stated structured inputs.  They are conditional positive strata, not
generic quitting-game existence theorems.

## Reusable infrastructure

| Tool | Module | Use |
| --- | --- | --- |
| Discrete hazard stopping | `Math/Probability/DiscreteHazardStopping.lean` | Survival products, first-hit weights, total stopping mass, and bounded stopped-payoff accounting independent of quitting games. |
| Survival products | `Math/SurvivalProduct.lean` | Generic finite-product and cumulative-hazard estimates shared by stopping arguments. |
| Compact finite-prefix relations | `Math/Topology/CompactFinitePrefixRelation.lean` | Inverse-limit selection from compatible compact finite prefixes; used by circulation paths. |
| Finite phase occupation duality | `Math/Probability/PhaseOccupationDuality.lean` | Semantic/LP primal equivalence, bounded attainment, phase-bias decoding, and strong duality conditional on occupation feasibility. |
| Cyclic exposure | `Math/CyclicExposure.lean` | Sharp exposure bounds for finite permutation systems; the shared-punishment calculation is an application. |
| Nonperiodic Snell supersolution | `QuittingInfinitePathSupersolution.lean` | Turns exact Continue transport, vanishing local Quit error, and survival decay into history-dependent unilateral caps. |
| Target-anchored stopping tail | `QuittingTargetAnchoredTail.lean` | Constructs one player's stationary-opponent closed tail at a prescribed target. |
| Joint-survival selection | `QuittingJointSurvivalSelection.lean` | Identifies compactly selected continuation values with actual infinite-path terminal values under joint-survival decay. |

Phase-occupation duality is optimization infrastructure.  Until a concrete
strategic construction supplies a feasible phase occupation, it is not itself
a game or strategy producer.

## Closure and transfer

- `UniformAsymptoticPayoffEquivalence.lean` transfers an exact target across
  profile-uniform finite-average payoff gaps tending to zero.
- `UniformExpectedPotentialShaping.lean` applies that transfer to bounded
  expected-potential coboundaries with an `O(1/T)` endpoint telescope.
- `UniformPayoffExistenceClosure.lean` proves target-free existence closure
  under uniform stage-payoff limits on a fixed finite skeleton.
- `QuittingUniformPayoffExistenceClosure.lean` specializes the closure theorem
  to uniformly convergent quitting reward tables.
- `QuittingRootPerturbation.lean` gives local one-coordinate payoff and regret
  bounds; it should not be confused with target-free closure.

These tools transport an existing mechanism or existence result.  They do not
supply density of solved games or construct a missing certificate.

## Boundary analysis and diagnostics

`QuittingBoundaryHolonomyAll.lean` has two complementary compactness modes.
Fixed-cutoff and fixed-last lifts retain the actual root block, endpoints, and
provenance.  Tangent compactness retains only bounded coefficient coordinates
and normalized safety obstructions.  Neither mode closes the escaping-length
problem: the first cannot compactify unbounded literal length, and the second
does not prove realized-image closedness or provide a decoder.

The general reverse diagnostics are:

- arbitrarily thin eventual payoff/deviation intervals are equivalent to
  uniform-payoff existence;
- a fixed target is uniform exactly when it has a bounded excess-work
  certificate;
- positive tail width and late exploitability gaps give exact nonexistence
  witnesses; and
- convergence of transition kernels alone does not preserve uniform-payoff
  targets.

These characterize or falsify proposed routes.  They are not forward
construction mechanisms.

`QuittingTruncatedLedgerCapCounterexample.lean` adds an interface-level no-go:
the common all-player deleted-survival requirement of the truncated ledger-cap
package fails even for a solved two-player zero-solo game.  The package remains
a sound compiler input, but it is not a universal producer normal form.  A
complete route must preserve a persistent-live branch or replace the common
reach condition by a weaker value-sensitive condition.

## Semantic fences

The following distinctions are load-bearing across the toolkit:

1. probabilistic stopped-law accounting is not strategic law realization;
2. a public response or detector is not a credible punishment certificate;
3. positive occupation circulation does not transport a continuation target
   without a separate harmonicity or target-identification theorem;
4. compact coefficient projections do not imply closedness of the set of
   realized strategic blocks;
5. terminal approximate Nash, fixed-profile uniform approximation, and a
   uniform-equilibrium payoff are different notions until a named bridge is
   invoked; and
6. a fixed-target closure theorem and target-free existence closure solve
   different problems.

## Open leaves

The intentional conjecture leaves remain in
`UniformExistenceConjecture.lean` and `QuittingConjecture.lean`.
`QuittingReducedCapConjecture.lean` no longer carries an open declaration: it
records the valid branch-relative reduction and the formal two-player no-go for
the former universal package producer. Existing compilers narrow what the two
remaining leaves must produce; they do not discharge the arbitrary-game
producer.

For new work, first identify the row above whose required input is closest to
the available data.  If no row accepts it, record the missing adapter or
producer explicitly rather than creating another parallel compiler surface.
