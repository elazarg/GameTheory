# Lean map: reverse consequences of uniform equilibrium

This file is the proof-engineering index for the reverse-consequence layer.
The conceptual and mathematical exposition is in
[ReverseConsequences.md](ReverseConsequences.md); the present document records
exact declarations, dependency direction, proof ideas, and scope boundaries.

The semantic object throughout is
`StochasticGame.IsUniformEquilibriumPayoff`: for each positive accuracy, one
history-dependent behavior profile and one horizon threshold must work for all
later finite horizons and every unilateral behavioral strategy.

## Entry point

`GameTheory/Concepts/Stochastic/UniformConsequences.lean` imports the complete
Lean layer added by this development:

1. `UniformTailWidth.lean`;
2. `UniformTailWidthObstruction.lean`;
3. `UniformBoundedWork.lean`;
4. `UniformAsymptoticPayoffEquivalence.lean`;
5. `UniformExpectedPotentialShaping.lean`;
6. `TransitionPerturbationDiscontinuity.lean`.

`GameTheory/Theorems.lean` imports this entry point, so all declarations are
reachable from the root library import.

---

## 1. Uniform tail width

File: `GameTheory/Concepts/Stochastic/UniformTailWidth.lean`

### Definitions

#### `StochasticGame.HasUniformTailInterval`

For a profile `σ` and payoff vectors `lower`, `upper`, one common threshold
`T₀` eventually guarantees

- `lower i ≤ finiteAveragePayoff σ i` on prescribed play; and
- every unilateral behavioral deviation payoff is at most `upper i`.

Following `σ i` is itself one admissible deviation, so the second clause also
bounds prescribed play above.

#### `StochasticGame.tailIntervalMidpoint`

Coordinatewise midpoint `(lower i + upper i) / 2`.

#### `StochasticGame.HasArbitrarilyThinTailIntervals`

For every positive `δ`, some profile and tail interval have coordinatewise
width at most `δ`.

### Lemmas and theorems

#### `abs_onPath_sub_tailIntervalMidpoint_le`

If prescribed play lies between the two endpoints and the interval width is at
most `δ`, prescribed payoff is within `δ` of the midpoint. The constant is
intentionally loose: half-width sharpness is irrelevant to the existence
argument and would add arithmetic noise.

#### `IsUniformEquilibriumPayoff.hasArbitrarilyThinTailIntervals`

A uniform-equilibrium target `v` gives, at width `δ`, the interval

`[v - δ/3, v + 2δ/3]`.

The on-path approximation supplies the lower endpoint; the Nash inequality
plus on-path upper approximation supplies the all-deviation upper endpoint.

#### `exists_uniformEquilibriumPayoff_of_hasArbitrarilyThinTailIntervals`

Arbitrarily thin intervals imply existence of a uniform-equilibrium payoff.
The proof:

1. chooses widths `δ_n = 1/(n+1)`;
2. takes interval midpoints;
3. bounds them in one finite-dimensional payoff cube using the repository's
   stage-payoff bound;
4. extracts a convergent midpoint subsequence;
5. at a requested accuracy, uses one sufficiently late interval and its own
   profile.

No behavior profile is passed to a limit.

#### `exists_uniformEquilibriumPayoff_iff_hasArbitrarilyThinTailIntervals`

The exact quantifier-level spectral-width characterization:

`(∃ v, IsUniformEquilibriumPayoff v) ↔ HasArbitrarilyThinTailIntervals`.

### Scope

This characterization is over all behavior profiles and all unilateral
behavior strategies. It is not a statement about stationary, periodic,
finite-memory, or public-controller classes.

---

## 2. Positive tail-width obstruction

File: `GameTheory/Concepts/Stochastic/UniformTailWidthObstruction.lean`

### Theorems

#### `exists_pos_tailWidth_of_not_exists_uniformEquilibriumPayoff`

If no uniform-equilibrium payoff exists, one fixed `δ > 0` defeats every
proposed tail interval: for every profile and every eventual interval satisfying
the semantic lower/all-deviation-upper conditions, some player coordinate has
width strictly larger than `δ`.

#### `not_exists_uniformEquilibriumPayoff_iff_exists_pos_tailWidth`

Exact negative characterization. This is the direct theorem-search target for
a counterexample: prove a positive global tail-width gap.

### Interpretation

The witness need not be one fixed deviation or one fixed horizon. It certifies
that every profile leaves an asymptotic payoff/deviation band of positive width
somewhere.

---

## 3. Bounded excess work

File: `GameTheory/Concepts/Stochastic/UniformBoundedWork.lean`

### Definitions

#### `StochasticGame.HasBoundedWorkCertificate`

For every positive linear penalty `η`, one profile and one nonnegative constant
`B` bound, for all horizons and players,

- every deviation's cumulative excess above `v + η`; and
- prescribed play's cumulative deficit below `v - η`.

The cumulative quantity is written as `T` times a finite-average difference,
so it has the same meaning as total excess work without adding another payoff
API.

#### `StochasticGame.HasUnboundedWorkObstruction`

One positive penalty defeats every profile and every proposed finite budget:
at some horizon and player, either a unilateral behavior deviation exceeds the
budget or prescribed play accumulates too much target deficit.

### Theorems

#### `IsUniformEquilibriumPayoff.hasBoundedWorkCertificate`

For late horizons, a uniform `η/2` certificate makes penalized work
nonpositive. The finitely many early horizons are controlled by one common
stage-payoff and target-coordinate bound.

#### `isUniformEquilibriumPayoff_of_hasBoundedWorkCertificate`

Choose the work certificate at penalty `ε/4`, then choose `T₀` so that
`B/T < ε/4` for every `T ≥ T₀`. The two work inequalities yield payoff
delivery and the full unilateral Nash inequality.

#### `isUniformEquilibriumPayoff_iff_hasBoundedWorkCertificate`

Exact fixed-target bounded-work characterization.

#### `not_isUniformEquilibriumPayoff_iff_hasUnboundedWorkObstruction`

Exact fixed-target negative characterization, obtained by logical negation of
the bounded-work theorem.

### Scope boundary

This is a root-level semantic ledger. It does not assert that the account is
finite-memory, public, continuous, semialgebraic, or uniformly bounded at every
continuation distribution. Those are compression and implementation claims.

---

## 4. Uniformly vanishing payoff transformations

File:
`GameTheory/Concepts/Stochastic/UniformAsymptoticPayoffEquivalence.lean`

### Definition

#### `StochasticGame.HasFiniteAverageGapAtMost`

For a fixed-skeleton replacement reward table and horizon modulus `gap T`, the
absolute finite-average payoff difference is at most `gap T` for every
behavior profile and player. Because the quantifier covers every profile, it
also covers every unilateral deviation profile.

### Theorems

#### `isUniformEquilibriumPayoff_of_withStagePayoff_of_tendsto_gap_zero`

If `gap T → 0`, every uniform-equilibrium payoff of the transformed game is a
uniform-equilibrium payoff of the original game.

#### `isUniformEquilibriumPayoff_withStagePayoff_of_tendsto_gap_zero`

The converse transfer.

#### `isUniformEquilibriumPayoff_withStagePayoff_iff_of_tendsto_gap_zero`

Exact equality of the fixed-target uniform-equilibrium payoff predicates under
a uniformly vanishing all-profile payoff transformation.

### Proof accounting

At a requested accuracy, choose the original/transformed uniform certificate at
quarter accuracy and a horizon after which the gap is at most one quarter.
One gap copy pays for on-path delivery; two copies pay for the two sides of a
Nash comparison.

---

## 5. Expected-potential gauge invariance

File: `GameTheory/Concepts/Stochastic/UniformExpectedPotentialShaping.lean`

### Definitions

#### `expectedPotentialShapedReward`

For player `i`, add

`expect (transition s a) (F i) - F i s`

to the current stage payoff.

#### `withExpectedPotentialShaping`

The corresponding fixed-skeleton game.

### Exact telescope

#### `stageEUAt_withExpectedPotentialShaping`

One-stage expected payoff equals original expected payoff plus expected next
potential minus current potential.

#### `expectedStagePayoff_withExpectedPotentialShaping`

After averaging over the history distribution, the shaping term is

`expectedStateValue (t+1) - expectedStateValue t`.

#### `expect_totalPayoff_withExpectedPotentialShaping`

The cumulative expected shaping term telescopes exactly to

`expectedStateValue T - F s₀`.

#### `finiteAveragePayoff_withExpectedPotentialShaping_sub`

The finite-average difference is the endpoint term divided by `T`.

### Bounds and invariance

#### `abs_finiteAveragePayoff_withExpectedPotentialShaping_sub_le`

If `|F i s| ≤ C`, the finite-average gap is at most `2C/T`.

#### `hasFiniteAverageGapAtMost_withExpectedPotentialShaping`

Provides the all-horizon modulus `4C/(T+1)`, including the zero horizon.

#### `tendsto_expectedPotentialShapingGap_zero`

The modulus tends to zero.

#### `isUniformEquilibriumPayoff_withExpectedPotentialShaping_iff`

Bounded expected-potential shaping preserves exactly the set of
uniform-equilibrium payoff vectors.

### Interpretation

This is the formal gauge-invariance theorem. Any valid asymptotic obstruction
must survive addition of a bounded expected coboundary.

---

## 6. Transition perturbation discontinuity

File:
`GameTheory/Concepts/Stochastic/TransitionPerturbationDiscontinuity.lean`

### Game

`rareTransitionGame p` has:

- one player and one action;
- bad state `false`, paying `0`;
- good absorbing state `true`, paying `1`;
- from the bad state, transition to the good state with probability `p`.

### Kernel convergence

The four coordinate lemmas compute every real transition probability. Theorem
`tendsto_transition_toReal_at_zero` proves coordinatewise convergence of the
kernel table whenever `p_n → 0`. Since the state/action table is finite, this
is also uniform convergence of the table.

### Payoff computation

- `badMass_succ`: remaining bad mass is multiplied by `1-p`;
- `badMass_eq_pow`: bad mass at date `t` is `(1-p)^t`;
- `expectedStagePayoff_eq_one_sub_pow`: expected stage payoff is
  `1-(1-p)^t`;
- `tendsto_expectedStagePayoff_one`: for `p>0`, stage payoffs converge to `1`;
- `tendsto_finiteAveragePayoff_one`: Cesàro averages converge to `1`.

### Strategic conclusion

- `isUniformEquilibriumPayoff_one_of_pos`: target `1` is a
  uniform-equilibrium payoff for every `p>0`; there is no strategic choice.
- `finiteAveragePayoff_zero`: at `p=0`, every finite average from the bad state
  is zero.
- `not_isUniformEquilibriumPayoff_one_at_zero`: target `1` fails at the limit
  kernel.

### Meaning

Uniform-equilibrium payoff closedness under arbitrary transition-kernel
perturbations is false. Small one-step changes can alter eventual recurrent
class entry and create an order-one long-run effect.

---

## 7. Dependency and honesty boundary

The Lean layer proves:

- reward-table closure from the pre-existing perturbation modules;
- tail-width existence and nonexistence characterizations;
- bounded-work existence and fixed-target failure characterizations;
- semantic invariance under uniformly vanishing all-profile payoff changes;
- bounded expected-potential gauge invariance;
- a transition-kernel continuity counterexample.

The following mathematics is documented in
[ReverseConsequences.md](ReverseConsequences.md) but is not claimed as landed
Lean in this PR:

- the `limsup`/`liminf` scalar spectral defect and its `2`-Lipschitz estimate;
- the full causal distribution-state available-storage construction;
- finite signed current duality and the current-or-escape replacement in
  infinite systems;
- additive tensor-product closure against arbitrary correlated component
  deviations;
- patient-evaluation mixture theorems;
- rooted continuation-tree invariant shadows;
- marked multiscale absorption currents, their topology, and both strategic
  decoders;
- the compact-semigroup idempotent-sandwich heuristic.

The enriched quitting-game compactification and its valid-path/failed-path
decoders remain open. The documentation states finite formalization targets and
falsification tests without upgrading them to proved consequences.

## Validation record

The declarations are written against the current `uniform-existence` APIs and
imported through `UniformConsequences.lean`. Review should build

```text
lake build +GameTheory.Concepts.Stochastic.UniformConsequences
```

and run the repository placeholder/axiom audit. The PR description records the
actual validation state; this document does not claim a successful build until
one has been observed.
