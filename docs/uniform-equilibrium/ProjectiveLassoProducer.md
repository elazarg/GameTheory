# Projective packets and charged lassos: compiler and producer boundary

## Status

This note separates five statements which must not be conflated.

1. **Exact first-event normalization** is Lean-checked in
   `Math.ProjectiveBellmanPacket`.
2. **The normalized singleton packet satisfies an affine LCP** is
   Lean-checked in `QuittingProjectiveSingletonLCP` once the limiting packet
   hypotheses have been supplied.
3. **A resolved affine tangent is feasible or has a decoded Farkas row** is
   Lean-checked in `Math.AffineEqualityFarkas`.
4. **A charged projective lasso can be corrected and compiled** is
   Lean-checked in `QuittingProjectiveLasso` and
   `QuittingProjectiveLassoWeighted`.
5. **Every finite quitting game supplies a strategic output or such a lasso**
   is not proved.  It requires two separate new theorems: semantic Farkas
   decoding and relative projective return.

The last item is the producer.  The preceding items are normalization,
linear-algebra alternatives, recurrence bookkeeping, and certificate
compilers.  None of them is silently counted as the arbitrary-game producer.

## 1. First-event projectivization

Let `ε > 0` be the discount complement and write `β = 1 - ε`.  At a stationary
root, let

- `c` be the probability that everybody continues;
- `q = 1 - c` be real absorption; and
- `a` be the unconditional one-stage absorbing payoff contribution.

The discounted Bellman equation in one coordinate is

```text
v = β * (a + c * v).
```

Define

```text
D  = ε + β * q = 1 - β * c,
ω₀ = ε / D,
ω₁ = β * q / D.
```

Then

```text
ω₀ + ω₁ = 1,
D * v = β * a.
```

When `q > 0`,

```text
v = ω₁ * (a / q).
```

Thus `ω₀` is the normalized cemetery mass and `ω₁` is the normalized real
absorption mass.  The matching regime is the interior face `0 < ω₀ < 1`;
discarding `ω₀` loses part of the first-event packet.

The exact scalar algebra is formalized by:

```text
Math.projectiveCemeteryWeight_add_absorptionWeight
Math.projectiveBellman_balance
Math.projectiveBellman_value_eq_absorptionWeight_mul_conditional
```

## 2. The normalized singleton LCP

Suppose a limiting first-event packet has cemetery mass `z₀`, singleton masses
`z i`, and value `value`, with

```text
z₀ + ∑ i, z i = 1,
value who = ∑ i, z i * reward {i} who.
```

Assume also the endpoint consequences

```text
reward {i} i ≤ value i,
z i > 0 → value i = reward {i} i.
```

Set

```text
d i   = reward {i} i,
a i   = -d i,
M i j = reward {j} i - d i,
w i   = value i - d i.
```

Then

```text
w i = z₀ * a i + ∑ j, z j * M i j,
w i ≥ 0,
z i * w i = 0.
```

This exact algebra is the theorem

```text
quittingProjectiveSingletonPacket_isLCP.
```

At `z₀ = 1`, the same module proves that every singleton mass vanishes, the
packet value is zero, and every solo payoff is nonpositive: the Never
boundary.

The module does not claim the analytic extraction of the packet from every
prescribed discounted sequence.  That extraction must establish vanishing of
nonsingleton first-event mass and pass endpoint complementarity to the limit.

## 3. The legitimate local pivot theorem

Once a resolved chart, complementary basis, valuation cone, and active jet
order are fixed, a candidate physical tangent has the finite affine form

```text
A h = b,
G h ≥ 0.
```

`Math.AffineEqualityFarkas` encodes each equality by two weak inequalities and
applies the repository's Fourier--Motzkin theorem of the alternative.  It
proves

```text
affineEqualityInequality_feasible_or_farkas
```

whose second branch supplies `y` and `lambda` with

```text
lambda ≥ 0,
Aᵀ y + Gᵀ lambda = 0,
bᵀ y > 0.
```

This is the correct local statement:

```text
physical candidate tangent  OR  normalized/rescalable Farkas obstruction.
```

It is only linear algebra.  The Farkas row does not itself contain an
executable profile, chronology, target-selection proof, arbitrary-behavior
deviation cap, credible punishment, or reconstruction map.

## 4. The invariant charged-lasso condition

Fix a finite root word `cycle`, proposed cyclic values `value`, and a starting
phase.  Write

```text
e_k = value k - F(cycle k, value (next k)),
c_k = quittingStationaryContinueMass (cycle k),
q_k = 1 - c_k,
s_k = product of c before phase k.
```

The invariant finite condition is the weighted cyclewise estimate

```text
∑ k, s_k * |e_k| ≤ η * ∑ k, s_k * q_k.
```

The denominator is exactly

```text
∑ k, s_k * q_k = 1 - ∏ k, c_k.
```

Therefore, if `u` is the actual value selected by periodic repetition,

```text
|value - u|
  ≤ (∑ k, s_k * |e_k|) / (∑ k, s_k * q_k)
  ≤ η.
```

This is formalized by

```text
abs_quittingCyclicValue_sub_terminalValue_le_of_weightedResidual.
```

It handles zero-charge phases without dropping their seams.

The original structure

```text
QuittingFiniteChargedProjectiveLasso reward K η
```

uses the stronger pointwise hypothesis

```text
|e_k(i)| ≤ η * q_k.
```

That condition is sound and implies the weighted criterion; in particular,
`q_k = 0` forces `e_k(i) = 0`.  The implication is

```text
quittingCyclicWeightedResidual_le_of_pointwise.
```

## 5. Exact correction and compilation

Endpoint differences are `1`-Lipschitz in the relevant continuation
coordinate:

```text
abs_quittingRootEndpointDifference_sub_le_tail.
```

Consequently replacing the proposed values by the exact periodic values costs
at most one additional lasso error in support optimality and punishment
rationality.  The pointwise certificate compiles through

```text
QuittingFiniteChargedProjectiveLasso.toFiniteSupportRationalCycle
QuittingFiniteChargedProjectiveLasso.exists_supportRationalDivergentPath
quittingGame_exists_uniformEquilibriumPayoff_of_chargedProjectiveLassos.
```

This is a complete **consumer** of charged lassos.  It does not construct them
for arbitrary games.

## 6. What finite recurrence does and does not prove

`Math.FinitePivotOrbit` proves only a finite-label pigeonhole statement:
within the first `card Cell + 1` iterates, either an output label appears or a
non-output label repeats.

A projective or tropical cell generally contains continuously many coefficient
points.  Repetition of a label does not imply:

- equality of the underlying projective states;
- a fixed point of the chart monodromy;
- small absolute return seam; or
- a seam small relative to a vanishing absorption charge.

The scalar regression in
`QuittingVanishingChargeRecurrenceNoGo.lean` makes the last failure explicit:

```text
state n  = 1 / (n + 1),
charge n = 1 / (n + 1)^3,
```

and every strict return has seam at least half the source charge.  Compact
recurrence alone therefore cannot create the relative return needed by the
lasso compiler.

## 7. Missing theorem A: semantic Farkas decoding

The local Farkas alternative must be followed by a genuinely strategic
classification:

> Every normalized obstruction arising from the projective quitting Bellman
> system yields one of:
>
> 1. a stationary or pure terminal certificate;
> 2. Never;
> 3. an executable target-closed tail together with its required prefix and
>    deviation interface;
> 4. zero-cemetery positive real absorption; or
> 5. a strict well-founded rank descent whose child certificate can be
>    reconstructed at the parent target.

The reconstruction and credibility clauses are part of the theorem.  Farkas'
lemma alone does not provide them.

## 8. Missing theorem B: relative projective return

Every infinite non-output pivot trajectory must supply recurrent segments
whose weighted seam is negligible relative to weighted real absorption, for
example

```text
weightedResidual(segment) /
  weightedAbsorption(segment) → 0.
```

Equivalently, one may prove a contraction or fixed-point theorem for every
recurrent chart monodromy.  Finite label recurrence is not a substitute.

## 9. Correct producer statement

Only after both missing theorems are established does the projective route
become an arbitrary-game producer:

```text
positive-cemetery branch
  → resolved tangent or Farkas row
  → strategic output or infinite physical pivot path
  → relative return segment
  → weighted charged lasso
  → exact periodic support-rational cycle
  → uniform-equilibrium payoff.
```

The current PR formalizes the exact normalization, singleton-LCP algebra,
local affine Farkas alternative, finite repeated-label lemma, and the complete
weighted lasso consumer.  It deliberately leaves the two strategic producer
theorems explicit.
