# Projective packets and charged lassos: exact compiler boundary

## Status

This note separates the proved projective layer from the arbitrary-game
producer.  The distinction is structural: normalization, compactness,
linear-algebra alternatives, recurrence on finite labels, and certificate
compilation do not by themselves construct an executable strategic path.

The Lean-checked layer consists of:

1. exact first-event normalization;
2. canonical matching-order analytic singleton-packet extraction;
3. zero-anchor and affine-anchor singleton LCP algebra;
4. affine tangent feasibility or a Farkas obstruction;
5. a typed resolved-chart/arc-lifting interface;
6. finite output-or-repeated-label recurrence;
7. pointwise and rotation-uniform weighted lasso correction; and
8. compilation of a weighted lasso into a divergent support-rational path and
   then a uniform-equilibrium payoff; together with
9. a concrete analytic target-rejection theorem showing why packet extraction
   cannot be connected directly to target-preserving realization.

The arbitrary-game producer first requires a target dispatcher: accept the
packet value with an executable continuation contract, or reject it and
retarget through a proved strategic alternative.  Conditional on acceptance,
it requires three separate theorems:

1. resolved-chart construction, coverage, and arc lifting;
2. semantic Farkas decoding; and
3. rotation-uniform relative projective return.

None of these three obligations is silently bundled into “Physical Pivot
Completeness,” and target acceptance is not silently bundled into packet
normalization.

## 1. Exact first-event projectivization

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

Thus `ω₀` is the normalized cemetery mass and `ω₁` is normalized real
absorption mass.  The matching regime is the interior face `0 < ω₀ < 1`;
discarding `ω₀` loses part of the first-event packet.

The exact scalar algebra is formalized by:

```text
Math.projectiveCemeteryWeight_add_absorptionWeight
Math.projectiveBellman_balance
Math.projectiveBellman_value_eq_absorptionWeight_mul_conditional
```

## The cemetery coordinate is not a strategic continuation

The normalized cemetery mass contributes its anchor to the affine Bellman
identity.  It does not specify behavior that can implement the same event in
the undiscounted game.  This distinction is necessary even for a genuine
matching-order analytic branch of exact discounted equilibria.

The two-player reward table

```text
r({false})     = (1, 2),
r({true})      = (2, 1),
r({false,true}) = (2, 2)
```

has an analytic branch at discount factor `1 - t` in which both players quit
with probability `t / (1 - t)` and the live value is `(1,1)`.  Its quit order
matches the discount order and its extracted packet is

```text
cemetery = singleton false = singleton true = 1/3,
value = (1,1).
```

Nevertheless, if a terminal `epsilon`-Nash profile has payoff `u` with
`|u_i - 1| <= delta` for both players, then

```text
1 - delta <= 4 * (delta + epsilon).
```

The proof tests each player against quitting at a late deterministic date.
That deviation converges to `2` minus the probability that the opponent never
quits.  Both opponent exit probabilities are therefore at most
`delta + epsilon`; survival-product domination then bounds the prescribed
payoff by twice their sum.  At equal errors, `eta >= 1/9`, and the packet value
is not a uniform-equilibrium payoff.  The singleton sure-exit profiles still
give exact uniform payoffs `(1,2)` and `(2,1)`.

Thus the correct producer interface is a disjunction:

```text
packet
  -> accepted target plus executable cemetery continuation
   | rejected target plus certified strategic retarget.
```

The general analytic target-selection layer already distinguishes endpoint
acceptance from obstruction and retargeting.  The quitting example is the
projective regression ensuring that finite packet and lasso code is connected
through that layer, rather than treating an affine anchor as a strategy.

## 2. Zero-anchor and affine-anchor singleton packets

### 2.1 Initial discounted chart

For the initial vanishing-discount chart the cemetery payoff is `0`.  Suppose a
limiting packet has cemetery mass `z₀`, singleton masses `z i`, and value
`value`, with

```text
z₀ + ∑ i, z i = 1,
value who = ∑ i, z i * reward {i} who.
```

Assume endpoint complementarity supplies

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

This is `quittingProjectiveSingletonPacket_isLCP` in
`QuittingProjectiveSingletonLCP.lean`.  At `z₀ = 1`, the module proves
`value = 0` and every solo payoff is nonpositive, the Never boundary.

### 2.2 Cemetery rebasing

Projective pivoting may replace the zero cemetery payoff by an affine
continuation anchor `anchor`.  The packet identity must then retain that
coordinate:

```text
value who = cemetery * anchor who +
  ∑ owner, singleton owner * reward {owner} who.
```

With

```text
a i = anchor i - reward {i} i,
```

the same LCP balance and complementarity hold.  This is formalized by
`QuittingAnchoredProjectiveSingletonPacket` in
`QuittingProjectiveAnchoredSingletonLCP.lean`.

At cemetery mass one the correct conclusion is

```text
value = anchor,
reward {i} i ≤ anchor i.
```

It is Never only when `anchor = 0`.  The original packet embeds into the
anchored interface through `QuittingProjectiveSingletonPacket.toAnchored`.

## 3. Analytic packet extraction in the matching regime

The packet modules are algebraic, while
`QuittingProjectiveAnalyticPacket.lean` constructs their assumptions from a
matching analytic quitting germ.

Let the germ discount complement be

```text
λ(t) = t^q
```

and suppose the quit family has matching leading order `q`:

```text
y_i(t) = α_i t^q + o(t^q),
L = ∑ i, α_i > 0.
```

The existing analytic-order library proves

```text
Q(t) = 1 - ∏ i (1 - y_i(t)) = L t^q + o(t^q).
```

For singleton `i`,

```text
P_i(t) = y_i(t) * ∏ j ≠ i (1 - y_j(t))
       = α_i t^q + o(t^q).
```

The first-event denominator is

```text
D(t) = λ(t) + (1 - λ(t)) Q(t)
     = (1 + L) t^q + o(t^q).
```

Hence the expected limiting packet is

```text
z₀ = 1 / (1 + L),
z_i = α_i / (1 + L).
```

Nonsingleton mass is quadratic.  Bonferroni gives

```text
0 ≤ Q(t) - ∑ i P_i(t)
  ≤ 1/2 * (∑ i y_i(t))^2,
```

so normalized nonsingleton first-event mass tends to zero.  Exact endpoint
complementarity passes to the limit because the proof works on an explicit
punctured physical discount slice, every quit rate tends to zero, and a
positive leading coefficient gives eventual positive support and therefore
owner pinning.  The Bellman balance gives the limiting singleton-mixture
identity.  Together these facts construct
`QuittingProjectiveSingletonPacket` directly.

This theorem closes the matching-order case only.  The complete order
trichotomy remains

```text
m < q  → cemetery mass 0,
m = q  → cemetery mass 1 / (1 + ∑ α_i),
q < m  → cemetery mass 1 and Never in the zero-anchor chart.
```

The other two regimes require separate boundary theorems; they are not hidden
inside the matching packet.  Matching extraction is independent of the later
pivot and lasso problems.

## 4. The legitimate local affine alternative

After a resolved chart, complementary basis, valuation cone, and active jet
order have been fixed, a candidate tangent has finite affine form

```text
A h = b,
G h ≥ 0.
```

`Math.AffineEqualityFarkas` proves

```text
affineEqualityInequality_feasible_or_farkas
```

whose second branch supplies `y` and `lambda` with

```text
lambda ≥ 0,
Aᵀ y + Gᵀ lambda = 0,
bᵀ y > 0.
```

This is linear algebra only.  A Farkas row does not contain an executable
profile, chronology, target-selection theorem, arbitrary-behavior deviation
cap, credible punishment, or reconstruction map.

## 5. Resolved charts and arc lifting are an additional obligation

The affine theorem starts after `A`, `b`, and `G` have been supplied.  A real
producer must construct them from the projective quitting Bellman boundary,
prove that finitely many resolved charts cover the relevant boundary, and
show that every feasible tangent integrates to an actual positive analytic or
Puiseux successor.

Linearized feasibility alone is insufficient.  For example, the real variety

```text
x^2 + y^2 = 0
```

has the entire plane as its linear tangent space at the origin but has no
nonconstant real arc through the origin.

`QuittingProjectiveResolvedChart.lean` records the exact contract:

```text
QuittingResolvedProjectiveChartInterface
```

contains the finite chart data, a physical-successor relation, and an explicit
field `lift_feasible`.  Once that field is supplied,

```text
QuittingResolvedProjectiveChartInterface.physicalSuccessor_or_farkas
```

returns an actual physical successor or the corresponding affine Farkas row.
The module does not construct an instance for the quitting Bellman variety;
that construction, coverage proof, and arc-lifting theorem remain producer
work.

## 6. Semantic Farkas decoding remains strategic

A normalized obstruction arising from a resolved quitting chart must be
converted into one of the following fully typed outputs:

1. a stationary or pure terminal certificate;
2. Never;
3. an executable target-closed tail together with the prefix and deviation
   interface needed by its compiler;
4. zero-cemetery positive real absorption; or
5. a strict well-founded rank descent whose child certificate reconstructs at
   the parent target.

The reconstruction and credibility clauses are part of the theorem.  Generic
Farkas duality does not imply them.

## 7. Finite recurrence is only repeated-label recurrence

`Math.FinitePivotOrbit` proves a finite pigeonhole statement: within the first
`card Cell + 1` iterates, either an output label appears or a non-output label
repeats.

A projective or tropical cell generally contains continuously many coefficient
points.  Repetition of its label does not imply:

- equality of the underlying projective states;
- a fixed point of chart monodromy;
- a small return seam; or
- a seam small relative to vanishing real absorption.

`QuittingVanishingChargeRecurrenceNoGo.lean` records the scalar regression

```text
state n  = 1 / (n + 1),
charge n = 1 / (n + 1)^3,
```

for which compact recurrence does not give a return negligible relative to
charge.

## 8. The invariant weighted lasso condition

Fix a cyclic root word `cycle`, proposed cyclic values `value`, and an entry
phase.  Write

```text
e_k = value k - F(cycle k, value (next k)),
c_k = quittingStationaryContinueMass (cycle k),
q_k = 1 - c_k,
s_k = product of c before phase k.
```

The invariant finite condition is

```text
∑ k, s_k * |e_k| ≤ η * ∑ k, s_k * q_k.
```

The denominator is exactly

```text
∑ k, s_k * q_k = 1 - ∏ k, c_k.
```

Consequently, if `u` is the actual periodic value,

```text
|value - u|
  ≤ (∑ k, s_k * |e_k|) / (∑ k, s_k * q_k)
  ≤ η.
```

This is

```text
abs_quittingCyclicValue_sub_terminalValue_le_of_weightedResidual.
```

It handles zero-charge phases and unequal scales without dropping seams.

## 9. Relative return must be uniform over cyclic rotations

A return estimate in one orientation is insufficient.  A seam hidden behind a
zero-survival phase may be fully exposed when the same word is entered one
phase later.  The required target is therefore

```text
∀ phase who,
  weightedResidual phase who ≤ η * weightedAbsorption,
```

or an equivalent bound on the maximum ratio over all phases and players.

`IsQuittingRotationUniformWeightedResidual` formalizes this requirement, and
`QuittingFiniteWeightedProjectiveLasso` uses it as its canonical seam field.
The pointwise certificate

```text
|e_k(i)| ≤ η * q_k
```

is stronger and maps into the weighted interface through

```text
QuittingFiniteChargedProjectiveLasso.toWeighted.
```

## 10. Canonical weighted compilation

`QuittingWeightedProjectiveLasso.lean` carries the weighted certificate through
all downstream stages:

```text
QuittingFiniteWeightedProjectiveLasso
  → exact periodic value
  → IsQuittingFiniteSupportRationalCycle
  → divergent support-rational path
  → IsUniformEquilibriumPayoff.
```

The public terminal theorem is

```text
quittingGame_exists_uniformEquilibriumPayoff_of_weightedProjectiveLassos.
```

Endpoint differences are `1`-Lipschitz in the continuation coordinate, so
exact periodic correction costs one additional lasso error in support
optimality and rationality.

## 11. Correct dependency graph

The arbitrary-game route has the explicit form

```text
analytic quitting germ
  → matching singleton first-event packet
  → target gate
      rejected → certified strategic retarget
      accepted → executable cemetery continuation
               → resolved chart construction and coverage
               → feasible tangent or Farkas row
               → arc-lifted physical successor or semantic Farkas output
               → physical orbit
               → rotation-uniform relative return
               → weighted projective lasso
               → exact periodic support-rational cycle
               → divergent path
               → uniform-equilibrium payoff.
```

A failure at any producer arrow must be exposed as its own theorem or finite
barrier.  It may not be replaced by the corresponding verifier or compiler.
