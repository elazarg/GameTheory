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
7. exact signed-monodromy correction, with absolute-weighted and pointwise
   compatibility interfaces;
8. finite charged return and single-seam closing for exact forward packets;
9. compilation of either lasso interface into a divergent support-rational
   path and then a uniform-equilibrium payoff; together with
10. a concrete analytic target-rejection theorem showing why packet extraction
   cannot be connected directly to target-preserving realization.

The arbitrary-game producer first requires a target dispatcher: accept the
packet value with an executable continuation contract, or reject it and
retarget through a proved strategic alternative.  Conditional on acceptance,
it requires three separate theorems:

1. resolved-chart construction, coverage, and arc lifting;
2. semantic Farkas decoding; and
3. arbitrarily charged finite forward packets in one compact carrier, or
   another rotation-uniform signed-monodromy producer, together with a
   strategic consumer for the complementary bounded-charge boundary.

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
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`.  At `z₀ = 1`, the module proves
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
`UniformEquilibrium/Quitting/Projective/AnchoredSingletonLCP.lean`.

At cemetery mass one the correct conclusion is

```text
value = anchor,
reward {i} i ≤ anchor i.
```

It is Never only when `anchor = 0`.  The original packet embeds into the
anchored interface through `QuittingProjectiveSingletonPacket.toAnchored`.

## 3. Analytic packet extraction in the matching regime

The packet modules are algebraic, while
`UniformEquilibrium/Quitting/Projective/AnalyticPacket.lean` constructs their assumptions from a
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

`UniformEquilibrium/Quitting/Projective/ResolvedChart.lean` records the exact contract:

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

`UniformEquilibrium/Quitting/Debt/Ledger/VanishingChargeRecurrenceNoGo.lean` records the scalar regression

```text
state n  = 1 / (n + 1),
charge n = 1 / (n + 1)^3,
```

for which compact recurrence does not give a return negligible relative to
charge.

## 8. Signed monodromy is the exact correction coordinate

Fix a cyclic root word `cycle`, proposed cyclic values `value`, and an entry
phase.  Write

```text
e_k = value k - F(cycle k, value (next k)),
c_k = quittingStationaryContinueMass (cycle k),
q_k = 1 - c_k,
s_k = product of c before phase k.
```

The exact one-turn affine identity is

```text
(1 - ∏ k, c_k) * (value phase - periodicValue phase)
  = ∑ k, s_k * e_k.
```

Thus, under positive aggregate absorption, the rotation-uniform signed bound

```text
∀ phase who,
  |∑ k, s_k * e_k(who)| ≤ η * (1 - ∏ k, c_k)
```

is equivalent to coordinatewise `η`-closeness to the actual periodic values.
Cancellation inside one turn is legitimate; checking every cyclic entry is
still load-bearing.

The older absolute condition

```text
∑ k, s_k * |e_k| ≤ η * (1 - ∏ k, c_k)
```

is stronger by the triangle inequality.  A formal two-phase example satisfies
the signed bound and violates the absolute bound for the same candidate.
Nevertheless, at every positive accuracy, signed-lasso production is
equivalent to exact finite support-rational-cycle production after correction;
this sharpens candidate acceptance without proving a broader existence class.

The principal declarations are

```text
one_sub_prod_mul_quittingCyclicDifference_eq_residualCharge
isQuittingRotationUniformSignedResidual_iff_value_close
QuittingFiniteSignedProjectiveLasso.
```

## 9. Relative return must be uniform over cyclic rotations

A return estimate in one orientation is insufficient.  A seam hidden behind a
zero-survival phase may be fully exposed when the same word is entered one
phase later.  The required target is therefore

```text
∀ phase who,
  |signedResidual phase who| ≤ η * weightedAbsorption,
```

or an equivalent bound on the maximum ratio over all phases and players.

`IsQuittingRotationUniformSignedResidual` is the canonical exact predicate.
`QuittingFiniteWeightedProjectiveLasso` remains a stronger compatibility
certificate and delegates through its `.toSigned` adapter.  The pointwise
certificate

```text
|e_k(i)| ≤ η * q_k
```

is stronger still and maps through the same compiler chain.

## 10. Finite charged closing

Repeated labels are insufficient, but compactness becomes decisive once the
returned block carries a fixed amount of real charge.  For a requested endpoint
radius, cover one compact carrier by finitely many small balls.  A finite path
whose nonnegative unit-bounded charge reaches twice the number of labels has
two ordered points in one ball with intervening charge at least one.  The path
may depend on this finite threshold.

For `0 ≤ q_k ≤ 1`,

```text
product_k (1-q_k) * (1 + sum_k q_k) ≤ 1.
```

Hence a returned block of raw charge at least one has aggregate absorption at
least one half.  Reversing an exact forward Bellman block makes every internal
cyclic seam zero; only the endpoint closure remains.  Every rotation encounters
that seam exactly once with survival prefix at most one.  Therefore

```text
∀ chargeTarget ≥ 0, ∃ one finite exact forward packet
```

in a carrier independent of `chargeTarget` already implies single-seam lassos
at every accuracy.  It does not require one orbit that works for all charge
targets or a separate rotation-recurrence theorem.

## 11. Canonical compilation

The signed certificate is the compiler base; the absolute-weighted and
single-seam certificates are adapters:

```text
QuittingFiniteSingleSeamProjectiveLasso
  → QuittingFiniteWeightedProjectiveLasso
  → QuittingFiniteSignedProjectiveLasso
  → exact periodic value
  → IsQuittingFiniteSupportRationalCycle
  → divergent support-rational path
  → IsUniformEquilibriumPayoff.
```

The corresponding terminal theorems consume signed, absolute-weighted,
single-seam, or finite-forward packet producers.  Endpoint differences are
`1`-Lipschitz in the continuation coordinate, so exact periodic correction
costs one additional lasso error in support optimality and rationality.

## 12. Correct dependency graph

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
               → arbitrarily charged finite forward packets
                    → compact finite charged return
                    → single-seam lasso
                  or
                  another rotation-uniform signed-monodromy candidate
                    → signed projective lasso
               → exact periodic support-rational cycle
               → divergent path
               → uniform-equilibrium payoff.
```

A failure at any producer arrow must be exposed as its own theorem or finite
barrier.  It may not be replaced by the corresponding verifier or compiler.
