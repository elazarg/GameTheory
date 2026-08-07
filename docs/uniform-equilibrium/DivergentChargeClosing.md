# Finite charged closing of projective Bellman orbits

## Result

The rotation-uniform relative-return obligation is not independent once a
physical producer can generate arbitrarily large **finite-prefix real
absorption**.

Let

```text
V_(n+1) = F(x_n, V_n),
q_n     = quittingRootAbsorptionMass(x_n),
c_n     = 1 - q_n.
```

Assume that all `V_n` lie in one compact set and `0 <= q_n <= 1`.  For every
`eta > 0` there is a finite number `Q(eta)` with the following property:
whenever one finite orbit has prefix charge at least `Q(eta)`, it contains
`a < b` such that

```text
dist(V_a,V_b) < eta / 2,
sum_{n=a}^{b-1} q_n >= 1.
```

Reverse that block and close it periodically.  Every interior Bellman seam is
zero.  The unique closing seam is smaller than `eta / 2`, while the whole
cycle absorbs with probability at least `1/2`.  Hence every cyclic rotation
satisfies

```text
weightedResidual <= eta * weightedAbsorption.
```

Thus an exact bounded forward Bellman producer with arbitrarily large finite
prefix absorption already produces the repository's rotation-uniform weighted
projective lassos.  A single infinite orbit working for all charge targets is
unnecessary.

## 1. Finite charged-return pigeonhole theorem

Fix a finite labelling with `m` labels and let

```text
S_t = sum_{n<t} q_n.
```

Suppose `S_T >= 2m`.  For `j = 0,...,m`, let `t_j` be the first time at which

```text
S_(t_j) >= 2j.
```

Because each increment is at most one, minimality gives

```text
2j <= S_(t_j) < 2j + 1.
```

There are `m+1` sampled times and only `m` labels.  Hence two sampled times,
with ranks `j < k`, have the same label.  Their clock gap satisfies

```text
S_(t_k) - S_(t_j)
  > 2k - (2j+1)
  >= 1.
```

This is formalized by

```text
Math.exists_same_label_with_large_clock_gap
Math.exists_same_label_with_large_charge_gap
Math.exists_close_pair_with_large_charge_gap_of_finite_labels
```

in `Math/FiniteChargedReturn.lean`.

## 2. Compactness computes one sufficient finite target

For a requested radius `r > 0`, choose a finite `r/3`-cover of the compact
value set.  Let `m` be the number of cover centres and label every value by one
nearby centre.  Equal labels imply

```text
dist(V_a,V_b) <= 2r/3 < r.
```

The finite theorem therefore applies with the explicit target

```text
Q(r) = 2m.
```

The compact wrapper is

```text
Math.exists_charge_threshold_for_close_pair_of_compact
```

in `Math/CompactFiniteChargedReturn.lean`.

The quantifier pattern is important:

```text
for every r > 0,
  there exists Q(r),
    such that every finite orbit reaching Q(r)
    contains the required returned block.
```

Consequently a producer of the form

```text
for every eta > 0 and Q,
  there exists one finite orbit with charge >= Q
```

is already sufficient.  There is no need to strengthen it to one orbit that
works simultaneously for every `Q`.

## 3. Fixed aggregate absorption

For numbers `0 <= q_k <= 1`,

```text
prod_k (1-q_k) * (1 + sum_k q_k) <= 1.
```

The induction step is

```text
(1-q)(1+S+q) = 1+S-qS-q^2 <= 1+S.
```

Therefore

```text
sum_k q_k >= 1
  => prod_k (1-q_k) <= 1/2
  => 1 - prod_k (1-q_k) >= 1/2.
```

The last term is exactly the weighted-absorption denominator used by the
projective-lasso correction theorem.  The Lean declarations are

```text
Math.prod_one_sub_mul_one_add_sum_range_le_one
Math.half_le_one_sub_prod_one_sub_of_one_le_sum_range
```

in `Math/DivergentChargeRecurrence.lean`.

The useful denominator is the absorption of the **whole returned block**, not
the one-step charge at either endpoint.

## 4. Reverse the forward block

Put `K = b-a`.  Index the cyclic word so that phase `p` carries

```text
root(p)  = x_(b-1-p),
value(p) = V_(b-p).
```

For every nonclosing phase, the chronological Bellman equation is simply the
forward equation read backwards:

```text
value(p) = F(root(p), value(next(p))).
```

Only the last phase fails to close exactly.  There the proposed continuation
is `V_b` instead of `V_a`.  Since the successor map is affine in the
all-Continue continuation with coefficient `c_a`,

```text
e = F(x_a,V_a) - F(x_a,V_b)
  = c_a * (V_a-V_b).
```

Thus every coordinate of the seam has magnitude at most
`dist(V_a,V_b)` in the sup metric.

No chart label has to repeat.  No coefficient point has to recur.  No exact
monodromy fixed point is used.

## 5. Rotation-uniformity is automatic

Every cyclic entry encounters the same unique nonzero seam exactly once.  Its
survival prefix is at most one, so for every entry phase and every player,

```text
weightedResidual <= |e_i|.
```

The returned block has weighted absorption at least `1/2`.  Selecting the
metric radius below `eta/2` yields

```text
weightedResidual
  < eta/2
  <= eta * weightedAbsorption.
```

The cyclic bookkeeping is formalized by

```text
GameTheory.quittingCyclicWeightedResidual_le_of_single_seam
GameTheory.QuittingFiniteSingleSeamProjectiveLasso
toWeighted
quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos
```

in `QuittingSingleSeamProjectiveLasso.lean`.

This removes rotation-uniform recurrence as a separate producer theorem in the
exact-forward-orbit regime.

## 6. Support and rationality survive closing

Suppose every forward edge satisfies

```text
IsQuittingRootSupportApproxNash reward V_n (eta/2) x_n
```

and every forward value satisfies

```text
quittingPunishmentValue reward i - eta/2 <= V_n(i).
```

All nonclosing phases inherit these conditions unchanged.  At the closing
phase the continuation changes from `V_a` to `V_b`.  Endpoint differences are
`1`-Lipschitz in the continuation coordinate, so the existing tail-transfer
lemma adds at most `eta/2` to the support error.  The displayed cyclic values
are forward values, so the punishment floor is inherited directly.

Positive aggregate absorption supplies an absorbing phase.  The existing
weighted-lasso compiler then performs

```text
exact periodic correction
  -> finite support-rational cycle
  -> divergent support-rational path
  -> uniform-equilibrium payoff.
```

## 7. Correct producer interface

For every `eta > 0` and every finite charge target `Q`, it is enough to
produce a bounded finite forward sequence `(x_n,V_n)` satisfying

```text
V_(n+1) = F(x_n,V_n),
support error <= eta/2,
punishment rationality error <= eta/2,
sum_n q_n >= Q.
```

Compact finite charged closing chooses the needed `Q = Q(eta)` and produces
the weighted lasso automatically.

This replaces

```text
physical orbit
  -> strengthen finite-prefix quantifiers
  -> rotation-uniform relative-return theorem
  -> weighted lasso
```

by

```text
one sufficiently charged finite physical orbit
  -> finite-cover hitting-time pigeonhole
  -> one-seam weighted lasso.
```

The remaining hard work is upstream:

1. accept or strategically retarget the analytic packet value;
2. construct and cover the resolved physical charts and lift feasible arcs;
3. decode Farkas outputs strategically; and
4. prove arbitrarily large finite-prefix real absorption on the continuing
   physical branch, or consume the complementary bounded-charge boundary.

The fourth item is now a genuine progress dichotomy, not a topological return
problem.

## 8. Why the recurrence no-go does not apply

`QuittingVanishingChargeRecurrenceNoGo.lean` uses

```text
state(n)  = 1/(n+1),
charge(n) = 1/(n+1)^3.
```

Its total charge is bounded.  It correctly shows that compactness alone cannot
make a seam small relative to the **source one-step charge**.  It does not
address a block selected after a fixed amount of accumulated charge.  The
finite charged-return theorem says precisely that sufficiently large total
prefix charge forces such a block.

## 9. Approximate and signed extension

For an approximate forward orbit, internal Bellman seams need not vanish.  The
same finite closing works whenever their survival-weighted signed sum on the
selected block is small relative to block absorption.  The signed projective
monodromy interface isolates that extension.  The exact-orbit result above is
the clean base case: every internal seam is zero and only the compact closing
seam remains.
