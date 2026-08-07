# Divergent-charge compact closing

## Result

The rotation-uniform relative-return problem is not independent once the
physical orbit carries **nonsummable real absorption**.

Let

```text
V_(n+1) = F(x_n, V_n)
q_n     = quittingRootAbsorptionMass(x_n)
c_n     = 1 - q_n.
```

Assume that the values `V_n` remain in a compact finite-dimensional set and

```text
sum_n q_n = infinity.
```

Then, for every `eta > 0`, there are `a < b` such that

```text
||V_a - V_b||_infinity < eta / 2,
sum_{n=a}^{b-1} q_n >= 1.
```

The reversed block `x_(b-1), ..., x_a`, closed periodically, is a
rotation-uniform weighted projective lasso with error `eta`, provided the
forward orbit already carries support error and punishment-rationality error
at most `eta / 2`.

Thus a producer no longer needs a separate recurrent-monodromy theorem.  It is
enough to produce a bounded exact forward Bellman orbit with nonsummable real
absorption.

## 1. Compact recurrence with a charge budget

Let `S_N = sum_{n<N} q_n`.  Since `q_n >= 0` and the series is not summable,
`S_N -> infinity`.

Choose a convergent subsequence

```text
V_(n_k) -> V_*.
```

Fix a sufficiently late `k`.  Because `S_(n_l) -> infinity` along every
strictly increasing subsequence, choose `l > k` so late that

```text
S_(n_l) - S_(n_k) >= 1.
```

Both values are close to `V_*`, hence they are close to each other.  This is
formalized game-independently by

```text
Math.exists_close_pair_with_large_prefix_gap_of_compact
Math.exists_close_pair_with_large_charge_gap_of_compact
```

in `Math/DivergentChargeRecurrence.lean`.

This is stronger than ordinary recurrence: the return is selected only after
a prescribed amount of charge has elapsed.

## 2. Fixed aggregate absorption

For numbers `0 <= q_k <= 1`,

```text
prod_k (1 - q_k) * (1 + sum_k q_k) <= 1.
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

The last quantity is exactly the weighted-absorption denominator of the
projective-lasso correction theorem.  The corresponding Lean declarations are

```text
Math.prod_one_sub_mul_one_add_sum_range_le_one
Math.half_le_one_sub_prod_one_sub_of_one_le_sum_range
```

The crucial denominator is thus the absorption of the **whole returned
block**, not the one-step charge at the first visit.

## 3. Reverse the forward block

Put `K = b-a`.  Index the cyclic word so that phase `p` carries

```text
root(p)  = x_(b-1-p),
value(p) = V_(b-p).
```

For every nonclosing phase, the chronological Bellman equation is just the
forward equation read backwards:

```text
value(p) = F(root(p), value(next(p))).
```

Only the last phase fails to close exactly.  There the proposed continuation
is `V_b` instead of `V_a`.  Since the quitting successor map is affine in the
all-Continue continuation with coefficient `c_a`, the closing residual is

```text
e = F(x_a, V_a) - F(x_a, V_b)
  = c_a * (V_a - V_b).
```

Consequently

```text
|e_i| <= ||V_a - V_b||_infinity < eta/2
```

for every player `i`.

No chart label needs to repeat.  No exact projective coefficient point needs
to recur.  No monodromy fixed point is used.

## 4. Rotation-uniformity is automatic

Every cyclic rotation encounters the same unique nonzero seam exactly once.
Its survival prefix is at most one.  Hence for every entry phase and every
player,

```text
weightedResidual <= |e_i| < eta/2.
```

The block charge selected above gives

```text
weightedAbsorption >= 1/2.
```

Therefore

```text
weightedResidual
  < eta/2
  <= eta * weightedAbsorption.
```

This is precisely `IsQuittingRotationUniformWeightedResidual`.  The
rotation-uniform condition is load-bearing at the compiler, but it does not
require a separate producer theorem in the exact-forward-orbit regime.

## 5. Support and rationality survive closing

Suppose every forward edge satisfies

```text
IsQuittingRootSupportApproxNash reward V_n (eta/2) x_n
```

and every forward value satisfies

```text
quittingPunishmentValue reward i - eta/2 <= V_n(i).
```

All nonclosing phases inherit these statements unchanged.  At the closing
phase, the continuation moves from `V_a` to `V_b`.  Endpoint differences are
`1`-Lipschitz in the continuation coordinate, so the existing tail-transfer
lemma adds at most `eta/2` to support error.  Thus every phase has support
error at most `eta`.  The displayed cyclic values are forward values, so the
punishment floor is inherited with room to spare.

Positive aggregate absorption implies that at least one phase has positive
one-stage absorption.  The resulting object is a
`QuittingFiniteWeightedProjectiveLasso reward K eta`, and the existing
compiler gives

```text
exact periodic correction
  -> finite support-rational cycle
  -> divergent support-rational path
  -> uniform-equilibrium payoff.
```

## 6. Correct replacement for the current return obligation

The useful producer interface is the following.

For every `eta > 0`, produce a bounded forward sequence `(x_n,V_n)` with

```text
V_(n+1) = F(x_n,V_n),
support error <= eta/2,
punishment rationality error <= eta/2,
sum_n quittingRootAbsorptionMass(x_n) = infinity.
```

Then compact divergent-charge closing produces the weighted lasso at error
`eta` automatically.

This replaces

```text
physical orbit
  -> separate rotation-uniform relative-return theorem
  -> weighted lasso
```

by

```text
bounded physical orbit + nonsummable real absorption
  -> compact divergent-charge closing
  -> weighted lasso.
```

The remaining hard work is upstream:

1. accept or strategically retarget the analytic packet value;
2. construct and cover the resolved physical charts and lift feasible arcs;
3. decode Farkas outputs strategically; and
4. on the continuing physical branch, prove nonsummable real absorption or
   consume the complementary finite-charge boundary.

The fourth item is a genuine progress dichotomy rather than a metric return
problem.

## 7. Why the existing recurrence no-go does not apply

`QuittingVanishingChargeRecurrenceNoGo.lean` uses

```text
state(n)  = 1/(n+1),
charge(n) = 1/(n+1)^3.
```

Its charge is summable.  It correctly shows that compactness alone cannot make
an endpoint seam small relative to the **source one-step charge**.  It does not
address a returned block whose accumulated charge is bounded below.  In the
nonsummable regime, the compact-return pair can be selected after any fixed
charge budget, which is exactly the missing ingredient.

## 8. Approximate and signed extension

For an approximate forward orbit, internal Bellman seams need not vanish.  The
same closing argument works whenever their survival-weighted signed sum on the
selected block is `o` of the block absorption.  The cancellation-aware signed
monodromy interface isolates exactly that weaker hypothesis.  The exact-orbit
theorem above is the clean base case: all internal signed seams are zero and
only the compact closing seam remains.
