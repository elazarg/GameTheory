# Finite charged closing of projective Bellman orbits

## Result

Rotation-uniform relative return is not an independent producer obligation in
the exact finite-forward regime.

Fix a compact set \(K\) of continuation values.  For every local strategic
accuracy \(\delta>0\) and every charge target \(Q\ge0\), suppose a producer
returns one finite packet

```text
roots   : 0,...,T-1 -> product quitting roots
values  : 0,...,T   -> K
```

with

```text
V_(t+1) = F(root_t,V_t),
support error <= delta,
punishment rationality error <= delta,
sum_(t<T) quittingRootAbsorptionMass(root_t) >= Q.
```

The compact carrier \(K\) is fixed before \(Q\) is chosen.  In the Lean
capstone it is fixed for the whole producer family; in particular it is
independent of both the requested strategic accuracy and the later charge
target.  Merely asking each finite packet to be bounded is insufficient:
every finite sequence is bounded, and its bound could grow with \(Q\).

For every requested lasso error \(\eta>0\), compactness computes one finite
threshold \(Q(\eta)\).  Invoking the producer once at that target yields a
returned block \(a<b\) satisfying

```text
dist(V_a,V_b) < eta / 2,
sum_(t=a)^(b-1) q_t >= 1.
```

Reversing this block gives an exact chronological cycle except for one closing
seam.  The seam is below \(\eta/2\), while the whole block absorbs with
probability at least \(1/2\).  Every cyclic entry encounters the same seam
once, so the block is a rotation-uniform single-seam projective lasso at error
\(\eta\).

The complete Lean interface is

```text
QuittingFiniteForwardPacket
exists_singleSeamProjectiveLasso_of_finiteForwardPackets
quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets
```

in
`GameTheory/Concepts/Stochastic/UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`.

## 1. Finite charged-return pigeonhole theorem

Let a finite path be labelled by one of \(m\) cells and let

```text
S_t = sum_(n<t) q_n,
0 <= q_n <= 1.
```

Suppose \(S_T\ge 2m\).  For \(j=0,\ldots,m\), let \(t_j\) be the first time at
which \(S_{t_j}\ge 2j\).  Since each clock increment is at most one,

```text
2j <= S_(t_j) < 2j + 1.
```

There are \(m+1\) sampled times and only \(m\) labels.  Two sampled times of
ranks \(j<k\) therefore have the same label, and

```text
S_(t_k) - S_(t_j) > 2k - (2j+1) >= 1.
```

This is formalized by

```text
Math.exists_same_label_with_large_clock_gap
Math.exists_same_label_with_large_charge_gap
Math.exists_close_pair_with_large_charge_gap_of_finite_labels
```

in `Math/FiniteChargedReturn.lean`.

## 2. Compactness selects the target before the packet

For a radius \(r>0\), take a finite \(r/3\)-cover of the fixed compact carrier.
If the cover has \(m\) centres, the preceding theorem applies at charge target

```text
Q(r) = 2m.
```

Equal cover labels imply endpoint distance at most \(2r/3<r\).  The compact
wrapper is

```text
Math.exists_charge_threshold_for_close_pair_of_compact
Math.exists_close_pair_of_arbitrarily_large_finite_charge
```

in `Math/CompactFiniteChargedReturn.lean`.

The useful quantifier order is

```text
fix one compact carrier K;
for every r > 0:
  choose Q(r);
  invoke the rich finite-packet producer once at Q(r);
  select a close charged pair inside that same packet.
```

The game-facing capstone deliberately applies the threshold theorem only after
obtaining the rich packet.  It therefore retains the roots, Bellman proof,
support witnesses, rationality floor, and source provenance attached to the
selected pair; none of this payload is projected away.

## 3. Whole-block absorption has a fixed denominator

For \(0\le q_k\le1\),

```text
prod_k (1-q_k) * (1 + sum_k q_k) <= 1.
```

The induction step is

```text
(1-q)(1+S+q) = 1+S-qS-q^2 <= 1+S.
```

Hence

```text
sum_k q_k >= 1
  => prod_k (1-q_k) <= 1/2
  => 1 - prod_k (1-q_k) >= 1/2.
```

The final expression is exactly the weighted absorption of the returned
cycle.  The relevant declarations are

```text
Math.prod_one_sub_mul_one_add_sum_range_le_one
Math.half_le_one_sub_prod_one_sub_of_one_le_sum_range
```

in `Math/DivergentChargeRecurrence.lean`.

The denominator is the absorption of the entire block, not the source
one-stage charge.

## 4. Reverse the finite forward block

For a block of length \(n+1=b-a\), phase \(p:\mathrm{Fin}(n+1)\) carries

```text
root(p)  = root_(a + p.rev),
value(p) = V_(a + p.rev + 1).
```

For every phase other than `Fin.last n`, the chronological Bellman equation is
the forward equation read backwards.  At the closing phase,

```text
e = F(root_a,V_a) - F(root_a,V_b)
  = continueMass(root_a) * (V_a - V_b).
```

Thus every coordinate of the seam is bounded by the endpoint distance in the
sup metric.

The finite, interval-local adapter is

```text
quittingReversedForwardCycle
quittingReversedForwardValue
quittingCyclicWeightedAbsorption_reversedForwardCycle
quittingCyclicPolicyResidual_reversedForward_eq_zero_of_ne_last
abs_quittingCyclicPolicyResidual_reversedForward_last_le
quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock
```

in
`GameTheory/Concepts/Stochastic/UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`.

Its Bellman, support, and rationality hypotheses are restricted to the
selected interval.  It does not require an infinite extension satisfying
those properties outside the finite packet.

## 5. Rotation-uniformity is automatic

Every cyclic entry encounters the unique closing seam exactly once.  The
survival prefix multiplying it is at most one, so

```text
weightedResidual(entry,player) <= |closingSeam(player)|.
```

Since the returned block has weighted absorption at least \(1/2\), endpoint
distance below \(\eta/2\) gives

```text
weightedResidual
  <= eta / 2
  <= eta * weightedAbsorption
```

for every cyclic entry and every player.

This is packaged by

```text
quittingCyclicWeightedResidual_le_of_single_seam
QuittingFiniteSingleSeamProjectiveLasso
QuittingFiniteSingleSeamProjectiveLasso.toWeighted
quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos
```

in `UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`.

## 6. Support and rationality survive closing

All nonclosing phases inherit the packet's support condition exactly.  At the
closing phase the continuation changes from \(V_a\) to \(V_b\).
`isQuittingRootSupportApproxNash_of_tail_close` adds at most the endpoint
distance to the support error.

The displayed cyclic values are packet values, so the punishment floor is
inherited directly.  Positive block charge supplies a phase of positive
one-stage absorption.  Exact periodic correction then performs

```text
single-seam lasso
  -> rotation-uniform weighted lasso
  -> exact finite support-rational cycle
  -> divergent support-rational path
  -> uniform-equilibrium payoff.
```

## 7. The motivating circulation producer now uses the finite route

`MultiOwnerFaceCirculationFiniteClosing.lean` retains the interval data hidden
by the older public tuple from `exists_multiCirculation_orbit`, converts the
real hazard rows into PMF roots, and places every target-dependent orbit in the
common compact carrier

```text
[-B,B]^I,
B = M + sum_i |C.vertex 0 i|.
```

It exports

```text
exists_multiCirculation_finiteOrbitData
exists_finiteForwardPacket_of_multiCirculation
quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation_finiteClosing
```

The final theorem consumes the original quantifier pattern

```text
forall epsilon > 0, forall Q,
  exists one finite circulation orbit reaching Q
```

and does not call `exists_multiCirculation_orbit_uniform_prefix`.
This is the repository regression showing that the stronger one-orbit-for-all-
targets theorem is unnecessary for projective closing.

## 8. Why the old recurrence no-go does not apply

`UniformEquilibrium/Quitting/Debt/Ledger/VanishingChargeRecurrenceNoGo.lean` uses

```text
state(n)  = 1/(n+1),
charge(n) = 1/(n+1)^3.
```

Its total charge is bounded.  It correctly proves that compactness alone
cannot make endpoint distance small relative to the source one-stage charge.
It does not address a returned block selected after a fixed amount of
accumulated charge.  Finite charged return is precisely the missing
large-total-charge hypothesis.

## 9. Approximate and signed extension

The exact finite-forward theorem has zero internal seams, so
only the closing seam remains.

For an approximate forward orbit, internal signed seams may cancel.  The
appropriate extension is the cancellation-aware signed projective monodromy
interface in `QuittingSignedProjectiveLasso`.  The current finite-packet
compiler deliberately assumes exact forward Bellman transport and therefore
uses the smaller single-seam certificate.  A genuinely approximate packet
producer should target the signed interface directly rather than replace
signed cancellation by accumulated absolute local error.

## 10. Remaining producer obligations

Finite charged closing removes only the independent recurrence/return
obligation.  For arbitrary quitting games, the remaining upstream work is:

1. accept the projective packet target with executable continuation data, or
   reject and strategically retarget it;
2. construct and cover resolved physical charts and lift feasible tangents to
   real or Puiseux successors;
3. decode projective Farkas outputs strategically; and
4. produce finite forward packets of arbitrarily large real absorption inside
   a compact carrier fixed independently of the charge target, or consume the
   complementary bounded-charge boundary.

The fourth item is now a progress dichotomy rather than a metric recurrence
problem.
