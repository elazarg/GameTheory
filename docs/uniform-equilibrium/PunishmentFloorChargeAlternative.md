# Punishment-floor charge alternative

This note separates two statements that look similar but have different
mathematical status.

1. The strategically useful conclusion

   ```text
   uniform-equilibrium payoff
   or
   one finite constant bounds every cumulative-charge prefix of every
   punishment-floor exact forward orbit
   ```

   is valid and is formalized in
   `UniformEquilibrium/Quitting/Projective/PunishmentFloorForwardBudget.lean`.

2. The raw path-selection principle

   ```text
   arbitrarily large finite charge across legal orbits
   implies one orbit of unbounded charge
   ```

   is false for compact serial charged relations, even in a finite-dimensional
   semialgebraic example with continuous nonnegative charge.  It needs an
   additional no-delay or charge-regeneration hypothesis.

The finite charged-closing compiler makes the raw selection principle
unnecessary for the first conclusion.  It accepts a target-dependent finite
packet: for each requested charge threshold, the packet and its orbit may be
different.

## Formalized strategic theorem

`QuittingPunishmentFloorForwardOrbit reward carrier` packages arbitrary choices
of exact roots and values:

```text
value 0 = coordinatewise punishment value,
value (t+1) = quittingRootSuccessorPayoff reward (value t) (roots t),
roots t is support-locally exact Nash against value t,
punishmentValue_i <= value t i,
value t belongs to one fixed compact carrier.
```

It does not use the repository's selected predecessor function.

Its prefix through `N` converts to a `QuittingFiniteForwardPacket` at every
nonnegative support tolerance.  Consequently, failure of a common bound gives,
for every nonnegative charge target, one packet whose accumulated charge
reaches that target.  The landed finite charged-closing theorem then produces a
single-seam projective lasso and a uniform-equilibrium payoff.

The proof is therefore the direct classical alternative:

```text
by_cases there is a common all-orbits prefix bound
  right: return the bound
  left:  negate the bound, choose one sufficiently charged prefix at each
         compiler-requested threshold, and invoke finite charged closing
```

No infinite high-charge orbit, diagonal extraction, or compactness of the full
orbit space is used.

## Compact serial delayed-charge regression

Let

```text
X = {anchor} disjoint-union ([0,1] x [0,1]).
```

This is compact.  The charged edges are the following compact families.

```text
anchor -> anchor                         charge 0
anchor -> (t,1)                          charge 0
(t,y) -> (t,y-t^2),  t^2 <= y            charge t
(t,y) -> (t,y),      y <= t^2            charge 0
```

Treat an edge as the triple `(source,target,charge)`.  Each displayed family is
a compact semialgebraic set, so their finite union is compact.  Hence the legal
relation is closed and the charge is continuous on the edge space.  The
relation is serial: `anchor` and every terminal strip point have a zero-charge
self-loop, while a point above the strip has a descent edge.

Every infinite orbit has finite total charge.  An orbit either stays at
`anchor`, or launches once at a fixed parameter `t`.

* At `t = 0`, every subsequent charge is zero.
* At `t > 0`, every positive-charge edge lowers `y` by `t^2`.  There are at
  most `ceil(1/t^2)` such edges, each of charge `t`, so the total is finite.

The totals are nevertheless not uniformly bounded.  For an integer `n >= 1`,
launch at `t = 1/n` and take exactly `n^2` descent edges.  The accumulated
charge is

```text
n^2 * (1/n) = n.
```

Charge can also be delayed arbitrarily.  Let the `n`-th orbit wait at `anchor`
for `n` stages, launch at `1/n`, and then descend.  These orbits converge on
every fixed prefix to the all-`anchor` zero-charge orbit, while their total
charges tend to infinity.

Thus compactness, closedness, seriality, finite dimension, semialgebraicity,
and continuity of the charge do not exchange the quantifiers.

## Why one-step unbounded-future viability is insufficient

Let `U(z)` mean that finite extensions from `z` can achieve arbitrarily large
additional charge.  In the regression above,

```text
U = {anchor}.
```

It is closed, indeed clopen.  The zero-charge edge

```text
anchor -> anchor
```

preserves `U`.  Therefore the implication

```text
U(z) -> exists z', legalEdge z z' and U(z')
```

holds, but dependent choice may select the zero-charge self-loop forever.  The
resulting orbit has total charge zero.

The same issue invalidates an extended-real Bellman selection argument stated
only as preservation of infinity.  The future-charge value at `anchor` is
infinite, and the zero-charge self-loop satisfies

```text
infinity = 0 + infinity.
```

Attainment of the extended Bellman value does not force charge progress.

## A sufficient no-delay hypothesis: closed unit-charge blocks

Assume one-stage charges lie in `[0,1]`.  Define the block relation

```text
B(z,z') iff some finite legal path from z to z'
           has total charge in [1,2].
```

If the state space is compact Hausdorff and `B` is closed, then arbitrarily
large finite charge from an anchor does imply an unbounded-charge orbit.

Indeed, a path of charge at least `2m` can be cut greedily at the first crossing
of each next unit level.  The bound `q <= 1` makes every resulting block charge
belong to `[1,2]`, producing a `B`-chain of length `m`.  Compact finite-prefix
selection gives one infinite `B`-chain.  Choosing and concatenating one finite
legal witness for each block yields an ordinary legal orbit with at least one
unit of charge per block.

The regression fails exactly this hypothesis.  For `t_n = 1/n`, the first `n`
descent edges form a unit-charge block

```text
(t_n,1) -> (t_n,1-1/n).
```

Both endpoints converge to `(0,1)`, but at `t=0` every legal edge has charge
zero, so no unit-charge block begins and ends at `(0,1)`.  Hence `B` is not
closed.

A concrete sufficient condition for closedness is a uniform calendar bound on
unit-charge witnesses: if every pair in `B` has a witnessing path of length at
most one common `L`, then `B` is a finite union of compact finite-horizon
projections and is closed.  Proving such a bound, or another condition implying
closed block regeneration, is the genuine game-specific no-delay problem.

## Potential form of the bounded branch

`Math/ChargedPathBudget.lean` already proves the exact abstract duality

```text
finite path budget
iff
exists a bounded potential Phi with
  Phi(target edge) + charge(edge) <= Phi(source edge).
```

It also identifies the least nonnegative supersolution with the budget-to-go
and proves that its oscillation is the minimum possible bound.  Applied to the
anchor-reachable restriction of the punishment-floor exact relation, the
second branch of the strategic theorem can therefore be strengthened from an
opaque constant to a bounded charge potential.  Continuity of that potential
must not be asserted: the existing compact interpolation regression shows that
an exact bounded potential need not be continuous.

## Formalization boundary

Formalized in `PunishmentFloorForwardBudget.lean`:

* arbitrary exact punishment-floor forward orbits;
* cumulative prefix charge;
* conversion of every exact prefix to the landed finite-forward packet;
* uniform payoff versus one all-orbits prefix bound;
* the no-uniform-payoff contrapositive.

Already formalized elsewhere:

* compact finite charged return and the target-dependent packet compiler;
* support-witness and projective-lasso compilation;
* finite-budget/bounded-potential duality;
* compact inverse limits for closed finite-prefix relations.

This note records, but the current Lean module does not yet formalize, the
compact semialgebraic delayed-charge regression and the closed unit-charge
block hypothesis.  Neither is used in the strategic theorem.
