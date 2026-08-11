# Exact search after the auxiliary-Nash plateau reduction

## Verdict

The exposed finite constraints of the now-sole all-Continue plateau regime
remain mutually consistent.  They do not, by themselves, certify membership
in the positive minimum-debt fibre.

`minimum_plateau_q_budget_search.py` gives an exact four-player negative
control.  The profile in which player `0` quits immediately and every outsider
waits has semantic pair

```text
u = (-1,2,2,2)
b = ( 0,2,2,2)
d = ( 1,0,0,0),   D=1.
```

It simultaneously has:

- the sharp Q.md margin `b_i-r_i({i})=D` for every player;
- a unique singleton-tight coordinate, player `0`, carrying all debt;
- a negative tight debtor `u_0=r_0({0})=-1`;
- a literal profitable Never deviation of mass one and gain one;
- saturation of the new common-outcome aggregate certificate:
  the realized atom `{0}` has total surplus
  `sum_i (r_i({0})-r_i({i}))=3=(4-1)D`.

Thus neither the minimum-budget scalar inequalities, reward-moment/tightness
atoms, nor literal time disintegration make the residual negative/Never
passport statically inconsistent.

## Auxiliary-cube and elementary equilibrium screens

All arithmetic uses `fractions.Fraction`.  The script exhausts:

- every shift coordinate in `{0,1/4,1/2,3/4,1}`;
- every product-root coordinate of reduced denominator at most three.

It finds 1,440 exact root/shift incidences.  Every one obeys

```text
D * collision_mass + sum_i singleton_mass_i * (D-h_i) <= 0,
```

and every exact root strictly inside the cube is all-Continue.  This is a
finite grid audit, not a quantifier-elimination proof over all real roots.

The table has no admissible pure stationary root.  Exhaustive stationary
screens on reduced-fraction grids of denominator at most three, four, and five
find respectively 4, 6, and 10 exact roots, none admissible.  Consequently the
passport does not expose an obvious small stationary solution.

## Why it is nevertheless not a counterexample

The same table has an explicit stationary zero-debt escape.  For
`epsilon > 0`, use quit rates

```text
q(epsilon) = (1-epsilon, 21*epsilon, 11*epsilon, 0).
```

As `epsilon -> 0+`, the terminal law tends to `{0}`, hence its prescribed
payoff tends to `u`.  If player `0` refuses to quit, the asymptotic opponent
owner weights are `21/32` and `11/32`, and

```text
(21/32)*r_0({1}) + (11/32)*r_0({2})
  = (21/32)*(-18/7) + (11/32)*2
  = -1
  = r_0({0}).
```

Every outsider's prescribed and refusal values tend to `2`, while its joined
Quit endpoint is no larger.  Therefore every debt coordinate tends to zero.
Exact rational evaluations give total debt

```text
epsilon=1/256    0.393875597720
epsilon=1/512    0.195069771442
epsilon=1/1024   0.097059868684
epsilon=1/2048   0.048410162893
```

so the displayed positive-debt pair is not minimum in its executable carrier.
This is the load-bearing failure, not a missed local reward inequality.

## New finite certificate extracted

The production module
`TerminalSemanticMinimumAggregateSurplus.lean` proves, for every player subset
`J` at a positive minimum pair,

```text
(|J|-1)D <= sum_{i in J} (u_i-r_i({i})).
```

Reward-moment provenance then selects one **common** terminal outcome `T` with

```text
(|J|-1)D <= sum_{i in J} (r_i(T)-r_i({i})).
```

This is stronger than retaining player-dependent profitable atoms.  It is the
most useful finite search restriction obtained here, but the negative control
shows that it still needs minimum-owned chronology to close the conjecture.

## Load-bearing next seam

Further static enumeration should not be the priority.  A successful consumer
must use minimum provenance to prevent the kind of vanishing opponent-hazard
escape above, or turn that escape itself into approximate equilibria.  In the
remaining unique negative/Never case, the decisive datum is therefore a
common realizing/minimizing chronology, not another independent terminal-law
or reward-table inequality.
