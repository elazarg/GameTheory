# Exact search at the final minimum-semantic regimes

## Scope

This experiment consumes the exact passports in Proof Mining Session XVIII,
including the sharp rate-one support boundary.  It separates two questions:

1. Are the finite reward inequalities and marked-atom alternatives mutually
   consistent?
2. Can the witness be a *minimum positive-debt* semantic pair in a game with no
   uniform equilibrium?

Only the first question is a finite reward-table problem.  The second includes
the global minimum-carrier provenance condition.  In particular, any exact
equilibrium creates a zero-debt carrier point and immediately disqualifies an
otherwise valid positive-debt witness from being minimum.

The executable artifact is `semantic_final_regime_search.py`.  It uses
`fractions.Fraction` throughout.  `SemanticFinalRegimeArithmetic.lean` replays
the decisive breakpoint, collision, punishment-gap, and marked-debt arithmetic.

## Atomic results

Players are `0,1,2,3`, with owner `0` and entrant `1`.  All examples have an
explicit executable semantic pair produced by player `0` quitting immediately:

```text
prescribed = (-2,0,0,0)
envelope   = ( 0,0,0,0)
debt       = ( 2,0,0,0).
```

Opponent-only coalitions pay player `0` zero and coalitions obtained by adding
player `0` pay it `-1`.  Therefore every stationary punishment cap is at least
zero through its Continue branch, while any pure nonempty opponent set attains
cap `max(-1,0)=0`.  Stationary min-max equality gives the exact certificate

```text
s_0 = -2 < chi_0 = 0,
pi_0 = chi_0-s_0 = 2 = debt_0.
```

Two support boundaries were checked.

### Interior boundary

The entrant rewards are

```text
r_1({1})=1,  r_1({0})=0,  r_1({0,1})=-1.
```

Its affine gain is `1-2p`; hence the first feasible rate is exactly `p=1/2`.
The reciprocal owner collision is

```text
r_0({0,1})-r_0({1})=-1 != 0.
```

Thus every finite condition of the interior sharp boundary, the exact endpoint
root, unique positive debt, and punishment sandwich is jointly satisfiable.

### Sure-Quit boundary

Changing only `r_1({0,1})` to zero makes the entrant gain `1-p`.  Its first
feasible rate is exactly `p=1`.  At that point the sharpened conditions hold
simultaneously:

```text
owner collision          r_0({0,1})-r_0({1}) = -1 < 0,
reverse entrant collision r_1({0,1})-r_1({0}) =  0,
one-outsider cap          max(-1,0) = 0,
punishment gap            2 <= 0-(-2).
```

The new rate-one theorem is therefore a genuine restriction, but not a static
inconsistency.

### Solved-cycle screen

The integral interior and rate-one tables both have the exact admissible
period-one root

```text
q=(0,1/2,1/2,1/2),  value=(0,0,0,0).
```

It is an already solved cycle, so their positive-debt semantic pairs are not
minimum.  This is the useful negative control: deleting minimum provenance
from the atomic passport creates many false candidates.

A deterministic denominator-101 perturbation preserves every strict atomic
inequality and the exact `p=1/2` breakpoint.  It has no admissible pure root and
no admissible exact stationary root on the exhaustive reduced-fraction grid of
denominator at most five.  This is not a no-equilibrium certificate; it only
shows that the sharp static passport need not expose an obvious small-rational
cycle.  Any future search must retain minimum provenance or a sound global
exclusion certificate rather than equating grid failure with a counterexample.

## Plateau results

There are tiny integral executable semantic pairs for every marked atom in the
production trichotomy:

- Never: player `0` quits for `-1` while Never pays zero.
- Collision: player `1` quits and player `0` can join, improving `0` to `1`.
- Waiting/opponent absorption: `{0,1}` quits for payoff `0` to player `0`, who
  can Continue and let `{1}` absorb for payoff `1`.

In all cases the displayed debtor has exact debt one, the all-Continue root is
locally complementary at the prescribed vector, and the profitable atom has
mass one.  Every table also has many admissible pure stationary roots.  Hence
the marked atom trichotomy alone is consistent and cannot close the plateau
branch; the missing datum is exactly the report's common chronology/marked
coupling at a *minimum* positive-debt point.

## Search restriction extracted

The finite scan supports the following tighter regime for subsequent work:

1. Enumerate the solo rate only from its exact affine reward breakpoints.
2. At an interior first boundary retain `owner collision != 0` or cotightness.
3. At rate one retain the stronger oriented packet: negative owner collision,
   reverse entrant collision zero, and the one-outsider punishment-gap bound,
   unless a third outsider is cotight.
4. Reject a candidate immediately when an admissible exact cycle gives a
   zero-debt semantic point.
5. Do not search the plateau law without the marked chronology needed to turn
   its persistent atom into stagewise support or debt utilization.

The outcome is a useful negative result: neither final branch is statically
inconsistent.  The decisive obstruction remains global path lifting at the
minimum semantic fibre—support/punishment completion on the atomic side and
marked co-realization on the plateau side.
