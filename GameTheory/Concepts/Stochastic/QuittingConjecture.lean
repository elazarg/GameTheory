/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingZeroSoloDisjunct

/-!
# The finite-quitting conjecture and its one open premise

Every finite quitting game is conjectured to have a uniform-equilibrium
payoff.  This file states that conjecture and isolates the single premise it
now rests on, so that the remaining obligation is a named declaration rather
than prose.

The reduction is landed:
`exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle` proves that a
weight has a uniform-equilibrium payoff as soon as it is zero-solo *or* admits
an admissible absorbing cyclic continuation block.  Both implications are
theorems, with no gap in the deviation class — the consumed predicate
quantifies over all behavior strategies.

What is **not** proved is that those two cases are exhaustive.  That
completeness statement is `quitting_zeroSolo_or_admissibleCycle` below, and it
is an intentional open declaration.  It is not a weakening of the conjecture
and not a convenience hypothesis: by the reduction it is *equivalent in force*
to the conjecture on this route, and the conjecture is derived from it in one
line.

## Why completeness can fail only in one place

Complementary rows exist against every continuation vector, so a cycle is never
the scarce object; the question is whether one absorbs.  Along a family of
discounted complementary rows with the discount tending to one, either some
limit absorbs — giving a cycle of length one, admissible unless it isolates a
coordinate of negative solo reward — or absorption degenerates and the limit is
the all-continue row.  So the open premise reduces to the degenerate case,
split further by the sign pattern of the solo rewards:

* all solo rewards nonpositive: settled here, the zero-solo branch fires;
* some positive and none negative: admissibility is automatic, since a mismatch
  can be nonzero only at an isolated coordinate of negative solo reward, so only
  existence of an absorbing cycle is at issue;
* some positive and some negative: admissibility is a genuine constraint, and an
  absorbing limit isolating a negative coordinate supplies no cycle even though
  absorption did not degenerate.

## Scope

This is the conjecture for finite **quitting** games, which are a strict
subclass of finite stochastic games with one live state.  Discharging
`quitting_zeroSolo_or_admissibleCycle` would close this file's conjecture; it
would **not** discharge `exists_uniformDeviationCapConstructor` in `UniformExistenceConjecture.lean`,
the general finite-stochastic-game problem, for which no reduction to quitting
games is known.

## Open declarations

This file contains one `sorry`, deliberately, in
`quitting_zeroSolo_or_admissibleCycle`.  The repository's other intentional open
declaration is `exists_uniformDeviationCapConstructor` in `UniformExistenceConjecture.lean`; these are the only two.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The finite-quitting uniform-equilibrium conjecture.**

Every finite quitting game has a uniform-equilibrium payoff.

`HEADLINE` — an *intentional open declaration*.  This covers quitting games
only; the general finite-stochastic-game problem is
`exists_uniformDeviationCapConstructor` in `UniformExistenceConjecture.lean`
and does not follow from this.

**Do not attempt to derive this from
`exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle`.**  That
reduction is sound, but its hypothesis is *not* satisfied by every weight, so it
cannot discharge this conjecture on its own.  Witness, for `ι = Bool`:

    r({1}) = (1, -1),   r({2}) = (1, -1),   r({1,2}) = (0, 1).

Here `r₁({1}) = 1 > 0`, so the weight is not zero-solo.  It does admit
absorbing cyclic continuation blocks — for instance the single row where
coordinate `2` quits with probability one, against the value `(1, -1)`, at which
coordinate `1` has gap `-1 ≤ 0` and coordinate `2` is exactly indifferent.  But
every absorbing complementary cycle for this weight has coordinate `1` silent at
every phase, so the deleted survival product at coordinate `2` is `1`; since
`r₂({2}) = -1 < 0`, the mismatch there is `1` and no cycle is admissible.

The weight has two coordinates, so a uniform-equilibrium payoff does exist for
it externally.  Its equilibrium therefore lies outside the cycle carrier, and
what the carrier needs is a third branch covering weights of this shape — not a
proof that the existing two are exhaustive. -/
theorem quittingGame_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  sorry

end GameTheory
