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

/-- **The open premise of the finite-quitting route.**

Every weight is zero-solo, or admits an admissible absorbing cyclic
continuation block.

`HEADLINE` — this is the sole remaining obligation on the finite-quitting
route, and it is an *intentional open declaration*.  Both implications from
this disjunction to a uniform-equilibrium payoff are proved
(`exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle`); only
exhaustiveness is missing.

Known constraints on any proof.  The first disjunct is not removable: there are
zero-solo weights admitting no admissible absorbing cycle of any length, so the
statement genuinely needs both cases.  The absorption clause inside the second
disjunct is not removable either: without it the all-continue list reproduces
every value vector and the disjunct would be vacuously true for every weight.
No bound on the block's period is asserted or needed.  Two natural routes are
refuted: the construction following the blocking digraph does not always yield a
solvable system, and the complementary-successor correspondence is not
convex-valued, so a direct Kakutani argument does not apply. -/
theorem quitting_zeroSolo_or_admissibleCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsQuittingZeroSolo reward ∨ HasAdmissibleAbsorbingQuittingCycle reward := by
  sorry

/-- **The finite-quitting uniform-equilibrium conjecture.**

Every finite quitting game has a uniform-equilibrium payoff.

`HEADLINE` — derived in one line from the open premise above together with the
landed reduction, so the entire finite-quitting route now has exactly one
unproved input.  This covers quitting games only; the general
finite-stochastic-game problem is `exists_uniformDeviationCapConstructor` in
`UniformExistenceConjecture.lean` and does not follow from this. -/
theorem quittingGame_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle reward
    (quitting_zeroSolo_or_admissibleCycle reward)

end GameTheory
