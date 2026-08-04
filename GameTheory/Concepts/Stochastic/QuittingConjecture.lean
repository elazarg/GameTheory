/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingZeroSoloDisjunct
import GameTheory.Concepts.Stochastic.UniformExistenceConjecture

/-!
# The finite-quitting conjecture

Every finite quitting game is conjectured to have a uniform-equilibrium
payoff.  This file states that conjecture, and nothing else, so that the
`sorry` warning a build emits names the conjecture itself.

## What reaches the target

`exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle` proves that a
weight has a uniform-equilibrium payoff as soon as it is zero-solo *or* admits
an admissible absorbing cyclic continuation block.  Both implications are
theorems, with no gap in the deviation class — the consumed predicate
quantifies over all behavior strategies.

Those two cases are **not** exhaustive.
`not_forall_isQuittingZeroSolo_or_hasAdmissibleAbsorbingQuittingCycle` in
`QuittingDisjunctionCounterexample.lean` refutes the disjunction outright, on
the two-coordinate weight quoted in the conjecture's own docstring below.  So
the conjecture carries its own `sorry` rather than being reduced to a
completeness premise; an earlier architecture that stated such a premise was
removed once it was refuted.

What is proved about exhaustiveness is weaker and precisely scoped:
`quittingCycle_zeroSolo_or_admissible_or_isolatedNegative` gives a
**three**-branch disjunction — zero-solo, admissible, or isolated-negative —
exhaustive over weights that admit *some* absorbing complementary cycle.  Its
branches are not mutually exclusive, the third has no sufficiency theorem, and
weights admitting no absorbing cycle at all lie outside its scope.

## External status of the target

Two-player quitting games are settled, and three-player quitting games follow
from Solan (1999) on three-player absorbing games; the open range is `n ≥ 4`.
There is a published characterization — Ashkenazi-Golan--Krasikov--Rainer--Solan,
Math. Program. 203 (2024), Theorem 3.4, after Simon (2007) and
Solan--Vieille (2001) — of when a quitting game has `ε`-equilibria for every
`ε > 0`, as a disjunction of three conditions on *strategies* rather than on
the weight.  It is not consumed here, and it is not the same trichotomy as the
one above.

Note also that Simon, arXiv:2310.04217 (2023), states a belief that a
counterexample exists for quitting games, and claims one for four-player
finite stochastic games.  Neither claim has been assessed in this repository.
Read the `sorry` as *not proved here*, not as *believed true*.

## Scope

This is the conjecture for finite **quitting** games, a strict subclass of
finite stochastic games with one live state.  Discharging it would **not**
discharge `exists_uniformDeviationCapConstructor` in
`UniformExistenceConjecture.lean`, the general finite-stochastic-game problem,
for which no reduction to quitting games is known.  The implication that does
hold, from the general problem to this one, is
`quittingGame_exists_uniformEquilibriumPayoff_of_general` below.

## Open declarations

This file contains one `sorry`, deliberately, in
`quittingGame_exists_uniformEquilibriumPayoff`.  The repository's other
intentional open declaration is `exists_uniformDeviationCapConstructor` in
`UniformExistenceConjecture.lean`; these are the only two.
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

All of that is machine-checked in
`QuittingDisjunctionCounterexample.lean`, whose
`not_forall_isQuittingZeroSolo_or_hasAdmissibleAbsorbingQuittingCycle` refutes
the disjunction outright; this paragraph is a summary of that file, not a hand
argument.

The weight has two coordinates, so a uniform-equilibrium payoff does exist for
it externally.  Its equilibrium therefore lies outside the cycle carrier, and
what the carrier needs is a third branch covering weights of this shape — not a
proof that the existing two are exhaustive. -/
theorem quittingGame_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  sorry

/-- The general conjecture implies this one, since a quitting game *is* a
finite stochastic game.

`HEADLINE` — the direction that actually holds between the two intentional open
declarations, recorded so the relation between them is a theorem rather than a
remark.  The converse fails to be available: no reduction from arbitrary finite
stochastic games to quitting games is known, which is why
`quittingGame_exists_uniformEquilibriumPayoff` carries its own `sorry` rather
than being derived from this.  Discharging the quitting conjecture directly, by
means special to one live state, is the point of stating it separately. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_general
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hgeneral : ∀ (G : StochasticGame ι) [Finite G.State]
      [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State),
      ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  haveI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  haveI : ∀ i : ι, Finite ((quittingGame reward).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  haveI : ∀ i : ι, Nonempty ((quittingGame reward).Act i) :=
    fun _ => inferInstanceAs (Nonempty Bool)
  exact hgeneral (quittingGame reward) none

end GameTheory
