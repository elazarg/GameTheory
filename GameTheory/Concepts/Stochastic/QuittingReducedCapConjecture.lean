/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the LICENSE file.
-/

import GameTheory.Concepts.Stochastic.QuittingPunishmentFreeReduction
import GameTheory.Concepts.Stochastic.QuittingRankOneCrossing
import GameTheory.Concepts.Stochastic.QuittingSupportWitnessSourceCompiler

/-!
# A truncated-ledger reduction of the finite-quitting conjecture

The truncation fold reduces finite-quitting uniform-equilibrium existence to
one quantitative producer problem.  At every positive tolerance, construct a
finite root sequence whose ledgers and quit regrets remain controlled until a
switch index and whose deleted opponent-survival weights are small there.

The resulting profile is the truncated plan itself.  No punishment tail or
simultaneous punishment-attainment theorem is needed: this is precisely the
content of
`quittingGame_exists_uniformEquilibriumPayoff_of_truncatedLedgerCapPackage`.

The producer is stated only for nontrivial player types.  This restriction is
substantive for the ledger interface: in a one-player game the deleted
opponent-survival weight is identically one, so a positive constant reward
cannot satisfy the required small-error estimate.  The formal obstruction is
`not_hasQuittingTruncatedLedgerCapPackage_unit_one`; it concerns this
particular quantitative reduction, not equilibrium existence in one-player
games.

The declaration below remains intentionally open.  The support-witness route
now provides a separate source-facing reduction:
`quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`
compiles witness-retaining, individually rational paths with divergent total
absorption directly to a uniform-equilibrium payoff.  On that stronger path
interface the ledger clock is dominated deterministically by the own-survival
clock, so the all-player deleted-survival producer below is not needed.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Truncated-ledger producer conjecture.**

Every finite quitting game with at least two players admits, at every positive
tolerance, a truncated ledger-cap package.  Together with
`quittingGame_exists_uniformEquilibriumPayoff_of_truncatedLedgerCapPackage`,
this yields a uniform-equilibrium payoff for every game in this scope.

This is an intentional open declaration.  The restriction `[Nontrivial ι]`
excludes the one-player obstruction inherent in the package interface.
-/
theorem quittingGame_hasQuittingTruncatedLedgerCapPackage
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) (hε : 0 < ε) :
    HasQuittingTruncatedLedgerCapPackage reward ε := by
  sorry

end GameTheory
