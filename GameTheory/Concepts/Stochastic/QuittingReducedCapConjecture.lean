/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the LICENSE file.
-/

import GameTheory.Concepts.Stochastic.QuittingTruncatedLedgerCapCounterexample

/-!
# Boundary of the truncated-ledger reduction

`HasQuittingTruncatedLedgerCapPackage` is a sound sufficient certificate: a
package at every positive tolerance compiles to a uniform-equilibrium payoff.
It is not, however, a universal producer target.

The former declaration
`quittingGame_hasQuittingTruncatedLedgerCapPackage` asserted that every finite
quitting game with at least two players produced such packages.  The
counterexample in `QuittingTruncatedLedgerCapCounterexample` refutes that
statement on `Bool`.  Its reward is zero-sum: a singleton quitter receives
`-1`, the continuing opponent receives `1`, and simultaneous quitting pays
`0`.  All-Continue is an exact uniform equilibrium with payoff zero, but a
truncated ledger-cap package at tolerance `1/2` would force its common reach
parameter both above `1/2` and below `1/10`.

The obstruction is the certificate's common all-player deleted-survival
requirement, not equilibrium existence and not merely the absence of a
punishment tail.  The richer phase-switch package projects to the truncated
one and therefore has the same obstruction.  A complete producer must retain a
persistent-live branch (the landed zero-solo branch is one such class), or use
a weaker value-sensitive/active-set tail condition.  No exhaustiveness claim
for either repair is made here.

This module keeps the valid branch-relative reduction and the formal no-go.  It
contains no conjectural declaration.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Packages at every positive tolerance, isolated as the producer property
consumed by the existing truncation compiler. -/
def HasQuittingTruncatedLedgerCapProducer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → HasQuittingTruncatedLedgerCapPackage reward ε

/-- The sound replacement for the false unconditional producer conjecture.
A zero-solo game is handled by its exact persistent-live all-Continue
profile; otherwise a supplied all-errors truncated-ledger producer is consumed
by the existing compiler.  This theorem does not claim that the disjunction is
exhaustive. -/
theorem exists_uniformEquilibriumPayoff_of_zeroSolo_or_truncatedLedgerCapProducer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hbranch : IsQuittingZeroSolo reward ∨
      HasQuittingTruncatedLedgerCapProducer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases hbranch with hzero | hproducer
  · exact exists_uniformEquilibriumPayoff_of_zeroSolo reward hzero
  · exact quittingGame_exists_uniformEquilibriumPayoff_of_truncatedLedgerCapPackage
      reward hproducer

/-- The two-player zero-sum counterexample has no all-errors truncated-ledger
producer, despite having the exact zero uniform-equilibrium payoff. -/
theorem not_hasQuittingTruncatedLedgerCapProducer_counterexample :
    ¬HasQuittingTruncatedLedgerCapProducer
      QuittingTruncatedLedgerCapCounterexample.reward := by
  simpa [HasQuittingTruncatedLedgerCapProducer] using
    QuittingTruncatedLedgerCapCounterexample.
      not_quittingGame_hasQuittingTruncatedLedgerCapPackage

end GameTheory
