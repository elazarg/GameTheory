/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.CutoffOneSafety
import UniformEquilibrium.Quitting.Stationary.FullRateStationaryVerifier
import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler

/-!
# Kernel-checked certificate types for the finite quitting repair ladder

The search code in `experiments/quitting_repair_cegis/` works with exact
rational tables, but its positive output is deliberately phrased in terms of
three existing semantic compilers:

* a safe cutoff-one zero-tail root;
* an arbitrary stationary product root verified by the exact full-rate
  behavioral unilateral cap; and
* a finite cyclic word satisfying exact policy recursion, exact phasewise root
  Nash, and playerwise opponent-cycle contraction.

The structures below merely package those stable hypotheses and re-export the
corresponding terminal-Nash and uniform-payoff conclusions.  They are checkers,
not search procedures.  In particular there is no constructor from failure of
any finite grammar, and no theorem turns stationary or bounded-period failure
into nonexistence.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A proof-carrying cutoff-one repair: an exact Nash root at zero continuation
whose positive-singleton Continue endpoint is safe for every player. -/
structure QuittingCutoffOneRepairCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  root : ι → PMF Bool
  rootNash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root
  safe : ∀ who,
    quittingCutoffOnePositiveContinuePayoff reward root who ≤
      quittingRootSuccessorPayoff reward (0 : Payoff ι) root who

namespace QuittingCutoffOneRepairCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The exact terminal vector delivered by the one-root/all-Continue profile. -/
def payoff (certificate : QuittingCutoffOneRepairCertificate reward) :
    Payoff ι :=
  quittingRootSuccessorPayoff reward (0 : Payoff ι) certificate.root

/-- The packaged cutoff-one repair is an exact terminal Nash profile against
arbitrary behavioral unilateral deviations. -/
theorem isZeroAsymptoticNash
    (certificate : QuittingCutoffOneRepairCertificate reward) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingInfinitePathProfile reward
        (quittingCutoffOneRoots certificate.root)) :=
  cutoffOneProfile_isZeroAsymptoticNash_of_safe reward certificate.root
    certificate.rootNash certificate.safe

/-- A proof-carrying cutoff-one repair yields its named uniform-equilibrium
payoff through the existing terminal-to-uniform bridge. -/
theorem isUniformEquilibriumPayoff
    (certificate : QuittingCutoffOneRepairCertificate reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none certificate.payoff :=
  quittingGame_isUniformEquilibriumPayoff_of_cutoffOneSafeRoot reward
    certificate.root certificate.rootNash certificate.safe

end QuittingCutoffOneRepairCertificate

/-- A proof-carrying stationary repair.  The premise uses the exact full-rate
cap, which already quantifies over arbitrary behavioral deviations and covers
both contracting and saturated opponent faces. -/
structure QuittingStationaryRepairCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  root : ι → PMF Bool
  cap_le : ∀ who,
    quittingStationaryFullRateUnilateralCap reward root who ≤
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who

namespace QuittingStationaryRepairCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The terminal vector of the supplied stationary root. -/
def payoff (certificate : QuittingStationaryRepairCertificate reward) :
    Payoff ι :=
  quittingTerminalPayoff reward
    (quittingStationaryProfile reward certificate.root)

/-- The exact full-rate cap inequalities are equivalent to terminal Nash for
the stationary profile. -/
theorem isZeroAsymptoticNash
    (certificate : QuittingStationaryRepairCertificate reward) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward certificate.root) := by
  rw [isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le]
  intro who
  simpa using certificate.cap_le who

/-- A proof-carrying stationary repair yields its terminal vector as a
uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff
    (certificate : QuittingStationaryRepairCertificate reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none certificate.payoff :=
  quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact reward
    (quittingStationaryProfile reward certificate.root)
    certificate.isZeroAsymptoticNash

end QuittingStationaryRepairCertificate

/-- A proof-carrying accepted cyclic/holonomy word.  A small affine return is
not enough: the certificate retains exact policy recursion, exact local root
Nash at every phase, and playerwise opponent-cycle contraction. -/
structure QuittingCyclicRepairCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (K : ℕ) where
  cycle : Fin K → ι → PMF Bool
  value : Fin K → Payoff ι
  policy : ∀ phase,
    value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase)
  rootNash : ∀ phase,
    IsεQuittingRootNash reward
      (value (finRotate K phase)) 0 (cycle phase)
  contracts : ∀ who,
    (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1

namespace QuittingCyclicRepairCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {K : ℕ}

/-- The executable cyclic behavior profile at a chosen entry phase. -/
def profile (certificate : QuittingCyclicRepairCertificate reward K)
    (phase : Fin K) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward certificate.cycle phase

/-- The actual terminal vector selected by the executable cyclic profile. -/
def payoff (certificate : QuittingCyclicRepairCertificate reward K)
    (phase : Fin K) : Payoff ι :=
  quittingCyclicTerminalValue reward certificate.cycle phase

/-- Every entry phase of an accepted cyclic certificate is exact terminal
Nash against arbitrary behavioral unilateral deviations. -/
theorem isZeroAsymptoticNash
    (certificate : QuittingCyclicRepairCertificate reward K)
    (phase : Fin K) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (certificate.profile phase) :=
  isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate_finite
    reward certificate.cycle certificate.value phase certificate.policy
      certificate.rootNash certificate.contracts

/-- Every entry phase of an accepted cyclic certificate supplies a
uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff
    (certificate : QuittingCyclicRepairCertificate reward K)
    (phase : Fin K) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (certificate.payoff phase) :=
  isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
    reward certificate.cycle certificate.value phase certificate.policy
      certificate.rootNash certificate.contracts

end QuittingCyclicRepairCertificate

end GameTheory
