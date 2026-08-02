/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ReachablePublicResponseCredibilityCriterion

/-!
# Arbitrary-start prescribed-delivery telescope

This module isolates the exact prescribed-play consequence of a target
harmonicity equation and a Poisson (bias) equation on one explicitly declared
prescribed-closed region.  The entry may be any configuration in that region:
the architecture is rebased there without enlarging the domain of either
hypothesis.

No unilateral arena, recurrent-class coverage, credibility converse, or
additional obstruction is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)

section RebaseRegion

variable [Fintype ι] [DecidableEq ι]

namespace ClosedResponseRegion

/-- Regard the same closed region as a region of the architecture restarted at
one of its prescribed configurations.  No predicate is enlarged. -/
def rebase (R : A.ClosedResponseRegion) {z : A.Config}
    (hz : R.prescribed z) : (A.rebase z).ClosedResponseRegion where
  unilateral := R.unilateral
  prescribed := R.prescribed
  start_unilateral := fun who => R.prescribed_unilateral who z hz
  start_prescribed := hz
  prescribed_unilateral := R.prescribed_unilateral
  unilateral_closed := by
    intro who x hx act y hy
    exact R.unilateral_closed who x hx act y (by simpa using hy)
  prescribed_closed := by
    intro x hx y hy
    exact R.prescribed_closed x hx y (by simpa using hy)

@[simp] theorem rebase_prescribed {R : A.ClosedResponseRegion} {z : A.Config}
    (hz : R.prescribed z) (y : A.Config) :
    (ClosedResponseRegion.rebase (A := A) R hz).prescribed y =
      R.prescribed y :=
  rfl

end ClosedResponseRegion
end RebaseRegion

section ExactTelescopeAtStart

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- Exact finite-horizon prescribed-payoff telescope on a declared closed
region.  The terminal term is the expected bias at the horizon. -/
theorem expectedCumulativePayoff_prescribed_eq_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ z : A.Config, R.prescribed z →
      u z who + bias z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) bias)
    (T : ℕ) :
    (∑ t ∈ Finset.range T,
        G.expectedStagePayoff A.phaseProfile.behaviorProfile initial t who) =
      (T : ℝ) * u A.start who + bias A.start -
        G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
          (fun t h => bias (A.configAt t h)) T := by
  have hstep : ∀ t : ℕ,
      G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => u (A.configAt t h) who) t +
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => bias (A.configAt t h)) t =
        G.expectedStagePayoff A.phaseProfile.behaviorProfile initial t who +
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => bias (A.configAt t h)) (t + 1) := by
    intro t
    have hleft :
        G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
              (fun t h => u (A.configAt t h) who) t +
            G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
              (fun t h => bias (A.configAt t h)) t =
          expect (G.histDist A.phaseProfile.behaviorProfile initial t)
            (fun h => u (A.configAt t h) who + bias (A.configAt t h)) :=
      (expect_add _ _ _).symm
    have hright :
        G.expectedStagePayoff A.phaseProfile.behaviorProfile initial t who +
            G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
              (fun t h => bias (A.configAt t h)) (t + 1) =
          expect (G.histDist A.phaseProfile.behaviorProfile initial t)
            (fun h =>
              G.stageEUAt A.phaseProfile.behaviorProfile h who +
                G.historyContinuationEU A.phaseProfile.behaviorProfile
                  (fun t h => bias (A.configAt t h)) h) := by
      rw [G.expectedHistoryValue_succ]
      exact (expect_add _ _ _).symm
    rw [hleft, hright]
    refine expect_histDist_congr_of_succ_on_support _ initial
      (fun t h => u (A.configAt t h) who + bias (A.configAt t h))
      (fun t h =>
        G.stageEUAt A.phaseProfile.behaviorProfile h who +
          G.historyContinuationEU A.phaseProfile.behaviorProfile
            (fun t h => bias (A.configAt t h)) h) ?_ ?_ t
    · rw [A.stageEUAt_prescribed who _ A.publicState_configAt_emptyHist,
        A.historyContinuationEU_prescribed _ _
          A.publicState_configAt_emptyHist]
      exact hbias _ R.start_prescribed
    · intro m h hh
      rw [A.stageEUAt_prescribed who _ (A.publicState_configAt_succ h),
        A.historyContinuationEU_prescribed _ _
          (A.publicState_configAt_succ h)]
      exact hbias _ (A.configAt_prescribed_of_mem_support R h hh)
  have htel :
      (∑ t ∈ Finset.range T,
          G.expectedStagePayoff A.phaseProfile.behaviorProfile initial t who) +
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => bias (A.configAt t h)) T =
        (∑ t ∈ Finset.range T,
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => u (A.configAt t h) who) t) +
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => bias (A.configAt t h)) 0 := by
    apply le_antisymm
    · exact sumStep_telescope_le (fun t => (hstep t).ge) T
    · exact sumStep_telescope_ge (fun t => (hstep t).le) T
  have hsumTarget :
      (∑ t ∈ Finset.range T,
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => u (A.configAt t h) who) t) =
        (T : ℝ) * u A.start who := by
    rw [Finset.sum_congr rfl fun t _ =>
      A.expectedTarget_prescribed_eq_on hT0 who t]
    simp
  have hbiasZero :
      G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
          (fun t h => bias (A.configAt t h)) 0 = bias A.start := by
    simp [expectedHistoryValue]
  rw [hsumTarget, hbiasZero] at htel
  linarith

/-- Average form of the exact prescribed-payoff telescope. -/
theorem finiteAveragePayoff_prescribed_eq_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ z : A.Config, R.prescribed z →
      u z who + bias z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) bias)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff initial T A.phaseProfile.behaviorProfile who =
      u A.start who +
        (bias A.start -
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => bias (A.configAt t h)) T) / T := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    A.expectedCumulativePayoff_prescribed_eq_on hT0 who bias hbias T]
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  field_simp
  ring

/-- Uniform `O(1/T)` prescribed-delivery estimate obtained from the exact
bias telescope. -/
theorem abs_finiteAveragePayoff_prescribed_sub_le_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ z : A.Config, R.prescribed z →
      u z who + bias z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) bias)
    {T : ℕ} (hT : 0 < T) :
    |G.finiteAveragePayoff initial T A.phaseProfile.behaviorProfile who -
        u A.start who| ≤ 2 * A.configBound bias / T := by
  have havg := A.finiteAveragePayoff_prescribed_eq_on
    hT0 who bias hbias hT
  have hstart := A.abs_le_configBound bias A.start
  have hend := A.abs_expectedHistoryValue_le_configBound
    A.phaseProfile.behaviorProfile bias T
  rw [abs_le] at hstart hend
  have hlower : -(2 * A.configBound bias) ≤
      bias A.start -
        G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
          (fun t h => bias (A.configAt t h)) T := by
    linarith
  have hupper :
      bias A.start -
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => bias (A.configAt t h)) T ≤
        2 * A.configBound bias := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hlowerDiv := (div_le_div_iff_of_pos_right hTreal).2 hlower
  have hupperDiv := (div_le_div_iff_of_pos_right hTreal).2 hupper
  rw [havg, add_sub_cancel_left, abs_le]
  constructor
  · simpa only [neg_div] using hlowerDiv
  · exact hupperDiv

end ExactTelescopeAtStart

section ArbitraryStart

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- Exact finite-horizon prescribed-payoff identity after restarting at any
configuration in the declared prescribed-closed region. -/
theorem expectedCumulativePayoff_prescribed_from_eq_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ y : A.Config, R.prescribed y →
      u y who + bias y = A.prescribedStagePayoff y who +
        expect (A.prescribedConfigDist y) bias)
    (z : A.Config) (hz : R.prescribed z) (T : ℕ) :
    (∑ t ∈ Finset.range T,
        G.expectedStagePayoff (A.rebase z).phaseProfile.behaviorProfile
          (A.publicState z) t who) =
      (T : ℝ) * u z who + bias z -
        G.expectedHistoryValue (A.rebase z).phaseProfile.behaviorProfile
          (A.publicState z)
          (fun t h => bias ((A.rebase z).configAt t h)) T := by
  let Rz : (A.rebase z).ClosedResponseRegion :=
    ClosedResponseRegion.rebase (A := A) R hz
  have hT0z : (A.rebase z).IsPrescribedTargetHarmonicOn Rz u := by
    intro player y hy
    change R.prescribed y at hy
    exact hT0 player y hy
  have hbiasz : ∀ y : A.Config, Rz.prescribed y →
      u y who + bias y = (A.rebase z).prescribedStagePayoff y who +
        expect ((A.rebase z).prescribedConfigDist y) bias := by
    intro y hy
    change R.prescribed y at hy
    simpa using hbias y hy
  exact (A.rebase z).expectedCumulativePayoff_prescribed_eq_on
    hT0z who bias hbiasz T

/-- Exact average-payoff identity after restarting at any prescribed
configuration of the declared region. -/
theorem finiteAveragePayoff_prescribed_from_eq_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ y : A.Config, R.prescribed y →
      u y who + bias y = A.prescribedStagePayoff y who +
        expect (A.prescribedConfigDist y) bias)
    (z : A.Config) (hz : R.prescribed z) {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff (A.publicState z) T
        (A.rebase z).phaseProfile.behaviorProfile who =
      u z who +
        (bias z -
          G.expectedHistoryValue (A.rebase z).phaseProfile.behaviorProfile
            (A.publicState z)
            (fun t h => bias ((A.rebase z).configAt t h)) T) / T := by
  let Rz : (A.rebase z).ClosedResponseRegion :=
    ClosedResponseRegion.rebase (A := A) R hz
  have hT0z : (A.rebase z).IsPrescribedTargetHarmonicOn Rz u := by
    intro player y hy
    change R.prescribed y at hy
    exact hT0 player y hy
  have hbiasz : ∀ y : A.Config, Rz.prescribed y →
      u y who + bias y = (A.rebase z).prescribedStagePayoff y who +
        expect ((A.rebase z).prescribedConfigDist y) bias := by
    intro y hy
    change R.prescribed y at hy
    simpa using hbias y hy
  exact (A.rebase z).finiteAveragePayoff_prescribed_eq_on
    hT0z who bias hbiasz hT

/-- Arbitrary-start `O(1/T)` delivery on the same explicitly prescribed-closed
domain.  This is only a prescribed-play conclusion. -/
theorem abs_finiteAveragePayoff_prescribed_from_sub_le_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ y : A.Config, R.prescribed y →
      u y who + bias y = A.prescribedStagePayoff y who +
        expect (A.prescribedConfigDist y) bias)
    (z : A.Config) (hz : R.prescribed z) {T : ℕ} (hT : 0 < T) :
    |G.finiteAveragePayoff (A.publicState z) T
          (A.rebase z).phaseProfile.behaviorProfile who - u z who| ≤
      2 * A.configBound bias / T := by
  let Rz : (A.rebase z).ClosedResponseRegion :=
    ClosedResponseRegion.rebase (A := A) R hz
  have hT0z : (A.rebase z).IsPrescribedTargetHarmonicOn Rz u := by
    intro player y hy
    change R.prescribed y at hy
    exact hT0 player y hy
  have hbiasz : ∀ y : A.Config, Rz.prescribed y →
      u y who + bias y = (A.rebase z).prescribedStagePayoff y who +
        expect ((A.rebase z).prescribedConfigDist y) bias := by
    intro y hy
    change R.prescribed y at hy
    simpa using hbias y hy
  exact (A.rebase z).abs_finiteAveragePayoff_prescribed_sub_le_on
    hT0z who bias hbiasz hT

end ArbitraryStart

end FiniteResponseArchitecture
end StochasticGame
end GameTheory
