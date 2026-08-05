/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ArbitraryStartPrescribedDeliveryTelescope

/-!
# Arbitrary-start unilateral cap on one owner arena

This module proves the finite-horizon sufficiency direction of the unilateral
gain--bias conditions on one explicitly declared owner-specific closed arena.
The controller may be restarted at any configuration in that owner's arena,
including configurations which are not prescribed-reachable and need not lie
in another player's arena.

The result is only a unilateral payoff cap from target superharmonicity and a
row-wise bias inequality.  It makes no converse, necessity, union-domain,
recurrent-coverage, or prescribed-delivery claim.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)

section OwnerArenaHistories

variable [Fintype ι] [DecidableEq ι]

/-- Every supported history of a unilateral deviation restarted inside one
owner's arena remains in that same arena.  This uses only the selected
owner's closure field; in particular, the new entry need not be prescribed or
belong to every other owner's arena. -/
theorem configAt_unilateral_from_of_mem_support
    (R : A.ClosedResponseRegion) (who : ι) (z : A.Config)
    (hz : R.unilateral who z) (dev : G.BehaviorStrategy who) :
    ∀ {t : ℕ} (h : G.Hist t),
      h ∈ (G.histDist
        (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
        (A.publicState z) t).support →
        R.unilateral who ((A.rebase z).configAt t h) := by
  intro t
  induction t with
  | zero =>
      intro h hh
      have heq : h = G.emptyHist (A.publicState z) := by
        simpa [G.histDist_zero] using hh
      subst heq
      simpa using hz
  | succ n ih =>
      intro h' hh'
      rw [G.mem_support_histDist_succ] at hh'
      obtain ⟨h, hh, act, hact, s', hs', rfl⟩ := hh'
      have hx := ih h hh
      apply R.unilateral_closed_mixed who hx (dev n h)
      rw [(A.rebase z).stageActionDist_update who dev h] at hact
      have hstate := (A.rebase z).publicState_configAt_of_mem_support
        (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
        h hh
      rw [nextConfigDist, PMF.mem_support_bind_iff]
      refine ⟨act, by simpa using hact, ?_⟩
      rw [hstate, PMF.mem_support_bind_iff]
      exact ⟨s', hs', by
        simpa using (A.rebase z).configAt_snoc h act s'⟩

variable [Finite G.State] [∀ i, Finite (G.Act i)]

/-- Target superharmonicity on one owner arena remains valid after restarting
at any configuration of that arena. -/
theorem expectedTarget_update_from_le_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (who : ι) (z : A.Config) (hz : R.unilateral who z)
    (dev : G.BehaviorStrategy who) (t : ℕ) :
    G.expectedHistoryValue
        (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
        (A.publicState z)
        (fun t h => u ((A.rebase z).configAt t h) who) t ≤ u z who := by
  induction t with
  | zero => simp [expectedHistoryValue]
  | succ n ih =>
      refine le_trans ?_ ih
      rw [G.expectedHistoryValue_succ]
      refine expect_histDist_le_of_succ_on_support _ (A.publicState z)
        (fun t h => G.historyContinuationEU
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          (fun t h => u ((A.rebase z).configAt t h) who) h)
        (fun t h => u ((A.rebase z).configAt t h) who) ?_ ?_ n
      · rw [(A.rebase z).historyContinuationEU_update who dev
          (fun y => u y who) _
          (A.rebase z).publicState_configAt_emptyHist]
        simpa using A.expect_nextConfigDist_target_le_on hTi who hz (dev 0 _)
      · intro m h hh
        rw [(A.rebase z).historyContinuationEU_update who dev
          (fun y => u y who) h
          ((A.rebase z).publicState_configAt_succ h)]
        have hconfig := A.configAt_unilateral_from_of_mem_support
          R who z hz dev h hh
        simpa using A.expect_nextConfigDist_target_le_on
          hTi who hconfig (dev (m + 1) h)

end OwnerArenaHistories

section OwnerArenaCap

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- Endpoint-sensitive cumulative-payoff cap from the unilateral target and
bias inequalities on one owner-specific arena.  This is the finite-horizon
form of the gain--bias sufficiency telescope. -/
theorem expectedCumulativePayoff_update_from_le_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ (y : A.Config), R.unilateral who y → ∀ act : G.Act who,
      A.stagePayoffAt who y (PMF.pure act) +
          expect (A.nextConfigDist who y (PMF.pure act)) bias ≤
        u y who + bias y)
    (z : A.Config) (hz : R.unilateral who z)
    (dev : G.BehaviorStrategy who) (T : ℕ) :
    (∑ t ∈ Finset.range T,
        G.expectedStagePayoff
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          (A.publicState z) t who) ≤
      (T : ℝ) * u z who + bias z -
        G.expectedHistoryValue
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          (A.publicState z)
          (fun t h => bias ((A.rebase z).configAt t h)) T := by
  have hbiasMixed : ∀ (y : A.Config), R.unilateral who y →
      ∀ mixed : PMF (G.Act who),
        A.stagePayoffAt who y mixed +
            expect (A.nextConfigDist who y mixed) bias ≤
          u y who + bias y := by
    intro y hy mixed
    rw [A.stagePayoffAt_eq_expect who y mixed,
      A.expect_nextConfigDist_eq_expect who y mixed bias, ← expect_add]
    calc
      expect mixed (fun act => A.stagePayoffAt who y (PMF.pure act) +
          expect (A.nextConfigDist who y (PMF.pure act)) bias) ≤
          expect mixed (fun _ => u y who + bias y) :=
        expect_mono _ _ _ fun act => hbias y hy act
      _ = u y who + bias y := expect_const _ _
  have hstep : ∀ t : ℕ,
      G.expectedStagePayoff
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (A.publicState z) t who +
          G.expectedHistoryValue
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (A.publicState z)
            (fun t h => bias ((A.rebase z).configAt t h)) (t + 1) ≤
        G.expectedHistoryValue
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (A.publicState z)
            (fun t h => u ((A.rebase z).configAt t h) who) t +
          G.expectedHistoryValue
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (A.publicState z)
            (fun t h => bias ((A.rebase z).configAt t h)) t := by
    intro t
    have hleft :
        G.expectedStagePayoff
              (Function.update (A.rebase z).phaseProfile.behaviorProfile
                who dev)
              (A.publicState z) t who +
            G.expectedHistoryValue
              (Function.update (A.rebase z).phaseProfile.behaviorProfile
                who dev)
              (A.publicState z)
              (fun t h => bias ((A.rebase z).configAt t h)) (t + 1) =
          expect (G.histDist
              (Function.update (A.rebase z).phaseProfile.behaviorProfile
                who dev)
              (A.publicState z) t)
            (fun h =>
              G.stageEUAt
                  (Function.update (A.rebase z).phaseProfile.behaviorProfile
                    who dev)
                  h who +
                G.historyContinuationEU
                  (Function.update (A.rebase z).phaseProfile.behaviorProfile
                    who dev)
                  (fun t h => bias ((A.rebase z).configAt t h)) h) := by
      rw [G.expectedHistoryValue_succ]
      exact (expect_add _ _ _).symm
    have hright :
        G.expectedHistoryValue
              (Function.update (A.rebase z).phaseProfile.behaviorProfile
                who dev)
              (A.publicState z)
              (fun t h => u ((A.rebase z).configAt t h) who) t +
            G.expectedHistoryValue
              (Function.update (A.rebase z).phaseProfile.behaviorProfile
                who dev)
              (A.publicState z)
              (fun t h => bias ((A.rebase z).configAt t h)) t =
          expect (G.histDist
              (Function.update (A.rebase z).phaseProfile.behaviorProfile
                who dev)
              (A.publicState z) t)
            (fun h => u ((A.rebase z).configAt t h) who +
              bias ((A.rebase z).configAt t h)) :=
      (expect_add _ _ _).symm
    rw [hleft, hright]
    refine expect_histDist_le_of_succ_on_support _ (A.publicState z)
      (fun t h =>
        G.stageEUAt
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            h who +
          G.historyContinuationEU
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (fun t h => bias ((A.rebase z).configAt t h)) h)
      (fun t h => u ((A.rebase z).configAt t h) who +
        bias ((A.rebase z).configAt t h)) ?_ ?_ t
    · rw [(A.rebase z).stageEUAt_update who dev _
          (A.rebase z).publicState_configAt_emptyHist,
        (A.rebase z).historyContinuationEU_update who dev _ _
          (A.rebase z).publicState_configAt_emptyHist]
      simpa using hbiasMixed z hz (dev 0 _)
    · intro m h hh
      rw [(A.rebase z).stageEUAt_update who dev _
          ((A.rebase z).publicState_configAt_succ h),
        (A.rebase z).historyContinuationEU_update who dev _ _
          ((A.rebase z).publicState_configAt_succ h)]
      have hconfig := A.configAt_unilateral_from_of_mem_support
        R who z hz dev h hh
      simpa using hbiasMixed ((A.rebase z).configAt (m + 1) h)
        hconfig (dev (m + 1) h)
  have htel := sumStep_telescope_le hstep T
  have hsumTarget :
      (∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (A.publicState z)
            (fun t h => u ((A.rebase z).configAt t h) who) t) ≤
        (T : ℝ) * u z who := by
    calc
      (∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (A.publicState z)
            (fun t h => u ((A.rebase z).configAt t h) who) t) ≤
          ∑ _t ∈ Finset.range T, u z who :=
        Finset.sum_le_sum fun t _ =>
          A.expectedTarget_update_from_le_on hTi who z hz dev t
      _ = (T : ℝ) * u z who := by simp
  have hbiasZero :
      G.expectedHistoryValue
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          (A.publicState z)
          (fun t h => bias ((A.rebase z).configAt t h)) 0 = bias z := by
    simp [expectedHistoryValue]
  rw [hbiasZero] at htel
  linarith

/-- Endpoint-sensitive average-payoff version of the arbitrary-start
unilateral cap. -/
theorem finiteAveragePayoff_update_from_le_endpoint_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ (y : A.Config), R.unilateral who y → ∀ act : G.Act who,
      A.stagePayoffAt who y (PMF.pure act) +
          expect (A.nextConfigDist who y (PMF.pure act)) bias ≤
        u y who + bias y)
    (z : A.Config) (hz : R.unilateral who z)
    (dev : G.BehaviorStrategy who) {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff (A.publicState z) T
        (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
        who ≤
      u z who +
        (bias z -
          G.expectedHistoryValue
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (A.publicState z)
            (fun t h => bias ((A.rebase z).configAt t h)) T) / T := by
  have hsum := A.expectedCumulativePayoff_update_from_le_on
    hTi who bias hbias z hz dev T
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  rw [show u z who +
      (bias z -
        G.expectedHistoryValue
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          (A.publicState z)
          (fun t h => bias ((A.rebase z).configAt t h)) T) / (T : ℝ) =
      ((T : ℝ) * u z who + bias z -
        G.expectedHistoryValue
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          (A.publicState z)
          (fun t h => bias ((A.rebase z).configAt t h)) T) / (T : ℝ) by
    field_simp
    ring]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Uniform arbitrary-start unilateral cap with an explicit `O(1/T)`
constant independent of the behavior deviation. -/
theorem finiteAveragePayoff_update_from_le_on
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (who : ι) (bias : A.Config → ℝ)
    (hbias : ∀ (y : A.Config), R.unilateral who y → ∀ act : G.Act who,
      A.stagePayoffAt who y (PMF.pure act) +
          expect (A.nextConfigDist who y (PMF.pure act)) bias ≤
        u y who + bias y)
    (z : A.Config) (hz : R.unilateral who z)
    (dev : G.BehaviorStrategy who) {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff (A.publicState z) T
        (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
        who ≤ u z who + 2 * A.configBound bias / T := by
  have hendpoint := A.finiteAveragePayoff_update_from_le_endpoint_on
    hTi who bias hbias z hz dev hT
  have hstart := A.abs_le_configBound bias z
  have hend :
      |G.expectedHistoryValue
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          (A.publicState z)
          (fun t h => bias ((A.rebase z).configAt t h)) T| ≤
        A.configBound bias := by
    simpa [configBound] using
      (A.rebase z).abs_expectedHistoryValue_le_configBound
        (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
        bias T
  rw [abs_le] at hstart hend
  have hnumerator :
      bias z -
          G.expectedHistoryValue
            (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
            (A.publicState z)
            (fun t h => bias ((A.rebase z).configAt t h)) T ≤
        2 * A.configBound bias := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hdiv := (div_le_div_iff_of_pos_right hTreal).2 hnumerator
  linarith

end OwnerArenaCap

end FiniteResponseArchitecture
end StochasticGame
end GameTheory
