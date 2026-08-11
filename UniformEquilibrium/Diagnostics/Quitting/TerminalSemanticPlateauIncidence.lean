/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration

/-!
# Exact semantic incidence of actual plateau rows

The time disintegration of a terminal law exposes actual live rows.  This
module records the precise semantic data carried by such a row.  The current
profile is the semantic prefix of its all-Continue continuation by its actual
live root, and both ends are executable carrier points.

This closes the profile/prefix incidence issue, but deliberately does not
turn an actual row into an exact Nash row or put its shifted tail on the
minimum-debt fiber.  Indeed the final theorem shows that a positive stage atom
over a positive minimum tail certifies failure of exact root Nash.  Thus the
remaining plateau seam is quantitatively charging this local Nash defect (or
the tail's excess debt), rather than identifying the row with a minimum exact
edge for free.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Arbitrary-profile semantic prefix factorization -/

/-- The canonical first-stage representative has exactly the same
all-behavior best-response envelope as the original profile. -/
theorem quittingContinuationBestResponseValue_firstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingFirstStageAdapter reward profile) who =
      quittingContinuationBestResponseValue reward profile who := by
  unfold quittingContinuationBestResponseValue
  apply congrArg sSup
  ext value
  simp only [Set.mem_range]
  constructor
  · rintro ⟨deviation, rfl⟩
    refine ⟨deviation, ?_⟩
    exact (quittingTerminalPayoff_update_firstStageAdapter
      reward profile who deviation).symm
  · rintro ⟨deviation, rfl⟩
    refine ⟨deviation, ?_⟩
    exact quittingTerminalPayoff_update_firstStageAdapter
      reward profile who deviation

/-- Semantic data is unchanged by the canonical root/continuation adapter. -/
@[simp] theorem quittingTerminalSemanticPair_firstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingFirstStageAdapter reward profile) =
      quittingTerminalSemanticPair reward profile := by
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_firstStageAdapter reward profile who
  · funext who
    exact quittingContinuationBestResponseValue_firstStageAdapter
      reward profile who

/-- Every actual profile is, at the level of complete terminal semantics,
exactly its actual time-zero live root prefixed to its shifted all-Continue
continuation. -/
theorem quittingTerminalSemanticPair_eq_prefix_allContinueContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticPair reward profile =
      quittingTerminalSemanticPrefix reward
        (quittingProfileRoot reward profile)
        (quittingTerminalSemanticPair reward
          (quittingProfileAllContinueContinuation reward profile)) := by
  rw [← quittingTerminalSemanticPair_firstStageAdapter reward profile]
  unfold quittingFirstStageAdapter
  exact quittingTerminalSemanticPair_rootThenContinuation
    reward (quittingProfileRoot reward profile)
      (quittingProfileAllContinueContinuation reward profile) hM hreward

/-- The exact semantic prefix factorization at every actual live row. -/
theorem quittingTerminalSemanticPair_spine_eq_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile time) =
      quittingTerminalSemanticPrefix reward
        (quittingProfileLiveRoot reward profile time)
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))) := by
  rw [quittingTerminalSemanticPair_eq_prefix_allContinueContinuation
    reward (quittingAllContinueProfileSpine reward profile time) hM hreward]
  have hroot : quittingProfileRoot reward
      (quittingAllContinueProfileSpine reward profile time) =
        quittingProfileLiveRoot reward profile time := by
    funext player
    unfold quittingProfileRoot quittingProfileLiveRoot
    simpa [quittingGame] using
      (quittingAllContinueProfileSpine_apply_liveHist
        reward profile time player 0)
  rw [hroot]
  rfl

/-- Every literal profile pair is, without taking a closure limit, a point of
the compact semantic carrier. -/
theorem quittingTerminalSemanticPair_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward profile ∈
      quittingTerminalSemanticCarrier reward := by
  apply subset_closure
  exact ⟨profile, rfl⟩

/-! ## Positive local mass exposes a semantic edge and a Nash defect -/

/-- The conditional coalition mass at an actual live row is exactly the
finite product-law coalition mass of the extracted live root. -/
theorem quittingLiveRowCoalitionMass_eq_rootCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingLiveRowCoalitionMass reward profile time terminal =
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) terminal.val := by
  let root := quittingProfileLiveRoot reward profile time
  unfold quittingLiveRowCoalitionMass
  change ((pmfPi root)
    (quittingTerminalCoalitionAction terminal)).toReal = _
  rw [pmfPi_apply, ENNReal.toReal_prod]
  have hproduct :
      (∏ x, ((root x)
        (quittingTerminalCoalitionAction terminal x)).toReal) =
        (∏ x ∈ terminal.val, (root x true).toReal) *
          ∏ x ∈ terminal.valᶜ, (1 - (root x true).toReal) := by
    rw [← Finset.prod_mul_prod_compl terminal.val
      (fun x => ((root x)
        (quittingTerminalCoalitionAction terminal x)).toReal)]
    congr 1
    · apply Finset.prod_congr rfl
      intro x hx
      simp [quittingTerminalCoalitionAction, hx]
    · apply Finset.prod_congr rfl
      intro x hx
      have hnot : x ∉ terminal.val := by
        simpa using hx
      have hsum := quittingRoot_continueProbability_add_quitProbability root x
      simp only [quittingTerminalCoalitionAction, hnot, decide_false]
      linarith
  rw [hproduct]
  rfl

/-- Unconditional stage mass factors through survival and the actual live
root's exact coalition mass. -/
theorem quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal =
      quittingLiveMass reward profile time *
        quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) terminal.val := by
  rw [quittingStageCoalitionMass,
    quittingLiveRowCoalitionMass_eq_rootCoalitionMass]

/-- Positive mass on an actual stage coalition exposes each quitter in the
support of the corresponding actual live-root marginal. -/
theorem positive_profileLiveRoot_quit_of_positive_stageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι)
    (hmem : who ∈ terminal.val)
    (hpositive : 0 < quittingStageCoalitionMass reward profile time terminal) :
    0 < (quittingProfileLiveRoot reward profile time who true).toReal := by
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  have hrow : 0 < quittingLiveRowCoalitionMass reward profile time terminal := by
    have hrowNonneg :=
      quittingLiveRowCoalitionMass_nonneg reward profile time terminal
    unfold quittingStageCoalitionMass at hpositive
    nlinarith [quittingLiveMass_nonneg reward profile time]
  have hactionNe :
      (quittingGame reward).stageActionDist profile
          (quittingLiveHist reward time)
          (quittingTerminalCoalitionAction terminal) ≠ 0 := by
    intro hzero
    unfold quittingLiveRowCoalitionMass at hrow
    rw [hzero] at hrow
    simp at hrow
  have hactionSupport : quittingTerminalCoalitionAction terminal ∈
      ((quittingGame reward).stageActionDist profile
        (quittingLiveHist reward time)).support :=
    (PMF.mem_support_iff _ _).2 hactionNe
  have hcoord := (quittingGame reward).coord_mem_support_stageActionDist
    profile (quittingLiveHist reward time) hactionSupport who
  have hactionWho : quittingTerminalCoalitionAction terminal who = true := by
    simp [quittingTerminalCoalitionAction, hmem]
  rw [hactionWho] at hcoord
  exact ENNReal.toReal_pos ((PMF.mem_support_iff _ _).1 hcoord)
    (PMF.apply_ne_top _ _)

/-- A positive chronological atom carries a completely literal semantic
prefix incidence: executable carrier points at both ends, the actual live
root between them, and positive root coalition mass.  No Nash or minimum
claim is included. -/
theorem positive_stageCoalitionMass_has_semanticPrefixIncidence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 <
      quittingStageCoalitionMass reward profile time terminal) :
    let current := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))
    let root := quittingProfileLiveRoot reward profile time
    current ∈ quittingTerminalSemanticCarrier reward ∧
      tail ∈ quittingTerminalSemanticCarrier reward ∧
      current = quittingTerminalSemanticPrefix reward root tail ∧
      0 < quittingRootCoalitionMass root terminal.val := by
  dsimp only
  refine ⟨quittingTerminalSemanticPair_mem_carrier reward _,
    quittingTerminalSemanticPair_mem_carrier reward _,
    quittingTerminalSemanticPair_spine_eq_prefix
      reward profile time hM hreward, ?_⟩
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
    at hpositive
  nlinarith [quittingLiveMass_nonneg reward profile time,
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      (quittingProfileLiveRoot reward profile time) terminal.val]

/-- A positive non-singleton stage atom above a positive minimum semantic
tail cannot be an exact Nash prefix row.  Exact Nash rows at such a tail are
collision-free. -/
theorem not_isZeroQuittingRootNash_profileLiveRoot_of_positive_collisionStageMass_at_minimumTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (pair : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositiveDebt : 0 < quittingTerminalSemanticDebtSum pair)
    (htail : quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1)) = pair)
    (hcollision : 2 ≤ terminal.val.card)
    (hpositiveMass : 0 <
      quittingStageCoalitionMass reward profile time terminal) :
    ¬ IsεQuittingRootNash reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).1
        0 (quittingProfileLiveRoot reward profile time) := by
  intro hnash
  rw [htail] at hnash
  let root := quittingProfileLiveRoot reward profile time
  have hcollisionZero : quittingRootCollisionMass root = 0 :=
    (minimumTerminalSemantic_exactNash_criticalFace
      (reward := reward) pair root hM hreward hpair hminimum
        hpositiveDebt hnash).1
  have hrootCoalition : 0 < quittingRootCoalitionMass root terminal.val := by
    have hrow : 0 < quittingLiveRowCoalitionMass reward profile time terminal := by
      unfold quittingStageCoalitionMass at hpositiveMass
      nlinarith [quittingLiveMass_nonneg reward profile time]
    rw [quittingLiveRowCoalitionMass_eq_rootCoalitionMass] at hrow
    exact hrow
  have htermLe : quittingRootCoalitionMass root terminal.val ≤
      quittingRootCollisionMass root := by
    rw [quittingRootCollisionMass_eq_sum_coalitionMass]
    exact Finset.single_le_sum
      (fun coalition _ =>
        MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root coalition)
      (by simp [hcollision])
  rw [hcollisionZero] at htermLe
  linarith

end GameTheory
