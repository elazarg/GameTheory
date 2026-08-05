/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFirstStageAdapter
import GameTheory.Concepts.Stochastic.QuittingRootSuccessorCertificate

/-!
# Advancing a same-date marked transfer

A marked first-opponent selection may transfer the player flag without
advancing calendar time.  This file isolates the elementary Bellman estimate
which controls that obstruction.

For a one-stage Nash--Bellman edge `current → successor` with absorption
mass `p`, bounded terminal rewards and bounded successor values give

`|current i - successor i| ≤ 2 M p`.

Consequently, if a newly marked player has current value at most `-θ`, then
either the root has the quantitatively positive jump `p ≥ θ/(4M)`, or the
same player remains at most `-θ/2` at the survived successor.  In the latter
case the flag can be moved forward by one actual stage.

The positive-jump alternative is an actual compatible Bellman edge, but this
file does not claim that its successor is again negatively marked or that one
such edge is already a terminal discharge.  Those are separate SCC/path
questions.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The expectation of the indicator of a nonempty quitter set is exactly
the one-stage absorption mass. -/
theorem expect_quittingNonemptyIndicator_eq_absorptionMass
    (root : ι → PMF Bool) :
    expect (pmfPi root) (fun action ↦
        if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
      quittingRootAbsorptionMass root := by
  let allContinue : ι → Bool := quittingAllContinueAction
  have hindicator :
      (fun action : ι → Bool ↦
          if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
        fun action ↦ 1 - if action = allContinue then (1 : ℝ) else 0 := by
    funext action
    by_cases hquit : (quittingQuitters action).Nonempty
    · have hne : action ≠ allContinue := by
        intro heq
        subst action
        simp [allContinue] at hquit
      simp [hquit, hne]
    · have heq : action = allContinue :=
        eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
          action hquit
      subst action
      simp [allContinue]
  rw [hindicator, expect_sub, expect_const,
    ← Math.Probability.apply_toReal_eq_expect_indicator]
  rfl

omit [DecidableEq ι] in
/-- The one-stage absorbing contribution is bounded by the reward bound times
the probability of absorption. -/
theorem abs_quittingRootAbsorbingContribution_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingRootAbsorbingContribution reward root who| ≤
      M * quittingRootAbsorptionMass root := by
  let absorbingBound : (ι → Bool) → ℝ := fun action ↦
    if (quittingQuitters action).Nonempty then M else 0
  have hpointUpper (action : ι → Bool) :
      quittingRootPayoff reward (0 : Payoff ι) action who ≤
        absorbingBound action := by
    by_cases hquit : (quittingQuitters action).Nonempty
    · have h := hreward ⟨quittingQuitters action, hquit⟩ who
      simp only [quittingRootPayoff, dif_pos hquit, absorbingBound,
        if_pos hquit]
      exact (le_abs_self _).trans h
    · simp only [quittingRootPayoff, dif_neg hquit, Pi.zero_apply,
        absorbingBound, if_neg hquit]
      norm_num
  have hpointLower (action : ι → Bool) :
      -absorbingBound action ≤
        quittingRootPayoff reward (0 : Payoff ι) action who := by
    by_cases hquit : (quittingQuitters action).Nonempty
    · have h := hreward ⟨quittingQuitters action, hquit⟩ who
      simp only [quittingRootPayoff, dif_pos hquit, absorbingBound,
        if_pos hquit]
      exact (neg_le_of_abs_le h)
    · simp only [quittingRootPayoff, dif_neg hquit, Pi.zero_apply,
        absorbingBound, if_neg hquit]
      norm_num
  have hupper :
      quittingRootAbsorbingContribution reward root who ≤
        expect (pmfPi root) absorbingBound := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    exact expect_mono _ _ _ hpointUpper
  have hlower :
      -expect (pmfPi root) absorbingBound ≤
        quittingRootAbsorbingContribution reward root who := by
    have hmono := expect_mono (pmfPi root)
      (fun action ↦ -absorbingBound action)
      (fun action ↦ quittingRootPayoff reward (0 : Payoff ι) action who)
      hpointLower
    have hneg :
        expect (pmfPi root) (fun action ↦ -absorbingBound action) =
          -expect (pmfPi root) absorbingBound := by
      rw [show (fun action ↦ -absorbingBound action) =
          fun action ↦ (-1 : ℝ) * absorbingBound action by
        funext action
        ring,
        expect_const_mul]
      ring
    rw [hneg] at hmono
    exact hmono
  have hboundExpectation :
      expect (pmfPi root) absorbingBound =
        M * quittingRootAbsorptionMass root := by
    unfold absorbingBound
    rw [show (fun action : ι → Bool ↦
        if (quittingQuitters action).Nonempty then M else 0) =
        fun action ↦ M *
          (if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) by
      funext action
      split <;> simp_all]
    rw [expect_const_mul,
      expect_quittingNonemptyIndicator_eq_absorptionMass]
  rw [hboundExpectation] at hupper hlower
  exact (abs_le).2 ⟨hlower, hupper⟩

omit [DecidableEq ι] in
/-- A bounded Bellman edge moves each payoff coordinate by at most twice the
reward bound times its one-stage absorption mass. -/
theorem abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : |tail who| ≤ M) :
    |quittingRootSuccessorPayoff reward tail root who - tail who| ≤
      2 * M * quittingRootAbsorptionMass root := by
  rw [quittingRootSuccessorPayoff_sub_tail]
  have habsorbing :=
    abs_quittingRootAbsorbingContribution_le reward root who M hreward
  have hp0 : 0 ≤ quittingRootAbsorptionMass root := by
    unfold quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_le_one root]
  calc
    |quittingRootAbsorbingContribution reward root who -
        quittingRootAbsorptionMass root * tail who| ≤
      |quittingRootAbsorbingContribution reward root who| +
        |quittingRootAbsorptionMass root * tail who| := abs_sub _ _
    _ ≤ M * quittingRootAbsorptionMass root +
        quittingRootAbsorptionMass root * M := by
      apply add_le_add habsorbing
      rw [abs_mul, abs_of_nonneg hp0]
      exact mul_le_mul_of_nonneg_left htail hp0
    _ = 2 * M * quittingRootAbsorptionMass root := by ring

omit [DecidableEq ι] in
/-- Parameterized same-date transfer dichotomy.  Advancing the marked flag
one actual stage spends at most the supplied negativity budget `η`; otherwise
the root has absorption mass at least `η / (2M)`.  This additive form can be
iterated without repeatedly halving the negative threshold. -/
theorem markedNegative_advance_or_absorptionMass_ge_of_budget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η : ℝ)
    (hM : 0 < M) (_hη : 0 ≤ η)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnegative : current marked ≤ -θ) :
    η / (2 * M) ≤ quittingRootAbsorptionMass root ∨
      successor marked ≤ -θ + η := by
  by_cases hjump : η / (2 * M) ≤ quittingRootAbsorptionMass root
  · exact Or.inl hjump
  · right
    have hpSmall :
        quittingRootAbsorptionMass root < η / (2 * M) :=
      lt_of_not_ge hjump
    have hden : 0 < 2 * M := mul_pos (by norm_num) hM
    have hscaled :
        2 * M * quittingRootAbsorptionMass root < η := by
      simpa [mul_comm] using (lt_div_iff₀ hden).1 hpSmall
    have hjumpBound :=
      abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
        reward successor root marked M hreward hsuccessorBound
    have hcoordinate :
        current marked =
          quittingRootSuccessorPayoff reward successor root marked := by
      exact congrFun hbellman marked
    rw [← hcoordinate] at hjumpBound
    have hforward : successor marked - current marked ≤
        |current marked - successor marked| := by
      simpa [abs_sub_comm] using le_abs_self (successor marked - current marked)
    nlinarith

omit [DecidableEq ι] in
/-- Half-margin form of the additive budget theorem.  A player which is
`θ`-negative at the current endpoint either lies on a root with absorption
mass at least `θ/(4M)`, or remains `θ/2`-negative after advancing one actual
stage. -/
theorem markedNegative_advance_or_absorptionMass_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ : ℝ)
    (hM : 0 < M) (hθ : 0 ≤ θ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnegative : current marked ≤ -θ) :
    θ / (4 * M) ≤ quittingRootAbsorptionMass root ∨
      successor marked ≤ -(θ / 2) := by
  have hbudget := markedNegative_advance_or_absorptionMass_ge_of_budget
    reward current successor root marked M θ (θ / 2) hM
      (div_nonneg hθ (by norm_num)) hreward hsuccessorBound
      hbellman hnegative
  rcases hbudget with hjump | hadvance
  · left
    have hratio : (θ / 2) / (2 * M) = θ / (4 * M) := by
      field_simp
      ring
    rw [hratio] at hjump
    exact hjump
  · right
    linarith

/-! ## A successor escape makes the product jump playerwise charged -/

/-- One-stage absorption probability after forcing `who` to Continue.  This
is the opponent-absorption hazard for `who` at the root. -/
def quittingRootOpponentAbsorptionMass
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootAbsorptionMass
    (Function.update root who (PMF.pure false))

omit [DecidableEq ι] in
/-- The all-continue mass is the product of the displayed Continue
probabilities. -/
theorem quittingStationaryContinueMass_eq_prod_continueProbability
    (root : ι → PMF Bool) :
    quittingStationaryContinueMass root =
      ∏ player, (root player false).toReal := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  rfl

/-- A marked player's Quit hazard is part of every other player's opponent
absorption hazard. -/
theorem quittingProbability_le_opponentAbsorptionMass
    (root : ι → PMF Bool) {marked who : ι} (hne : marked ≠ who) :
    (root marked true).toReal ≤
      quittingRootOpponentAbsorptionMass root who := by
  let forced : ι → PMF Bool :=
    Function.update root who (PMF.pure false)
  let continueProbability : ι → ℝ := fun player ↦
    (forced player false).toReal
  have hfactor0 (player : ι) : 0 ≤ continueProbability player :=
    ENNReal.toReal_nonneg
  have hfactor1 (player : ι) : continueProbability player ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (forced player) false)
  have hrest0 :
      0 ≤ ∏ player ∈ (Finset.univ.erase marked : Finset ι),
        continueProbability player :=
    Finset.prod_nonneg fun player _ ↦ hfactor0 player
  have hrest1 :
      (∏ player ∈ (Finset.univ.erase marked : Finset ι),
        continueProbability player) ≤ 1 :=
    Finset.prod_le_one
      (fun player _ ↦ hfactor0 player)
      (fun player _ ↦ hfactor1 player)
  have hproductSplit :
      (∏ player, continueProbability player) =
        (∏ player ∈ (Finset.univ.erase marked : Finset ι),
          continueProbability player) * continueProbability marked := by
    simpa using (Finset.prod_erase_mul Finset.univ continueProbability
      (Finset.mem_univ marked)).symm
  have hproductLe :
      (∏ player, continueProbability player) ≤
        continueProbability marked := by
    rw [hproductSplit]
    nlinarith [mul_nonneg (sub_nonneg.mpr hrest1)
      (hfactor0 marked)]
  have hforcedMarked : forced marked = root marked := by
    simp [forced, hne]
  have hcontinueLe :
      quittingStationaryContinueMass forced ≤
        (root marked false).toReal := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    change (∏ player, continueProbability player) ≤ _
    rw [← hforcedMarked]
    exact hproductLe
  have hsum :=
    quittingRoot_continueProbability_add_quitProbability root marked
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  change (root marked true).toReal ≤
    1 - quittingStationaryContinueMass forced
  linarith

/-- If an exact-Nash root starts with a `θ`-negative marked value but its
survived successor rises by `η`, the marked player's *opponents* must absorb
with mass at least `η/(2M)`.  Otherwise pure Continue would beat the current
value. -/
theorem successorEscape_le_two_mul_opponentAbsorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hescape : -θ + η ≤ successor marked) :
    η ≤ 2 * M * quittingRootOpponentAbsorptionMass root marked := by
  have hcontinueNash := hnash marked (PMF.pure false)
  have hcontinue :
      quittingRootContinuePayoff reward successor root marked ≤
        current marked := by
    rw [congrFun hbellman marked]
    simpa [quittingRootContinuePayoff,
      quittingRootSuccessorPayoff] using hcontinueNash
  have hjumpBound :=
    abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward successor
        (Function.update root marked (PMF.pure false)) marked M
        hreward hsuccessorBound
  change
    |quittingRootContinuePayoff reward successor root marked -
        successor marked| ≤
      2 * M * quittingRootOpponentAbsorptionMass root marked at hjumpBound
  have hforward :
      successor marked -
          quittingRootContinuePayoff reward successor root marked ≤
        |quittingRootContinuePayoff reward successor root marked -
          successor marked| := by
    simpa [abs_sub_comm] using le_abs_self
      (successor marked -
        quittingRootContinuePayoff reward successor root marked)
  linarith

/-- Ratio form of `successorEscape_le_two_mul_opponentAbsorptionMass`. -/
theorem ratio_le_opponentAbsorptionMass_of_successorEscape
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η : ℝ) (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hescape : -θ + η ≤ successor marked) :
    η / (2 * M) ≤ quittingRootOpponentAbsorptionMass root marked := by
  have hcharge := successorEscape_le_two_mul_opponentAbsorptionMass
    reward current successor root marked M θ η hreward hsuccessorBound
      hbellman hnash hnegative hescape
  exact (div_le_iff₀ (mul_pos (by norm_num) hM)).2
    (by simpa [mul_comm] using hcharge)

/-- A same-date marked root with marked Quit mass `β` and a successor escape
of size `η` is charged for every player.  Other players see the marked Quit
hazard; the marked player sees the opponent hazard forced by exact Nash. -/
theorem min_le_opponentAbsorptionMass_of_markedHazard_of_successorEscape
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η β : ℝ) (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hescape : -θ + η ≤ successor marked)
    (hmarkedHazard : β ≤ (root marked true).toReal) :
    ∀ who, min β (η / (2 * M)) ≤
      quittingRootOpponentAbsorptionMass root who := by
  intro who
  by_cases hwho : who = marked
  · subst who
    exact (min_le_right β (η / (2 * M))).trans
      (ratio_le_opponentAbsorptionMass_of_successorEscape
        reward current successor root marked M θ η hM hreward
          hsuccessorBound hbellman hnash hnegative hescape)
  · exact (min_le_left β (η / (2 * M))).trans
      (hmarkedHazard.trans
        (quittingProbability_le_opponentAbsorptionMass root
          (Ne.symm hwho)))

/-- **Actual-suffix restart or playerwise-charged jump.**  The carrier is the
genuine Bellman edge `current → successor`, not a re-rooted copy.  If the
marked coordinate stays inside its negative band at `successor`, the marked
construction can restart one calendar stage later.  Otherwise the current
root has a quantitative opponent-absorption charge for every player: other
players see the marked Quit hazard `β`, while the marked player sees the
Nash-forced opponent charge `η/(2M)`.

This is the local jump-or-strict-time rule.  The charged edge still has to be
retained in a compatible recurrent segment or consumed by a separately
proved local discharge; it is not itself asserted to be an equilibrium. -/
theorem markedNegative_advance_or_playerwiseChargedJump
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η β : ℝ) (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hmarkedHazard : β ≤ (root marked true).toReal) :
    successor marked ≤ -θ + η ∨
      ∀ who, min β (η / (2 * M)) ≤
        quittingRootOpponentAbsorptionMass root who := by
  by_cases hadvance : successor marked ≤ -θ + η
  · exact Or.inl hadvance
  · right
    exact min_le_opponentAbsorptionMass_of_markedHazard_of_successorEscape
      reward current successor root marked M θ η β hM hreward
        hsuccessorBound hbellman hnash hnegative (le_of_not_ge hadvance)
        hmarkedHazard

/-- With positive marked mass and a positive escape budget, the charged-jump
branch contracts every player's one-stage opponent clock. -/
theorem opponentAbsorptionMass_pos_of_chargedJump
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η β : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hβ : 0 < β)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hescape : -θ + η ≤ successor marked)
    (hmarkedHazard : β ≤ (root marked true).toReal) :
    ∀ who, 0 < quittingRootOpponentAbsorptionMass root who := by
  have hcharge :=
    min_le_opponentAbsorptionMass_of_markedHazard_of_successorEscape
      reward current successor root marked M θ η β hM hreward
        hsuccessorBound hbellman hnash hnegative hescape hmarkedHazard
  have hratio : 0 < η / (2 * M) :=
    div_pos hη (mul_pos (by norm_num) hM)
  intro who
  exact (lt_min hβ hratio).trans_le (hcharge who)

end GameTheory
