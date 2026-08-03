/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingStationaryBestResponse

/-!
# Exceptional-tail stationary fallback

This file formalizes the deterministic assembly at the exceptional seam.
A solo stationary root, at which only one player has positive quit hazard,
has terminal payoff equal to the corresponding singleton reward.  Its exact
unilateral caps are Quit versus Never for the exceptional player and Quit-now
versus waiting for solo absorption for every other player.

The capstone exposes the two probabilistic inputs as hypotheses: concentration
of the tail payoff near the singleton reward, and stability of an immediate-
Quit payoff after deleting the other current hazards.  Together with tail
Nash inequalities, the resulting stationary profile is a terminal
`β + 4Mη`-Nash profile.  A filter-level corollary selects errors approaching
`β` when `η` tends to zero.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A stationary root at which only `owner` may quit. -/
def quittingSoloStationaryRoot (owner : ι) (hazard : PMF Bool) :
    ι → PMF Bool :=
  Function.update (fun _ => PMF.pure false) owner hazard

/-- Joint action at which only `owner` may take the supplied action. -/
def quittingSoloAction (owner : ι) (action : Bool) : ι → Bool :=
  Function.update (fun _ => false) owner action

/-- Terminal reward when `owner` is the unique quitter. -/
def quittingSoloReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) : Payoff ι :=
  reward ⟨{owner}, Finset.singleton_nonempty owner⟩

omit [Fintype ι] in
@[simp] theorem update_quittingSoloStationaryRoot_owner
    (owner : ι) (first second : PMF Bool) :
    Function.update (quittingSoloStationaryRoot owner first) owner second =
      quittingSoloStationaryRoot owner second := by
  simp [quittingSoloStationaryRoot]

omit [Fintype ι] in
@[simp] theorem update_quittingSoloStationaryRoot_other
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    Function.update (quittingSoloStationaryRoot owner hazard) other
        (PMF.pure false) =
      quittingSoloStationaryRoot owner hazard := by
  funext player
  by_cases hp : player = other
  · subst player
    simp [quittingSoloStationaryRoot, hne]
  · simp [Function.update_of_ne hp]

theorem pmfPi_quittingSoloStationaryRoot
    (owner : ι) (hazard : PMF Bool) :
    pmfPi (quittingSoloStationaryRoot owner hazard) =
      hazard.bind (fun action => PMF.pure (quittingSoloAction owner action)) := by
  rw [quittingSoloStationaryRoot, pmfPi_update_bind]
  apply congrArg (PMF.bind hazard)
  funext action
  rw [show Function.update (fun _ : ι => PMF.pure false) owner
      (PMF.pure action) =
      fun player => PMF.pure (quittingSoloAction owner action player) by
        funext player
        by_cases hp : player = owner
        · subst player
          simp [quittingSoloAction]
        · simp [quittingSoloAction, Function.update_of_ne hp]]
  exact pmfPi_pure _

theorem expect_quittingSoloStationaryRoot
    (owner : ι) (hazard : PMF Bool) (value : (ι → Bool) → ℝ) :
    expect (pmfPi (quittingSoloStationaryRoot owner hazard)) value =
      (hazard false).toReal * value (quittingSoloAction owner false) +
        (hazard true).toReal * value (quittingSoloAction owner true) := by
  rw [pmfPi_quittingSoloStationaryRoot, expect_bind]
  simp only [expect_pure]
  rw [expect_eq_sum, Fintype.sum_bool]
  ring

omit [Fintype ι] in
@[simp] theorem quittingSoloAction_false (owner : ι) :
    quittingSoloAction owner false = quittingAllContinueAction := by
  funext player
  simp [quittingSoloAction, quittingAllContinueAction]

@[simp] theorem quittingQuitters_soloAction_true (owner : ι) :
    quittingQuitters (quittingSoloAction owner true) = {owner} := by
  ext player
  by_cases hp : player = owner
  · subst player
    simp [quittingSoloAction, quittingQuitters]
  · simp [quittingSoloAction, quittingQuitters, hp]

@[simp] theorem quittingStationaryContinueMass_solo
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryContinueMass
        (quittingSoloStationaryRoot owner hazard) =
      (hazard false).toReal := by
  have hne : quittingAllContinueAction ≠
      quittingSoloAction owner true := by
    intro h
    have howner := congrFun h owner
    simp [quittingAllContinueAction, quittingSoloAction] at howner
  unfold quittingStationaryContinueMass
  rw [pmfPi_quittingSoloStationaryRoot]
  simp [quittingSoloAction_false, hne]

theorem quittingRootAbsorbingContribution_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) (hazard : PMF Bool) :
    quittingRootAbsorbingContribution reward
        (quittingSoloStationaryRoot owner hazard) who =
      (hazard true).toReal * quittingSoloReward reward owner who := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_quittingSoloStationaryRoot]
  simp [quittingRootPayoff, quittingSoloReward]

theorem quittingTerminalPayoff_soloStationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner hazard)) who =
      quittingSoloReward reward owner who := by
  have hsum : (hazard false).toReal + (hazard true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one hazard
  have hcontracts : quittingStationaryContinueMass
      (quittingSoloStationaryRoot owner hazard) < 1 := by
    rw [quittingStationaryContinueMass_solo]
    linarith
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward _ who hcontracts,
    quittingRootAbsorbingContribution_solo,
    quittingStationaryContinueMass_solo]
  have hne : (hazard true).toReal ≠ 0 := ne_of_gt hpositive
  have hden : 1 - (hazard false).toReal = (hazard true).toReal := by
    linarith
  rw [hden]
  field_simp [hne]

@[simp] theorem quittingStationaryFixedOpponentsQuitValue_solo_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingSoloStationaryRoot owner hazard) owner =
      quittingSoloReward reward owner owner := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
  rw [update_quittingSoloStationaryRoot_owner,
    quittingRootAbsorbingContribution_solo]
  simp [quittingSoloReward]

@[simp] theorem quittingStationaryFixedOpponentsContinueReward_solo_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingSoloStationaryRoot owner hazard) owner = 0 := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  rw [update_quittingSoloStationaryRoot_owner,
    quittingRootAbsorbingContribution_solo]
  simp

@[simp] theorem quittingStationaryFixedOpponentsContinueMass_solo_owner
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSoloStationaryRoot owner hazard) owner = 1 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_quittingSoloStationaryRoot_owner,
    quittingStationaryContinueMass_solo]
  simp

@[simp] theorem quittingStationaryUnilateralCap_solo_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryUnilateralCap reward
        (quittingSoloStationaryRoot owner hazard) owner =
      max (quittingSoloReward reward owner owner) 0 := by
  simp [quittingStationaryUnilateralCap,
    quittingStationarySelectedCap, quittingStationaryNeverValue]

@[simp] theorem quittingStationaryFixedOpponentsContinueReward_solo_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard true).toReal * quittingSoloReward reward owner other := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  rw [update_quittingSoloStationaryRoot_other hne,
    quittingRootAbsorbingContribution_solo]

@[simp] theorem quittingStationaryFixedOpponentsContinueMass_solo_other
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard false).toReal := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_quittingSoloStationaryRoot_other hne,
    quittingStationaryContinueMass_solo]

theorem quittingStationaryUnilateralCap_solo_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal) :
    quittingStationaryUnilateralCap reward
        (quittingSoloStationaryRoot owner hazard) other =
      max
        (quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner hazard) other)
        (quittingSoloReward reward owner other) := by
  have hsum : (hazard false).toReal + (hazard true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one hazard
  have hneHazard : (hazard true).toReal ≠ 0 := ne_of_gt hpositive
  unfold quittingStationaryUnilateralCap
  rw [quittingStationaryFixedOpponentsContinueReward_solo_other
      reward hne hazard,
    quittingStationaryFixedOpponentsContinueMass_solo_other hne hazard]
  unfold quittingStationarySelectedCap quittingStationaryNeverValue
  congr 1
  have hden : 1 - (hazard false).toReal = (hazard true).toReal := by
    linarith
  rw [hden]
  field_simp [hneHazard]

theorem quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSoloStationaryRoot owner hazard) other < 1 := by
  rw [quittingStationaryFixedOpponentsContinueMass_solo_other hne]
  have hsum : (hazard false).toReal + (hazard true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one hazard
  linarith

/-- When the prescribed stationary root only lets `owner` quit, arbitrary
deviations by `owner` face all-continuing opponents and hence are bounded by
Quit-versus-Never. -/
theorem quittingTerminalPayoff_update_solo_owner_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingStationaryProfile reward
            (quittingSoloStationaryRoot owner hazard)) owner deviation) owner ≤
      max 0 (quittingSoloReward reward owner owner) := by
  have hprofiles :
      Function.update
          (quittingStationaryProfile reward
            (quittingSoloStationaryRoot owner hazard)) owner deviation =
        Function.update (quittingAlwaysContinueProfile reward) owner
          deviation := by
    funext player time history
    by_cases hp : player = owner
    · subst player
      simp
    · simp [quittingStationaryProfile, quittingSoloStationaryRoot,
        quittingAlwaysContinueProfile, hp,
        StochasticGame.stationaryBehaviorProfile]
      rfl
  rw [hprofiles]
  exact quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
    reward owner deviation

/-- The two `2Mη` estimates and the tail Nash inequalities assemble into the
stationary `β + 4Mη` exceptional fallback.  The concentration and root-
deletion estimates are explicit hypotheses so their probabilistic adapters
can be proved independently. -/
theorem isεAsymptoticNash_soloStationary_of_tail_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (originalRoot : ι → PMF Bool) (tailValue : Payoff ι)
    (owner : ι) {β M η : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hpositive : 0 < (originalRoot owner true).toReal)
    (hconcentration : ∀ who,
      |tailValue who - quittingSoloReward reward owner who| ≤ 2 * M * η)
    (hneverNash : -M * η ≤ tailValue owner + β)
    (hquitNash : ∀ who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward originalRoot who ≤
        tailValue who + β)
    (hdelete : ∀ who, who ≠ owner →
      |quittingStationaryFixedOpponentsQuitValue reward originalRoot who -
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner (originalRoot owner)) who| ≤
        2 * M * η) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (β + 4 * M * η)
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner (originalRoot owner))) := by
  let soloRoot := quittingSoloStationaryRoot owner (originalRoot owner)
  let error := β + 4 * M * η
  have hMη : 0 ≤ M * η := mul_nonneg hM hη
  have herror : 0 ≤ error := by
    dsimp only [error]
    positivity
  have hsoloOwnerLower :
      -β - 3 * M * η ≤ quittingSoloReward reward owner owner := by
    have hcloseUpper := (abs_le.mp (hconcentration owner)).2
    linarith
  have hsoloQuitUpper : ∀ who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward soloRoot who ≤
        quittingSoloReward reward owner who + error := by
    intro who hne
    have hdeleteLower := (abs_le.mp (hdelete who hne)).1
    have htailUpper := (abs_le.mp (hconcentration who)).2
    have hquit := hquitNash who hne
    dsimp only [soloRoot, error] at hdeleteLower ⊢
    linarith
  intro who deviation
  by_cases hwho : who = owner
  · subst who
    have hcap := quittingTerminalPayoff_update_solo_owner_le
      reward owner (originalRoot owner) deviation
    rw [quittingTerminalPayoff_soloStationary reward owner owner
      (originalRoot owner) hpositive]
    apply hcap.trans
    apply max_le
    · nlinarith [hMη]
    · exact le_add_of_nonneg_right herror
  · have hcap :=
      quittingTerminalPayoff_update_stationary_le_unilateralCap
        reward soloRoot who deviation
        (quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
          hwho (originalRoot owner) hpositive)
    rw [quittingTerminalPayoff_soloStationary reward owner who
      (originalRoot owner) hpositive]
    apply hcap.trans
    rw [quittingStationaryUnilateralCap_solo_other reward hwho
      (originalRoot owner) hpositive]
    apply max_le
    · exact hsoloQuitUpper who hwho
    · exact le_add_of_nonneg_right herror

/-- If the opponent-tail error tends to zero and positive owner hazards occur
arbitrarily late, the stationary solo fallbacks can be selected with error
arbitrarily close to `β`. -/
theorem exists_isεAsymptoticNash_soloStationary_of_tendsto_tail_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (tailValue : ℕ → Payoff ι)
    (owner : ι) (η : ℕ → ℝ) {β M : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hη : ∀ time, 0 ≤ η time)
    (hηzero : Tendsto η atTop (nhds 0))
    (hpositiveLate : ∀ threshold,
      ∃ time ≥ threshold, 0 < (roots time owner true).toReal)
    (hconcentration : ∀ time who,
      |tailValue time who - quittingSoloReward reward owner who| ≤
        2 * M * η time)
    (hneverNash : ∀ time,
      -M * η time ≤ tailValue time owner + β)
    (hquitNash : ∀ time who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
        tailValue time who + β)
    (hdelete : ∀ time who, who ≠ owner →
      |quittingStationaryFixedOpponentsQuitValue reward (roots time) who -
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner (roots time owner)) who| ≤
        2 * M * η time) :
    ∀ ζ > 0, ∃ time,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (β + ζ)
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner (roots time owner))) := by
  intro ζ hζ
  have hscaled : Tendsto (fun time => 4 * M * η time)
      atTop (nhds 0) := by
    simpa using hηzero.const_mul (4 * M)
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hscaled) ζ hζ
  obtain ⟨time, htime, hpositive⟩ := hpositiveLate threshold
  have hclose := hthreshold time htime
  rw [Real.dist_eq, sub_zero] at hclose
  have herror : 4 * M * η time ≤ ζ :=
    (le_abs_self (4 * M * η time)).trans hclose.le
  refine ⟨time, ?_⟩
  have hnash := isεAsymptoticNash_soloStationary_of_tail_bounds
    reward (roots time) (tailValue time) owner hβ hM (hη time)
      hpositive (hconcentration time) (hneverNash time)
      (hquitNash time) (hdelete time)
  intro who deviation
  have herror' : β + 4 * M * η time ≤ β + ζ := by linarith
  exact (hnash who deviation).trans (add_le_add_right herror' _)

end GameTheory
