/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair
import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification

/-!
# Cap--Nash endpoint transport for literal terminal profiles

An actual behavior profile has two terminal coordinates: its prescribed payoff
and its coordinatewise all-behavior best-response cap.  Selecting a one-stage
mixed Nash root against the cap vector, then executing the original profile
after all Continue, scales every literal debt by the joint Continue mass.

This exact cancellation turns near-minimality of total literal debt into a
small-absorption estimate.  A sharp playerwise joining-loss bound then shows
that every solo endpoint nearly lies below the cap.  The final estimate
transports a singleton gap at any comparison vector to positive literal debt
of the actual profile.  No joint realization of the cap vector is asserted or
used.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Exact cap--Nash prefix scaling -/

/-- Prefixing an abstract semantic pair by an exact Nash root selected against
its envelope scales each debt coordinate by the joint Continue mass.  The
envelope need not be jointly realizable. -/
theorem quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward pair.2 0 root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebt pair who := by
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [hquit, hcontinue,
    ← quittingRootSuccessorPayoff_eq_max_of_isZeroNash
      reward pair.2 root who hnash,
    quittingRootSuccessorPayoff_sub_eq_continueMass_mul]

/-- Literal specialization of exact cap--Nash debt scaling.  The root is
selected against the continuation's coordinatewise unilateral cap, while the
profile actually executed after all Continue remains the common continuation.
-/
theorem quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      quittingStationaryContinueMass root *
        quittingTerminalDeviationDebt reward continuation who := by
  have hpair := quittingTerminalSemanticPair_rootThenContinuation
    reward root continuation hM hreward
  have hsemantic :=
    quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) (quittingTerminalSemanticPair reward continuation)
      root who hnash
  rw [← hpair] at hsemantic
  exact hsemantic

/-- Total literal debt obeys the same exact cap--Nash scaling. -/
theorem quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    quittingTerminalDebtSum reward
        (quittingRootThenContinuationProfile reward root continuation) =
      quittingStationaryContinueMass root *
        quittingTerminalDebtSum reward continuation := by
  unfold quittingTerminalDebtSum
  simp_rw [quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
    (reward := reward) root continuation _ hM hreward hnash]
  rw [Finset.mul_sum]

/-! ## The actual-profile total-debt infimum -/

/-- Infimum of total literal debt over executable behavior profiles. -/
def quittingTerminalDebtSumInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  sInf (Set.range (quittingTerminalDebtSum reward))

theorem bddBelow_range_quittingTerminalDebtSum
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    BddBelow (Set.range (quittingTerminalDebtSum reward)) := by
  refine ⟨0, ?_⟩
  rintro total ⟨profile, rfl⟩
  unfold quittingTerminalDebtSum
  exact Finset.sum_nonneg fun player _ =>
    quittingTerminalDeviationDebt_nonneg reward profile player hM hreward

/-- The total-debt infimum lies below every actual profile. -/
theorem quittingTerminalDebtSumInf_le
    (profile : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalDebtSumInf reward ≤
      quittingTerminalDebtSum reward profile := by
  exact csInf_le (bddBelow_range_quittingTerminalDebtSum
    (reward := reward) hM hreward) ⟨profile, rfl⟩

/-- Exact cap--Nash scaling and the literal infimum force positive joint
Continue mass whenever the infimum is positive. -/
theorem capNash_continueMass_pos_of_debtSumInf_pos
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    0 < quittingStationaryContinueMass root := by
  have hinfLe := quittingTerminalDebtSumInf_le
    (reward := reward)
    (quittingRootThenContinuationProfile reward root continuation)
    hM hreward
  rw [quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
    (reward := reward) root continuation hM hreward hnash] at hinfLe
  have hcontinueNonneg := quittingStationaryContinueMass_nonneg root
  have hdebtNonneg : 0 ≤ quittingTerminalDebtSum reward continuation := by
    unfold quittingTerminalDebtSum
    exact Finset.sum_nonneg fun player _ =>
      quittingTerminalDeviationDebt_nonneg reward continuation player hM hreward
  nlinarith

/-- The literal total-debt infimum lies below the cap--Nash scaled debt. -/
theorem debtSumInf_le_continueMass_mul_debtSum_of_capNash
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    quittingTerminalDebtSumInf reward ≤
      quittingStationaryContinueMass root *
        quittingTerminalDebtSum reward continuation := by
  have hinfLe := quittingTerminalDebtSumInf_le
    (reward := reward)
    (quittingRootThenContinuationProfile reward root continuation)
    hM hreward
  rwa [quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
    (reward := reward) root continuation hM hreward hnash] at hinfLe

/-- Division-free absorption estimate: absorbed mass times current total debt
is paid entirely by excess above the global actual-profile infimum. -/
theorem capNash_absorptionMass_mul_debtSum_le_debtExcess
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    quittingRootAbsorptionMass root *
        quittingTerminalDebtSum reward continuation ≤
      quittingTerminalDebtSum reward continuation -
        quittingTerminalDebtSumInf reward := by
  have hinfLe := debtSumInf_le_continueMass_mul_debtSum_of_capNash
    (reward := reward) root continuation hM hreward hnash
  unfold quittingRootAbsorptionMass
  nlinarith

/-- Ratio form of the division-free absorption estimate. -/
theorem capNash_absorptionMass_le_debtExcess_div_debtSum
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    quittingRootAbsorptionMass root ≤
      (quittingTerminalDebtSum reward continuation -
          quittingTerminalDebtSumInf reward) /
        quittingTerminalDebtSum reward continuation := by
  have hdebtPos : 0 < quittingTerminalDebtSum reward continuation :=
    hinf.trans_le (quittingTerminalDebtSumInf_le
      (reward := reward) continuation hM hreward)
  exact (le_div_iff₀ hdebtPos).2
    (capNash_absorptionMass_mul_debtSum_le_debtExcess
      (reward := reward) root continuation hM hreward hnash)

/-- Near-minimal total debt bounds cap--Nash absorption odds.  This is the
division form used by endpoint transport. -/
theorem capNash_absorptionOdds_le_debtExcess_div_inf
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    (1 - quittingStationaryContinueMass root) /
        quittingStationaryContinueMass root ≤
      (quittingTerminalDebtSum reward continuation -
          quittingTerminalDebtSumInf reward) /
        quittingTerminalDebtSumInf reward := by
  let prefixed := quittingRootThenContinuationProfile reward root continuation
  have hinfLe := quittingTerminalDebtSumInf_le
    (reward := reward) prefixed hM hreward
  have hscale :=
    quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
      (reward := reward) root continuation hM hreward hnash
  have hcontinue := capNash_continueMass_pos_of_debtSumInf_pos
    (reward := reward) root continuation hM hreward hinf hnash
  dsimp [prefixed] at hinfLe
  rw [hscale] at hinfLe
  apply (div_le_div_iff₀ hcontinue hinf).2
  nlinarith

/-! ## Sharp joining loss -/

/-- Maximum positive loss suffered by `who` upon joining a nonempty coalition
of opponents.  The empty coalition and coalitions already containing `who`
contribute zero, so the definition also covers the one-player game. -/
def quittingJoiningLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Finset ι)) Finset.univ_nonempty fun S =>
    if S.Nonempty ∧ who ∉ S then
      max 0
        (QuittingSureSetOwnerRepair.quittingSetReward reward S who -
          QuittingSureSetOwnerRepair.quittingSetReward reward
            (insert who S) who)
    else 0

theorem quittingJoiningLoss_nonneg (who : ι) :
    0 ≤ quittingJoiningLoss reward who := by
  unfold quittingJoiningLoss
  have hempty : (∅ : Finset ι) ∈
      (Finset.univ : Finset (Finset ι)) := Finset.mem_univ _
  have hle := Finset.le_sup' (s := (Finset.univ : Finset (Finset ι)))
    (fun S => if S.Nonempty ∧ who ∉ S then
      max 0
        (QuittingSureSetOwnerRepair.quittingSetReward reward S who -
          QuittingSureSetOwnerRepair.quittingSetReward reward
            (insert who S) who)
      else 0) hempty
  simpa using hle

/-- Every opponent coalition's joining loss is bounded by the sharp maximum.
-/
theorem quittingSetReward_sub_insert_le_joiningLoss
    (who : ι) (S : Finset ι) (hS : S.Nonempty) (hwho : who ∉ S) :
    QuittingSureSetOwnerRepair.quittingSetReward reward S who -
        QuittingSureSetOwnerRepair.quittingSetReward reward (insert who S) who ≤
      quittingJoiningLoss reward who := by
  let loss : Finset ι → ℝ := fun T =>
    if T.Nonempty ∧ who ∉ T then
      max 0
        (QuittingSureSetOwnerRepair.quittingSetReward reward T who -
          QuittingSureSetOwnerRepair.quittingSetReward reward
            (insert who T) who)
    else 0
  have hmax :
      QuittingSureSetOwnerRepair.quittingSetReward reward S who -
          QuittingSureSetOwnerRepair.quittingSetReward reward
            (insert who S) who ≤ loss S := by
    dsimp [loss]
    rw [if_pos ⟨hS, hwho⟩]
    exact le_max_right _ _
  have hsup : loss S ≤
      Finset.sup' (Finset.univ : Finset (Finset ι))
        Finset.univ_nonempty loss :=
    Finset.le_sup' loss (Finset.mem_univ S)
  exact hmax.trans hsup

/-- Under an `M` reward bound, the sharp joining loss is at most `2M`. -/
theorem quittingJoiningLoss_le_two_mul
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingJoiningLoss reward who ≤ 2 * M := by
  unfold quittingJoiningLoss
  apply Finset.sup'_le
  intro S hS
  split_ifs with hvalid
  · apply max_le
    · linarith
    · rcases hvalid with ⟨hSNonempty, hwho⟩
      have hfirst :
          |QuittingSureSetOwnerRepair.quittingSetReward reward S who| ≤ M := by
        simpa [QuittingSureSetOwnerRepair.quittingSetReward, hSNonempty] using
          hreward ⟨S, hSNonempty⟩ who
      have hinsertNonempty : (insert who S).Nonempty :=
        Finset.insert_nonempty who S
      have hsecond :
          |QuittingSureSetOwnerRepair.quittingSetReward reward
              (insert who S) who| ≤ M := by
        simpa [QuittingSureSetOwnerRepair.quittingSetReward,
          hinsertNonempty] using
          hreward ⟨insert who S, hinsertNonempty⟩ who
      have hfirstUpper := le_of_abs_le hfirst
      have hsecondLower := neg_le_of_abs_le hsecond
      linarith
  · linarith

/-- The expected effect of joining opponent quitters is bounded below by the
negative sharp joining loss times opponent absorption. -/
theorem neg_joiningLoss_mul_opponentAbsorption_le_joiningContribution
    (root : ι → PMF Bool) (who : ι) :
    -(quittingJoiningLoss reward who *
        quittingRootOpponentAbsorptionMass root who) ≤
      quittingOutsiderJoiningContribution reward root who := by
  let opponentRoot := Function.update root who (PMF.pure false)
  let advantage := quittingTerminalOpponentAdvantage reward who
  let indicator : (ι → Bool) → ℝ := fun action =>
    if (quittingQuitters action).Nonempty then 1 else 0
  have hpoint : ∀ action : ι → Bool,
      advantage action ≤ quittingJoiningLoss reward who * indicator action := by
    intro action
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp only [indicator, if_pos hquit, mul_one]
      by_cases hown : action who = true
      · have hupdate : Function.update action who true = action := by
          funext player
          by_cases hplayer : player = who
          · subst player
            simp [hown]
          · simp [Function.update_of_ne hplayer]
        change quittingTerminalOpponentAdvantage reward who action ≤
          quittingJoiningLoss reward who
        have hadvantage :
            quittingTerminalOpponentAdvantage reward who action = 0 := by
          unfold quittingTerminalOpponentAdvantage
          rw [hupdate]
          simp [quittingRootPayoff, hquit]
        rw [hadvantage]
        exact quittingJoiningLoss_nonneg (reward := reward) who
      · have hownFalse : action who = false := Bool.eq_false_of_not_eq_true hown
        have hwho : who ∉ quittingQuitters action := by
          simp [quittingQuitters, hownFalse]
        have hupdated := quittingQuitters_update_true_of_apply_false action who
        change quittingTerminalOpponentAdvantage reward who action ≤
          quittingJoiningLoss reward who
        unfold quittingTerminalOpponentAdvantage quittingRootPayoff
        rw [dif_pos hquit]
        have hupdatedNonempty :
            (quittingQuitters (Function.update action who true)).Nonempty := by
          rw [hupdated]
          exact Finset.insert_nonempty who _
        rw [dif_pos hupdatedNonempty]
        have hloss := quittingSetReward_sub_insert_le_joiningLoss
          (reward := reward) who (quittingQuitters action) hquit hwho
        simpa [QuittingSureSetOwnerRepair.quittingSetReward,
          hquit, hupdatedNonempty, hupdated] using hloss
    · simp only [indicator, if_neg hquit, mul_zero]
      change quittingTerminalOpponentAdvantage reward who action ≤ 0
      rw [quittingTerminalOpponentAdvantage_eq_zero_of_quitters_not_nonempty
        reward who action hquit]
  have hmono := expect_mono (pmfPi opponentRoot) advantage
    (fun action => quittingJoiningLoss reward who * indicator action) hpoint
  have hright :
      expect (pmfPi opponentRoot)
          (fun action => quittingJoiningLoss reward who * indicator action) =
        quittingJoiningLoss reward who *
          quittingRootOpponentAbsorptionMass root who := by
    rw [expect_const_mul]
    change quittingJoiningLoss reward who *
        expect (pmfPi opponentRoot) indicator =
      quittingJoiningLoss reward who *
        quittingRootAbsorptionMass opponentRoot
    rw [show expect (pmfPi opponentRoot) indicator =
        quittingRootAbsorptionMass opponentRoot by
      simpa [indicator] using
        expect_quittingNonemptyIndicator_eq_absorptionMass opponentRoot]
  unfold quittingOutsiderJoiningContribution
  change -(quittingJoiningLoss reward who *
      quittingRootOpponentAbsorptionMass root who) ≤
    -expect (pmfPi opponentRoot) advantage
  rw [← hright]
  exact neg_le_neg hmono

/-! ## Nash endpoint and transport estimates -/

/-- A positive-survival exact Nash root nearly dominates the player's solo
endpoint.  This generic statement accepts an arbitrary auxiliary tail, so it
also applies to shifted-cap Nash selections. -/
theorem singleton_sub_tail_le_joiningLoss_mul_absorptionOdds_of_nash
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hcontinue : 0 < quittingStationaryContinueMass root)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    reward (quittingSingletonTerminal who) who - tail who ≤
      quittingJoiningLoss reward who *
        ((1 - quittingStationaryContinueMass root) /
          quittingStationaryContinueMass root) := by
  let ownContinue := (root who false).toReal
  let opponentContinue := quittingRootOpponentContinueMass root who
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root who
  have hownContinue : 0 < ownContinue :=
    quittingRoot_continueProbability_pos_of_continueMass_pos
      root hcontinue who
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mpr hnash
  have hendpointNonpos :
      quittingRootEndpointDifference reward tail root who ≤ 0 := by
    exact nonpos_of_mul_nonpos_left
      (by simpa [mul_comm] using (hendpoint who).1) hownContinue
  have hcontinueLeOpponent :
      quittingStationaryContinueMass root ≤ opponentContinue := by
    exact quittingStationaryContinueMass_le_update_pure_false root who
  have hopponentContinue : 0 < opponentContinue :=
    hcontinue.trans_le hcontinueLeOpponent
  have hopponentContinueLeOne : opponentContinue ≤ 1 :=
    quittingRootOpponentContinueMass_le_one root who
  have habsorption : opponentAbsorption = 1 - opponentContinue := by
    have hcomplement :=
      quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root who
    dsimp [opponentAbsorption, opponentContinue] at *
    linarith
  have hjoining :=
    neg_joiningLoss_mul_opponentAbsorption_le_joiningContribution
      (reward := reward) root who
  have hdecomposition :=
    quittingRootEndpointDifference_eq_outsiderNever reward tail root who
  change quittingRootEndpointDifference reward tail root who =
      (1 - opponentAbsorption) *
          (reward (quittingSingletonTerminal who) who - tail who) +
        quittingOutsiderJoiningContribution reward root who at hdecomposition
  rw [show 1 - opponentAbsorption = opponentContinue by linarith]
      at hdecomposition
  change -(quittingJoiningLoss reward who * opponentAbsorption) ≤
      quittingOutsiderJoiningContribution reward root who at hjoining
  have hraw : opponentContinue *
      (reward (quittingSingletonTerminal who) who - tail who) ≤
        quittingJoiningLoss reward who * opponentAbsorption := by
    nlinarith [hendpointNonpos, hjoining, hdecomposition]
  have hlocal : reward (quittingSingletonTerminal who) who - tail who ≤
      quittingJoiningLoss reward who *
        (opponentAbsorption / opponentContinue) := by
    rw [show quittingJoiningLoss reward who *
        (opponentAbsorption / opponentContinue) =
      (quittingJoiningLoss reward who * opponentAbsorption) /
        opponentContinue by field_simp]
    apply (le_div_iff₀ hopponentContinue).2
    simpa [mul_comm] using hraw
  have hratio : opponentAbsorption / opponentContinue ≤
      (1 - quittingStationaryContinueMass root) /
        quittingStationaryContinueMass root := by
    rw [habsorption]
    apply (div_le_div_iff₀ hopponentContinue hcontinue).2
    nlinarith
  exact hlocal.trans (mul_le_mul_of_nonneg_left hratio
    (quittingJoiningLoss_nonneg (reward := reward) who))

/-- Exact Nash against `cap - shift` yields the shifted endpoint margin used
by auxiliary-target consumers. -/
theorem cap_sub_singleton_ge_shift_sub_joiningLoss_mul_absorptionOdds
    (cap shift : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hcontinue : 0 < quittingStationaryContinueMass root)
    (hnash : IsεQuittingRootNash reward (cap - shift) 0 root) :
    cap who - reward (quittingSingletonTerminal who) who ≥
      shift who - quittingJoiningLoss reward who *
        ((1 - quittingStationaryContinueMass root) /
          quittingStationaryContinueMass root) := by
  have hendpoint :=
    singleton_sub_tail_le_joiningLoss_mul_absorptionOdds_of_nash
      (reward := reward) (cap - shift) root who hcontinue hnash
  dsimp only [Pi.sub_apply] at hendpoint
  linarith

/-- Every actual profile's solo endpoint lies below its unilateral cap up to
the sharp joining loss times relative excess above the total-debt infimum. -/
theorem singleton_sub_cap_le_joiningLoss_mul_debtExcess_div_inf
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward) :
    reward (quittingSingletonTerminal who) who -
        quittingContinuationBestResponseValue reward profile who ≤
      quittingJoiningLoss reward who *
        ((quittingTerminalDebtSum reward profile -
            quittingTerminalDebtSumInf reward) /
          quittingTerminalDebtSumInf reward) := by
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash
    (reward := reward)
    (fun player => quittingContinuationBestResponseValue reward profile player)
  have hcontinue := capNash_continueMass_pos_of_debtSumInf_pos
    (reward := reward) root profile hM hreward hinf hnash
  have hendpoint :=
    singleton_sub_tail_le_joiningLoss_mul_absorptionOdds_of_nash
      (reward := reward)
      (fun player => quittingContinuationBestResponseValue reward profile player)
      root who hcontinue hnash
  have hodds := capNash_absorptionOdds_le_debtExcess_div_inf
    (reward := reward) root profile hM hreward hinf hnash
  exact hendpoint.trans (mul_le_mul_of_nonneg_left hodds
    (quittingJoiningLoss_nonneg (reward := reward) who))

/-- Cap--Nash endpoint transport to a literal positive-debt coordinate. -/
theorem terminalDebt_ge_endpointGap_sub_error_sub_joiningLossExcess
    (profile : (quittingGame reward).BehaviorProfile)
    (comparison : Payoff ι) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward) :
    reward (quittingSingletonTerminal who) who - comparison who -
        |quittingTerminalPayoff reward profile who - comparison who| -
        quittingJoiningLoss reward who *
          ((quittingTerminalDebtSum reward profile -
              quittingTerminalDebtSumInf reward) /
            quittingTerminalDebtSumInf reward) ≤
      quittingTerminalDeviationDebt reward profile who := by
  have hcap := singleton_sub_cap_le_joiningLoss_mul_debtExcess_div_inf
    (reward := reward) profile who hM hreward hinf
  have herror : quittingTerminalPayoff reward profile who -
      comparison who ≤
        |quittingTerminalPayoff reward profile who - comparison who| := by
    exact le_abs_self _
  unfold quittingTerminalDeviationDebt
  linarith

end GameTheory
