/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.StoppingLawMixture
import UniformEquilibrium.Quitting.Debt.Marked.FencePacket
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration

/-!
# Terminal-law retention under complete stopping-law mixtures

The behavioral hazard realizing a convex mixture of two unilateral stopping
laws also realizes the same convex mixture of every chronological terminal
coalition atom.  If the selected player belongs to the coalition, the relevant
player factor is stopping mass; if not, it is next-date survival.  Both are
affine under the reconstructed hazard.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open Math.Probability.DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Joint survival under a unilateral hazard factors into opponent survival
and that hazard's own survival. -/
theorem quittingJointSurvivalWeight_update_eq_opponent_mul_hazardSurvival
    (roots : ℕ → iota → PMF Bool) (who : iota)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingJointSurvivalWeight
        (quittingRootSequenceUpdate roots who hazard) 0 cutoff =
      quittingOpponentSurvivalWeight roots who 0 cutoff *
        quittingHazardSurvival hazard cutoff := by
  rw [quittingJointSurvivalWeight_eq_prod,
    quittingOpponentSurvivalWeight, quittingHazardSurvival_eq_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro time _htime
  simp only [Nat.zero_add, quittingRootSequenceUpdate]
  rw [quittingStationaryContinueMass_eq_forcedContinue_mul_own
    (Function.update (roots time) who (hazard time)) who]
  simp [quittingFixedOpponentsContinueMass, Function.update_idem]

/-- A coalition probability under an updated marginal is the selected
action probability times the same coalition probability after forcing that
action. -/
theorem quittingRootCoalitionMass_update_eq_actionProbability_mul_forced
    (root : iota → PMF Bool) (who : iota) (marginal : PMF Bool)
    (coalition : Finset iota) :
    quittingRootCoalitionMass (Function.update root who marginal) coalition =
      (marginal (decide (who ∈ coalition))).toReal *
        quittingRootCoalitionMass
          (Function.update root who (PMF.pure (decide (who ∈ coalition))))
          coalition := by
  let action := decide (who ∈ coalition)
  have hfactor := quittingRootCoalitionMass_eq_actionProbability_mul_routed
    (Function.update root who marginal) coalition who action
  have hrouted : quittingPureEndpointRoutedCoalition coalition who action =
      coalition := by
    by_cases hwho : who ∈ coalition
    · simp [action, hwho, quittingPureEndpointRoutedCoalition]
    · simp [action, hwho, quittingPureEndpointRoutedCoalition]
  rw [hrouted] at hfactor
  by_cases hwho : who ∈ coalition
  · simpa [action, hwho, Function.update_idem] using hfactor
  · simpa [action, hwho, Function.update_idem] using hfactor

/-- Finite survival is affine under the reconstructed Boolean mixture
hazard. -/
theorem quittingHazardSurvival_convexMix
    (source target : ℕ → PMF Bool) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (cutoff : ℕ) :
    quittingHazardSurvival
        (BooleanHazard.convexMix source target lambda hlambda0 hlambda1)
        cutoff =
      (1 - lambda) * quittingHazardSurvival source cutoff +
        lambda * quittingHazardSurvival target cutoff := by
  change Math.survivalProduct
      (continueProbability
        (BooleanHazard.convexMix source target lambda hlambda0 hlambda1))
      0 cutoff =
    (1 - lambda) * Math.survivalProduct (continueProbability source) 0 cutoff +
      lambda * Math.survivalProduct (continueProbability target) 0 cutoff
  rw [BooleanHazard.survival_eq_scalar,
    BooleanHazard.survival_eq_scalar,
    BooleanHazard.survival_eq_scalar,
    BooleanHazard.toScalar_convexMix,
    ScalarHazard.convexMix_survival]
  rfl

/-- The opponent contribution to a chronological coalition atom after
deleting one player's stopping factor. -/
def quittingStageCoalitionOpponentFactor
    (roots : ℕ → iota → PMF Bool) (who : iota) (time : ℕ)
    (terminal : {S : Finset iota // S.Nonempty}) : ℝ :=
  quittingOpponentSurvivalWeight roots who 0 time *
    quittingRootCoalitionMass
      (Function.update (roots time) who
        (PMF.pure (decide (who ∈ terminal.val)))) terminal.val

/-- Exact chronological atom factorization for an arbitrary unilateral
behavior strategy. -/
theorem quittingStageCoalitionMass_update_eq_opponentFactor_mul
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (strategy : (quittingGame reward).BehaviorStrategy who)
    (time : ℕ) (terminal : {S : Finset iota // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (Function.update profile who strategy) time terminal =
      quittingStageCoalitionOpponentFactor
          (quittingProfileLiveRoot reward profile) who time terminal *
        (if who ∈ terminal.val
          then quittingHazardStopMass
            (quittingBehaviorLiveHazard reward strategy) time
          else quittingHazardSurvival
            (quittingBehaviorLiveHazard reward strategy) (time + 1)) := by
  let roots := quittingProfileLiveRoot reward profile
  let hazard := quittingBehaviorLiveHazard reward strategy
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingJointSurvivalWeight_update_eq_opponent_mul_hazardSurvival]
  change
    (quittingOpponentSurvivalWeight roots who 0 time *
        quittingHazardSurvival hazard time) *
      quittingRootCoalitionMass
        (Function.update (roots time) who (hazard time)) terminal.val = _
  rw [quittingRootCoalitionMass_update_eq_actionProbability_mul_forced]
  unfold quittingStageCoalitionOpponentFactor
  by_cases hwho : who ∈ terminal.val
  · simp only [hwho, decide_true, if_true]
    rw [quittingHazardStopMass_eq_survival_mul_stop]
    ring
  · simp only [hwho, decide_false, if_false]
    rw [quittingHazardSurvival_succ]
    ring

/-- Every chronological terminal atom is exactly affine under a complete
stopping-law mixture. -/
theorem quittingStageCoalitionMass_stoppingLawMixture_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (time : ℕ) (terminal : {S : Finset iota // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingStoppingLawMixtureBehaviorStrategy reward who source target
            lambda hlambda0 hlambda1)) time terminal =
      (1 - lambda) * quittingStageCoalitionMass reward
          (Function.update profile who source) time terminal +
        lambda * quittingStageCoalitionMass reward
          (Function.update profile who target) time terminal := by
  rw [quittingStageCoalitionMass_update_eq_opponentFactor_mul,
    quittingStageCoalitionMass_update_eq_opponentFactor_mul,
    quittingStageCoalitionMass_update_eq_opponentFactor_mul]
  let sourceHazard := quittingBehaviorLiveHazard reward source
  let targetHazard := quittingBehaviorLiveHazard reward target
  simp only [quittingBehaviorLiveHazard_stoppingLawMixture]
  by_cases hwho : who ∈ terminal.val
  · simp only [hwho, if_true, quittingHazardStopMass]
    rw [BooleanHazard.toScalar_convexMix,
      ScalarHazard.convexMix_stopMass]
    unfold ScalarHazard.mixedStopMass
    ring
  · simp only [hwho, if_false]
    rw [quittingHazardSurvival_convexMix]
    ring

/-- In particular, the complete stopping-law mixture retains at least its
`1 - lambda` share of every source chronological atom. -/
theorem one_sub_mul_stageCoalitionMass_le_stoppingLawMixture
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (time : ℕ) (terminal : {S : Finset iota // S.Nonempty}) :
    (1 - lambda) * quittingStageCoalitionMass reward
        (Function.update profile who source) time terminal ≤
      quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingStoppingLawMixtureBehaviorStrategy reward who source target
            lambda hlambda0 hlambda1)) time terminal := by
  rw [quittingStageCoalitionMass_stoppingLawMixture_eq]
  exact le_add_of_nonneg_right
    (mul_nonneg hlambda0 (quittingStageCoalitionMass_nonneg reward _ time terminal))

/-- **Cutoff-free stopping-law reset.**  Mix the prescribed strategy with an
actual approximate best response at the level of their complete stopping
laws.  The resulting literal behavior profile collects `lambda` times the
approximate global best-response gain, contracts the mover's semantic debt
by the corresponding affine formula, and retains at least `1 - lambda` of
every finite chronological coalition window.  No factor depending on the
window length appears. -/
theorem exists_stoppingLawMixture_debtContraction_and_windowRetention
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota)
    (terminal : {S : Finset iota // S.Nonempty}) (cutoff : ℕ)
    (lambda error : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (herror : 0 < error)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M) :
    ∃ bestResponse : (quittingGame reward).BehaviorStrategy who,
      let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
        reward who (profile who) bestResponse lambda hlambda0 hlambda1
      let mixedProfile := Function.update profile who mixedStrategy
      let bestResponseProfile := Function.update profile who bestResponse
      (quittingTerminalSemanticPair reward mixedProfile,
          quittingTerminalOutcomeMass reward mixedProfile) ∈
        quittingTerminalSemanticLawCarrier reward ∧
      lambda *
          (quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) who - error) ≤
        quittingTerminalPayoff reward mixedProfile who -
          quittingTerminalPayoff reward profile who ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward mixedProfile) who =
        (1 - lambda) * quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) who +
          lambda *
            (quittingContinuationBestResponseValue reward profile who -
              quittingTerminalPayoff reward bestResponseProfile who) ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward mixedProfile) who ≤
        (1 - lambda) * quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) who +
          lambda * error ∧
      (1 - lambda) *
          (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time terminal) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward mixedProfile time terminal := by
  obtain ⟨bestResponse, hbestResponse⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward profile who herror hM hreward
  refine ⟨bestResponse, ?_⟩
  dsimp only
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward who (profile who) bestResponse lambda hlambda0 hlambda1
  let mixedProfile := Function.update profile who mixedStrategy
  let bestResponseProfile := Function.update profile who bestResponse
  have hlaw :
      (quittingTerminalSemanticPair reward mixedProfile,
          quittingTerminalOutcomeMass reward mixedProfile) ∈
        quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward mixedProfile
  have hgain := quittingTerminalPayoff_stoppingLawMixture_sub_eq
    reward profile who bestResponse lambda hlambda0 hlambda1 hM hreward
  have hbestResidual :
      quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward bestResponseProfile who ≤ error := by
    dsimp only [bestResponseProfile]
    linarith
  have hgainLower : lambda *
        (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) who - error) ≤
      quittingTerminalPayoff reward mixedProfile who -
        quittingTerminalPayoff reward profile who := by
    dsimp only [mixedProfile, mixedStrategy]
    rw [hgain]
    have hraw : quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who - error ≤
        quittingTerminalPayoff reward bestResponseProfile who -
          quittingTerminalPayoff reward profile who := by
      dsimp only [quittingTerminalSemanticDebt,
        quittingTerminalSemanticPair, bestResponseProfile] at hbestResidual ⊢
      linarith
    exact mul_le_mul_of_nonneg_left hraw hlambda0
  have hdebtExact : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward mixedProfile) who =
      (1 - lambda) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who +
        lambda *
          (quittingContinuationBestResponseValue reward profile who -
            quittingTerminalPayoff reward bestResponseProfile who) := by
    have hpayoff := quittingTerminalPayoff_update_stoppingLawMixture_eq
      reward profile who (profile who) bestResponse lambda
        hlambda0 hlambda1 hM hreward
    dsimp only [mixedProfile, mixedStrategy, bestResponseProfile]
    rw [Function.update_eq_self] at hpayoff
    dsimp only [quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair]
    rw [quittingContinuationBestResponseValue_update_self, hpayoff]
    ring
  have hdebtUpper : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward mixedProfile) who ≤
      (1 - lambda) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who +
        lambda * error := by
    rw [hdebtExact]
    have hscaled := mul_le_mul_of_nonneg_left hbestResidual hlambda0
    linarith
  have hwindow : (1 - lambda) *
        (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time terminal) ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward mixedProfile time terminal := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro time _htime
    dsimp only [mixedProfile, mixedStrategy]
    simpa only [Function.update_eq_self] using
      one_sub_mul_stageCoalitionMass_le_stoppingLawMixture
        reward profile who (profile who) bestResponse lambda
          hlambda0 hlambda1 time terminal
  exact ⟨hlaw, hgainLower, hdebtExact, hdebtUpper, hwindow⟩

/-- A positive total semantic debt therefore gives a literal half-law reset
with strictly positive cutoff-independent gain.  One positive debtor is mixed
halfway with a sufficiently accurate best response; its debt contracts by a
factor at most `3/4`, while half of any chosen singleton-clock window remains.
The conclusion has no row-selection or cutoff-cardinality loss. -/
theorem exists_halfStoppingLawReset_of_totalDebt_pos
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota) (cutoff : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hdebt : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ who, ∃ bestResponse : (quittingGame reward).BehaviorStrategy who,
      let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
        reward who (profile who) bestResponse (1 / 2) (by norm_num) (by norm_num)
      let mixedProfile := Function.update profile who mixedStrategy
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        4 * (Fintype.card iota : ℝ) *
          (quittingTerminalPayoff reward mixedProfile who -
            quittingTerminalPayoff reward profile who) ∧
      0 < quittingTerminalPayoff reward mixedProfile who -
        quittingTerminalPayoff reward profile who ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward mixedProfile) who ≤
        (3 / 4) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who ∧
      (1 / 2) *
          (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time
              (quittingSingletonTerminal owner)) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward mixedProfile time
            (quittingSingletonTerminal owner) := by
  have hcarrier : quittingTerminalSemanticPair reward profile ∈
      quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward profile
  have hnonneg : ∀ who ∈ (Finset.univ : Finset iota),
      0 ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
    intro who _
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hcarrier who
  have hsum : 0 < ∑ who,
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
    simpa only [quittingTerminalSemanticDebtSum] using hdebt
  have huniv : (Finset.univ : Finset iota).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
    simp at hsum
  obtain ⟨who, _hwho, haverageRaw⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul
      (Finset.univ : Finset iota) huniv
      (fun player => quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) player)
  have haverage : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      (Fintype.card iota : ℝ) * quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
    unfold quittingTerminalSemanticDebtSum
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte,
      Finset.card_univ] using haverageRaw
  have hwhoDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who := by
    have hcardNonneg : 0 ≤ (Fintype.card iota : ℝ) := by positivity
    by_contra hnot
    have hnonpos : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ≤ 0 :=
      le_of_not_gt hnot
    nlinarith
  let error := quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward profile) who / 2
  have herror : 0 < error := by
    dsimp only [error]
    linarith
  obtain ⟨bestResponse, _hlaw, hgain, _hdebtExact, hdebtUpper, hwindow⟩ :=
    exists_stoppingLawMixture_debtContraction_and_windowRetention
      reward profile who (quittingSingletonTerminal owner) cutoff
        (1 / 2) error (by norm_num) (by norm_num) herror hM hreward
  refine ⟨who, bestResponse, ?_⟩
  dsimp only
  have hgainPos : 0 < quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
            bestResponse (1 / 2) (by norm_num) (by norm_num))) who -
      quittingTerminalPayoff reward profile who := by
    have hlower : 0 < (1 / 2 : ℝ) *
        (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who - error) := by
      dsimp only [error]
      nlinarith
    exact hlower.trans_le hgain
  have hcontract : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile who
            (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
              bestResponse (1 / 2) (by norm_num) (by norm_num)))) who ≤
      (3 / 4) * quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
    dsimp only [error] at hdebtUpper
    nlinarith
  have hgainQuantitative : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      4 * (Fintype.card iota : ℝ) *
        (quittingTerminalPayoff reward
            (Function.update profile who
              (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
                bestResponse (1 / 2) (by norm_num) (by norm_num))) who -
          quittingTerminalPayoff reward profile who) := by
    let gain := quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
            bestResponse (1 / 2) (by norm_num) (by norm_num))) who -
      quittingTerminalPayoff reward profile who
    have hcoordinate : quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who ≤ 4 * gain := by
      dsimp only [error] at hgain
      dsimp only [gain]
      nlinarith
    have hcardNonneg : 0 ≤ (Fintype.card iota : ℝ) := by positivity
    calc
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        (Fintype.card iota : ℝ) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who := haverage
      _ ≤ (Fintype.card iota : ℝ) * (4 * gain) :=
        mul_le_mul_of_nonneg_left hcoordinate hcardNonneg
      _ = 4 * (Fintype.card iota : ℝ) * gain := by ring
  refine ⟨hgainQuantitative, hgainPos, hcontract, ?_⟩
  norm_num at hwindow ⊢
  exact hwindow

end GameTheory
