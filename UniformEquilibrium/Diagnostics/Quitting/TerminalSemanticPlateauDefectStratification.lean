/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer

/-!
# Finite strategic strata for a localized Nash defect

Replacing one player's live marginal by a pure endpoint either preserves a
displayed coalition cylinder or routes it across the adjacent Boolean-cube
edge at that player.  This module records the exact four cases and couples
that routing with the literal reached-row best-endpoint deviation.

The result is deliberately local.  The routed cylinder remains attached to
the same source row and shifted tail, but the modified row need not be Nash
for the other players and no chronological return is asserted.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Boolean action profile corresponding to a coalition. -/
def quittingCoalitionAction (coalition : Finset ι) : ι → Bool :=
  fun who => decide (who ∈ coalition)

/-- Product-root mass and the explicit Bernoulli coalition formula agree for
every coalition, including the empty coalition. -/
theorem quittingRootCoalitionMass_eq_pmfPi
    (root : ι → PMF Bool) (coalition : Finset ι) :
    quittingRootCoalitionMass root coalition =
      ((pmfPi root) (quittingCoalitionAction coalition)).toReal := by
  rw [pmfPi_apply, ENNReal.toReal_prod]
  have hproduct :
      (∏ who, ((root who) (quittingCoalitionAction coalition who)).toReal) =
        (∏ who ∈ coalition, (root who true).toReal) *
          ∏ who ∈ coalitionᶜ, (1 - (root who true).toReal) := by
    rw [← Finset.prod_mul_prod_compl coalition
      (fun who => ((root who)
        (quittingCoalitionAction coalition who)).toReal)]
    congr 1
    · apply Finset.prod_congr rfl
      intro who hwho
      simp [quittingCoalitionAction, hwho]
    · apply Finset.prod_congr rfl
      intro who hwho
      have hnot : who ∉ coalition := by simpa using hwho
      have hsum := quittingRoot_continueProbability_add_quitProbability root who
      simp only [quittingCoalitionAction, hnot, decide_false]
      linarith
  rw [hproduct]
  rfl

/-- The coalition prescribed after making `who`'s action pure.  Pure Quit
inserts the player and pure Continue erases the player. -/
def quittingPureEndpointRoutedCoalition
    (coalition : Finset ι) (who : ι) (action : Bool) : Finset ι :=
  if action then insert who coalition else coalition.erase who

omit [Fintype ι] in
@[simp] theorem quittingPureEndpointRoutedCoalition_true
    (coalition : Finset ι) (who : ι) :
    quittingPureEndpointRoutedCoalition coalition who true =
      insert who coalition := by
  simp [quittingPureEndpointRoutedCoalition]

omit [Fintype ι] in
@[simp] theorem quittingPureEndpointRoutedCoalition_false
    (coalition : Finset ι) (who : ι) :
    quittingPureEndpointRoutedCoalition coalition who false =
      coalition.erase who := by
  simp [quittingPureEndpointRoutedCoalition]

omit [Fintype ι] in
/-- Routing changes exactly the selected player's coordinate of the Boolean
coalition action. -/
theorem quittingCoalitionAction_routed
    (coalition : Finset ι) (who : ι) (action : Bool) :
    quittingCoalitionAction
        (quittingPureEndpointRoutedCoalition coalition who action) =
      Function.update (quittingCoalitionAction coalition) who action := by
  funext player
  by_cases hplayer : player = who
  · subst player
    cases action <;> simp [quittingCoalitionAction,
      quittingPureEndpointRoutedCoalition]
  · cases action <;> simp [quittingCoalitionAction,
      quittingPureEndpointRoutedCoalition, hplayer]

/-- **Exact routed-cylinder factorization.**  The old coalition mass is its
old `who`-action probability times the mass of the coalition obtained after
making the new endpoint pure.  This single identity contains all four
membership/endpoint cases. -/
theorem quittingRootCoalitionMass_eq_actionProbability_mul_routed
    (root : ι → PMF Bool) (coalition : Finset ι) (who : ι)
    (action : Bool) :
    quittingRootCoalitionMass root coalition =
      (if who ∈ coalition then (root who true).toReal
        else (root who false).toReal) *
        quittingRootCoalitionMass
          (Function.update root who (PMF.pure action))
          (quittingPureEndpointRoutedCoalition coalition who action) := by
  rw [quittingRootCoalitionMass_eq_pmfPi,
    quittingRootCoalitionMass_eq_pmfPi,
    quittingCoalitionAction_routed]
  let oldAction := quittingCoalitionAction coalition
  let rest : ENNReal :=
    ∏ player ∈ Finset.univ.erase who, root player (oldAction player)
  have hold : (pmfPi root) oldAction =
      root who (oldAction who) * rest := by
    rw [pmfPi_apply]
    simpa [rest, mul_comm] using
      (Finset.prod_erase_mul Finset.univ
        (fun player => root player (oldAction player))
        (Finset.mem_univ who)).symm
  have hnew :
      (pmfPi (Function.update root who (PMF.pure action)))
        (Function.update oldAction who action) = rest := by
    rw [pmfPi_apply_update_family]
    simp only [Function.update_self, PMF.pure_apply, if_true, one_mul]
    apply Finset.prod_congr rfl
    intro player hplayer
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hplayer)]
  rw [hold, hnew, ENNReal.toReal_mul]
  by_cases hwho : who ∈ coalition <;>
    simp [oldAction, quittingCoalitionAction, hwho]

/-- Making one marginal pure cannot decrease the mass of the coalition
routed to agree with that pure action. -/
theorem quittingRootCoalitionMass_le_pureEndpointRouted
    (root : ι → PMF Bool) (coalition : Finset ι) (who : ι)
    (action : Bool) :
    quittingRootCoalitionMass root coalition ≤
      quittingRootCoalitionMass
        (Function.update root who (PMF.pure action))
        (quittingPureEndpointRoutedCoalition coalition who action) := by
  rw [quittingRootCoalitionMass_eq_actionProbability_mul_routed]
  apply mul_le_of_le_one_left
  · exact MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _
  · split_ifs
    · exact ENNReal.toReal_mono ENNReal.one_ne_top
        ((root who).coe_le_one true)
    · exact ENNReal.toReal_mono ENNReal.one_ne_top
        ((root who).coe_le_one false)

omit [Fintype ι] in
/-- The routed coalition belongs to exactly one of the four finite strategic
classes: member reinforcement, member dropout, outsider join, or outsider
suppression. -/
theorem quittingPureEndpointRoutedCoalition_four_way
    (coalition : Finset ι) (who : ι) (action : Bool) :
    (who ∈ coalition ∧ action = true ∧
        quittingPureEndpointRoutedCoalition coalition who action = coalition) ∨
      (who ∈ coalition ∧ action = false ∧
        quittingPureEndpointRoutedCoalition coalition who action =
          coalition.erase who) ∨
      (who ∉ coalition ∧ action = true ∧
        quittingPureEndpointRoutedCoalition coalition who action =
          insert who coalition) ∨
      (who ∉ coalition ∧ action = false ∧
        quittingPureEndpointRoutedCoalition coalition who action = coalition) := by
  by_cases hwho : who ∈ coalition <;> cases action <;>
    simp [hwho, quittingPureEndpointRoutedCoalition]

/-- **Four-way marked-defect routing.**  At a reached live row, the literal
best-endpoint deviation has its exact global gain and routes every positive
marked coalition cylinder to the same coalition or its one-player toggle
without losing mass.  The final disjunction records the four strategic
classes. -/
theorem quittingTerminalPayoff_stageBestEndpointDeviation_markedRouting
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (coalition : Finset ι)
    (hlive : 0 < quittingLiveMass reward profile stage)
    (hmass : 0 < quittingRootCoalitionMass
      (quittingProfileLiveRoot reward profile stage) coalition)
    (hdefect : 0 < quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))).1
      (quittingProfileLiveRoot reward profile stage) who) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let routed := quittingPureEndpointRoutedCoalition coalition who action
    quittingTerminalPayoff reward
          (Function.update profile who
            (quittingStagePureEndpointBehaviorDeviation
              reward profile who stage action)) who -
        quittingTerminalPayoff reward profile who =
          quittingLiveMass reward profile stage *
            quittingRootCoordinateNashDefect reward tail.1 root who ∧
      0 < quittingTerminalPayoff reward
          (Function.update profile who
            (quittingStagePureEndpointBehaviorDeviation
              reward profile who stage action)) who -
        quittingTerminalPayoff reward profile who ∧
      0 < quittingRootCoalitionMass
        (Function.update root who (PMF.pure action)) routed ∧
      quittingRootCoalitionMass root coalition ≤
        quittingRootCoalitionMass
          (Function.update root who (PMF.pure action)) routed ∧
      ((who ∈ coalition ∧ action = true ∧ routed = coalition) ∨
        (who ∈ coalition ∧ action = false ∧ routed = coalition.erase who) ∨
        (who ∉ coalition ∧ action = true ∧ routed = insert who coalition) ∨
        (who ∉ coalition ∧ action = false ∧ routed = coalition)) := by
  dsimp only
  have hroute := quittingRootCoalitionMass_le_pureEndpointRouted
    (quittingProfileLiveRoot reward profile stage) coalition who
    (quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))).1
      (quittingProfileLiveRoot reward profile stage) who)
  have hgain :=
    quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
      reward profile who stage
  refine ⟨hgain, ?_, ?_, hroute, ?_⟩
  · rw [hgain]
    exact mul_pos hlive hdefect
  · exact hmass.trans_le hroute
  · exact quittingPureEndpointRoutedCoalition_four_way coalition who _

end GameTheory
