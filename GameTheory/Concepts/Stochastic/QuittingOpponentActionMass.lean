/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingOpponentLiveMass
import Math.PMFProduct.Update

/-!
# The one-stage mass of an opponent quitting

Under a product action law, the event that some opponent of `who` quits is
independent of `who`'s mixed action.  Its probability is one minus the
all-continue coordinate after forcing `who` to continue.  This finite
one-stage identity is the action-level kernel for the persistent-live case
of quitting-game uniformization.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Some player other than `who` quits in this joint action. -/
def quittingSomeOpponentQuits (who : ι) (action : ι → Bool) : Prop :=
  ∃ other, other ≠ who ∧ action other = true

/-- Boolean flag that some opponent quits. -/
noncomputable def quittingOpponentQuitFlag
    (who : ι) (action : ι → Bool) : Bool := by
  classical
  exact decide (quittingSomeOpponentQuits who action)

/-- Real-valued indicator that some opponent quits. -/
def quittingSomeOpponentQuitsIndicator
    (who : ι) (action : ι → Bool) : ℝ :=
  if quittingOpponentQuitFlag who action = true then 1 else 0

omit [Fintype ι] in
theorem quittingSomeOpponentQuits_update_iff
    (who : ι) (action : ι → Bool) (ownAction : Bool) :
    quittingSomeOpponentQuits who (Function.update action who ownAction) ↔
      quittingSomeOpponentQuits who action := by
  constructor
  · rintro ⟨other, hother, hquit⟩
    refine ⟨other, hother, ?_⟩
    simpa [Function.update_of_ne hother] using hquit
  · rintro ⟨other, hother, hquit⟩
    refine ⟨other, hother, ?_⟩
    simpa [Function.update_of_ne hother] using hquit

omit [Fintype ι] [DecidableEq ι] in
theorem quittingOpponentQuitFlag_eq_true_iff
    (who : ι) (action : ι → Bool) :
    quittingOpponentQuitFlag who action = true ↔
      quittingSomeOpponentQuits who action := by
  classical
  simp [quittingOpponentQuitFlag]

omit [Fintype ι] in
/-- The opponent-quit flag ignores `who`'s coordinate. -/
theorem quittingOpponentQuitFlag_ignores
    (who : ι) :
    Ignores (A := fun _ : ι => Bool) who
      (fun action => PMF.pure
        (quittingOpponentQuitFlag who action)) := by
  intro action ownAction
  apply congrArg PMF.pure
  rw [Bool.eq_iff_iff,
    quittingOpponentQuitFlag_eq_true_iff,
    quittingOpponentQuitFlag_eq_true_iff]
  exact quittingSomeOpponentQuits_update_iff who action ownAction

/-- Updating `who`'s mixed action does not change the expected indicator that
some opponent quits. -/
theorem expect_pmfPi_someOpponentQuits_update_invariant
    (root : ι → PMF Bool) (who : ι) (marginal : PMF Bool) :
    expect (pmfPi (Function.update root who marginal))
        (quittingSomeOpponentQuitsIndicator who) =
      expect (pmfPi (Function.update root who (PMF.pure false)))
        (quittingSomeOpponentQuitsIndicator who) := by
  let base := Function.update root who (PMF.pure false)
  have hbind := pmfPi_bind_ignores_coord
    (A := fun _ : ι => Bool) base who marginal
    (fun action => PMF.pure
      (quittingOpponentQuitFlag who action))
    (quittingOpponentQuitFlag_ignores who)
  have hupdated : Function.update base who marginal =
      Function.update root who marginal := by
    ext player action
    by_cases hp : player = who
    · subst player
      simp
    · simp [base, Function.update_of_ne hp]
  rw [hupdated] at hbind
  have hexpect := congrArg (fun distribution : PMF Bool =>
    expect distribution (fun flag => if flag = true then (1 : ℝ) else 0))
    hbind
  change expect (pmfPi (Function.update root who marginal))
      (fun action => if quittingOpponentQuitFlag who action = true
        then (1 : ℝ) else 0) =
    expect (pmfPi (Function.update root who (PMF.pure false)))
      (fun action => if quittingOpponentQuitFlag who action = true
        then (1 : ℝ) else 0)
  simpa [expect_bind, expect_pure,
    base] using hexpect

/-- A supported action under a pure-continue marginal has `who` continuing. -/
theorem action_eq_false_of_mem_support_pmfPi_update_pure_false
    (root : ι → PMF Bool) (who : ι) (action : ι → Bool)
    (haction : action ∈
      (pmfPi (Function.update root who (PMF.pure false))).support) :
    action who = false := by
  have hcoordinate : action who ∈
      (pushforward
        (pmfPi (Function.update root who (PMF.pure false)))
        (fun joint => joint who)).support := by
    rw [pushforward, PMF.mem_support_map_iff]
    exact ⟨action, haction, rfl⟩
  rw [pmfPi_push_coord] at hcoordinate
  simpa using hcoordinate

/-- With `who` forced to continue, failure of the opponent-quit event on a
supported action means that the whole joint action is all-continue. -/
theorem eq_allContinue_of_not_someOpponentQuits_of_mem_support
    (root : ι → PMF Bool) (who : ι) (action : ι → Bool)
    (haction : action ∈
      (pmfPi (Function.update root who (PMF.pure false))).support)
    (hnoQuit : ¬quittingSomeOpponentQuits who action) :
    action = (quittingAllContinueAction : ι → Bool) := by
  funext player
  change action player = false
  by_cases hp : player = who
  · subst player
    exact action_eq_false_of_mem_support_pmfPi_update_pure_false
      root who action haction
  · cases hactionPlayer : action player with
    | false => rfl
    | true =>
        exact (hnoQuit ⟨player, hp, hactionPlayer⟩).elim

/-- The probability that some opponent quits is one minus the all-continue
coordinate after forcing `who` to continue. -/
theorem expect_pmfPi_someOpponentQuits_eq_one_sub_continueMass
    (root : ι → PMF Bool) (who : ι) (marginal : PMF Bool) :
    expect (pmfPi (Function.update root who marginal))
        (quittingSomeOpponentQuitsIndicator who) =
      1 - ((pmfPi (Function.update root who (PMF.pure false)))
        (quittingAllContinueAction : ι → Bool)).toReal := by
  rw [expect_pmfPi_someOpponentQuits_update_invariant]
  let distribution :=
    pmfPi (Function.update root who (PMF.pure false))
  calc
    expect distribution (quittingSomeOpponentQuitsIndicator who) =
      expect distribution (fun action =>
        (1 : ℝ) - if action = quittingAllContinueAction then 1 else 0) := by
          apply expect_congr_on_support
          intro action haction
          by_cases hopponent : quittingSomeOpponentQuits who action
          · have hne :
                action ≠ (quittingAllContinueAction : ι → Bool) := by
              intro heq
              subst action
              simp [quittingSomeOpponentQuits,
                quittingAllContinueAction] at hopponent
            have hflag :=
              (quittingOpponentQuitFlag_eq_true_iff who action).2 hopponent
            simp [quittingSomeOpponentQuitsIndicator, hflag, hne]
          · have heq :=
              eq_allContinue_of_not_someOpponentQuits_of_mem_support
                root who action haction hopponent
            have hflag : quittingOpponentQuitFlag who action ≠ true :=
              fun h => hopponent
                ((quittingOpponentQuitFlag_eq_true_iff who action).1 h)
            have hflagFalse : quittingOpponentQuitFlag who action = false := by
              cases h : quittingOpponentQuitFlag who action
              · rfl
              · exact (hflag h).elim
            subst action
            simp [quittingSomeOpponentQuitsIndicator, hflagFalse]
    _ = 1 - expect distribution (fun action =>
        if action = quittingAllContinueAction then 1 else 0) := by
      rw [expect_sub, expect_const]
    _ = 1 - ((pmfPi (Function.update root who (PMF.pure false)))
        (quittingAllContinueAction : ι → Bool)).toReal := by
      rw [← Math.Probability.apply_toReal_eq_expect_indicator]

end GameTheory
