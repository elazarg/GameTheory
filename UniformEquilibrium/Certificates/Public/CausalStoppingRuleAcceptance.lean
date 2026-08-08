/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.VariableStoppingPrefixLawCompiler

/-!
# Acceptance model for sound online stopping

This one-state, one-action game carries an honestly inhabited online stopping
rule with positive fuel.  The rule stops at the fixed public depth one and
uses the canonical root decomposition thereafter.  It is a small semantic
acceptance test for `OnlineCausalBoundedStoppingRule`: the repaired
reconstruction, occurrence, compatible-persistence, and completion fields are
jointly satisfiable.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace CausalStoppingRuleAcceptance

open Math.Probability

/-- A one-player, one-state, one-action stochastic game. -/
def game : StochasticGame Unit where
  State := Unit
  Act := fun _ => Unit
  stagePayoff := fun _ _ _ => 0
  transition := fun _ _ => PMF.pure ()
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := by norm_num

/-- Stop at the positive fixed depth one. -/
def selector : game.BoundedPublicStopSelector 1 :=
  fun _ => ⟨1, by decide⟩

theorem selector_causal :
    game.IsCausalBoundedStopSelector selector := by
  intro time left right _prefix_eq
  simp [selector]

/-- Before depth one there is no stopped base; from depth one onward use the
canonical root stopped path. -/
def view :
    (time : ℕ) → game.Hist time →
      Option (game.OnlineStoppedPath 1 time) :=
  fun time history =>
    if htime : 1 ≤ time then
      some
        (game.rootOnlineStoppedPathOfHistory
          selector htime history)
    else
      none

private theorem hist_ext {length : ℕ}
    (left right : game.Hist length) :
    left = right := by
  apply Prod.ext
  · funext index
    apply Prod.ext
    · cases (left.1 index).1
      cases (right.1 index).1
      rfl
    · funext who
      cases who
      cases (left.1 index).2 ()
      cases (right.1 index).2 ()
      rfl
  · cases left.2
    cases right.2
    rfl

private theorem path_ext {time : ℕ}
    (left right : game.OnlineStoppedPath 1 time)
    (hbase : left.base.1.val = right.base.1.val) :
    left = right := by
  rcases left with
    ⟨⟨leftIndex, leftHistory⟩,
      leftLength, leftSuffix, leftEq⟩
  rcases right with
    ⟨⟨rightIndex, rightHistory⟩,
      rightLength, rightSuffix, rightEq⟩
  simp only at hbase
  have hindex : leftIndex = rightIndex := Fin.ext hbase
  subst rightIndex
  have hhistory : leftHistory = rightHistory :=
    hist_ext _ _
  subst rightHistory
  have hlength : leftLength = rightLength := by
    omega
  subst rightLength
  have hsuffix : leftSuffix = rightSuffix :=
    hist_ext _ _
  subst rightSuffix
  rfl

private theorem canonical_base_length {time : ℕ}
    (htime : 1 ≤ time) (history : game.Hist time) :
    (game.rootOnlineStoppedPathOfHistory
      selector htime history).base.1.val = 1 := by
  rfl

private theorem startsAt_unit {length : ℕ}
    (history : game.Hist length) (state : game.State) :
    history.StartsAt state := by
  cases length with
  | zero =>
      change history.2 = state
      cases history.2
      cases state
      rfl
  | succ length =>
      change (history.1 0).1 = state
      cases (history.1 0).1
      cases state
      rfl

private theorem root_suffix_startsAt {time : ℕ}
    (htime : 1 ≤ time) (history : game.Hist time) :
    (game.rootOnlineStoppedPathOfHistory
      selector htime history).suffix.StartsAt
        (game.rootOnlineStoppedPathOfHistory
          selector htime history).base.2.2 := by
  exact startsAt_unit _ _

/-- Positive-fuel acceptance witness for the repaired online-rule API. -/
def rule : game.OnlineCausalBoundedStoppingRule 1 where
  selector := selector
  causal := selector_causal
  view := view
  reconstructs := by
    intro time history path hview
    unfold view at hview
    split at hview
    next htime =>
      simp only [Option.some.injEq] at hview
      subst path
      constructor
      · exact root_suffix_startsAt htime history
      · exact hist_ext _ _
    next _ =>
      contradiction
  base_occurs := by
    intro time history path hview
    unfold view at hview
    split at hview
    next htime =>
      simp only [Option.some.injEq] at hview
      subst path
      unfold OnlineStoppedBaseOccurs view
      have hbaseLength :=
        canonical_base_length htime history
      have hone :
          (game.rootOnlineStoppedPathOfHistory
            selector htime history).base.1.val = 1 :=
        hbaseLength
      have hbaseTime :
          1 ≤
            (game.rootOnlineStoppedPathOfHistory
              selector htime history).base.1.val := by
        omega
      simp only [hbaseTime, ↓reduceDIte,
        Option.some.injEq]
      apply path_ext
      rfl
    next _ =>
      contradiction
  persistent := by
    intro base hoccurs suffixLength suffix _hstart
    have hbaseTime : 1 ≤ base.1.val := by
      by_contra hnot
      change
        view base.1.val base.2 =
          some
            (game.onlineStoppedPathOfAppend base
              (game.emptyHist base.2.2)) at hoccurs
      have hnone : view base.1.val base.2 = none := by
        simp [view, hnot]
      rw [hnone] at hoccurs
      contradiction
    have hbaseLe : base.1.val ≤ 1 :=
      Nat.lt_succ_iff.mp base.1.isLt
    have hbaseEq : base.1.val = 1 := by omega
    have htime : 1 ≤ base.1.val + suffixLength := by omega
    simp only [view, htime, ↓reduceDIte, Option.some.injEq]
    apply path_ext
    change 1 = base.1.val
    exact hbaseEq.symm
  complete := by
    intro time htime history
    simp [view, htime]

/-- The repaired structure is genuinely inhabited at positive fuel. -/
theorem rule_nonempty :
    Nonempty (game.OnlineCausalBoundedStoppingRule 1) :=
  ⟨rule⟩

end CausalStoppingRuleAcceptance
end StochasticGame
end GameTheory
