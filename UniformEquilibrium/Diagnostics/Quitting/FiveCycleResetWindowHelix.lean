/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# The exceptional five-label reset window is a pentagonal helix

This file isolates the finite combinatorics behind a proposed five-to-four
reset reduction.  At reset step `i : Fin 5`, the transferred debt token moves
from `i` to `i + 1`, while `incidence i` is one marked incidence label.  The
base role window consists of those three labels.

If two consecutive base windows use all five labels at every step, then the
incidence labels are forced: `incidence i = i + 3`.  Conversely that helical
pattern has full consecutive windows.  Hence every nonhelical labelling has a
consecutive window omitting a player.

The result is deliberately only combinatorial.  It does not identify the
abstract transfer edge with a behavioral reset, transport a terminal-law atom
between state-matched reset laws, or justify deleting the omitted player.
-/

namespace GameTheory

/-- The three base labels at one step of a directed five-cycle: its owner,
its debt recipient, and one marked incidence label. -/
def fiveCycleResetRoleWindow (incidence : Fin 5 → Fin 5) (i : Fin 5) :
    Finset (Fin 5) :=
  {i, i + 1, incidence i}

/-- Every pair of consecutive reset-role windows uses all five labels exactly
when the marked incidence follows the unique lag-three helix. -/
theorem fiveCycleResetRoleWindow_full_iff_helix :
    ∀ incidence : Fin 5 → Fin 5,
      (∀ i, fiveCycleResetRoleWindow incidence i ∪
            fiveCycleResetRoleWindow incidence (i + 1) = Finset.univ) ↔
        ∀ i, incidence i = i + 3 := by
  intro incidence
  constructor
  · intro hfull
    have mem_of_full (i label : Fin 5) :
        label ∈ fiveCycleResetRoleWindow incidence i ∪
          fiveCycleResetRoleWindow incidence (i + 1) := by
      rw [hfull i]
      simp
    have h03 := mem_of_full 0 3
    have h04 := mem_of_full 0 4
    have h10 := mem_of_full 1 0
    have h14 := mem_of_full 1 4
    have hq0 : incidence 0 = 3 := by
      clear hfull mem_of_full
      generalize h0 : incidence 0 = value
      fin_cases value <;>
        simp_all [fiveCycleResetRoleWindow] <;> omega
    have hq1 : incidence 1 = 4 := by
      clear hfull mem_of_full h03 h10 h14
      generalize h1 : incidence 1 = value
      fin_cases value <;>
        simp_all [fiveCycleResetRoleWindow]
    have h20 := mem_of_full 1 0
    have hq2 : incidence 2 = 0 := by
      clear hfull mem_of_full h03 h04 h10 h14
      generalize h2 : incidence 2 = value
      fin_cases value <;>
        simp_all [fiveCycleResetRoleWindow]
    have h31 := mem_of_full 2 1
    have hq3 : incidence 3 = 1 := by
      clear hfull mem_of_full h03 h04 h10 h14 h20
      generalize h3 : incidence 3 = value
      fin_cases value <;>
        simp_all [fiveCycleResetRoleWindow]
    have h42 := mem_of_full 3 2
    have hq4 : incidence 4 = 2 := by
      clear hfull mem_of_full h03 h04 h10 h14 h20 h31
      generalize h4 : incidence 4 = value
      fin_cases value <;>
        simp_all [fiveCycleResetRoleWindow]
    intro i
    fin_cases i
    · simpa using hq0
    · simpa using hq1
    · simpa using hq2
    · simpa using hq3
    · simpa using hq4
  · intro hhelix i
    fin_cases i
    · have h0 := hhelix 0
      have h1 := hhelix 1
      ext label
      fin_cases label <;> simp [fiveCycleResetRoleWindow, h0, h1]
    · have h1 := hhelix 1
      have h2 := hhelix 2
      ext label
      fin_cases label <;> simp [fiveCycleResetRoleWindow, h1, h2]
    · have h2 := hhelix 2
      have h3 := hhelix 3
      ext label
      fin_cases label <;> simp [fiveCycleResetRoleWindow, h2, h3]
    · have h3 := hhelix 3
      have h4 := hhelix 4
      ext label
      fin_cases label <;> simp [fiveCycleResetRoleWindow, h3, h4]
    · have h4 := hhelix 4
      have h0 := hhelix 0
      ext label
      fin_cases label <;> simp [fiveCycleResetRoleWindow, h4, h0]

/-- Ordinary/exceptional form of the window classification.  Either some
two-step packet omits an explicit fifth label, or every incidence label lies
on the pentagonal helix. -/
theorem exists_omitted_fiveCycleResetWindow_or_helix :
    ∀ incidence : Fin 5 → Fin 5,
      (∃ i omitted,
          omitted ∉ fiveCycleResetRoleWindow incidence i ∪
            fiveCycleResetRoleWindow incidence (i + 1)) ∨
        ∀ i, incidence i = i + 3 := by
  intro incidence
  by_cases hfull : ∀ i,
      fiveCycleResetRoleWindow incidence i ∪
        fiveCycleResetRoleWindow incidence (i + 1) = Finset.univ
  · exact Or.inr
      ((fiveCycleResetRoleWindow_full_iff_helix incidence).mp hfull)
  · left
    push Not at hfull
    obtain ⟨i, hi⟩ := hfull
    have homitted : ∃ omitted,
        omitted ∉ fiveCycleResetRoleWindow incidence i ∪
          fiveCycleResetRoleWindow incidence (i + 1) := by
      by_contra hnone
      push Not at hnone
      apply hi
      exact Finset.eq_univ_iff_forall.mpr hnone
    obtain ⟨omitted, homitted⟩ := homitted
    exact ⟨i, omitted, homitted⟩

/-- In the exceptional helix, the marked incidence at step `i` is the debt
recipient two steps later, and the owner at step `i` is the marked incidence
two steps later.  These lag-two matches are the only chronological leverage
provided by the finite classification. -/
theorem fiveCycleResetHelix_lagTwo_matches :
    ∀ incidence : Fin 5 → Fin 5,
      (∀ i, incidence i = i + 3) →
        ∀ i, incidence i = (i + 2) + 1 ∧ incidence (i + 2) = i := by
  intro incidence hhelix i
  constructor
  · rw [hhelix i]
    fin_cases i <;> rfl
  · rw [hhelix (i + 2)]
    fin_cases i <;> rfl

end GameTheory
