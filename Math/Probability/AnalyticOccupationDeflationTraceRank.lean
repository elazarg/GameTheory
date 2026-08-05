/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticFiniteOccupationDeflation

/-!
# Rank information carried by an analytic deflation trace

An analytic occupation deflation trace either makes no move at all or
strictly lowers active-set rank.  These are the unconditional rank facts the
trace carries, stated independently of any strategic interpretation.
-/

noncomputable section

namespace Math
namespace Probability
namespace AnalyticOccupationDeflationTrace

/-- A zero-length analytic deflation trace is reflexive. -/
theorem initial_eq_terminal_of_length_eq_zero
    {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {anchor : S}
    {initial terminal : FiniteDeflationState I}
    (trace :
      AnalyticOccupationDeflationTrace
        column charge anchor initial terminal)
    (length_eq_zero : trace.length = 0) :
    initial = terminal := by
  cases trace with
  | refl _ =>
      rfl
  | strict next strict_nonempty tail =>
      simp only [length] at length_eq_zero
      omega

/-- A deflation trace either makes no move or strictly lowers active-set
rank.  This packages the strongest unconditional rank information carried
by the trace. -/
theorem initial_eq_terminal_or_terminal_rank_lt
    {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {anchor : S}
    {initial terminal : FiniteDeflationState I}
    (trace :
      AnalyticOccupationDeflationTrace
        column charge anchor initial terminal) :
    initial = terminal ∨ terminal.rank < initial.rank := by
  by_cases length_eq_zero : trace.length = 0
  · exact Or.inl
      (trace.initial_eq_terminal_of_length_eq_zero length_eq_zero)
  · right
    have length_pos : 0 < trace.length :=
      Nat.pos_of_ne_zero length_eq_zero
    have rank_bound :=
      trace.terminal_rank_add_length_le_initial_rank
    omega

end AnalyticOccupationDeflationTrace
end Probability
end Math
