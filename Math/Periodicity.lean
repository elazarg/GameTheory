/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Elementary periodicity lemmas
-/

namespace Math

/-- A sequence with a positive additive period has finite range. -/
theorem finite_range_of_add_period {α : Type*} (sequence : ℕ → α)
    (period : ℕ) (hperiodPos : 0 < period)
    (hperiod : ∀ n, sequence (n + period) = sequence n) :
    Set.Finite (Set.range sequence) := by
  have hremainder : ∀ n, ∃ r < period, sequence n = sequence r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n < period
        · exact ⟨n, hn, rfl⟩
        · let earlier := n - period
          have hearlier : earlier < n := by
            dsimp [earlier]
            omega
          obtain ⟨r, hr, her⟩ := ih earlier hearlier
          refine ⟨r, hr, ?_⟩
          have hnEq : earlier + period = n := by
            dsimp [earlier]
            omega
          rw [← hnEq, hperiod earlier]
          exact her
  have hfiniteDomain : Set.Finite (↑(Finset.range period) : Set ℕ) :=
    Finset.finite_toSet _
  refine (hfiniteDomain.image sequence).subset ?_
  rintro value ⟨n, rfl⟩
  obtain ⟨r, hr, heq⟩ := hremainder n
  refine ⟨r, ?_, heq.symm⟩
  simpa using hr

end Math
