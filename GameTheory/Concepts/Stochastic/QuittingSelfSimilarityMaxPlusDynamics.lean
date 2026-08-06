/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityMaxAffineTangent

/-!
# Dynamics of the max-plus tangent operator

The absorbed-mass tangent of unilateral stopping is

`x ↦ max early (tail + x)`.

Its dynamics have an exact trichotomy:

* positive tail drift pumps every finite budget;
* zero tail drift is the idempotent threshold closure `x ↦ max early x`; and
* negative tail drift reaches the constant early projector after finitely many
  iterations.

This turns the relevant/marginal/irrelevant scaling heuristic into elementary
finite algebra.
-/

noncomputable section

namespace GameTheory
namespace QuittingMaxPlusTangent

/-- Max-plus tangent operator with early floor and tail drift. -/
def eval (early tail x : ℝ) : ℝ :=
  max early (tail + x)

/-- `extra + 1` iterates of the tangent operator. -/
def iterateNonempty (early tail : ℝ) : ℕ → ℝ → ℝ
  | 0, x => eval early tail x
  | extra + 1, x => eval early tail (iterateNonempty early tail extra x)

@[simp] theorem iterateNonempty_zero (early tail x : ℝ) :
    iterateNonempty early tail 0 x = eval early tail x := rfl

@[simp] theorem iterateNonempty_succ
    (early tail : ℝ) (extra : ℕ) (x : ℝ) :
    iterateNonempty early tail (extra + 1) x =
      eval early tail (iterateNonempty early tail extra x) := rfl

/-- Safety at the tangent origin is exactly nonpositive early and tail drift. -/
theorem eval_zero_le_zero_iff (early tail : ℝ) :
    eval early tail 0 ≤ 0 ↔ early ≤ 0 ∧ tail ≤ 0 := by
  unfold eval
  simpa using (max_le_iff : max early (tail + 0) ≤ 0 ↔ _)

/-- Every iterate dominates the pure tail branch. -/
theorem linear_tail_le_iterateNonempty
    (early tail x : ℝ) (extra : ℕ) :
    (((extra + 1 : ℕ) : ℝ) * tail + x) ≤
      iterateNonempty early tail extra x := by
  induction extra with
  | zero =>
      change tail + x ≤ max early (tail + x)
      exact le_max_right _ _
  | succ extra ih =>
      rw [iterateNonempty_succ]
      unfold eval
      calc
        (((extra + 2 : ℕ) : ℝ) * tail + x)
            = tail + ((((extra + 1 : ℕ) : ℝ) * tail) + x) := by
              push_cast
              ring
        _ ≤ tail + iterateNonempty early tail extra x :=
          add_le_add_left ih tail
        _ ≤ max early (tail + iterateNonempty early tail extra x) :=
          le_max_right _ _

/-- Under nonpositive tail drift, the only surviving branches are the outer
floor and the tail translated through every copy. -/
theorem iterateNonempty_eq_max_of_tail_nonpos
    (early tail x : ℝ) (htail : tail ≤ 0) (extra : ℕ) :
    iterateNonempty early tail extra x =
      max early ((((extra + 1 : ℕ) : ℝ) * tail) + x) := by
  induction extra with
  | zero =>
      simp [iterateNonempty, eval]
  | succ extra ih =>
      rw [iterateNonempty_succ, ih]
      unfold eval
      let y : ℝ := (((extra + 1 : ℕ) : ℝ) * tail) + x
      have hy : tail + y = (((extra + 2 : ℕ) : ℝ) * tail) + x := by
        dsimp [y]
        push_cast
        ring
      by_cases h : early ≤ y
      · rw [max_eq_right h, hy]
      · have h' : y ≤ early := le_of_not_ge h
        rw [max_eq_left h']
        have htailEarly : tail + early ≤ early := by linarith
        rw [max_eq_left htailEarly]
        rw [max_eq_left]
        calc
          (((extra + 2 : ℕ) : ℝ) * tail) + x
              = tail + y := hy.symm
          _ ≤ tail + early := add_le_add_left h' tail
          _ ≤ early := htailEarly

/-- Zero tail drift is already the threshold-closure idempotent after one
application. -/
theorem iterateNonempty_zero_tail
    (early x : ℝ) (extra : ℕ) :
    iterateNonempty early 0 extra x = max early x := by
  rw [iterateNonempty_eq_max_of_tail_nonpos early 0 x le_rfl]
  simp

/-- Positive tail drift makes the tangent value exceed every finite budget
under enough repetitions. -/
theorem exists_iterateNonempty_gt_of_tail_pos
    (early tail x budget : ℝ) (htail : 0 < tail) :
    ∃ extra : ℕ, budget < iterateNonempty early tail extra x := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((budget - x) / tail)
  refine ⟨n, ?_⟩
  have hlinear : budget < (((n + 1 : ℕ) : ℝ) * tail) + x := by
    have hn' : budget - x < (n : ℝ) * tail :=
      (div_lt_iff₀ htail).mp hn
    have hnle : (n : ℝ) * tail ≤ ((n + 1 : ℕ) : ℝ) * tail := by
      apply mul_le_mul_of_nonneg_right _ htail.le
      exact_mod_cast Nat.le_succ n
    linarith
  exact hlinear.trans_le
    (linear_tail_le_iterateNonempty early tail x n)

/-- Negative tail drift reaches the constant early projector after finitely
many iterates. -/
theorem exists_eventually_iterateNonempty_eq_early_of_tail_neg
    (early tail x : ℝ) (htail : tail < 0) :
    ∃ cutoff : ℕ, ∀ extra, cutoff ≤ extra →
      iterateNonempty early tail extra x = early := by
  have hden : 0 < -tail := neg_pos.mpr htail
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_nat_gt ((x - early) / (-tail))
  refine ⟨cutoff, ?_⟩
  intro extra hextra
  rw [iterateNonempty_eq_max_of_tail_nonpos early tail x htail.le]
  rw [max_eq_left]
  have hcutoffR : (cutoff : ℝ) ≤ ((extra + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hextra.trans (Nat.le_succ extra))
  have hbase : x - early < (cutoff : ℝ) * (-tail) :=
    (div_lt_iff₀ hden).mp hcutoff
  have htransport :
      (cutoff : ℝ) * (-tail) ≤ ((extra + 1 : ℕ) : ℝ) * (-tail) :=
    mul_le_mul_of_nonneg_right hcutoffR hden.le
  nlinarith

/-- Tangent-dynamics trichotomy, stated without choosing which sign case
holds. -/
theorem dynamics_trichotomy (early tail x : ℝ) :
    (tail < 0 ∧ ∃ cutoff : ℕ, ∀ extra, cutoff ≤ extra →
        iterateNonempty early tail extra x = early) ∨
      (tail = 0 ∧ ∀ extra, iterateNonempty early tail extra x = max early x) ∨
      (0 < tail ∧ ∀ budget : ℝ, ∃ extra : ℕ,
        budget < iterateNonempty early tail extra x) := by
  rcases lt_trichotomy tail 0 with hneg | hzero | hpos
  · exact Or.inl ⟨hneg,
      exists_eventually_iterateNonempty_eq_early_of_tail_neg
        early tail x hneg⟩
  · exact Or.inr (Or.inl ⟨hzero, fun extra => by
      subst tail
      exact iterateNonempty_zero_tail early x extra⟩)
  · exact Or.inr (Or.inr ⟨hpos, fun budget =>
      exists_iterateNonempty_gt_of_tail_pos early tail x budget hpos⟩)

end QuittingMaxPlusTangent
end GameTheory
