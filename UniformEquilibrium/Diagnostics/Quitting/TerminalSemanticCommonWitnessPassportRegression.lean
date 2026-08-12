/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# A common best-response witness is stronger than envelope integration

The finite alternative "one deviation is first-order optimal at every reset
vertex, or there is a first-order witness-switch charge" is formally valid
only because its second branch is the negation of its first.  The charge does
not by itself produce a positive debt slope.

This file gives the sharp max-affine fence.  Three uniformly bounded affine
deviation charts have an envelope which is exactly modular on a two-reset
square.  The prescribed chart is affine as well, and the resulting debt is
exactly constant at all four vertices.  Nevertheless every single deviation,
and even every randomized mixture of the three displayed deviations, misses
the envelope by at least `lambda / 2` at either the source or the simultaneous
vertex.

Thus a common-witness passport is sufficient but not necessary for combining
first-order envelope increments.  The strategically relevant finite
dichotomy must instead use first-order modularity of the envelope values.  A
failure of modularity can be tested against minimum debt and then telescoped
to an edge; bare minimax witness disagreement cannot be sent to the
positive-slope rectangle decoder.
-/

namespace GameTheory
namespace CommonWitnessPassportRegression

open scoped BigOperators

noncomputable section

/-- The three exposed affine deviation charts. -/
inductive Witness
  | left
  | right
  | bridge
  deriving DecidableEq, Fintype

/-- A moving family of affine deviation payoffs.  The bridge starts
`lambda` below the source envelope and becomes optimal only at the joint
vertex. -/
def chart (lambda : ℝ) : Witness → ℝ → ℝ → ℝ
  | Witness.left, left, _right => 1 + left
  | Witness.right, _left, right => 1 + right
  | Witness.bridge, left, right =>
      1 - lambda + (3 / 2 : ℝ) * (left + right)

/-- The best-response envelope of the three charts. -/
def envelope (lambda left right : ℝ) : ℝ :=
  max (chart lambda Witness.left left right)
    (max (chart lambda Witness.right left right)
      (chart lambda Witness.bridge left right))

/-- One affine prescribed-payoff chart. -/
def prescribed (left right : ℝ) : ℝ := left + right

/-- The envelope gap, or debt, against the prescribed chart. -/
def debt (lambda left right : ℝ) : ℝ :=
  envelope lambda left right - prescribed left right

/-- The pointwise finite passport alternative.  Without further structure,
the "switch charge" branch is just the logical negation of a common
approximate witness.  Neither finiteness nor attainment of an envelope is
needed for this elementary form. -/
theorem common_passport_or_uniform_switch_charge
    {Deviation Vertex : Type} (gap : Deviation → Vertex → ℝ) (error : ℝ) :
    (∃ deviation, ∀ vertex, gap deviation vertex ≤ error) ∨
      (∀ deviation, ∃ vertex, error < gap deviation vertex) := by
  classical
  by_cases h : ∃ deviation, ∀ vertex, gap deviation vertex ≤ error
  · exact Or.inl h
  · right
    intro deviation
    by_contra hvertex
    apply h
    refine ⟨deviation, ?_⟩
    intro vertex
    exact le_of_not_gt (not_exists.mp hvertex vertex)

/-- Every underlying deviation chart has zero mixed rectangle.  There is no
hidden multiaffine cross term. -/
theorem chart_rectangle_eq_zero (lambda : ℝ) (witness : Witness) :
    chart lambda witness lambda lambda -
        chart lambda witness lambda 0 -
        chart lambda witness 0 lambda +
        chart lambda witness 0 0 = 0 := by
  cases witness
  case left => simp [chart]
  case right => simp [chart]
  case bridge =>
    simp only [chart]
    ring

/-- Exact envelope values on the reset square. -/
theorem envelope_vertex_values (lambda : ℝ) (hlambda : 0 < lambda) :
    envelope lambda 0 0 = 1 ∧
      envelope lambda lambda 0 = 1 + lambda ∧
      envelope lambda 0 lambda = 1 + lambda ∧
      envelope lambda lambda lambda = 1 + 2 * lambda := by
  unfold envelope
  simp only [chart]
  constructor
  · have hinner : max (1 + 0) (1 - lambda + 3 / 2 * (0 + 0)) = 1 := by
      rw [max_eq_left] <;> linarith
    rw [hinner]
    norm_num
  · constructor
    · rw [max_eq_left]
      rw [max_le_iff]
      constructor <;> linarith
    · constructor
      · have hinner :
            max (1 + lambda) (1 - lambda + 3 / 2 * (0 + lambda)) =
              1 + lambda := by
            exact max_eq_left (by linarith)
        rw [hinner]
        exact max_eq_right (by linarith)
      · have hinner :
            max (1 + lambda)
                (1 - lambda + 3 / 2 * (lambda + lambda)) =
              1 + 2 * lambda := by
            calc
              max (1 + lambda)
                  (1 - lambda + 3 / 2 * (lambda + lambda)) =
                  1 - lambda + 3 / 2 * (lambda + lambda) :=
                max_eq_right (by nlinarith)
              _ = 1 + 2 * lambda := by ring
        rw [hinner]
        exact max_eq_right (by linarith)

/-- The envelope increments are exactly additive despite witness switching. -/
theorem envelope_is_modular_on_vertices
    (lambda : ℝ) (hlambda : 0 < lambda) :
    envelope lambda lambda lambda - envelope lambda 0 0 =
      (envelope lambda lambda 0 - envelope lambda 0 0) +
        (envelope lambda 0 lambda - envelope lambda 0 0) := by
  obtain ⟨h00, h10, h01, h11⟩ := envelope_vertex_values lambda hlambda
  rw [h00, h10, h01, h11]
  ring

/-- The prescribed chart lies below the displayed best-response envelope on
the whole small square.  It can therefore consistently be included among
the available deviations without changing the envelope. -/
theorem prescribed_le_envelope_on_square
    (lambda left right : ℝ) (_hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda ≤ 1) (_hleft0 : 0 ≤ left) (_hleft1 : left ≤ lambda)
    (_hright0 : 0 ≤ right) (hright1 : right ≤ lambda) :
    prescribed left right ≤ envelope lambda left right := by
  have hprescribed : prescribed left right ≤ chart lambda Witness.left left right := by
    simp only [prescribed, chart]
    linarith
  exact hprescribed.trans (le_max_left _ _)

/-- All three moving deviation charts remain uniformly bounded on the
relevant squares. -/
theorem abs_chart_le_four_on_square
    (lambda left right : ℝ) (witness : Witness)
    (_hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hleft0 : 0 ≤ left) (hleft1 : left ≤ lambda)
    (hright0 : 0 ≤ right) (hright1 : right ≤ lambda) :
    |chart lambda witness left right| ≤ 4 := by
  cases witness <;> simp only [chart]
  · rw [abs_of_nonneg] <;> linarith
  · rw [abs_of_nonneg] <;> linarith
  · apply (abs_le).2
    constructor <;> linarith

/-- The debt is exactly constant at every reset vertex. -/
theorem debt_vertex_values (lambda : ℝ) (hlambda : 0 < lambda) :
    debt lambda 0 0 = 1 ∧
      debt lambda lambda 0 = 1 ∧
      debt lambda 0 lambda = 1 ∧
      debt lambda lambda lambda = 1 := by
  obtain ⟨h00, h10, h01, h11⟩ := envelope_vertex_values lambda hlambda
  constructor
  · dsimp [debt, prescribed]
    rw [h00]
    ring
  · constructor
    · dsimp [debt, prescribed]
      rw [h10]
      ring
    · constructor
      · dsimp [debt, prescribed]
        rw [h01]
        ring
      · dsimp [debt, prescribed]
        rw [h11]
        ring

/-- A randomized mixture of the three deviations. -/
def mixedChart (lambda alpha beta gamma left right : ℝ) : ℝ :=
  alpha * chart lambda Witness.left left right +
    beta * chart lambda Witness.right left right +
    gamma * chart lambda Witness.bridge left right

/-- For every randomized mixture of the three witnesses, either its source
gap or its simultaneous-vertex gap is at least `lambda / 2`.  Hence the
normalized common-passport error is bounded below by `1/2`, even though the
envelope and debt integrate exactly. -/
theorem source_or_joint_gap_ge_half
    (lambda alpha beta gamma : ℝ) (hlambda : 0 < lambda)
    (_halpha : 0 ≤ alpha) (_hbeta : 0 ≤ beta) (_hgamma : 0 ≤ gamma)
    (hsum : alpha + beta + gamma = 1) :
    lambda / 2 ≤
        envelope lambda 0 0 - mixedChart lambda alpha beta gamma 0 0 ∨
      lambda / 2 ≤
        envelope lambda lambda lambda -
          mixedChart lambda alpha beta gamma lambda lambda := by
  obtain ⟨h00, _h10, _h01, h11⟩ := envelope_vertex_values lambda hlambda
  have hsource :
      envelope lambda 0 0 - mixedChart lambda alpha beta gamma 0 0 =
        gamma * lambda := by
    rw [h00]
    simp only [mixedChart, chart]
    nlinarith
  have hjoint :
      envelope lambda lambda lambda -
          mixedChart lambda alpha beta gamma lambda lambda =
        (1 - gamma) * lambda := by
    rw [h11]
    simp only [mixedChart, chart]
    nlinarith
  rw [hsource, hjoint]
  by_cases hhalf : gamma ≤ 1 / 2
  · right
    nlinarith
  · left
    have : 1 / 2 < gamma := lt_of_not_ge hhalf
    nlinarith

/-- No edge of the square carries a positive debt slope.  In particular, the
order-`lambda` common-witness failure above cannot satisfy the input of the
positive-slope rectangle decoder. -/
theorem all_forward_debt_edges_eq_zero
    (lambda : ℝ) (hlambda : 0 < lambda) :
    debt lambda lambda 0 - debt lambda 0 0 = 0 ∧
      debt lambda 0 lambda - debt lambda 0 0 = 0 ∧
      debt lambda lambda lambda - debt lambda lambda 0 = 0 ∧
      debt lambda lambda lambda - debt lambda 0 lambda = 0 := by
  obtain ⟨h00, h10, h01, h11⟩ := debt_vertex_values lambda hlambda
  rw [h00, h10, h01, h11]
  norm_num

end

end CommonWitnessPassportRegression
end GameTheory
