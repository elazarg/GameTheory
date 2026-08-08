/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.CertifiedBoundaryReinsertion

/-!
# Max-affine geometry of certified quitting boundaries

After a finite quitting prefix, one player's early best-response branch is a
constant `A`, the Continue-to-boundary branch is `T + χ * (w + β)`, and
prescribed play delivers `B + P * w`.  Its exact exploitability is therefore
a maximum of two affine functions.  This file identifies the resulting two
halfspaces, the interior acceptance interval, and its unique balance-point
minimizer.

The best-response and prescribed summaries are closed under concatenation.
Over real-valued stopping floors this is a composition semigroup; a literal
identity summary would require an extended-real early floor `-∞`.
-/

noncomputable section

namespace GameTheory

/-- Scalar exact exploitability of a finite prefix with certified terminal
payoff `w` and terminal relative debt `β`. -/
def quittingBoundaryGap
    (A T B P χ β w : ℝ) : ℝ :=
  max A (T + χ * (w + β)) - (B + P * w)

/-- The best-response part of one prefix summary. -/
def quittingBoundaryBestResponse (A T χ w : ℝ) : ℝ :=
  max A (T + χ * w)

/-- The boundary gap is literally the maximum of its two affine regret
branches. -/
theorem quittingBoundaryGap_eq_max_affine
    (A T B P χ β w : ℝ) :
    quittingBoundaryGap A T B P χ β w =
      max (A - B - P * w)
        (T - B + (χ - P) * w + χ * β) := by
  unfold quittingBoundaryGap
  rcases le_total A (T + χ * (w + β)) with h | h
  · rw [max_eq_right h, max_eq_right]
    · ring
    · nlinarith
  · rw [max_eq_left h, max_eq_left]
    · ring
    · nlinarith

/-- The abstract seven-scalar gap is the exact exploitability of a supplied
finite quitting prefix.  Thus the geometry below applies directly to the
finite best-response and prescribed-value recursions, rather than only to an
uninterpreted scalar model. -/
theorem quittingFiniteBoundaryExploitability_eq_boundaryGap
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (β w : ℝ) (start fuel : ℕ) :
    quittingFiniteTerminalBestResponseValue reward roots who (w + β)
          start (fuel + 1) -
        quittingFiniteTerminalHazardValue reward roots who hazard w
          start (fuel + 1) =
      quittingBoundaryGap
        (quittingFiniteEarlyBestResponseValue reward roots who start fuel)
        (quittingFiniteContinueToBoundaryValue reward roots who 0
          start (fuel + 1))
        (quittingFiniteTerminalHazardValue reward roots who hazard 0
          start (fuel + 1))
        (quittingFiniteFullSurvivalWeight roots who hazard
          start (fuel + 1))
        (quittingOpponentSurvivalWeight roots who start (fuel + 1))
        β w := by
  rw [quittingFiniteTerminalBestResponseValue_eq_max_early_boundary]
  rw [show w + β = 0 + (w + β) by ring,
    quittingFiniteContinueToBoundaryValue_add]
  rw [show w = 0 + w by ring,
    quittingFiniteTerminalHazardValue_add]
  unfold quittingBoundaryGap
  ring

/-- Max-affine best-response summaries are closed under concatenation.  The
early branch absorbs both an early stop in the first block and an early stop
after surviving into the second block; opponent survival multiplies. -/
theorem quittingBoundaryBestResponse_compose
    (A₁ T₁ χ₁ A₂ T₂ χ₂ w : ℝ) (hχ₁ : 0 ≤ χ₁) :
    quittingBoundaryBestResponse A₁ T₁ χ₁
        (quittingBoundaryBestResponse A₂ T₂ χ₂ w) =
      quittingBoundaryBestResponse
        (max A₁ (T₁ + χ₁ * A₂))
        (T₁ + χ₁ * T₂) (χ₁ * χ₂) w := by
  unfold quittingBoundaryBestResponse
  have hdistrib :
      T₁ + χ₁ * max A₂ (T₂ + χ₂ * w) =
        max (T₁ + χ₁ * A₂) (T₁ + χ₁ * (T₂ + χ₂ * w)) := by
    rcases le_total A₂ (T₂ + χ₂ * w) with h | h
    · rw [max_eq_right h, max_eq_right]
      nlinarith
    · rw [max_eq_left h, max_eq_left]
      nlinarith
  rw [hdistrib, max_assoc]
  congr 2
  ring

/-- Prescribed affine prefix summaries compose by the ordinary affine
semidirect-product law. -/
theorem quittingBoundaryPrescribed_compose
    (B₁ P₁ B₂ P₂ w : ℝ) :
    B₁ + P₁ * (B₂ + P₂ * w) =
      (B₁ + P₁ * B₂) + (P₁ * P₂) * w := by
  ring

/-- The exact prefix acceptance region is the intersection of two affine
halfspaces. -/
theorem quittingBoundaryGap_le_iff
    (A T B P χ β w ε : ℝ) :
    quittingBoundaryGap A T B P χ β w ≤ ε ↔
      A - B - P * w ≤ ε ∧
      T - B + (χ - P) * w + χ * β ≤ ε := by
  rw [quittingBoundaryGap_eq_max_affine, max_le_iff]

/-- In the genuinely interior case `0 < P < χ`, acceptable certified
terminal values form one explicit closed interval. -/
theorem quittingBoundaryGap_le_iff_interval
    (A T B P χ β w ε : ℝ) (hP : 0 < P) (hPχ : P < χ) :
    quittingBoundaryGap A T B P χ β w ≤ ε ↔
      (A - B - ε) / P ≤ w ∧
      w ≤ (B + ε - T - χ * β) / (χ - P) := by
  rw [quittingBoundaryGap_le_iff]
  constructor
  · rintro ⟨hA, hT⟩
    constructor
    · apply (div_le_iff₀ hP).2
      nlinarith
    · apply (le_div_iff₀ (sub_pos.mpr hPχ)).2
      nlinarith
  · rintro ⟨hlower, hupper⟩
    constructor
    · have := (div_le_iff₀ hP).1 hlower
      nlinarith
    · have := (le_div_iff₀ (sub_pos.mpr hPχ)).1 hupper
      nlinarith

/-- A prefix admits an epsilon-certified scalar boundary exactly when the
two explicit interval endpoints are ordered. -/
theorem exists_quittingBoundaryGap_le_iff
    (A T B P χ β ε : ℝ) (hP : 0 < P) (hPχ : P < χ) :
    (∃ w, quittingBoundaryGap A T B P χ β w ≤ ε) ↔
      (A - B - ε) / P ≤
        (B + ε - T - χ * β) / (χ - P) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ((quittingBoundaryGap_le_iff_interval
      A T B P χ β w ε hP hPχ).1 hw).1.trans
        ((quittingBoundaryGap_le_iff_interval
          A T B P χ β w ε hP hPχ).1 hw).2
  · intro horder
    refine ⟨(A - B - ε) / P, ?_⟩
    apply (quittingBoundaryGap_le_iff_interval
      A T B P χ β ((A - B - ε) / P) ε hP hPχ).2
    exact ⟨le_rfl, horder⟩

/-- The boundary value which balances early stopping and continuing into the
certified tail. -/
def quittingBoundaryBalance
    (A T χ β : ℝ) : ℝ :=
  (A - T - χ * β) / χ

/-- At the balance point, the two best-response branches agree exactly. -/
theorem quittingBoundaryBalance_eq
    (A T χ β : ℝ) (hχ : χ ≠ 0) :
    T + χ * (quittingBoundaryBalance A T χ β + β) = A := by
  unfold quittingBoundaryBalance
  field_simp
  ring

/-- With `0 < P < χ`, the balance point globally minimizes exact scalar
exploitability. -/
theorem quittingBoundaryGap_balance_le
    (A T B P χ β w : ℝ) (hP : 0 < P) (hPχ : P < χ) :
    quittingBoundaryGap A T B P χ β
        (quittingBoundaryBalance A T χ β) ≤
      quittingBoundaryGap A T B P χ β w := by
  have hχ : 0 < χ := hP.trans hPχ
  have hbalance := quittingBoundaryBalance_eq A T χ β (ne_of_gt hχ)
  unfold quittingBoundaryGap
  rw [hbalance, max_self]
  rcases le_total w (quittingBoundaryBalance A T χ β) with hw | hw
  · have hA : A ≤ max A (T + χ * (w + β)) :=
      le_max_left _ _
    nlinarith
  · have hT : T + χ * (w + β) ≤
        max A (T + χ * (w + β)) :=
      le_max_right _ _
    nlinarith

/-- In the interior-slope case the minimizer is strict away from the balance
point. -/
theorem quittingBoundaryGap_balance_lt
    (A T B P χ β w : ℝ) (hP : 0 < P) (hPχ : P < χ)
    (hw : w ≠ quittingBoundaryBalance A T χ β) :
    quittingBoundaryGap A T B P χ β
        (quittingBoundaryBalance A T χ β) <
      quittingBoundaryGap A T B P χ β w := by
  have hχ : 0 < χ := hP.trans hPχ
  have hbalance := quittingBoundaryBalance_eq A T χ β (ne_of_gt hχ)
  unfold quittingBoundaryGap
  rw [hbalance, max_self]
  rcases lt_or_gt_of_ne hw with hwlt | hwgt
  · have hA : A ≤ max A (T + χ * (w + β)) :=
      le_max_left _ _
    nlinarith
  · have hT : T + χ * (w + β) ≤
        max A (T + χ * (w + β)) :=
      le_max_right _ _
    nlinarith

/-- The balance point is the unique global minimizer in the interior-slope
case. -/
theorem quittingBoundaryGap_eq_balance_iff
    (A T B P χ β w : ℝ) (hP : 0 < P) (hPχ : P < χ) :
    quittingBoundaryGap A T B P χ β w =
        quittingBoundaryGap A T B P χ β
          (quittingBoundaryBalance A T χ β) ↔
      w = quittingBoundaryBalance A T χ β := by
  constructor
  · intro heq
    by_contra hne
    have hlt := quittingBoundaryGap_balance_lt
      A T B P χ β w hP hPχ hne
    linarith
  · rintro rfl
    rfl

end GameTheory
