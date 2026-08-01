/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.ShadowSeparatorAccounting
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Sublinear shadow-or-separator ledgers

This file turns the finite-horizon shadow-or-separator identity into the
asymptotic estimate consumed by public-phase equilibrium certificates.

The game-specific construction remains responsible for proving that each
named cumulative budget is sublinear.  Once those estimates are available,
the theorem below combines them without reopening the pathwise accounting.
-/

open Filter Set Topology Asymptotics

namespace Math.Probability

noncomputable section

/-- A real cumulative budget is sublinear when it is little-o of calendar
time. -/
def IsAsymptoticallySublinear (budget : ℕ → ℝ) : Prop :=
  budget =o[atTop] fun T : ℕ => (T : ℝ)

/-- The little-o definition of sublinearity unfolds to the classical
ratio-to-zero limit used throughout the pathwise accounting. -/
theorem isAsymptoticallySublinear_iff_tendsto {budget : ℕ → ℝ} :
    IsAsymptoticallySublinear budget ↔
      Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * budget T) atTop (nhds 0) := by
  have hgf : ∀ᶠ T : ℕ in atTop, (T : ℝ) = 0 → budget T = 0 := by
    filter_upwards [eventually_gt_atTop 0] with T hT hT0
    exact absurd hT0 (Nat.cast_ne_zero.mpr hT.ne')
  unfold IsAsymptoticallySublinear
  rw [isLittleO_iff_tendsto' hgf]
  simp only [div_eq_inv_mul]

namespace IsAsymptoticallySublinear

theorem const (c : ℝ) :
    IsAsymptoticallySublinear (fun _ : ℕ => c) := by
  refine isLittleO_const_left.mpr (Or.inr ?_)
  have heq : (norm ∘ fun T : ℕ => (T : ℝ)) = fun T : ℕ => (T : ℝ) := by
    funext T
    change ‖(T : ℝ)‖ = (T : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg T)]
  rw [heq]
  exact tendsto_natCast_atTop_atTop

theorem add {f g : ℕ → ℝ}
    (hf : IsAsymptoticallySublinear f)
    (hg : IsAsymptoticallySublinear g) :
    IsAsymptoticallySublinear (fun T => f T + g T) :=
  Asymptotics.IsLittleO.add hf hg

theorem const_mul {f : ℕ → ℝ}
    (hf : IsAsymptoticallySublinear f) (c : ℝ) :
    IsAsymptoticallySublinear (fun T => c * f T) :=
  Asymptotics.IsLittleO.const_mul_left hf c

theorem eventually_average_le {f : ℕ → ℝ}
    (hf : IsAsymptoticallySublinear f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℕ in atTop, (T : ℝ)⁻¹ * f T ≤ δ := by
  have htendsto := isAsymptoticallySublinear_iff_tendsto.mp hf
  exact (htendsto.eventually (eventually_lt_nhds hδ)).mono
    (fun _ h => h.le)

end IsAsymptoticallySublinear

/-- The predictable cumulative budget appearing on the right-hand side of
the shadow-or-separator ledger. -/
def shadowSeparatorCumulativeBudget
    (T : ℕ)
    (potentialDrift goodBudget separatorCharge : ℕ → ℝ)
    (potentialNoise goodNoise separatorNoise : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T,
    (potentialDrift t + goodBudget t + separatorCharge t +
      potentialNoise t + goodNoise t + separatorNoise t)

/-- The finite-horizon ledger closes asymptotically once its predictable
budget and implementation cost are sublinear.

This is the exact interface needed by the public-phase verifier: for every
positive accuracy, all sufficiently long horizons have average payoff error
at most that accuracy.  No sign assumption is imposed on the individual
noise terms; they enter through their named cumulative sublinearity premise.
-/
theorem eventually_shadowSeparatorPayoffErrorAverage_le
    (L : ℝ)
    (potential payoffError implementationCost : ℕ → ℝ)
    (transientCost potentialDrift potentialNoise : ℕ → ℝ)
    (goodMismatch goodBudget goodNoise : ℕ → ℝ)
    (badTolerance separatorCharge separatorNoise : ℕ → ℝ)
    (hL : 0 ≤ L)
    (hpotential_nonneg : ∀ t, 0 ≤ potential t)
    (hbad_nonneg : ∀ t, 0 ≤ badTolerance t)
    (hpayoff : ∀ t,
      payoffError t ≤
        L * (transientCost t + goodMismatch t) + implementationCost t)
    (htransient : ∀ t,
      transientCost t =
        potential t - potential (t + 1) +
          potentialDrift t + potentialNoise t)
    (hgood : ∀ t,
      goodMismatch t ≤ goodBudget t + goodNoise t)
    (hbad : ∀ t,
      badTolerance t ≤ separatorCharge t + separatorNoise t)
    (hbudget :
      IsAsymptoticallySublinear (fun T =>
        shadowSeparatorCumulativeBudget T
          potentialDrift goodBudget separatorCharge
          potentialNoise goodNoise separatorNoise))
    (himplementation :
      IsAsymptoticallySublinear (fun T =>
        ∑ t ∈ Finset.range T, implementationCost t))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℕ in atTop,
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, payoffError t) ≤ δ := by
  let budget : ℕ → ℝ := fun T =>
    shadowSeparatorCumulativeBudget T
      potentialDrift goodBudget separatorCharge
      potentialNoise goodNoise separatorNoise
  let implementation : ℕ → ℝ := fun T =>
    ∑ t ∈ Finset.range T, implementationCost t
  let upper : ℕ → ℝ := fun T =>
    L * (potential 0 + budget T) + implementation T
  have hupper : IsAsymptoticallySublinear upper := by
    apply IsAsymptoticallySublinear.add
    · apply IsAsymptoticallySublinear.const_mul
      exact (IsAsymptoticallySublinear.const (potential 0)).add hbudget
    · exact himplementation
  filter_upwards
      [hupper.eventually_average_le hδ] with T hT
  have hledger :=
    shadowSeparatorPayoffErrorSum_le
      T L potential payoffError implementationCost
      transientCost potentialDrift potentialNoise
      goodMismatch goodBudget goodNoise
      badTolerance separatorCharge separatorNoise
      hL (hpotential_nonneg T)
      (fun t _ => hbad_nonneg t)
      (fun t _ => hpayoff t)
      (fun t _ => htransient t)
      (fun t _ => hgood t)
      (fun t _ => hbad t)
  have hscale : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg T)
  calc
    (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, payoffError t) ≤
        (T : ℝ)⁻¹ *
          (L * (potential 0 + budget T) + implementation T) :=
      mul_le_mul_of_nonneg_left
        (by
          simpa [budget, implementation,
            shadowSeparatorCumulativeBudget] using hledger)
        hscale
    _ = (T : ℝ)⁻¹ * upper T := rfl
    _ ≤ δ := hT

/-- Threshold form of
`eventually_shadowSeparatorPayoffErrorAverage_le`, matching the quantifier
shape used by uniform-equilibrium certificates. -/
theorem exists_shadowSeparatorPayoffErrorAverage_threshold
    (L : ℝ)
    (potential payoffError implementationCost : ℕ → ℝ)
    (transientCost potentialDrift potentialNoise : ℕ → ℝ)
    (goodMismatch goodBudget goodNoise : ℕ → ℝ)
    (badTolerance separatorCharge separatorNoise : ℕ → ℝ)
    (hL : 0 ≤ L)
    (hpotential_nonneg : ∀ t, 0 ≤ potential t)
    (hbad_nonneg : ∀ t, 0 ≤ badTolerance t)
    (hpayoff : ∀ t,
      payoffError t ≤
        L * (transientCost t + goodMismatch t) + implementationCost t)
    (htransient : ∀ t,
      transientCost t =
        potential t - potential (t + 1) +
          potentialDrift t + potentialNoise t)
    (hgood : ∀ t,
      goodMismatch t ≤ goodBudget t + goodNoise t)
    (hbad : ∀ t,
      badTolerance t ≤ separatorCharge t + separatorNoise t)
    (hbudget :
      IsAsymptoticallySublinear (fun T =>
        shadowSeparatorCumulativeBudget T
          potentialDrift goodBudget separatorCharge
          potentialNoise goodNoise separatorNoise))
    (himplementation :
      IsAsymptoticallySublinear (fun T =>
        ∑ t ∈ Finset.range T, implementationCost t))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, payoffError t) ≤ δ := by
  exact (eventually_atTop.mp
    (eventually_shadowSeparatorPayoffErrorAverage_le
      L potential payoffError implementationCost
      transientCost potentialDrift potentialNoise
      goodMismatch goodBudget goodNoise
      badTolerance separatorCharge separatorNoise
      hL hpotential_nonneg hbad_nonneg hpayoff htransient hgood hbad
      hbudget himplementation hδ))

end

end Math.Probability
