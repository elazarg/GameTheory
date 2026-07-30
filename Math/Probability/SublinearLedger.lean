/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.ShadowSeparatorAccounting

/-!
# Sublinear shadow-or-separator ledgers

This file turns the finite-horizon shadow-or-separator identity into the
asymptotic estimate consumed by public-phase equilibrium certificates.

The game-specific construction remains responsible for proving that each
named cumulative budget is sublinear.  Once those estimates are available,
the theorem below combines them without reopening the pathwise accounting.
-/

open Filter Set Topology

namespace Math.Probability

noncomputable section

/-- A real cumulative budget is sublinear when its ratio to calendar time
converges to zero. -/
def IsAsymptoticallySublinear (budget : ℕ → ℝ) : Prop :=
  Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * budget T) atTop (nhds 0)

namespace IsAsymptoticallySublinear

theorem const (c : ℝ) :
    IsAsymptoticallySublinear (fun _ : ℕ => c) := by
  simpa [IsAsymptoticallySublinear] using
    (tendsto_natCast_atTop_atTop.inv_tendsto_atTop.mul_const c)

theorem add {f g : ℕ → ℝ}
    (hf : IsAsymptoticallySublinear f)
    (hg : IsAsymptoticallySublinear g) :
    IsAsymptoticallySublinear (fun T => f T + g T) := by
  change Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * f T) atTop (nhds 0) at hf
  change Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * g T) atTop (nhds 0) at hg
  simpa only [IsAsymptoticallySublinear, mul_add, add_zero] using
    Filter.Tendsto.add hf hg

theorem const_mul {f : ℕ → ℝ}
    (hf : IsAsymptoticallySublinear f) (c : ℝ) :
    IsAsymptoticallySublinear (fun T => c * f T) := by
  change Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * f T) atTop (nhds 0) at hf
  simpa only [IsAsymptoticallySublinear, ← mul_assoc, mul_comm c,
    mul_zero, zero_mul] using Filter.Tendsto.const_mul c hf

theorem eventually_average_le {f : ℕ → ℝ}
    (hf : IsAsymptoticallySublinear f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℕ in atTop, (T : ℝ)⁻¹ * f T ≤ δ := by
  exact (hf.eventually (eventually_lt_nhds hδ)).mono
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
