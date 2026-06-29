/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.ApproximateNash
import GameTheory.Concepts.Mixed.MixedExtension

/-!
# Mixed improvement gaps

This file provides a lightweight endpoint for convergence arguments: if the
sum of positive pure-deviation gains at a mixed profile is small, then the
profile is an approximate Nash equilibrium of the mixed extension.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Filter
open Math.Probability

namespace KernelGame

variable {ι : Type}

private theorem max_zero_eq_zero_iff {x : ℝ} : max x 0 = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    exact (le_max_left x 0).trans_eq h
  · intro hx
    exact max_eq_right hx

/-- The aggregate positive pure-deviation gain at a mixed profile. -/
def mixedImprovement [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) : ℝ :=
  ∑ who, ∑ a : G.Strategy who, max (G.mixedGain σ who a) 0

theorem mixedImprovement_nonneg [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    0 ≤ G.mixedImprovement σ := by
  rw [mixedImprovement]
  exact Finset.sum_nonneg fun who _ =>
    Finset.sum_nonneg fun a _ => le_max_right _ _

theorem mixedGain_pospart_le_mixedImprovement [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (a : G.Strategy who) :
    max (G.mixedGain σ who a) 0 ≤ G.mixedImprovement σ := by
  have hterm :
      max (G.mixedGain σ who a) 0 ≤
        ∑ b : G.Strategy who, max (G.mixedGain σ who b) 0 := by
    exact Finset.single_le_sum (fun b _ => le_max_right _ _) (Finset.mem_univ a)
  have hplayer_nonneg :
      ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ ∑ b : G.Strategy i, max (G.mixedGain σ i b) 0 := by
    intro i _
    exact Finset.sum_nonneg fun b _ => le_max_right _ _
  have hplayer :
      (∑ b : G.Strategy who, max (G.mixedGain σ who b) 0) ≤
        G.mixedImprovement σ := by
    rw [mixedImprovement]
    exact Finset.single_le_sum hplayer_nonneg (Finset.mem_univ who)
  exact hterm.trans hplayer

theorem mixedGain_le_mixedImprovement [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (a : G.Strategy who) :
    G.mixedGain σ who a ≤ G.mixedImprovement σ :=
  (le_max_left _ _).trans (G.mixedGain_pospart_le_mixedImprovement σ who a)

theorem mixedGain_le_of_mixedImprovement_le [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    {σ : ∀ i, PMF (G.Strategy i)} {ε : ℝ}
    (hε : G.mixedImprovement σ ≤ ε) (who : ι) (a : G.Strategy who) :
    G.mixedGain σ who a ≤ ε :=
  (G.mixedGain_le_mixedImprovement σ who a).trans hε

theorem mixedImprovement_eq_zero_iff_gains_nonpos [DecidableEq ι] [Fintype ι]
    (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedImprovement σ = 0 ↔
      ∀ who (a : G.Strategy who), G.mixedGain σ who a ≤ 0 := by
  constructor
  · intro h who a
    have hpos :
        max (G.mixedGain σ who a) 0 ≤ 0 := by
      simpa [h] using G.mixedGain_pospart_le_mixedImprovement σ who a
    have hz : max (G.mixedGain σ who a) 0 = 0 :=
      le_antisymm hpos (le_max_right _ _)
    exact max_zero_eq_zero_iff.mp hz
  · intro h
    rw [mixedImprovement]
    simp [h]

theorem mixedImprovement_eq_zero_iff_isNash [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedImprovement σ = 0 ↔ G.mixedExtension.IsNash σ := by
  rw [G.mixedImprovement_eq_zero_iff_gains_nonpos σ, G.isNash_iff_gains_nonpos σ]

theorem isNash_iff_mixedImprovement_eq_zero [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedExtension.IsNash σ ↔ G.mixedImprovement σ = 0 :=
  (G.mixedImprovement_eq_zero_iff_isNash σ).symm

open Classical in
/-- Small aggregate positive pure-deviation gain implies ε-Nash for the mixed
extension. -/
theorem isεNash_of_mixedImprovement_le [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    {σ : ∀ i, PMF (G.Strategy i)} {ε : ℝ}
    (hε : G.mixedImprovement σ ≤ ε) :
    G.mixedExtension.IsεNash ε σ := by
  intro who τ
  rw [G.mixedExtension_eu_update σ who τ]
  have hpoint :
      ∀ a : G.Strategy who,
        G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who ≤
          G.mixedExtension.eu σ who + ε := by
    intro a
    have hg := G.mixedGain_le_of_mixedImprovement_le (σ := σ) hε who a
    rw [mixedGain] at hg
    linarith
  have hmono := expect_mono τ
    (fun a : G.Strategy who =>
      G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who)
    (fun _ => G.mixedExtension.eu σ who + ε) hpoint
  simpa [expect_const] using hmono

/-- A vanishing aggregate improvement gap eventually gives ε-Nash profiles. -/
theorem eventually_isεNash_of_mixedImprovement_tendsto_zero
    [DecidableEq ι] [Fintype ι] (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome]
    {σs : ℕ → ∀ i, PMF (G.Strategy i)}
    (hσ : Tendsto (fun n : ℕ => G.mixedImprovement (σs n)) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, G.mixedExtension.IsεNash ε (σs n) := by
  have hev : ∀ᶠ n in atTop, G.mixedImprovement (σs n) < ε :=
    hσ.eventually (eventually_lt_nhds hε)
  filter_upwards [hev] with n hn
  exact G.isεNash_of_mixedImprovement_le (σ := σs n) (le_of_lt hn)

end KernelGame

end GameTheory
