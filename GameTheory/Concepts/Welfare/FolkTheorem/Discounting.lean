/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Convex.Topology
import Math.SimplexApproximation
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Repeated.Discounted
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import GameTheory.Concepts.Welfare.FolkTheorem.Feasible

/-!
# Discounting Tools for Folk Theorems

Finite-cycle payoff constructions and patient-player margin lemmas used by
the discounted folk theorem. Repetition-generic discounted payoffs,
continuation values, and equilibrium are defined in
`GameTheory.Concepts.Repeated.Discounted`.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Average payoff of a nonempty finite cycle of stage profiles. -/
def cycleAveragePayoff (G : KernelGame ι) {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) : Payoff ι :=
  fun i => (n : ℝ)⁻¹ * ∑ t : Fin n, G.eu (cycle t) i

/-- The average payoff of a finite pure-profile cycle is feasible. -/
theorem cycleAveragePayoff_mem_feasibleSet (G : KernelGame ι)
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G) :
    G.cycleAveragePayoff cycle ∈ G.feasibleSet := by
  rw [feasibleSet]
  refine mem_convexHull_of_exists_fintype (s := G.purePayoffSet)
    (ι := Fin n) (fun _ => (n : ℝ)⁻¹) (fun t => G.payoffVector (cycle t)) ?_ ?_ ?_ ?_
  · intro _
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_comm,
      inv_mul_cancel₀ hn]
  · intro t
    exact ⟨cycle t, rfl⟩
  · ext i
    simp [cycleAveragePayoff, payoffVector, Finset.mul_sum, Pi.smul_apply,
      smul_eq_mul]

/-- Embed a finite pure-profile cycle into the mixed extension pointwise. -/
def pureMixedCycle (G : KernelGame ι) [Fintype ι]
    {n : ℕ} (cycle : Fin n → Profile G) : Fin n → Profile G.mixedExtension :=
  fun t => G.pureMixedProfile (cycle t)

/-- Cycle averages are preserved by embedding the cycle pointwise into the mixed
extension as Dirac mixed profiles. -/
theorem mixedExtension_cycleAveragePayoff_pureMixedCycle
    (G : KernelGame ι) [Fintype ι] {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) :
    G.mixedExtension.cycleAveragePayoff (G.pureMixedCycle cycle) =
      G.cycleAveragePayoff cycle := by
  funext i
  simp [cycleAveragePayoff, pureMixedCycle,
    G.mixedExtension_eu_pureMixedProfile]

/-- For sufficiently patient players, any fixed positive continuation margin
dominates a bounded one-period gain. -/
theorem exists_discountFactor_threshold_one_step
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 → (1 - δ) * M < δ * η := by
  let δ₀ : ℝ := M / (M + η)
  have hden_pos : 0 < M + η := by linarith
  refine ⟨δ₀, div_nonneg hM hden_pos.le, ?_, ?_⟩
  · rw [div_lt_one hden_pos]
    linarith
  · intro δ hδ _hδlt
    have hmul : M < δ * (M + η) := by
      exact (div_lt_iff₀ hden_pos).1 hδ
    nlinarith

/-- Strict coordinatewise domination over a finite player set has a uniform
positive slack. -/
theorem exists_pos_margin_of_mem_strictReservationSet [Finite ι]
    {r v : Payoff ι} (hv : v ∈ strictReservationSet r) :
    ∃ η : ℝ, 0 < η ∧ ∀ i, r i + η ≤ v i := by
  letI : Fintype ι := Fintype.ofFinite ι
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    let m : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : ι => v i - r i)
    have hmpos : 0 < m := by
      rw [Finset.lt_inf'_iff]
      intro i _hi
      exact sub_pos.mpr (hv i)
    refine ⟨m / 2, half_pos hmpos, ?_⟩
    intro i
    have hmi : m ≤ v i - r i := Finset.inf'_le _ (Finset.mem_univ i)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i
    exact False.elim (hι ⟨i⟩)

/-- Strict individual rationality over a finite player set has a uniform
positive slack over the reservation vector. -/
theorem exists_pos_margin_of_mem_strictIndividuallyRationalPayoffSet
    (G : KernelGame ι) [Finite ι] {r v : Payoff ι}
    (hv : v ∈ G.strictIndividuallyRationalPayoffSet r) :
    ∃ η : ℝ, 0 < η ∧ ∀ i, r i + η ≤ v i :=
  exists_pos_margin_of_mem_strictReservationSet hv.2

end KernelGame

end GameTheory
