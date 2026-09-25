import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.Mixture
import Mathlib.Probability.Distributions.Uniform

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

/-- Expected value under a finite uniform law is the arithmetic mean. -/
theorem expect_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    expect (PMF.uniformOfFintype α) f
        (payoffIntegrable_of_finite _ f) =
      (∑ a, f a) / Fintype.card α := by
  rw [expect_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  ring

/-- The uniform expectation formula specialized to `Fin T`. -/
theorem expect_uniformFin {T : ℕ} [NeZero T] (f : Fin T → ℝ) :
    expect (PMF.uniformOfFintype (Fin T)) f
        (payoffIntegrable_of_finite _ f) = (∑ t, f t) / T := by
  simpa only [Fintype.card_fin] using expect_uniformOfFintype f

/-- The mass of an atom under the image of a finite uniform law is its fiber
cardinality divided by the size of the source carrier. -/
theorem uniformOfFintype_map_apply {α β : Type*} [Fintype α] [Nonempty α]
    [DecidableEq β] (f : α → β) (b : β) :
    (PMF.uniformOfFintype α).map f b =
      ((Finset.univ.filter fun a => f a = b).card : ENNReal) /
        (Fintype.card α : ENNReal) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp [eq_comm, div_eq_mul_inv]

/-- Splitting the final point from a finite uniform sample gives the uniform
law on the initial segment mixed with the final atom. -/
theorem uniformOfFintype_map_fin_succ {β : Type*} (n : ℕ) [NeZero n]
    (f : Fin (n + 1) → β) :
    (PMF.uniformOfFintype (Fin (n + 1))).map f =
      mix ((n : ℝ) / (n + 1)) (by positivity) (by
        have hn : (0 : ℝ) < n + 1 := by positivity
        rw [div_le_iff₀ hn]
        norm_num)
        ((PMF.uniformOfFintype (Fin n)).map fun i => f i.castSucc)
        (PMF.pure (f (Fin.last n))) := by
  classical
  ext b
  have hcard :
      (Finset.univ.filter fun i : Fin (n + 1) => f i = b).card =
        (Finset.univ.filter fun i : Fin n => f i.castSucc = b).card +
          if f (Fin.last n) = b then 1 else 0 := by
    rw [Finset.card_filter, Finset.card_filter]
    simp only [Fin.sum_univ_castSucc]
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hratio : 1 - (n : ℝ) / (n + 1) = 1 / (n + 1) := by
    field_simp
    ring
  have hleft := PMF.apply_ne_top
    ((PMF.uniformOfFintype (Fin (n + 1))).map f) b
  have hright := PMF.apply_ne_top
    (mix ((n : ℝ) / (n + 1)) (by positivity) (by
      have hn : (0 : ℝ) < n + 1 := by positivity
      rw [div_le_iff₀ hn]
      norm_num)
      ((PMF.uniformOfFintype (Fin n)).map fun i => f i.castSucc)
      (PMF.pure (f (Fin.last n)))) b
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).1
  rw [uniformOfFintype_map_apply, mix_apply,
    uniformOfFintype_map_apply, PMF.pure_apply]
  rw [hcard]
  rw [ENNReal.ofReal_div_of_pos hn1, hratio,
    ENNReal.ofReal_div_of_pos hn1]
  simp only [Fintype.card_fin]
  have hcardne :
      ((Finset.univ.filter fun i : Fin n => b = f i.castSucc).card : ENNReal) ≠ ⊤ := by
    simp
  have hnne : (n : ENNReal) ≠ 0 := by
    exact_mod_cast NeZero.ne n
  have hdenne : ENNReal.ofReal (n + 1) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hn1
  have hterm : ((n : ENNReal) / ENNReal.ofReal (n + 1)) *
      (((Finset.univ.filter fun i : Fin n => b = f i.castSucc).card : ENNReal) /
        (n : ENNReal)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.div_ne_top (by simp) hdenne
    · exact ENNReal.div_ne_top hcardne hnne
  have hterm' : (1 : ENNReal) / ENNReal.ofReal (n + 1) * 1 ≠ ⊤ := by
    rw [mul_one]
    exact ENNReal.div_ne_top (by simp) hdenne
  have hdenreal : (ENNReal.ofReal (n + 1)).toReal = (n + 1 : ℝ) :=
    ENNReal.toReal_ofReal hn1.le
  by_cases hlast : f (Fin.last n) = b
  · simp only [hlast, eq_comm, ite_true]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    rw [ENNReal.toReal_add hterm (by simpa using hterm')]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div]
    rw [hdenreal]
    simp only [ENNReal.toReal_natCast]
    simp only [ENNReal.toReal_one]
    field_simp
    push_cast
    ring
  · have hneq : b ≠ f (Fin.last n) := by
      intro heq
      exact hlast heq.symm
    rw [ite_eq_right hlast, ite_eq_right hneq]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    simp only [mul_zero, add_zero]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div]
    rw [hdenreal]
    simp only [ENNReal.toReal_natCast]
    field_simp
    push_cast
    ring

end GameTheory.Math.Probability
