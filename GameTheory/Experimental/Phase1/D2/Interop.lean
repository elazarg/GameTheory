/- # EXP-003 interoperability, dependent-product, and concrete stress. -/

import GameTheory.Experimental.Phase1.D2.FiniteSupportPMF
import GameTheory.Experimental.Phase1.D2.NormalizedFinsupp

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.Phase1.D2.Interop

universe u

namespace A
abbrev Law (α : Type u) := FiniteSupportPMF.Law α
export FiniteSupportPMF.Law (toPMF support support_finite pure map product product_apply
  pi mix expect expect_mix simplexEquiv)
end A

namespace B
abbrev Law (α : Type u) := NormalizedFinsupp.Law α
export NormalizedFinsupp.Law (pure map bind product expect toPMF toPMF_apply simplexEquiv)
end B

variable {α β : Type u}

/-- Candidate B's canonical Mathlib `PMF` carries finite support. -/
def bToA {α : Type u} (μ : B.Law α) : A.Law α :=
  ⟨μ.toPMF, by
    apply (Set.finite_mem_finset μ.weight.support).subset
    intro a ha
    simp only [Set.mem_setOf_eq, B.toPMF_apply, PMF.mem_support_iff,
      ENNReal.coe_ne_zero, Finsupp.mem_support_iff] at ha ⊢
    exact ha⟩

@[simp]
theorem bToA_toPMF {α : Type u} (μ : B.Law α) : (bToA μ).toPMF = μ.toPMF := rfl

/-- Forget the PMF presentation by extracting its finite NNReal weight vector. -/
def aToB {α : Type u} (μ : A.Law α) : B.Law α where
  weight := Finsupp.onFinset μ.support_finite.toFinset
    (fun a => (μ.toPMF a).toNNReal)
    (fun a ha => by
      apply (Set.Finite.mem_toFinset μ.support_finite).2
      change μ.toPMF a ≠ 0
      intro hz
      exact ha (by simp [hz]))
  mass_one := by
    rw [Finsupp.sum_onFinset]
    · rw [← ENNReal.toNNReal_sum (fun a _ => PMF.apply_ne_top μ.toPMF a)]
      have hout : ∀ a ∉ μ.support_finite.toFinset, μ.toPMF a = 0 := by
        intro a ha
        apply μ.toPMF.apply_eq_zero_iff a |>.2
        change a ∉ μ.support
        simpa [Set.Finite.mem_toFinset] using ha
      have hfinite : (∑' a, μ.toPMF a) =
          ∑ a ∈ μ.support_finite.toFinset, μ.toPMF a := tsum_eq_sum hout
      have hsum : ∑ a ∈ μ.support_finite.toFinset, μ.toPMF a = 1 :=
        hfinite.symm.trans (PMF.tsum_coe μ.toPMF)
      rw [hsum]
      rfl
    · intros
      rfl

@[simp]
theorem aToB_weight {α : Type u} (μ : A.Law α) (a : α) :
    (aToB μ).weight a = (μ.toPMF a).toNNReal := by
  classical
  simp [aToB]

/-- Candidate B's dependent product, routed through its explicit PMF boundary.
This implementation is deliberately measured as interop overhead. -/
def bPi {ι : Type*} [Fintype ι] {S : ι → Type*} (μ : ∀ i, B.Law (S i)) :
    B.Law (∀ i, S i) :=
  aToB (A.pi fun i => bToA (μ i))

/-- A genuinely nontrivial finite-support law on the infinite carrier `Nat`. -/
def infiniteCarrierA : A.Law ℕ :=
  A.mix (1 / 2) (by norm_num) (A.pure 7) (A.pure 11)

/-- Candidate B's native `Finsupp` also carries two points on `Nat`. -/
def infiniteCarrierB : B.Law ℕ where
  weight := Finsupp.single 7 (1 / 2) + Finsupp.single 11 (1 / 2)
  mass_one := by
    classical
    rw [Finsupp.sum_add_index]
    · norm_num
    · simp
    · intros
      rfl

@[simp]
theorem inspect_infiniteCarrierA : A.expect infiniteCarrierA (fun n => (n : ℝ)) = 9 := by
  rw [infiniteCarrierA, A.expect_mix]
  norm_num

@[simp]
theorem inspect_infiniteCarrierB : B.expect infiniteCarrierB (fun n => (n : ℝ)) = 9 := by
  classical
  simp only [infiniteCarrierB, NormalizedFinsupp.Law.expect]
  rw [Finsupp.sum_add_index]
  · norm_num
  · simp
  · intros
    simp [add_mul]

theorem a_simplex_product [Fintype α] [Fintype β]
    (μ : A.Law α) (ν : A.Law β) (a : α) (b : β) :
    A.simplexEquiv (A.product μ ν) (a, b) =
      A.simplexEquiv μ a * A.simplexEquiv ν b := by
  change ((A.product μ ν).toPMF (a, b)).toReal =
    (μ.toPMF a).toReal * (ν.toPMF b).toReal
  rw [A.product_apply, ENNReal.toReal_mul]

theorem b_simplex_pure_product [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (a : α) (b : β) :
    B.simplexEquiv (B.product (B.pure a) (B.pure b)) =
      stdSimplex.vertex (S := ℝ) (a, b) := by
  simp [B.product]

end GameTheory.Experimental.Phase1.D2.Interop
