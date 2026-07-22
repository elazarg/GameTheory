/-
# EXP-003 candidate B: normalized finitely-supported weights

This file intentionally develops the candidate as a concrete `Finsupp` type.
The conversion to `PMF` is an interoperability boundary, not its definition.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open scoped BigOperators NNReal

namespace GameTheory.Experimental.Phase1.D2.NormalizedFinsupp

universe u v w

/-- A finitely supported nonnegative weight vector of total mass one. -/
structure Law (α : Type u) where
  weight : α →₀ ℝ≥0
  mass_one : weight.sum (fun _ p => p) = 1

namespace Law

variable {α : Type u} {β : Type v} {γ : Type w}

@[ext]
theorem ext {μ ν : Law α} (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  simp_all

/-- A point mass. -/
def pure (a : α) : Law α where
  weight := Finsupp.single a 1
  mass_one := by simp

/-- Push weights forward, summing collisions. -/
def map (f : α → β) (μ : Law α) : Law β where
  weight := μ.weight.mapDomain f
  mass_one := by
    rw [Finsupp.sum_mapDomain_index]
    · exact μ.mass_one
    · intro
      rfl
    · intros
      rfl

/-- Kleisli composition as a finite weighted sum. -/
def bind (μ : Law α) (f : α → Law β) : Law β where
  weight := μ.weight.sum fun a p => p • (f a).weight
  mass_one := by
    classical
    rw [Finsupp.sum_sum_index]
    · calc
        μ.weight.sum (fun a p => (p • (f a).weight).sum fun _ q => q) =
            μ.weight.sum (fun _ p => p) := by
              apply Finsupp.sum_congr
              intro a ha
              rw [Finsupp.sum_smul_index]
              · calc
                  (f a).weight.sum (fun _ q => μ.weight a * q) =
                      μ.weight a * ((f a).weight.sum fun _ q => q) := by
                        simp [Finsupp.sum, Finset.mul_sum]
                  _ = μ.weight a := by rw [(f a).mass_one, mul_one]
              · intro
                rfl
        _ = 1 := μ.mass_one
    · intro
      rfl
    · intros
      rfl

/-- Independent binary product. -/
def product (μ : Law α) (ν : Law β) : Law (α × β) :=
  bind μ fun a => map (fun b => (a, b)) ν

@[simp]
theorem pure_weight [DecidableEq α] (a a' : α) :
    (pure a).weight a' = if a = a' then 1 else 0 := by
  exact Finsupp.single_apply

@[simp]
theorem map_weight [DecidableEq β] (f : α → β) (μ : Law α) (b : β) :
    (map f μ).weight b = μ.weight.sum fun a p => if f a = b then p else 0 := by
  classical
  change (μ.weight.sum fun a p => Finsupp.single (f a) p) b = _
  rw [Finsupp.sum_apply]
  apply Finsupp.sum_congr
  intro a ha
  exact Finsupp.single_apply

@[simp]
theorem bind_weight (μ : Law α) (f : α → Law β) (b : β) :
    (bind μ f).weight b = μ.weight.sum fun a p => p * (f a).weight b := by
  classical
  simp [bind, smul_eq_mul]

@[simp]
theorem pure_bind (a : α) (f : α → Law β) : bind (pure a) f = f a := by
  apply ext
  ext b
  simp [bind, pure]

@[simp]
theorem map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) := by
  apply ext
  classical
  simp [map, pure, Finsupp.mapDomain]

@[simp]
theorem product_pure (a : α) (b : β) : product (pure a) (pure b) = pure (a, b) := by
  simp [product]

@[simp]
theorem bind_pure (μ : Law α) : bind μ pure = μ := by
  apply ext
  ext a
  classical
  simp [bind, pure]

@[simp]
theorem bind_bind (μ : Law α) (f : α → Law β) (g : β → Law γ) :
    bind (bind μ f) g = bind μ fun a => bind (f a) g := by
  apply Law.ext
  apply Finsupp.ext
  intro c
  classical
  simp only [bind, Finsupp.sum_apply]
  rw [Finsupp.sum_sum_index]
  · apply Finsupp.sum_congr
    intro a ha
    rw [Finsupp.sum_smul_index]
    · simp only [Finsupp.sum, Finsupp.smul_apply, Finset.smul_sum, smul_eq_mul]
      rw [Finset.sum_apply']
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Finsupp.smul_apply, smul_eq_mul]
      ac_rfl
    · intro
      simp
  · intro
    simp
  · intros
    simp [add_mul]

/-- Real expectation is a finite sum with no summability premise. -/
def expect (μ : Law α) (u : α → ℝ) : ℝ :=
  μ.weight.sum fun a p => (p : ℝ) * u a

@[simp]
theorem expect_pure (a : α) (u : α → ℝ) : expect (pure a) u = u a := by
  simp [expect, pure]

theorem expect_bind (μ : Law α) (f : α → Law β) (u : β → ℝ) :
    expect (bind μ f) u = expect μ fun a => expect (f a) u := by
  classical
  simp only [expect, bind]
  rw [Finsupp.sum_sum_index]
  · apply Finsupp.sum_congr
    intro a ha
    rw [Finsupp.sum_smul_index]
    · simp only [Finsupp.sum, NNReal.coe_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    · intro
      simp
  · intro
    simp
  · intros
    simp [add_mul]

/-- The finite support is directly inspectable. -/
def support (μ : Law α) : Finset α := μ.weight.support

/-- Interoperate with Mathlib's `PMF`; the proof uses the stored finite sum. -/
def toPMF (μ : Law α) : PMF α :=
  PMF.ofFinset (fun a => μ.weight a) μ.weight.support
    (by simpa [Finsupp.sum] using congrArg ((↑) : ℝ≥0 → ENNReal) μ.mass_one)
    (fun a ha => by simpa [Finsupp.mem_support_iff] using ha)

@[simp]
theorem toPMF_apply (μ : Law α) (a : α) : μ.toPMF a = μ.weight a := rfl

/-- On a finite carrier, normalized weights are exactly Mathlib's real simplex. -/
def toSimplex [Fintype α] (μ : Law α) : stdSimplex ℝ α :=
  ⟨fun a => μ.weight a, by
    constructor
    · intro a
      exact NNReal.zero_le_coe
    · simpa [Finsupp.sum_fintype] using congrArg ((↑) : ℝ≥0 → ℝ) μ.mass_one⟩

/-- Turn simplex coordinates into a normalized `Finsupp`. -/
def ofSimplex [Fintype α] (x : stdSimplex ℝ α) : Law α where
  weight := Finsupp.equivFunOnFinite.symm fun a => ⟨x a, stdSimplex.zero_le x a⟩
  mass_one := by
    rw [Finsupp.sum_fintype]
    · apply NNReal.eq
      rw [NNReal.coe_sum]
      change ∑ i, x i = (1 : ℝ)
      exact stdSimplex.sum_eq_one x
    · intro
      rfl

@[simp]
theorem toSimplex_apply [Fintype α] (μ : Law α) (a : α) : μ.toSimplex a = μ.weight a := rfl

@[simp]
theorem ofSimplex_weight [Fintype α] (x : stdSimplex ℝ α) (a : α) :
    ((ofSimplex x).weight a : ℝ) = x a := by
  change (↑((Finsupp.equivFunOnFinite.symm fun a =>
    (⟨x a, stdSimplex.zero_le x a⟩ : ℝ≥0)) a) : ℝ) = x a
  rfl

/-- Candidate B's finite-carrier Analysis bridge. -/
def simplexEquiv [Fintype α] : Law α ≃ stdSimplex ℝ α where
  toFun := toSimplex
  invFun := ofSimplex
  left_inv μ := by
    apply ext
    ext a
    simp
  right_inv x := by
    apply stdSimplex.ext
    funext a
    simp

@[simp]
theorem simplexEquiv_pure [Fintype α] [DecidableEq α] (a : α) :
    simplexEquiv (pure a) = stdSimplex.vertex (S := ℝ) a := by
  have h : simplexEquiv (α := α) (pure a) = toSimplex (pure a) := rfl
  rw [h]
  apply stdSimplex.ext
  funext b
  simp only [toSimplex_apply, stdSimplex.vertex_coe]
  rw [pure_weight]
  by_cases hab : a = b <;> simp [hab, eq_comm]

theorem simplexEquiv_expect [Fintype α] (μ : Law α) (u : α → ℝ) :
    expect μ u = ∑ a, simplexEquiv μ a * u a := by
  rw [expect, Finsupp.sum_fintype (h := fun i => by simp)]
  change (∑ i, (μ.weight i : ℝ) * u i) = ∑ a, (μ.weight a : ℝ) * u a
  rfl

end Law

end GameTheory.Experimental.Phase1.D2.NormalizedFinsupp
