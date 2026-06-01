/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.ProbabilityMassFunction
import Math.Reindex
import Math.PMFProduct.Basic

namespace Math
namespace PMFProduct

open scoped BigOperators
open Math.ProbabilityMassFunction

universe uι uA uα uβ uγ

set_option autoImplicit false


-- ============================================================================
-- Bind Factorization
-- ============================================================================

section BindFactor

variable {ι : Type uι} [DecidableEq ι]
variable {A : ι → Type uA}
variable {β : Type uβ}

@[simp] lemma update_update_same (σ : ∀ i, PMF (A i)) (j : ι) (τ₁ τ₂ : PMF (A j)) :
    Function.update (Function.update σ j τ₁) j τ₂ = Function.update σ j τ₂ := by
  exact Function.update_idem (a := j) τ₁ τ₂ σ

lemma update_update_comm (σ) {j k : ι} (hjk : j ≠ k) (τj : PMF (A j)) (τk : PMF (A k)) :
    Function.update (Function.update σ j τj) k τk =
    Function.update (Function.update σ k τk) j τj := by
  exact Function.update_comm (a := j) (b := k) hjk τj τk σ

variable [Fintype ι]

/-- `tsum` version: "Fubini" for product weights with an `Ignores₂` condition. -/
theorem tsum_pmfPi_factor
    (σ : ∀ i, PMF (A i)) (j : ι)
    (F : A j → (∀ i, A i) → ENNReal)
    (hF : Ignores₂ (A := A) j F) :
    (∑' s : (∀ i, A i), (∏ i, σ i (s i)) * F (s j) s)
      =
    ∑' a : A j, (σ j a) *
      (∑' s : (∀ i, A i), (∏ i, σ i (s i)) * F a s) := by
  have h_one : (∑' a : A j, σ j a) = 1 := PMF.tsum_coe (σ j)
  let W : (A j × (∀ i, A i)) → ENNReal := fun p =>
    σ j p.1 * ((σ j (p.2 j) * ∏ i ∈ Finset.univ.erase j, σ i (p.2 i)) * F p.1 p.2)
  let e := swapJA (A := A) j
  have he : Function.Involutive e := swapJA_involutive j
  have H_W_eq : ∀ (a : A j) (s : ∀ i, A i),
      σ j a * ((∏ i : ι, σ i (s i)) * F (s j) s) = W (e (a, s)) := by
    intro a s
    have hF_upd : F (s j) (@Function.update ι A (inferInstance) s j a) = F (s j) s := by
      simpa [update] using (hF (s j) s a)
    dsimp [W, e, swapJA]
    rw [prod_erase_update_eq (fun i x => σ i x) j s a, hF_upd]
    simp_rw [prod_factor_erase (fun i x => σ i x) j s]
    simp [mul_left_comm, mul_comm]
  calc
    (∑' s : (∀ i, A i), (∏ i, σ i (s i)) * F (s j) s)
        = (∑' s : (∀ i, A i), (∏ i, σ i (s i)) * F (s j) s) * 1 := by simp
    _ = (∑' s : (∀ i, A i), (∏ i, σ i (s i)) * F (s j) s) *
          (∑' a : A j, σ j a) := by simp [h_one]
    _ = ∑' a : A j, ∑' s : (∀ i, A i),
          σ j a * ((∏ i, σ i (s i)) * F (s j) s) := by
        rw [mul_comm]
        rw [← ENNReal.tsum_mul_right]
        congr 1
        ext a
        rw [ENNReal.tsum_mul_left]
    _ = ∑' a : A j, ∑' s : (∀ i, A i), W (e (a, s)) := by
        simp only [H_W_eq]
    _ = ∑' p : A j × (∀ i, A i), W (e p) := by
        rw [ENNReal.tsum_prod']
    _ = ∑' p : A j × (∀ i, A i), W p :=
        Math.Reindex.tsum_eq_tsum_of_involutive e he W
    _ = ∑' a : A j, σ j a *
          (∑' s : (∀ i, A i), (∏ i, σ i (s i)) * F a s) := by
        rw [ENNReal.tsum_prod']
        apply tsum_congr
        intro a
        dsimp [W]
        rw [ENNReal.tsum_mul_left]
        congr 1
        apply tsum_congr
        intro s
        rw [prod_factor_erase (fun i x => σ i x) j s]

/-- ENNReal-sum version: "Fubini" for product weights with an `Ignores₂` condition. -/
theorem sum_pmfPi_factor
    [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι)
    (F : A j → (∀ i, A i) → ENNReal)
    (hF : Ignores₂ (A := A) j F) :
    (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * F (s j) s)
      =
    ∑ a : A j, (σ j a) * (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * F a s) := by
  have h_one : (∑ a : A j, σ j a) = 1 := sum_coe_fintype (σ j)
  let W : (A j × (∀ i, A i)) → ENNReal := fun p =>
    σ j p.1 * ((σ j (p.2 j) * ∏ i ∈ Finset.univ.erase j, σ i (p.2 i)) * F p.1 p.2)
  let e := swapJA (A := A) j
  have he : Function.Involutive e := swapJA_involutive j
  -- Key: each summand under the swap equals the original summand
  have H_W_eq : ∀ (a : A j) (s : ∀ i, A i),
      σ j a * ((∏ i : ι, σ i (s i)) * F (s j) s) = W (e (a, s)) := by
    intro a s
    -- F (s j) (Function.update s j a) = F (s j) s by Ignores₂
    have hF_upd : F (s j) (@Function.update ι A (inferInstance) s j a) = F (s j) s := by
      simpa [update] using (hF (s j) s a)
    dsimp [W, e, swapJA]
    rw [prod_erase_update_eq (fun i x => σ i x) j s a, hF_upd]
    simp_rw [prod_factor_erase (fun i x => σ i x) j s]
    simp [mul_left_comm, mul_comm]
  calc (∑ s, (∏ i, σ i (s i)) * F (s j) s)
      = (∑ s, (∏ i, σ i (s i)) * F (s j) s) * 1 := by simp
    _ = (∑ s, (∏ i, σ i (s i)) * F (s j) s) * (∑ a, σ j a) := by
        simp [h_one]
    _ = ∑ a, ∑ s, σ j a * ((∏ i, σ i (s i)) * F (s j) s) := by
        simp only [mul_comm, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ a, ∑ s, W (e (a, s)) := by
        simp only [H_W_eq]
    _ = ∑ p : A j × (∀ i, A i), W (e p) :=
        (Fintype.sum_prod_type fun x ↦ W (e x)).symm
    _ = ∑ p : A j × (∀ i, A i), W p :=
        Math.Reindex.sum_univ_eq_sum_univ_of_involutive e he W
    _ = ∑ a, σ j a * ∑ s, (∏ i, σ i (s i)) * F a s := by
        simp [W, Fintype.sum_prod_type, Finset.mul_sum,
          prod_factor_erase (fun i x => σ i x) j, mul_left_comm, mul_comm]

/-- Bind factorization over a coordinate when the continuation ignores that coordinate. -/
theorem pmfPi_bind_factor [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι)
    (g : A j → (∀ i, A i) → PMF β)
    (hg : Ignores₂ (A := A) j g) :
    (pmfPi (A := A) σ).bind (fun s => g (s j) s)
      =
    (σ j).bind (fun a => (pmfPi (A := A) σ).bind (fun s => g a s)) := by
  classical
  letI (i : ι) : Fintype (A i) := Fintype.ofFinite (A i)
  ext b
  simp only [PMF.bind_apply, pmfPi_apply]
  exact tsum_pmfPi_factor σ j (fun a s => g a s b) (fun a0 s a => by
    exact congrFun (congrArg DFunLike.coe (hg a0 s a)) b)

omit [DecidableEq ι] in
/-- Marginalization: binding over the product and projecting to coordinate `j`
equals binding directly from the `j`-th marginal. -/
theorem pmfPi_bind_eval [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) {β : Type*} (f : A j → PMF β) :
    (pmfPi (A := A) σ).bind (fun s => f (s j)) = (σ j).bind f := by
  classical
  have hg : Ignores₂ (A := A) j (fun a (_ : ∀ i, A i) => f a) :=
    fun _ _ _ => rfl
  change (pmfPi (A := A) σ).bind
    (fun s => (fun a (_ : ∀ i, A i) => f a) (s j) s) = _
  rw [pmfPi_bind_factor σ j _ hg]
  simp only [PMF.bind_const]

end BindFactor

-- ============================================================================
-- Pushforward & Marginals
-- ============================================================================

section Pushforward

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA}
variable {α : Type uα} {β : Type uβ}

-- `pushforward` is defined in `Math.ProbabilityMassFunction`; re-exported here
-- so existing `PMFProduct.pushforward` references continue to resolve.
export Math.ProbabilityMassFunction
  (pushforward pushforward_comp pmfMask pmfMass pmfMass_ne_top pmfMass_pushforward
    pushforward_apply_eq_pmfMass pmfMass_true pmfCond pmfCond_apply pmfCond_ne_zero_implies
    pmfCond_ne_zero_iff pushforward_support_fibre)

omit [DecidableEq ι] in
open Classical in
/-- The pushforward of a product PMF through a coordinate-wise function
    is the product of pushforwards. -/
theorem pmfPi_push_coordwise
    {B : ι → Type*}
    (μ : ∀ i, PMF (A i)) (g : ∀ i, A i → B i) :
    pushforward (pmfPi (A := A) μ) (fun f => fun i => g i (f i))
      = pmfPi (A := B) (fun i => pushforward (μ i) (g i)) := by
  ext b
  simp only [pushforward, PMF.map_apply, pmfPi_apply]
  rw [← ENNReal_tsum_pi (g := fun i a => if b i = g i a then μ i a else 0)]
  apply tsum_congr
  intro f
  by_cases h : b = fun i => g i (f i)
  · subst h
    simp
  · rw [if_neg h]
    symm
    have ⟨i0, hi0⟩ : ∃ i0, b i0 ≠ g i0 (f i0) := by
      by_contra hall
      push Not at hall
      exact h (funext hall)
    exact Finset.prod_eq_zero (Finset.mem_univ i0) (by simp [hi0])

omit [DecidableEq ι] in
open Classical in
/-- The pushforward of a product distribution along a coordinate
    is the factor at that coordinate. -/
theorem pmfPi_push_coord [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) :
    pushforward (pmfPi (A := A) σ) (fun s => s j) = σ j := by
  change PMF.map (fun s : (∀ i, A i) => s j) (pmfPi (A := A) σ) = σ j
  rw [← PMF.bind_pure_comp (fun s : (∀ i, A i) => s j) (pmfPi (A := A) σ)]
  change (pmfPi (A := A) σ).bind (fun s => PMF.pure (s j)) = σ j
  rw [pmfPi_bind_eval σ j (fun a => PMF.pure a)]
  simp

omit [DecidableEq ι] in
open Classical in
/-- Pointwise marginal (`tsum` form) for a coordinate event. -/
theorem pmfPi_coord_mass_tsum
    [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) (a : A j) :
    (∑' s : (∀ i, A i), if s j = a then (pmfPi (A := A) σ) s else 0) = σ j a := by
  have h := congrFun (congrArg DFunLike.coe (pmfPi_push_coord σ j)) a
  simpa [pushforward, PMF.map_apply, pmfPi_apply, eq_comm] using h

open Classical in
/-- Pointwise marginal (sum-form) for a coordinate event. -/
theorem pmfPi_coord_mass
    [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) (a : A j) :
    (∑ s : (∀ i, A i), if s j = a then (pmfPi (A := A) σ) s else 0) = σ j a := by
  simpa [tsum_fintype] using pmfPi_coord_mass_tsum σ j a

end Pushforward

end PMFProduct

end Math
