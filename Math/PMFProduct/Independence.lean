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
import Math.PMFProduct.Update

namespace Math
namespace PMFProduct

open scoped BigOperators
open Math.ProbabilityMassFunction

universe uι uA uα uβ uγ

set_option autoImplicit false


-- ============================================================================
-- Product-measure independence for bind
-- ============================================================================

section BindIndep

variable {ι : Type uι}
variable [DecidableEq ι]
variable {A : ι → Type uA}

open Classical in
/-- Replace coordinates in `K` of `x` by those of `y`. -/
noncomputable def replaceOn (K : Finset ι) (x y : ∀ i, A i) : (∀ i, A i) :=
  K.piecewise y x

open Classical in
@[simp] lemma replaceOn_apply (K : Finset ι) (x y : ∀ i, A i) (i : ι) :
    replaceOn K x y i = (if i ∈ K then y i else x i) := by
  rfl

@[simp] lemma replaceOn_empty (x y : ∀ i, A i) :
    replaceOn (A := A) (K := ∅) x y = x := by
  simp [replaceOn]

open Classical in
lemma replaceOn_insert (K : Finset ι) (j : ι) (_hj : j ∉ K)
    (x y : ∀ i, A i) :
    replaceOn (A := A) (K := insert j K) x y =
      Function.update (replaceOn (A := A) (K := K) x y) j (y j) := by
  simpa [replaceOn] using Finset.piecewise_insert K y x j

open Classical in
lemma ignores_replaceOn_eq
    {β : Type*}
    (h : (∀ i, A i) → β)
    (K : Finset ι)
    (hign : ∀ j, j ∈ K → Ignores j h)
    (x y : ∀ i, A i) :
    h (replaceOn (A := A) K x y) = h x := by
  induction K using Finset.induction with
  | empty =>
      simp [replaceOn_empty]
  | @insert j K hj ih =>
      have hignj : Ignores j h := hign j (by simp)
      have hignK : ∀ k, k ∈ K → Ignores k h := by
        intro k hk
        exact hign k (by simp [hk])
      rw [replaceOn_insert (A := A) K j hj x y]
      have hstep :
          h (@Function.update ι A (inferInstance) (replaceOn (A := A) (K := K) x y) j (y j))
            = h (replaceOn (A := A) (K := K) x y) := by
        simpa [update] using (hignj (replaceOn (A := A) (K := K) x y) (y j))
      rw [hstep]
      exact ih hignK

lemma replaceOn_univ_snd [Fintype ι] (x y : ∀ i, A i) :
    replaceOn (A := A) (K := Finset.univ) x y = y := by
  simp [replaceOn]

open Classical in
lemma replaceOn_univ_diff [Fintype ι] (J : Finset ι) (x y : ∀ i, A i) :
    replaceOn (A := A) (K := Finset.univ \ J) x y =
      fun i => if i ∈ J then x i else y i := by
  funext i
  by_cases hi : i ∈ J
  · simp [replaceOn, hi]
  · simp [replaceOn, hi]

/-- **Product-measure independence for bind.**
    If `f` uses only `J`-coordinates (i.e., ignores all `j ∉ J`) and
    `g b` ignores `J`-coordinates, then drawing once from `pmfPi σ` and
    using the same sample for both `f` and `g` gives the same distribution
    as drawing independently for each. -/
theorem pmfPi_bind_indep [Fintype ι] [∀ i, Finite (A i)]
    {β γ : Type*} [Finite β]
    (σ : ∀ i, PMF (A i))
    (f : (∀ i, A i) → PMF β)
    (g : β → (∀ i, A i) → PMF γ)
    (J : Finset ι)
    (hf : ∀ j, j ∉ J → Ignores j f)
    (hg : ∀ j, j ∈ J → ∀ b, Ignores j (g b)) :
    (pmfPi σ).bind (fun s => (f s).bind (fun b => g b s)) =
    (pmfPi σ).bind (fun s => (f s).bind (fun b =>
      (pmfPi σ).bind (fun t => g b t))) := by
  classical
  letI (i : ι) : Fintype (A i) := Fintype.ofFinite (A i)
  letI : Fintype β := Fintype.ofFinite β
  ext y
  simp only [PMF.bind_apply, pmfPi_apply, tsum_fintype]
  let P : (∀ i, A i) → ENNReal := fun s => ∏ i, σ i (s i)
  let Fsame : ((∀ i, A i) × (∀ i, A i)) → ENNReal :=
    fun p => (P p.1 * P p.2) * ∑ b : β, f p.1 b * g b p.1 y
  let Fcross : ((∀ i, A i) × (∀ i, A i)) → ENNReal :=
    fun p => (P p.1 * P p.2) * ∑ b : β, f p.1 b * g b p.2 y
  let e : ((∀ i, A i) × (∀ i, A i)) → ((∀ i, A i) × (∀ i, A i)) :=
    fun p => (replaceOn (A := A) (Finset.univ \ J) p.1 p.2,
              replaceOn (A := A) J p.1 p.2)
  have he : Function.Involutive e := by
    intro p
    rcases p with ⟨s, t⟩
    apply Prod.ext
    · funext i
      by_cases hiJ : i ∈ J
      · simp [e, replaceOn, hiJ]
      · simp [e, replaceOn, hiJ]
    · funext i
      by_cases hiJ : i ∈ J
      · simp [e, replaceOn, hiJ]
      · simp [e, replaceOn, hiJ]
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro p
    rcases p with ⟨s, t⟩
    set s' : (∀ i, A i) := replaceOn (A := A) (Finset.univ \ J) s t
    set t' : (∀ i, A i) := replaceOn (A := A) J s t
    have hweight : P s * P t = P s' * P t' := by
      simp only [P]
      calc
        (∏ i, σ i (s i)) * (∏ i, σ i (t i))
            = ∏ i, (σ i (s i) * σ i (t i)) := by rw [← Finset.prod_mul_distrib]
        _ = ∏ i, (σ i (s' i) * σ i (t' i)) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            by_cases hiJ : i ∈ J
            · simp [s', t', hiJ]
            · simp [s', t', hiJ, mul_comm]
        _ = (∏ i, σ i (s' i)) * (∏ i, σ i (t' i)) := by rw [Finset.prod_mul_distrib]
    have hf' : f s' = f s := by
      have hignOut : ∀ j, j ∈ (Finset.univ \ J) → Ignores j f := by
        intro j hj
        exact hf j (by simpa using hj)
      simpa [s', replaceOn] using
        (ignores_replaceOn_eq (A := A) f (Finset.univ \ J) hignOut s t)
    have hg' : ∀ b : β, g b s' = g b t := by
      intro b
      have hignIn : ∀ j, j ∈ J → Ignores j (g b) := fun j hj => hg j hj b
      -- s' = replaceOn J t s
      have hs' : s' = replaceOn (A := A) J t s := by
        funext i
        by_cases hiJ : i ∈ J
        · simp [s', replaceOn, hiJ]
        · simp [s', replaceOn, hiJ]
      rw [hs']
      simpa using (ignores_replaceOn_eq (A := A) (g b) J hignIn t s)
    simp [Fcross, Fsame, e, s', t', hweight, hf', hg']
  have hpair : (∑ p, Fcross p) = ∑ p, Fsame p := by
    calc
      (∑ p, Fcross p) = ∑ p, Fsame (e p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p
      _ = ∑ p, Fsame p := Math.Reindex.sum_univ_eq_sum_univ_of_involutive e he Fsame
  have hsumP : (∑ t : (∀ i, A i), P t) = 1 := by
    simpa [P] using (sum_coe_fintype (pmfPi (A := A) σ))
  have hL :
      (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * ∑ b : β, f s b * g b s y)
      = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := by
    calc
      (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * ∑ b : β, f s b * g b s y)
          = (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * ∑ b : β, f s b * g b s y)
              * (∑ t : (∀ i, A i), P t) := by
              simp [hsumP]
      _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := by
          simp [Fsame, P, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
            mul_assoc, mul_comm]
  have hR :
      (∑ s : (∀ i, A i),
          (∏ i, σ i (s i)) * ∑ b : β, f s b * ∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g b t y)
      = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by
    calc
      (∑ s : (∀ i, A i),
          (∏ i, σ i (s i)) * ∑ b : β, f s b * ∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g b t y)
          = ∑ s : (∀ i, A i), ∑ t : (∀ i, A i),
              (P s * P t) * ∑ b : β, f s b * g b t y := by
                apply Finset.sum_congr rfl
                intro s hs
                calc
                  (∏ i, σ i (s i)) * ∑ b : β, f s b * ∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g b t y
                      = ∑ b : β, ∑ t : (∀ i, A i),
                          (P s) * (f s b * (P t * g b t y)) := by
                            simp [P, Finset.mul_sum, mul_comm]
                  _ = ∑ t : (∀ i, A i), ∑ b : β,
                        (P s) * (f s b * (P t * g b t y)) := by
                            simpa using
                              (Finset.sum_comm :
                                (∑ b : β, ∑ t : (∀ i, A i), (P s) * (f s b * (P t * g b t y)))
                                  = ∑ t : (∀ i, A i), ∑ b : β,
                                      (P s) * (f s b * (P t * g b t y)))
                  _ = ∑ t : (∀ i, A i), (P s * P t) * ∑ b : β, f s b * g b t y := by
                        apply Finset.sum_congr rfl
                        intro t ht
                        calc
                          ∑ b : β, (P s) * (f s b * (P t * g b t y))
                              = ∑ b : β, ((P s * P t) * (f s b * g b t y)) := by
                                  apply Finset.sum_congr rfl
                                  intro b hb
                                  ac_rfl
                          _ = (P s * P t) * ∑ b : β, f s b * g b t y := by
                                  rw [Finset.mul_sum]
      _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by
          simp [Fcross, Fintype.sum_prod_type]
  calc
    (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * ∑ b : β, f s b * g b s y)
        = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := hL
    _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by simpa using hpair.symm
    _ =
        (∑ s : (∀ i, A i),
          (∏ i, σ i (s i)) * ∑ b : β, f s b * ∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g b t y) :=
      hR.symm

end BindIndep

-- ============================================================================
-- Scalar independence under product measure
-- ============================================================================

section ScalarIndep

variable {ι : Type*}
variable {A : ι → Type*}

open Classical in
/-- **Scalar independence under product measure.**
    If `f` ignores all coordinates outside `J` and `g` ignores all coordinates
    inside `J`, then `E[f·g] = E[f]·E[g]` under the product measure `pmfPi σ`. -/
theorem pmfPi_expect_indep [Fintype ι] [DecidableEq ι] [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i))
    (f g : (∀ i, A i) → ENNReal)
    (J : Finset ι)
    (hf : ∀ j, j ∉ J → Ignores j f)
    (hg : ∀ j, j ∈ J → Ignores j g) :
    (∑ s, (pmfPi σ) s * (f s * g s)) =
      (∑ s, (pmfPi σ) s * f s) * (∑ s, (pmfPi σ) s * g s) := by
  classical
  simp only [pmfPi_apply]
  let P : (∀ i, A i) → ENNReal := fun s => ∏ i, σ i (s i)
  let Fsame : ((∀ i, A i) × (∀ i, A i)) → ENNReal :=
    fun p => (P p.1 * P p.2) * (f p.1 * g p.1)
  let Fcross : ((∀ i, A i) × (∀ i, A i)) → ENNReal :=
    fun p => (P p.1 * P p.2) * (f p.1 * g p.2)
  let e : ((∀ i, A i) × (∀ i, A i)) → ((∀ i, A i) × (∀ i, A i)) :=
    fun p => (replaceOn (A := A) (Finset.univ \ J) p.1 p.2,
              replaceOn (A := A) J p.1 p.2)
  have he : Function.Involutive e := by
    intro p
    rcases p with ⟨s, t⟩
    apply Prod.ext
    · funext i; by_cases hiJ : i ∈ J <;> simp [e, replaceOn, hiJ]
    · funext i; by_cases hiJ : i ∈ J <;> simp [e, replaceOn, hiJ]
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro ⟨s, t⟩
    set s' : (∀ i, A i) := replaceOn (A := A) (Finset.univ \ J) s t
    set t' : (∀ i, A i) := replaceOn (A := A) J s t
    have hweight : P s * P t = P s' * P t' := by
      simp only [P]
      calc
        (∏ i, σ i (s i)) * (∏ i, σ i (t i))
            = ∏ i, (σ i (s i) * σ i (t i)) := by rw [← Finset.prod_mul_distrib]
        _ = ∏ i, (σ i (s' i) * σ i (t' i)) := by
            refine Finset.prod_congr rfl ?_
            intro i _; by_cases hiJ : i ∈ J <;> simp [s', t', hiJ, mul_comm]
        _ = (∏ i, σ i (s' i)) * (∏ i, σ i (t' i)) := by rw [Finset.prod_mul_distrib]
    have hf' : f s' = f s := by
      have hignOut : ∀ j, j ∈ (Finset.univ \ J) → Ignores j f := by
        intro j hj
        exact hf j (by simpa using hj)
      simpa [s', replaceOn] using
        (ignores_replaceOn_eq (A := A) f (Finset.univ \ J) hignOut s t)
    have hg' : g s' = g t := by
      have hignIn : ∀ j, j ∈ J → Ignores j g := fun j hj => hg j hj
      have hs' : s' = replaceOn (A := A) J t s := by
        funext i; by_cases hiJ : i ∈ J <;> simp [s', replaceOn, hiJ]
      rw [hs']
      simpa using (ignores_replaceOn_eq (A := A) g J hignIn t s)
    simp [Fcross, Fsame, e, s', t', hweight, hf', hg']
  have hpair : (∑ p, Fcross p) = ∑ p, Fsame p := by
    calc
      (∑ p, Fcross p) = ∑ p, Fsame (e p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p
      _ = ∑ p, Fsame p := Math.Reindex.sum_univ_eq_sum_univ_of_involutive e he Fsame
  have hsumP : (∑ t : (∀ i, A i), P t) = 1 := by
    simpa [P] using (sum_coe_fintype (pmfPi (A := A) σ))
  have hL :
      (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * (f s * g s))
      = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := by
    calc
      (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * (f s * g s))
          = (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * (f s * g s))
              * (∑ t : (∀ i, A i), P t) := by
              simp [hsumP]
      _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := by
          simp [Fsame, P, Fintype.sum_prod_type, Finset.mul_sum,
            mul_assoc, mul_comm]
  have hR :
      (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * f s)
        * (∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g t)
      = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by
    calc
      (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * f s)
          * (∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g t)
          = ∑ s : (∀ i, A i), ∑ t : (∀ i, A i),
              ((∏ i, σ i (s i)) * f s) * ((∏ i, σ i (t i)) * g t) := by
                rw [Finset.sum_mul_sum]
      _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by
          simp [Fcross, P, Fintype.sum_prod_type, mul_assoc, mul_comm, mul_left_comm]
  calc
    (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * (f s * g s))
        = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fsame p := hL
    _ = ∑ p : ((∀ i, A i) × (∀ i, A i)), Fcross p := by simpa using hpair.symm
    _ = (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * f s)
          * (∑ t : (∀ i, A i), (∏ i, σ i (t i)) * g t) := hR.symm

end ScalarIndep

-- ============================================================================
-- Cross-index product-bind factorization
-- ============================================================================

/-- A `Finset.prod` of functions that all ignore coordinate `j` also ignores `j`. -/
lemma Ignores_finset_prod
    {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    {κ : Type*} {α : Type*} [CommMonoid α]
    (j : ι) (F : κ → (∀ i, A i) → α) (S : Finset κ)
    (hF : ∀ k, k ∈ S → Ignores j (F k)) :
    Ignores j (fun s => ∏ k ∈ S, F k s) := by
  intro s a
  exact Finset.prod_congr rfl (fun k hk => hF k hk s a)

/-- **Cross-index product-bind factorization.**

If each factor `G a k` of the inner product depends on at most one
coordinate of `a`, and no two factors share the same dependency, then
binding the outer product with the inner product equals the product
of individual bindings.

`coord k` specifies the single coordinate that `G · k` may depend on
(`none` = constant in `a`). The conditions are:
- `h_const`: if `coord k = none`, then `G · k` ignores all coordinates.
- `h_single`: if `coord k = some i`, then `G · k` ignores all `j ≠ i`.
- `h_inj`: no two factors depend on the same coordinate.

Proof: by `Finset.induction_on`, peeling off one factor at a time using
`pmfPi_expect_indep` (E[f·g] = E[f]·E[g] for independent f, g). -/
theorem pmfPi_bind_pmfPi_of_disjoint_coords
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Finite (A i)]
    {κ : Type*} [Fintype κ] {B : κ → Type*} [∀ k, Finite (B k)]
    (σ : ∀ i, PMF (A i))
    (G : (∀ i, A i) → ∀ k, PMF (B k))
    (coord : κ → Option ι)
    (h_const : ∀ k, coord k = none → ∀ j, Ignores j (fun a => G a k))
    (h_single : ∀ k i, coord k = some i → ∀ j, j ≠ i →
      Ignores j (fun a => G a k))
    (h_inj : ∀ k₁ k₂ i, coord k₁ = some i → coord k₂ = some i → k₁ = k₂) :
    (pmfPi σ).bind (fun a => pmfPi (G a)) =
      pmfPi (fun k => (pmfPi σ).bind (fun a => G a k)) := by
  classical
  letI (i : ι) : Fintype (A i) := Fintype.ofFinite (A i)
  letI (k : κ) : Fintype (B k) := Fintype.ofFinite (B k)
  ext vals
  simp only [PMF.bind_apply, pmfPi_apply, tsum_fintype]
  -- Helper: Ignores on PMFs implies Ignores on pointwise values
  have pt : ∀ k j, Ignores j (fun a => G a k) →
      Ignores j (fun a => (G a k) (vals k)) :=
    fun k j hign s a => congrFun (congrArg DFunLike.coe (hign s a)) (vals k)
  -- Main claim by Finset induction
  suffices hmain : ∀ S : Finset κ,
      (∀ k₁ k₂, k₁ ∈ S → k₂ ∈ S → k₁ ≠ k₂ →
        ∀ i, coord k₁ = some i → coord k₂ ≠ some i) →
      ∑ a, (pmfPi σ) a * ∏ k ∈ S, (G a k) (vals k) =
        ∏ k ∈ S, (∑ a, (pmfPi σ) a * (G a k) (vals k)) by
    simp only [pmfPi_apply] at hmain
    exact hmain Finset.univ
      (fun k₁ k₂ _ _ hne i h1 h2 => absurd (h_inj k₁ k₂ i h1 h2) hne)
  intro S hS
  induction S using Finset.induction_on with
  | empty =>
    simp only [pmfPi_apply, Finset.prod_empty, mul_one]
    exact sum_coe_fintype (pmfPi σ)
  | insert k₀ S' hk₀ ih =>
    have hS' : ∀ k₁ k₂, k₁ ∈ S' → k₂ ∈ S' → k₁ ≠ k₂ →
        ∀ i, coord k₁ = some i → coord k₂ ≠ some i :=
      fun k₁ k₂ h1 h2 => hS k₁ k₂
        (Finset.mem_insert_of_mem h1) (Finset.mem_insert_of_mem h2)
    conv_lhs => arg 2; ext a; rw [Finset.prod_insert hk₀]
    conv_rhs => rw [Finset.prod_insert hk₀, ← ih hS']
    -- Goal: ∑ a, P a * (f a * g a) = (∑ a, P a * f a) * (∑ a, P a * g a)
    -- where f a = (G a k₀)(vals k₀), g a = ∏_{S'} (G a k)(vals k)
    -- Choose J = {i₀} if coord k₀ = some i₀, else ∅
    set J : Finset ι := match coord k₀ with | none => ∅ | some i₀ => {i₀}
    -- f ignores j ∉ J
    have hf : ∀ j, j ∉ J → Ignores j (fun a => (G a k₀) (vals k₀)) := by
      intro j hj
      cases hc : coord k₀ with
      | none => exact pt k₀ j (h_const k₀ hc j)
      | some i₀ =>
        simp only [J, hc, Finset.mem_singleton] at hj
        exact pt k₀ j (h_single k₀ i₀ hc j hj)
    -- g ignores j ∈ J
    have hg : ∀ j, j ∈ J → Ignores j (fun a => ∏ k ∈ S', (G a k) (vals k)) := by
      intro j hj
      refine Ignores_finset_prod j (fun k a => (G a k) (vals k)) S' (fun k hk => ?_)
      cases hck : coord k with
      | none => exact pt k j (h_const k hck j)
      | some i' =>
        have hne : i' ≠ j := by
          intro heq; subst heq
          cases hc₀ : coord k₀ with
          | none => simp [J, hc₀] at hj
          | some i₀ =>
            simp only [J, hc₀, Finset.mem_singleton] at hj; subst hj
            exact absurd hc₀
              (hS k k₀ (Finset.mem_insert_of_mem hk)
                (Finset.mem_insert_self k₀ S')
                (ne_of_mem_of_not_mem hk hk₀) i' hck)
        exact pt k j (h_single k i' hck j (Ne.symm hne))
    exact pmfPi_expect_indep σ _ _ J hf hg

/-- Reweighting a product PMF by product weights gives a product of reweighted
marginals. This is the multiplicative Fubini identity for `reweightPMF`. -/
theorem reweightPMF_pmfPi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) (w : ∀ i, A i → ENNReal)
    (hC : ∀ i, ∑ a, σ i a * w i a ≠ 0)
    (hCt : ∀ i, ∑ a, σ i a * w i a ≠ ⊤) :
    reweightPMF (pmfPi σ) (fun f => ∏ i, w i (f i)) =
      pmfPi (fun i => reweightPMF (σ i) (w i)) := by
  have hfub : ∑ f : ∀ i, A i, (pmfPi σ) f * ∏ i, w i (f i) =
      ∏ i, ∑ a, σ i a * w i a := by
    simp only [pmfPi_apply, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i a => σ i a * w i a)).symm
  have hCL : ∑ f, (pmfPi σ) f * ∏ i, w i (f i) ≠ 0 := by
    rw [hfub]; exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hC i))
  have hCLt : ∑ f, (pmfPi σ) f * ∏ i, w i (f i) ≠ ⊤ := by
    rw [hfub]; exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCt i).lt_top))
  ext f
  rw [reweightPMF_apply _ _ _ hCL hCLt, pmfPi_apply, pmfPi_apply, hfub]
  simp_rw [reweightPMF_apply _ _ _ (hC _) (hCt _)]
  rw [← Finset.prod_mul_distrib]
  simp only [ENNReal.div_eq_inv_mul]
  conv_lhs =>
    rw [ENNReal.prod_inv_distrib (by
      intro i _ j _ _; exact Or.inl (hC i))]
  rw [← Finset.prod_mul_distrib]

open Classical in
/-- Reweighting a product distribution by a scalar weight that ignores
coordinate `j` preserves the `j`-marginal.

This is the product-measure independence calculation used when a reach event
depends only on the other coordinates: conditioning/reweighting on that event
does not change the unused coordinate's law. -/
theorem reweightPMF_pmfPi_push_coord_of_ignores
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι)
    (w : (∀ i, A i) → ENNReal)
    (hign : Ignores (A := A) j w)
    (hC0 : ∑ s, pmfPi (A := A) σ s * w s ≠ 0)
    (hCtop : ∑ s, pmfPi (A := A) σ s * w s ≠ ⊤) :
    pushforward
        (reweightPMF (pmfPi (A := A) σ) w) (fun s => s j) =
      σ j := by
  classical
  ext a
  set C : ENNReal := ∑ s, pmfPi (A := A) σ s * w s
  have hC0' : C ≠ 0 := by simpa [C] using hC0
  have hCtop' : C ≠ ⊤ := by simpa [C] using hCtop
  have hf :
      ∀ q, q ∉ ({j} : Finset ι) →
        Ignores (A := A) q
          (fun s : (∀ i, A i) => if s j = a then (1 : ENNReal) else 0) := by
    intro q hq s b
    have hqj : q ≠ j := by
      intro h
      exact hq (by simp [h])
    have hneq : j ≠ q := Ne.symm hqj
    simp [Function.update, hneq]
  have hg :
      ∀ q, q ∈ ({j} : Finset ι) →
        Ignores (A := A) q w := by
    intro q hq
    have hqj : q = j := by simpa using hq
    subst q
    exact hign
  have hindep :
      (∑ s : (∀ i, A i),
        pmfPi (A := A) σ s *
          (((if s j = a then (1 : ENNReal) else 0) * w s))) =
        (∑ s : (∀ i, A i),
          pmfPi (A := A) σ s *
            (if s j = a then (1 : ENNReal) else 0)) * C := by
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using
      pmfPi_expect_indep
        (A := A) σ
        (fun s : (∀ i, A i) => if s j = a then (1 : ENNReal) else 0)
        w ({j} : Finset ι) hf hg
  have hcoord :
      (∑ s : (∀ i, A i),
        pmfPi (A := A) σ s *
          (if s j = a then (1 : ENNReal) else 0)) = σ j a := by
    simpa [mul_ite, mul_one, mul_zero] using
      pmfPi_coord_mass (A := A) σ j a
  rw [pushforward, PMF.map_apply]
  simp only [tsum_fintype]
  simp_rw [@eq_comm _ a]
  calc
    (∑ s : (∀ i, A i),
        if s j = a then reweightPMF (pmfPi (A := A) σ) w s else 0)
        =
      (∑ s : (∀ i, A i),
        pmfPi (A := A) σ s *
          (((if s j = a then (1 : ENNReal) else 0) * w s))) * C⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [reweightPMF_apply (pmfPi (A := A) σ) w s hC0 hCtop]
        by_cases hs : s j = a
        · simp [hs, C, div_eq_mul_inv, mul_assoc, mul_comm]
        · simp [hs]
    _ = (σ j a * C) * C⁻¹ := by rw [hindep, hcoord]
    _ = σ j a := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hC0' hCtop', mul_one]

open Classical in
/-- Reweighting a product distribution by a scalar weight that ignores
coordinate `j` preserves the `j`-marginal, including the zero-total-weight
fallback case of `reweightPMF`. -/
theorem reweightPMF_pmfPi_push_coord_of_ignores'
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι)
    (w : (∀ i, A i) → ENNReal)
    (hign : Ignores (A := A) j w)
    (hCtop : ∑ s, pmfPi (A := A) σ s * w s ≠ ⊤) :
    pushforward
        (reweightPMF (pmfPi (A := A) σ) w) (fun s => s j) =
      σ j := by
  classical
  by_cases hC0 : ∑ s, pmfPi (A := A) σ s * w s = 0
  · rw [reweightPMF_degenerate _ _ (Or.inl hC0)]
    exact pmfPi_push_coord (A := A) σ j
  · exact reweightPMF_pmfPi_push_coord_of_ignores
      (A := A) σ j w hign hC0 hCtop

/-- Product of mapped marginals distributes over bind:
`(pmfPi (fun i => (σ i).map (f i))).bind g = (pmfPi σ).bind (fun s => g (fun i => f i (s i)))`. -/
theorem pmfPi_map_bind {ι : Type uι} [Fintype ι]
    {A : ι → Type uA}
    {B : ι → Type uβ}
    (σ : ∀ i, PMF (A i)) (f : ∀ i, A i → B i)
    {γ : Type uγ} (g : (∀ i, B i) → PMF γ) :
    (pmfPi (A := B) (fun i => (σ i).map (f i))).bind g =
      (pmfPi (A := A) σ).bind (fun s => g (fun i => f i (s i))) := by
  change (pmfPi (A := B) (fun i => pushforward (σ i) (f i))).bind g =
      (pmfPi (A := A) σ).bind (fun s => g (fun i => f i (s i)))
  rw [← pmfPi_push_coordwise (A := A) (B := B) σ f]
  change (PMF.map (fun s : (∀ i, A i) => fun i => f i (s i))
      (pmfPi (A := A) σ)).bind g =
    (pmfPi (A := A) σ).bind (fun s => g (fun i => f i (s i)))
  rw [← PMF.bind_pure_comp
    (fun s : (∀ i, A i) => fun i => f i (s i)) (pmfPi (A := A) σ)]
  rw [PMF.bind_bind]
  simp


end PMFProduct

end Math
