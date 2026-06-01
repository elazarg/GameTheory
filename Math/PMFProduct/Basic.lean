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

namespace Math
namespace PMFProduct

open scoped BigOperators
open Math.ProbabilityMassFunction

universe uι uA uα uβ uγ

set_option autoImplicit false

-- ============================================================================
-- Prod-tsum commutation for ENNReal (foundation for countable factors)
-- ============================================================================

/-- For a Fin-indexed dependent family `A : Fin n → Type*` and a family of
nonneg measure-like functions `g : ∀ i, A i → ℝ≥0∞`, the sum-of-products over
the product space equals the product-of-sums. -/
theorem ENNReal_tsum_pi_fin {n : ℕ} {A : Fin n → Type*}
    (g : (i : Fin n) → A i → ENNReal) :
    ∑' s : ((i : Fin n) → A i), ∏ i, g i (s i) = ∏ i, ∑' a : A i, g i a := by
  induction n with
  | zero =>
    -- `(i : Fin 0) → A i` is `Unique` (only the empty function).
    haveI : Unique ((i : Fin 0) → A i) := Pi.uniqueOfIsEmpty _
    rw [tsum_eq_single default (fun s hs => absurd (Unique.eq_default s) hs)]
    simp [Finset.prod_eq_one (fun (i : Fin 0) _ => Fin.elim0 i)]
  | succ n ih =>
    set e : A 0 × ((i : Fin n) → A i.succ) ≃ ((i : Fin (n+1)) → A i) :=
      Fin.consEquiv A with he
    rw [← e.tsum_eq (f := fun s => ∏ i, g i (s i))]
    rw [ENNReal.tsum_prod']
    have h_split : ∀ (a₀ : A 0) (s' : (i : Fin n) → A i.succ),
        (∏ i, g i (e (a₀, s') i)) = g 0 a₀ * ∏ i, g i.succ (s' i) := by
      intro a₀ s'
      have he_val : ∀ i : Fin (n+1), e (a₀, s') i = Fin.cons a₀ s' i := by intro i; rfl
      simp_rw [he_val]
      rw [Fin.prod_univ_succ (f := fun i => g i (Fin.cons a₀ s' i))]
      simp [Fin.cons_zero, Fin.cons_succ]
    simp_rw [h_split]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
    rw [ih]
    rw [Fin.prod_univ_succ (f := fun i => ∑' a, g i a)]

/-- For any Fintype-indexed dependent family `A : ι → Type*` and a family of
nonneg measure-like functions `g : ∀ i, A i → ENNReal`,

  ∑' s : (∀ i, A i), ∏ i, g i (s i) = ∏ i, ∑' a, g i a. -/
theorem ENNReal_tsum_pi {ι : Type*} [Fintype ι] {A : ι → Type*}
    (g : (i : ι) → A i → ENNReal) :
    ∑' s : ((i : ι) → A i), ∏ i, g i (s i) = ∏ i, ∑' a : A i, g i a := by
  classical
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  -- `ePi : (∀ j : Fin n, A (e j)) ≃ (∀ i : ι, A i)`
  set ePi : ((j : Fin (Fintype.card ι)) → A (e j)) ≃ ((i : ι) → A i) :=
    Equiv.piCongrLeft A e
  -- Transfer the tsum from the ι-side to the Fin-side.
  rw [← ePi.tsum_eq (f := fun s => ∏ i, g i (s i))]
  -- Reindex the inner product over ι via `e` to Fin n.
  have h_prod : ∀ t : ((j : Fin (Fintype.card ι)) → A (e j)),
      (∏ i : ι, g i (ePi t i)) = ∏ j, g (e j) (t j) := by
    intro t
    rw [← e.prod_comp (g := fun i => g i (ePi t i))]
    apply Finset.prod_congr rfl
    intro j _
    show g (e j) (ePi t (e j)) = g (e j) (t j)
    -- `piCongrLeft_apply_apply` reduces `ePi t (e j) = t j` without cast.
    rw [show (ePi t (e j) : A (e j)) = t j from Equiv.piCongrLeft_apply_apply A e t j]
  simp_rw [h_prod]
  rw [ENNReal_tsum_pi_fin (A := fun j => A (e j)) (g := fun j a => g (e j) a)]
  rw [← e.prod_comp (g := fun i => ∑' a : A i, g i a)]

section Aux

variable {ι : Type uι} [DecidableEq ι]
variable {A : ι → Type uA}

/-- Factor a product weight into the `j`-coordinate and the rest. -/
lemma prod_factor_erase [Fintype ι] {M : Type*} [CommMonoid M]
    (w : ∀ i, A i → M) (j : ι) (s : ∀ i, A i) :
    (∏ i : ι, w i (s i))
      = (w j) (s j) * (∏ i ∈ (Finset.univ.erase j), w i (s i)) := by
  classical
  simpa [Finset.mem_univ] using
    (Finset.mul_prod_erase (s := (Finset.univ : Finset ι))
      (f := fun i => w i (s i)) (a := j) (by simp)).symm

/-- Updating at coordinate `j` does not change the product over `univ.erase j`. -/
lemma prod_erase_update_eq [Fintype ι] {M : Type*} [CommMonoid M]
    (w : ∀ i, A i → M) (j : ι) (s : ∀ i, A i) (a : A j) :
    (∏ i ∈ Finset.univ.erase j, w i ((Function.update s j a) i))
      = (∏ i ∈ Finset.univ.erase j, w i (s i)) := by
  apply Finset.prod_congr rfl
  intro i hi
  simp [Function.update, Finset.ne_of_mem_erase hi]

/-- Swap outer `a` with the `j`-coordinate of `s`, and update `s` at `j` to `a`. -/
def swapJA (j : ι) : (A j × (∀ i, A i)) → (A j × (∀ i, A i)) :=
  fun p => (p.2 j, Function.update p.2 j p.1)

lemma swapJA_involutive (j : ι) : Function.Involutive (swapJA (A := A) j) := by
  intro ⟨a, s⟩
  apply Prod.ext
  · simp [swapJA]
  · funext i; by_cases h : i = j
    · subst h; simp [swapJA]
    · simp [swapJA, Function.update]

end Aux

-- ============================================================================
-- Product PMF & Coordinate Independence
-- ============================================================================

section Core

variable {ι : Type uι} [DecidableEq ι]
variable {A : ι → Type uA}

-- ---- Product PMF --------------------------------------------------------

open Classical in
/-- Product PMF over a finite index of arbitrary per-coordinate PMFs:
independently sample each coordinate. -/
noncomputable def pmfPi [Fintype ι] (σ : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  ⟨fun s => ∏ i, σ i (s i),
   ENNReal.summable.hasSum_iff.2 (by
     rw [ENNReal_tsum_pi (g := fun i a => σ i a)]
     simp [PMF.tsum_coe])⟩

omit [DecidableEq ι] in
@[simp] lemma pmfPi_apply [Fintype ι]
    (σ : ∀ i, PMF (A i)) (s : ∀ i, A i) :
    pmfPi (A := A) σ s = ∏ i, σ i (s i) := rfl

omit [DecidableEq ι] in
/-- Product of point masses is a point mass at the joint assignment. -/
theorem pmfPi_pure [Fintype ι] (σ : ∀ i, A i) :
    pmfPi (fun i => (PMF.pure (σ i) : PMF (A i))) = PMF.pure σ := by
  classical
  ext s
  by_cases hs : s = σ
  · subst hs
    simp [pmfPi_apply]
  · have hneq : ¬ ∀ i, s i = σ i := by
      intro hall
      apply hs
      funext i
      exact hall i
    obtain ⟨i, hi⟩ := not_forall.mp hneq
    have hfactor0 : (if s i = σ i then (1 : ENNReal) else 0) = 0 := by
      simp [hi]
    have hprod0 :
        (∏ x : ι, (if s x = σ x then (1 : ENNReal) else 0)) = 0 := by
      calc
        (∏ x : ι, (if s x = σ x then (1 : ENNReal) else 0))
            = (if s i = σ i then (1 : ENNReal) else 0) *
              (Finset.prod (Finset.univ.erase i)
                (fun x => (if s x = σ x then (1 : ENNReal) else 0))) := by
                simpa [Finset.mem_univ] using
                  (Finset.mul_prod_erase
                    (s := (Finset.univ : Finset ι))
                    (f := fun x => (if s x = σ x then (1 : ENNReal) else 0))
                    (a := i) (by simp)).symm
        _ = 0 := by simp [hfactor0]
    simpa [pmfPi_apply, PMF.pure_apply, hs] using hprod0

-- ---- Assignment operations -----------------------------------------------

/-- Coordinate projection. -/
@[simp] def coord (j : ι) (s : (∀ i, A i)) : A j := s j

/-- Update the `j`-coordinate of an assignment. -/
@[simp] def update (s : (∀ i, A i)) (j : ι) (a : A j) : (∀ i, A i) :=
  Function.update s j a

@[simp] lemma update_self (s : (∀ i, A i)) (j : ι) (a : A j) :
    update (A := A) s j a j = a := by
  simp [update]

@[simp] lemma update_ne (s : (∀ i, A i)) {i j : ι} (a : A j) (h : i ≠ j) :
    update (A := A) s j a i = s i := by
  simp [update, h]

-- ---- Coordinate independence (Ignores) -----------------------------------

/-- "`F` ignores coordinate `j`": updating `j` does not change `F`. -/
abbrev Ignores {α : Type uα} (j : ι) (F : (∀ i, A i) → α) : Prop :=
  ∀ s a, F (Function.update s j a) = F s

/-- "`G a0 s` ignores coordinate `j` in `s`", uniformly in the external parameter `a0`. -/
def Ignores₂ {α : Type uα} (j : ι) (G : A j → (∀ i, A i) → α) : Prop :=
  ∀ a0 s a, G a0 (update (A := A) s j a) = G a0 s

/-- A pointwise (extensional) criterion implying `Ignores`. -/
lemma Ignores_of_pointwise {α : Type uα} (j : ι) (F : (∀ i, A i) → α)
    (h : ∀ s₁ s₂, (∀ i, i ≠ j → s₁ i = s₂ i) → F s₁ = F s₂) :
    Ignores (A := A) j F := by
  intro s a
  apply h (update (A := A) s j a) s
  intro i hi
  simp [update, hi]

/-- A pointwise (extensional) criterion implying `Ignores₂`. -/
lemma Ignores₂_of_pointwise {α : Type uα} (j : ι) (G : A j → (∀ i, A i) → α)
    (h : ∀ a0 s₁ s₂, (∀ i, i ≠ j → s₁ i = s₂ i) → G a0 s₁ = G a0 s₂) :
    Ignores₂ (A := A) j G := by
  intro a0 s a
  apply h a0 (update (A := A) s j a) s
  intro i hi
  simp [update, hi]

lemma Ignores_coord_eq (j q : ι) (hq : q ≠ j) (a : A q) :
  Ignores (A := A) j (fun s => s q = a) := by
    intro s b; simp [hq]

lemma Ignores_coord_pred (j q : ι) (hq : q ≠ j) (E : A q → Prop) :
  Ignores (A := A) j (fun s => E (s q)) := by
    intro s b; simp [hq]

-- ---- Ignores algebra (closure properties) --------------------------------

section IgnoresAlgebra

variable {ι : Type uι} [DecidableEq ι]
variable {A : ι → Type uA}

/-- Prop-flavored version: ignoring a coordinate means iff, not Prop-equality. -/
def IgnoresP (j : ι) (P : (∀ i, A i) → Prop) : Prop :=
  ∀ s a, P (update (A := A) s j a) ↔ P s

/-- `Ignores` ⇒ `IgnoresP` (no classical axioms needed). -/
lemma IgnoresP_of_Ignores (j : ι) (P : (∀ i, A i) → Prop)
    (h : Ignores (A := A) j P) : IgnoresP (A := A) j P := by
  intro s a
  simp only [update]
  exact Eq.to_iff (h s a)

/-- `IgnoresP` ⇒ `Ignores` (needs propositional extensionality). -/
lemma Ignores_of_IgnoresP (j : ι) (P : (∀ i, A i) → Prop)
    (h : IgnoresP (A := A) j P) : Ignores (A := A) j P := by
  intro s a
  exact propext (h s a)

-- Generic (Type-valued) closure

lemma Ignores_const {α : Type uα} (j : ι) (c : α) :
    Ignores (A := A) j (fun _ => c) := by
  intro s a; rfl

lemma Ignores_comp {α : Type uα} {β : Type uβ} (j : ι)
    (F : (∀ i, A i) → α) (G : α → β)
    (hF : Ignores (A := A) j F) :
    Ignores (A := A) j (fun s => G (F s)) := by
  intro s a
  exact (congrArg G ∘ fun a_1 ↦ hF s a) ι

lemma Ignores_prod_mk {α : Type uα} {β : Type uβ} (j : ι)
    (F : (∀ i, A i) → α) (G : (∀ i, A i) → β)
    (hF : Ignores (A := A) j F) (hG : Ignores (A := A) j G) :
    Ignores (A := A) j (fun s => (F s, G s)) := by
  intro s a
  exact Prod.ext (hF s a) (hG s a)

lemma Ignores_fst {α : Type uα} {β : Type uβ} (j : ι)
    (F : (∀ i, A i) → α × β) (hF : Ignores (A := A) j F) :
    Ignores (A := A) j (fun s => (F s).1) :=
  Ignores_comp (A := A) j F Prod.fst hF

lemma Ignores_snd {α : Type uα} {β : Type uβ} (j : ι)
    (F : (∀ i, A i) → α × β) (hF : Ignores (A := A) j F) :
    Ignores (A := A) j (fun s => (F s).2) :=
  Ignores_comp (A := A) j F Prod.snd hF

lemma Ignores_app2 {α : Type uα} {β : Type uβ} {γ : Type uγ} (j : ι)
    (F : (∀ i, A i) → α) (G : (∀ i, A i) → β) (H : α → β → γ)
    (hF : Ignores (A := A) j F) (hG : Ignores (A := A) j G) :
    Ignores (A := A) j (fun s => H (F s) (G s)) := by
  intro s a
  exact
    Trans.simple (congrFun (congrArg H (hF s a)) (G (update s j a))) (congrArg (H (F s)) (hG s a))

open Classical in
lemma Ignores_ite {α : Type uα} (j : ι)
    (c : (∀ i, A i) → Prop)
    (t e : (∀ i, A i) → α)
    (hc : IgnoresP (A := A) j c)
    (ht : Ignores (A := A) j t) (he : Ignores (A := A) j e) :
    Ignores (A := A) j (fun s => if c s then t s else e s) := by
  intro s a
  have hc' : c (update (A := A) s j a) ↔ c s := hc s a
  by_cases hcs : c s
  · have : c (update (A := A) s j a) := (hc'.2 hcs)
    exact if_ctx_congr (hc s a) (fun a_1 ↦ ht s a) fun a_1 ↦ he s a
  · have : ¬ c (update (A := A) s j a) := by
      intro h; exact hcs ((hc'.1) h)
    exact if_ctx_congr (hc s a) (fun a_1 ↦ ht s a) fun a_1 ↦ he s a

-- Prop-valued closure

lemma IgnoresP_not (j : ι) (P : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) :
    IgnoresP (A := A) j (fun s => ¬ P s) := by
  intro s a
  exact not_congr (hP s a)

lemma IgnoresP_and (j : ι) (P Q : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) (hQ : IgnoresP (A := A) j Q) :
    IgnoresP (A := A) j (fun s => P s ∧ Q s) := by
  intro s a
  simp only [update]
  exact and_congr (hP s a) (hQ s a)

lemma IgnoresP_or (j : ι) (P Q : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) (hQ : IgnoresP (A := A) j Q) :
    IgnoresP (A := A) j (fun s => P s ∨ Q s) := by
  intro s a
  simp only [update]
  exact or_congr (hP s a) (hQ s a)

lemma IgnoresP_imp (j : ι) (P Q : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) (hQ : IgnoresP (A := A) j Q) :
    IgnoresP (A := A) j (fun s => P s → Q s) := by
  intro s a
  constructor
  · intro h hp
    have hp' : P (update (A := A) s j a) := (hP s a).2 hp
    have hq' : Q (update (A := A) s j a) := h hp'
    exact (hQ s a).1 hq'
  · intro h hp
    have hp' : P s := (hP s a).1 hp
    have hq : Q s := h hp'
    exact (hQ s a).2 hq

lemma IgnoresP_iff (j : ι) (P Q : (∀ i, A i) → Prop)
    (hP : IgnoresP (A := A) j P) (hQ : IgnoresP (A := A) j Q) :
    IgnoresP (A := A) j (fun s => P s ↔ Q s) := by
  intro s a
  exact iff_congr (hP s a) (hQ s a)

end IgnoresAlgebra

end Core

end PMFProduct

end Math
