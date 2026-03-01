import Mathlib
import Fixpoint.ProductSimplexCore

set_option autoImplicit false

namespace Fixpoint

open scoped BigOperators

/-!
# Brouwer fixed-point theorem for product simplices

Given Brouwer's theorem for compact convex sets in finite-dimensional normed
spaces, we derive a fixed-point theorem for `MixedSimplex` (a product of
standard simplices).
-/

-- ────────────────────────────────────────────────────────────
-- Brouwer's theorem (from fixed-point-theorems-lean4, sorry'd until integrated)
-- ────────────────────────────────────────────────────────────

theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcpt : IsCompact s) (hne : s.Nonempty)
    (f : C(↥s, ↥s)) : ∃ x : ↥s, f x = x := by
  sorry

-- ────────────────────────────────────────────────────────────
-- MixedSimplex as a set in a normed space
-- ────────────────────────────────────────────────────────────

section BrouwerMixed

variable {ι : Type*} {A : ι → Type*}
variable [Fintype ι] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

/-- Product of standard simplices, as a `Set` in the pi normed space. -/
def mixedSimplexAsSet (ι : Type*) (A : ι → Type*) [∀ i, Fintype (A i)] :
    Set (∀ i, A i → ℝ) :=
  Set.pi Set.univ (fun i => stdSimplex ℝ (A i))

omit [Fintype ι] [∀ i, Nonempty (A i)] in
theorem convex_mixedSimplexAsSet :
    Convex ℝ (mixedSimplexAsSet ι A) := by
  apply convex_pi
  intro i _
  exact convex_stdSimplex ℝ (A i)

omit [Fintype ι] [∀ i, Nonempty (A i)] in
theorem isCompact_mixedSimplexAsSet :
    IsCompact (mixedSimplexAsSet ι A) := by
  apply isCompact_univ_pi
  intro i
  exact isCompact_stdSimplex (A i)

omit [Fintype ι] in
theorem nonempty_mixedSimplexAsSet :
    (mixedSimplexAsSet ι A).Nonempty := by
  rw [mixedSimplexAsSet, Set.univ_pi_nonempty_iff]
  intro i
  exact ⟨fun _ => (1 : ℝ) / Fintype.card (A i),
    fun _ => div_nonneg one_pos.le (Nat.cast_nonneg _),
    by simp [Finset.card_univ]⟩

/-- Forward: `MixedSimplex → ↥(mixedSimplexAsSet)`. -/
def toMixedSet (σ : MixedSimplex ι A) : ↥(mixedSimplexAsSet ι A) :=
  ⟨fun i => (σ i).val, fun i _ => (σ i).property⟩

/-- Backward: `↥(mixedSimplexAsSet) → MixedSimplex`. -/
def fromMixedSet (x : ↥(mixedSimplexAsSet ι A)) : MixedSimplex ι A :=
  fun i => ⟨x.val i, x.property i (Set.mem_univ i)⟩

omit [∀ i, Nonempty (A i)] in
theorem fromMixedSet_toMixedSet (σ : MixedSimplex ι A) :
    fromMixedSet (toMixedSet σ) = σ := by
  ext i a; rfl

omit [∀ i, Nonempty (A i)] in
theorem toMixedSet_fromMixedSet (x : ↥(mixedSimplexAsSet ι A)) :
    toMixedSet (fromMixedSet x) = x := by
  ext; rfl

omit [∀ i, Nonempty (A i)] in
theorem continuous_toMixedSet : Continuous (toMixedSet (ι := ι) (A := A)) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))

omit [∀ i, Nonempty (A i)] in
theorem continuous_fromMixedSet : Continuous (fromMixedSet (ι := ι) (A := A)) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

/-- `MixedSimplex` is homeomorphic to the product-of-simplices set. -/
def mixedSimplexHomeomorph :
    MixedSimplex ι A ≃ₜ ↥(mixedSimplexAsSet ι A) where
  toEquiv := {
    toFun := toMixedSet
    invFun := fromMixedSet
    left_inv := fromMixedSet_toMixedSet
    right_inv := toMixedSet_fromMixedSet
  }
  continuous_toFun := continuous_toMixedSet
  continuous_invFun := continuous_fromMixedSet

-- ────────────────────────────────────────────────────────────
-- Main theorem
-- ────────────────────────────────────────────────────────────

/-- **Brouwer for product simplices**: every continuous self-map of `MixedSimplex`
    has a fixed point. -/
theorem brouwer_mixedSimplex
    (f : MixedSimplex ι A → MixedSimplex ι A) (hcont : Continuous f) :
    ∃ x : MixedSimplex ι A, Function.IsFixedPt f x := by
  let e := mixedSimplexHomeomorph (ι := ι) (A := A)
  -- Transport f to a map on the set
  let g : C(↥(mixedSimplexAsSet ι A), ↥(mixedSimplexAsSet ι A)) :=
    ⟨e ∘ f ∘ e.symm, e.continuous.comp (hcont.comp e.symm.continuous)⟩
  -- Apply Brouwer
  rcases brouwer_fixed_point (mixedSimplexAsSet ι A)
    convex_mixedSimplexAsSet isCompact_mixedSimplexAsSet nonempty_mixedSimplexAsSet g
    with ⟨x, hx⟩
  -- Transport back
  refine ⟨e.symm x, ?_⟩
  show f (e.symm x) = e.symm x
  have hgx : (e ∘ f ∘ e.symm) x = x := hx
  have : e (f (e.symm x)) = x := hgx
  calc f (e.symm x) = e.symm (e (f (e.symm x))) := (e.symm_apply_apply _).symm
    _ = e.symm x := by rw [this]

end BrouwerMixed

end Fixpoint
