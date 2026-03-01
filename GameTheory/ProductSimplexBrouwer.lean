import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import FixedPointTheorems.brouwer

/-!
# Brouwer fixed-point theorem for products of standard simplices

The product `∀ i, stdSimplex ℝ (A i)` is homeomorphic to a compact convex
subset of a finite-dimensional normed space.  Combined with Brouwer's
fixed-point theorem this gives `brouwer_productSimplex`: every continuous
self-map of such a product has a fixed point.

We also prove an approximate-to-exact fixed-point principle on compact sets,
specialised to the product-simplex domain.
-/

set_option autoImplicit false

namespace GameTheory

open Function

-- ────────────────────────────────────────────────────────────
-- Product of standard simplices
-- ────────────────────────────────────────────────────────────

/-- Product of standard simplices, indexed by `ι` with fibers `A i`. -/
abbrev MixedSimplex
    (ι : Type*) (A : ι → Type _) [Fintype ι] [∀ i, Fintype (A i)] : Type _ :=
  ∀ i, stdSimplex ℝ (A i)

section Compactness

variable {ι : Type*} {A : ι → Type _}
variable [Fintype ι] [∀ i, Fintype (A i)]

instance instCompactSpaceMixedSimplex :
    CompactSpace (MixedSimplex ι A) :=
  inferInstance

end Compactness

-- ────────────────────────────────────────────────────────────
-- Approximate → exact fixed points on compact sets
-- ────────────────────────────────────────────────────────────

section ApproxToExact

theorem exists_fixedPoint_of_approx_on_compact
    {X : Type*} [MetricSpace X]
    (S : Set X) (hScompact : IsCompact S)
    (f : X → X) (hcont : Continuous f)
    (happrox : ∀ n : ℕ, ∃ x ∈ S, dist (f x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ x ∈ S, IsFixedPt f x := by
  let t : ℕ → Set X := fun n => {x | x ∈ S ∧ dist (f x) x ≤ (1 : ℝ) / (n + 1)}
  have hmono : ∀ n, t (n + 1) ⊆ t n := by
    intro n x ⟨hxS, hxdist⟩
    exact ⟨hxS, le_trans hxdist (by
      have hpos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
      have hlt : (n + 1 : ℝ) < (n + 1) + 1 := by linarith
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
        (one_div_lt_one_div_of_lt hpos hlt).le)⟩
  have hnonempty : ∀ n, (t n).Nonempty := by
    intro n; rcases happrox n with ⟨x, hxS, hxdist⟩; exact ⟨x, hxS, hxdist⟩
  have hclosed : ∀ n, IsClosed (t n) := by
    intro n
    simpa [t] using hScompact.isClosed.inter
      (isClosed_le (hcont.dist continuous_id) continuous_const)
  have ht0_compact : IsCompact (t 0) :=
    hScompact.of_isClosed_subset (hclosed 0) (fun x hx => hx.1)
  rcases IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      t hmono hnonempty ht0_compact hclosed with ⟨x, hxall⟩
  have hxS : x ∈ S := (Set.mem_iInter.mp hxall 0).1
  have hdist_le_all (n : ℕ) : dist (f x) x ≤ (1 : ℝ) / (n + 1) :=
    (Set.mem_iInter.mp hxall n).2
  have hdist_zero : dist (f x) x = 0 := by
    by_contra hne
    rcases exists_nat_one_div_lt (lt_of_le_of_ne dist_nonneg (Ne.symm hne))
      with ⟨n, hn⟩
    exact (not_lt_of_ge (hdist_le_all n)) hn
  exact ⟨x, hxS, dist_eq_zero.mp hdist_zero⟩

variable {ι : Type*} {A : ι → Type _}
variable [Fintype ι] [∀ i, Fintype (A i)]

/-- Approximate fixed points on a product of simplices imply an exact one. -/
theorem exists_fixedPoint_of_approx_on_mixedSimplex
    (f : MixedSimplex ι A → MixedSimplex ι A)
    (hcont : Continuous f)
    (happrox : ∀ n : ℕ, ∃ x : MixedSimplex ι A,
      dist (f x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ x : MixedSimplex ι A, IsFixedPt f x := by
  rcases exists_fixedPoint_of_approx_on_compact Set.univ isCompact_univ f hcont
    (fun n => let ⟨x, hx⟩ := happrox n; ⟨x, Set.mem_univ x, hx⟩)
    with ⟨x, _, hfix⟩
  exact ⟨x, hfix⟩

end ApproxToExact

-- ────────────────────────────────────────────────────────────
-- Homeomorphism: MixedSimplex ≃ₜ compact convex set
-- ────────────────────────────────────────────────────────────

section BrouwerMixed

variable {ι : Type*} {A : ι → Type*}
variable [Fintype ι] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

/-- Product of standard simplices as a `Set` in the pi normed space. -/
def mixedSimplexAsSet (ι : Type*) (A : ι → Type*) [∀ i, Fintype (A i)] :
    Set (∀ i, A i → ℝ) :=
  Set.pi Set.univ (fun i => stdSimplex ℝ (A i))

omit [Fintype ι] [∀ i, Nonempty (A i)] in
theorem convex_mixedSimplexAsSet :
    Convex ℝ (mixedSimplexAsSet ι A) :=
  convex_pi (fun i _ => convex_stdSimplex ℝ (A i))

omit [Fintype ι] [∀ i, Nonempty (A i)] in
theorem isCompact_mixedSimplexAsSet :
    IsCompact (mixedSimplexAsSet ι A) :=
  isCompact_univ_pi (fun i => isCompact_stdSimplex (A i))

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
theorem continuous_toMixedSet :
    Continuous (toMixedSet (ι := ι) (A := A)) :=
  Continuous.subtype_mk
    (continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))) _

omit [∀ i, Nonempty (A i)] in
theorem continuous_fromMixedSet :
    Continuous (fromMixedSet (ι := ι) (A := A)) :=
  continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

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

/-- **Brouwer for product simplices**: every continuous self-map of
    `MixedSimplex` has a fixed point. -/
theorem brouwer_mixedSimplex
    (f : MixedSimplex ι A → MixedSimplex ι A) (hcont : Continuous f) :
    ∃ x : MixedSimplex ι A, IsFixedPt f x := by
  let e := mixedSimplexHomeomorph (ι := ι) (A := A)
  let g : C(↥(mixedSimplexAsSet ι A), ↥(mixedSimplexAsSet ι A)) :=
    ⟨e ∘ f ∘ e.symm, e.continuous.comp (hcont.comp e.symm.continuous)⟩
  rcases _root_.brouwer_fixed_point (mixedSimplexAsSet ι A)
    convex_mixedSimplexAsSet isCompact_mixedSimplexAsSet
    nonempty_mixedSimplexAsSet g with ⟨x, hx⟩
  refine ⟨e.symm x, ?_⟩
  change f (e.symm x) = e.symm x
  have : e (f (e.symm x)) = x := hx
  calc f (e.symm x)
      = e.symm (e (f (e.symm x))) := (e.symm_apply_apply _).symm
    _ = e.symm x := by rw [this]

end BrouwerMixed

end GameTheory
