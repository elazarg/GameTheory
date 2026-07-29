/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Closure
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Sign.Defs

/-!
# Finite polynomial sign cells

A finite family of real multivariate polynomials partitions its finite-dimensional
assignment space into basic sign cells.  The signs used here are exact: each
polynomial is required to be negative, zero, or positive according to the chosen
pattern.

Every set whose membership depends only on this finite sign pattern is a finite
union of cells.  Since closure commutes with finite unions, a point in the
closure of such a set is in the closure of one selected cell contained in the
set.  This is the purely finite topological reduction needed before invoking a
single-cell analytic curve-selection theorem; no curve selection is asserted in
this file.

## Main declarations

* `polynomialSignPattern`: the exact sign pattern at an assignment.
* `signCell`: the basic cell realizing one pattern.
* `iUnion_signCell`: the cells cover the whole assignment space.
* `disjoint_signCell`: cells with different patterns are disjoint.
* `SignInvariant`: membership depends only on the polynomial sign pattern.
* `signInvariant_eq_iUnion_signCell`: every sign-invariant set is a finite
  union of sign cells.
* `exists_signCell_subset_of_mem_closure`: a closure point of a sign-invariant
  set is a closure point of one cell contained in that set.
* `SignFormula`: finite Boolean formulas in exact sign conditions.
* `SignFormula.exists_signCell_subset_of_mem_closure`: the corresponding
  reduction for a Boolean sign formula.
-/

noncomputable section

open Set SignType Topology

namespace Math
namespace PolynomialSignCell

variable {ι σ : Type*}

/-- The finite-dimensional real assignment space for the variables `σ`. -/
abbrev Assignment (σ : Type*) := σ → ℝ

/-- An exact negative/zero/positive sign choice for every polynomial in `ι`. -/
abbrev SignPattern (ι : Type*) := ι → SignType

/-- The exact sign pattern of a polynomial family at an assignment. -/
def polynomialSignPattern
    (P : ι → MvPolynomial σ ℝ) (x : Assignment σ) :
    SignPattern ι :=
  fun i => SignType.sign (MvPolynomial.eval x (P i))

/-- The basic sign cell on which every polynomial in `P` has the prescribed
negative, zero, or positive sign. -/
def signCell
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι) :
    Set (Assignment σ) :=
  {x | polynomialSignPattern P x = τ}

@[simp]
theorem mem_signCell
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x : Assignment σ) :
    x ∈ signCell P τ ↔ polynomialSignPattern P x = τ :=
  Iff.rfl

@[simp]
theorem mem_signCell_self
    (P : ι → MvPolynomial σ ℝ) (x : Assignment σ) :
    x ∈ signCell P (polynomialSignPattern P x) :=
  rfl

/-- The zero part of a sign pattern records polynomial equality exactly. -/
theorem eval_eq_zero_iff_of_mem_signCell
    {P : ι → MvPolynomial σ ℝ} {τ : SignPattern ι}
    {x : Assignment σ} (hx : x ∈ signCell P τ) (i : ι) :
    MvPolynomial.eval x (P i) = 0 ↔ τ i = 0 := by
  have hi := congrFun hx i
  rw [← hi]
  exact (@sign_eq_zero_iff ℝ _ _ _).symm

/-- The positive part of a sign pattern records strict positivity exactly. -/
theorem eval_pos_iff_of_mem_signCell
    {P : ι → MvPolynomial σ ℝ} {τ : SignPattern ι}
    {x : Assignment σ} (hx : x ∈ signCell P τ) (i : ι) :
    0 < MvPolynomial.eval x (P i) ↔ τ i = 1 := by
  have hi := congrFun hx i
  rw [← hi]
  exact sign_eq_one_iff.symm

/-- The negative part of a sign pattern records strict negativity exactly. -/
theorem eval_neg_iff_of_mem_signCell
    {P : ι → MvPolynomial σ ℝ} {τ : SignPattern ι}
    {x : Assignment σ} (hx : x ∈ signCell P τ) (i : ι) :
    MvPolynomial.eval x (P i) < 0 ↔ τ i = -1 := by
  have hi := congrFun hx i
  rw [← hi]
  exact sign_eq_neg_one_iff.symm

/-- Membership in two cells forces the two sign patterns to agree. -/
theorem signPattern_eq_of_mem_signCell
    {P : ι → MvPolynomial σ ℝ} {τ υ : SignPattern ι}
    {x : Assignment σ} (hτ : x ∈ signCell P τ)
    (hυ : x ∈ signCell P υ) :
    τ = υ :=
  hτ.symm.trans hυ

/-- Distinct sign patterns define disjoint cells. -/
theorem disjoint_signCell
    (P : ι → MvPolynomial σ ℝ) {τ υ : SignPattern ι}
    (hτυ : τ ≠ υ) :
    Disjoint (signCell P τ) (signCell P υ) := by
  rw [Set.disjoint_left]
  intro x hxτ hxυ
  exact hτυ (signPattern_eq_of_mem_signCell hxτ hxυ)

/-- The sign cells cover the entire assignment space.  Together with
`disjoint_signCell`, this is the partition statement. -/
@[simp]
theorem iUnion_signCell
    (P : ι → MvPolynomial σ ℝ) :
    ⋃ τ : SignPattern ι, signCell P τ = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨polynomialSignPattern P x, mem_signCell_self P x⟩

/-- A single exact sign condition for one polynomial. -/
def signCondition
    (p : MvPolynomial σ ℝ) (s : SignType) :
    Set (Assignment σ) :=
  {x | SignType.sign (MvPolynomial.eval x p) = s}

/-- A basic cell is the intersection of its individual exact sign
conditions. -/
theorem signCell_eq_iInter_signCondition
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι) :
    signCell P τ = ⋂ i, signCondition (P i) (τ i) := by
  ext x
  simp only [mem_signCell, Set.mem_iInter, signCondition]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- Each individual negative, zero, or positive polynomial sign condition is
locally closed. -/
theorem isLocallyClosed_signCondition
    (p : MvPolynomial σ ℝ) (s : SignType) :
    IsLocallyClosed (signCondition p s) := by
  cases s with
  | zero =>
      have hclosed :
          IsClosed {x : Assignment σ | MvPolynomial.eval x p = 0} :=
        isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
      simpa [signCondition, sign_eq_zero_iff] using
        hclosed.isLocallyClosed
  | neg =>
      have hopen :
          IsOpen {x : Assignment σ | MvPolynomial.eval x p < 0} :=
        isOpen_lt (MvPolynomial.continuous_eval p) continuous_const
      simpa [signCondition, sign_eq_neg_one_iff] using
        hopen.isLocallyClosed
  | pos =>
      have hopen :
          IsOpen {x : Assignment σ | 0 < MvPolynomial.eval x p} :=
        isOpen_lt continuous_const (MvPolynomial.continuous_eval p)
      simpa [signCondition, sign_eq_one_iff] using
        hopen.isLocallyClosed

/-- A finite intersection of locally closed sets is locally closed. -/
theorem isLocallyClosed_iInter_of_finite
    [Finite ι] {X : Type*} [TopologicalSpace X]
    (s : ι → Set X) (hs : ∀ i, IsLocallyClosed (s i)) :
    IsLocallyClosed (⋂ i, s i) := by
  letI := Fintype.ofFinite ι
  classical
  have hfin :
      ∀ T : Finset ι, IsLocallyClosed (⋂ i ∈ T, s i) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        simpa using isOpen_univ.isLocallyClosed
    | @insert i T hi hT =>
        simpa [hi] using (hs i).inter hT
  simpa using hfin Finset.univ

/-- Every basic sign cell of a finite polynomial family is locally closed. -/
theorem isLocallyClosed_signCell
    [Finite ι] (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι) :
    IsLocallyClosed (signCell P τ) := by
  rw [signCell_eq_iInter_signCondition]
  exact isLocallyClosed_iInter_of_finite _ fun i =>
    isLocallyClosed_signCondition (P i) (τ i)

/-- A set is sign-invariant if its membership depends only on the sign pattern
of the finite polynomial family. -/
def SignInvariant
    (P : ι → MvPolynomial σ ℝ) (A : Set (Assignment σ)) :
    Prop :=
  ∀ ⦃x y : Assignment σ⦄,
    polynomialSignPattern P x = polynomialSignPattern P y →
      (x ∈ A ↔ y ∈ A)

/-- The finite set of patterns whose cells meet a given set. -/
def selectedPatterns
    [Finite ι] (P : ι → MvPolynomial σ ℝ)
    (A : Set (Assignment σ)) :
    Finset (SignPattern ι) := by
  letI := Fintype.ofFinite ι
  classical
  exact Finset.univ.filter fun τ => (signCell P τ ∩ A).Nonempty

theorem mem_selectedPatterns_iff
    [Finite ι] {P : ι → MvPolynomial σ ℝ}
    {A : Set (Assignment σ)} {τ : SignPattern ι} :
    τ ∈ selectedPatterns P A ↔
      ∃ x ∈ A, polynomialSignPattern P x = τ := by
  simp only [selectedPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hxcell, hxA⟩
    exact ⟨x, hxA, hxcell⟩
  · rintro ⟨x, hxA, hxcell⟩
    exact ⟨x, hxcell, hxA⟩

/-- For a sign-invariant set, a selected pattern contributes its entire cell,
not merely the point witnessing selection. -/
theorem signCell_subset_of_mem_selectedPatterns
    [Finite ι] {P : ι → MvPolynomial σ ℝ}
    {A : Set (Assignment σ)} (hA : SignInvariant P A)
    {τ : SignPattern ι} (hτ : τ ∈ selectedPatterns P A) :
    signCell P τ ⊆ A := by
  obtain ⟨y, hyA, hyτ⟩ := mem_selectedPatterns_iff.mp hτ
  intro x hxτ
  exact (hA (hxτ.trans hyτ.symm)).mpr hyA

/-- Every sign-invariant set is the union of the finitely many exact sign
cells that it meets. -/
theorem signInvariant_eq_iUnion_signCell
    [Finite ι] {P : ι → MvPolynomial σ ℝ}
    {A : Set (Assignment σ)} (hA : SignInvariant P A) :
    A = ⋃ τ ∈ selectedPatterns P A, signCell P τ := by
  ext x
  constructor
  · intro hxA
    rw [Set.mem_iUnion]
    refine ⟨polynomialSignPattern P x, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨mem_selectedPatterns_iff.mpr
      ⟨x, hxA, rfl⟩, mem_signCell_self P x⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨τ, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hτ, hxτ⟩ := hx
    exact signCell_subset_of_mem_selectedPatterns hA hτ hxτ

/-- Existential finite-union packaging of
`signInvariant_eq_iUnion_signCell`. -/
theorem signInvariant_eq_finiteUnion_signCell
    [Finite ι] {P : ι → MvPolynomial σ ℝ}
    {A : Set (Assignment σ)} (hA : SignInvariant P A) :
    ∃ T : Finset (SignPattern ι),
      A = ⋃ τ ∈ T, signCell P τ :=
  ⟨selectedPatterns P A, signInvariant_eq_iUnion_signCell hA⟩

/-- Closure of a finite union of sign cells is the union of their closures. -/
theorem closure_iUnion_signCell
    (P : ι → MvPolynomial σ ℝ)
    (T : Finset (SignPattern ι)) :
    closure (⋃ τ ∈ T, signCell P τ) =
      ⋃ τ ∈ T, closure (signCell P τ) :=
  T.closure_biUnion fun τ => signCell P τ

/-- A closure point of a finite union of cells is a closure point of one
selected cell. -/
theorem exists_mem_closure_signCell_of_mem_closure_iUnion
    {P : ι → MvPolynomial σ ℝ}
    {T : Finset (SignPattern ι)} {x : Assignment σ}
    (hx : x ∈ closure (⋃ τ ∈ T, signCell P τ)) :
    ∃ τ ∈ T, x ∈ closure (signCell P τ) := by
  rw [closure_iUnion_signCell] at hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨τ, hx⟩ := hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨hτ, hxτ⟩ := hx
  exact ⟨τ, hτ, hxτ⟩

/-- The finite topological reduction to one basic cell.

If `A` is sign-invariant and `x` lies in its closure, one exact sign cell is
contained in `A` and has `x` in its closure.  A single-cell analytic
curve-selection theorem may therefore be applied to that cell. -/
theorem exists_signCell_subset_of_mem_closure
    [Finite ι] {P : ι → MvPolynomial σ ℝ}
    {A : Set (Assignment σ)} (hA : SignInvariant P A)
    {x : Assignment σ} (hx : x ∈ closure A) :
    ∃ τ : SignPattern ι,
      signCell P τ ⊆ A ∧ x ∈ closure (signCell P τ) := by
  rw [signInvariant_eq_iUnion_signCell hA] at hx
  obtain ⟨τ, hτ, hxτ⟩ :=
    exists_mem_closure_signCell_of_mem_closure_iUnion hx
  exact ⟨τ, signCell_subset_of_mem_selectedPatterns hA hτ, hxτ⟩

/-- A finite Boolean formula in exact polynomial sign atoms. -/
inductive SignFormula (ι : Type*)
  | atom (i : ι) (s : SignType)
  | top
  | bot
  | and (φ ψ : SignFormula ι)
  | or (φ ψ : SignFormula ι)
  | not (φ : SignFormula ι)

namespace SignFormula

/-- Truth of a Boolean sign formula on a sign pattern. -/
def Holds : SignFormula ι → SignPattern ι → Prop
  | atom i s, τ => τ i = s
  | top, _ => True
  | bot, _ => False
  | and φ ψ, τ => φ.Holds τ ∧ ψ.Holds τ
  | or φ ψ, τ => φ.Holds τ ∨ ψ.Holds τ
  | not φ, τ => ¬φ.Holds τ

/-- The assignments satisfying a Boolean formula in the signs of `P`. -/
def realization
    (φ : SignFormula ι) (P : ι → MvPolynomial σ ℝ) :
    Set (Assignment σ) :=
  {x | φ.Holds (polynomialSignPattern P x)}

@[simp]
theorem mem_realization
    (φ : SignFormula ι) (P : ι → MvPolynomial σ ℝ)
    (x : Assignment σ) :
    x ∈ φ.realization P ↔
      φ.Holds (polynomialSignPattern P x) :=
  Iff.rfl

/-- Every finite Boolean formula in polynomial signs is sign-invariant. -/
theorem signInvariant_realization
    (φ : SignFormula ι) (P : ι → MvPolynomial σ ℝ) :
    SignInvariant P (φ.realization P) := by
  intro x y hxy
  simp only [mem_realization]
  rw [hxy]

/-- A Boolean combination of finitely many polynomial sign conditions is a
finite union of exact basic sign cells. -/
theorem realization_eq_finiteUnion_signCell
    [Finite ι] (φ : SignFormula ι)
    (P : ι → MvPolynomial σ ℝ) :
    ∃ T : Finset (SignPattern ι),
      φ.realization P = ⋃ τ ∈ T, signCell P τ :=
  signInvariant_eq_finiteUnion_signCell
    (signInvariant_realization φ P)

/-- The one-cell closure reduction specialized to a finite Boolean sign
formula. -/
theorem exists_signCell_subset_of_mem_closure
    [Finite ι] {φ : SignFormula ι}
    {P : ι → MvPolynomial σ ℝ} {x : Assignment σ}
    (hx : x ∈ closure (φ.realization P)) :
    ∃ τ : SignPattern ι,
      signCell P τ ⊆ φ.realization P ∧
        x ∈ closure (signCell P τ) :=
  PolynomialSignCell.exists_signCell_subset_of_mem_closure
    (signInvariant_realization φ P) hx

end SignFormula
end PolynomialSignCell
end Math
