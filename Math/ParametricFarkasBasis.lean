/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AlgebraicSelection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Stabilizing bases in parameter-dependent Farkas systems

This file isolates the part of the moving-certificate argument that is
available from ordinary real analyticity.  Determinants of finitely many
analytic matrix germs have stable zero/nonzero and sign data.  For a fixed
nonsingular basis at the limiting parameter, Cramer's rule then gives
analytic coordinates whose feasibility and objective ordering stabilize.

The case in which a basis determinant vanishes at the limiting parameter but
is nonzero on the punctured interval requires Laurent--Puiseux, rather than
ordinary analytic, coordinates.  That ramified-meromorphic step is kept
outside the statements below.
-/

open Set Topology

namespace Math
namespace LinearAlgebra

noncomputable section

open scoped BigOperators

theorem analyticAt_matrix_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀) :
    AnalyticAt ℝ (fun x => (A x).det) x₀ := by
  classical
  simp only [Matrix.det_apply']
  fun_prop

/-- A finite family of analytic matrix germs has stable determinant sign
data on one common punctured right neighborhood.  Both predicates hold
exactly for determinant zero. -/
theorem finite_analytic_matrix_det_sign_stabilizes
    {n Basis : Type*} [Fintype n] [DecidableEq n] [Finite Basis]
    (A : Basis → ℝ → Matrix n n ℝ) {x₀ : ℝ}
    (hA : ∀ basis i j,
      AnalyticAt ℝ (fun x => A basis x i j) x₀) :
    ∃ Nonnegative Nonpositive : Basis → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ basis,
        (0 ≤ (A basis x).det ↔ Nonnegative basis) ∧
          ((A basis x).det ≤ 0 ↔ Nonpositive basis) := by
  let f : Option Basis → ℝ → ℝ
    | none => fun _ => 0
    | some basis => fun x => (A basis x).det
  have hf : ∀ i, AnalyticAt ℝ (f i) x₀ := by
    intro i
    cases i with
    | none => exact analyticAt_const
    | some basis => exact analyticAt_matrix_det (A basis) (hA basis)
  obtain ⟨R, hR⟩ :=
    finite_analytic_family_eventually_stable f hf
  exact ⟨fun basis => R none (some basis),
    fun basis => R (some basis) none, by
      filter_upwards [hR] with x hx
      intro basis
      simpa [f] using And.intro
        (hx none (some basis)) (hx (some basis) none)⟩

/-- Sign and zero data stabilize simultaneously for any finite collection
of square minors of a rectangular analytic matrix germ.  Taking the
collection of all square minors is the determinant-level content needed to
freeze rank. -/
theorem finite_analytic_minor_sign_stabilizes
    {Row Col k Minor : Type*}
    [Finite Row] [Finite Col] [Fintype k] [DecidableEq k]
    [Finite Minor]
    (A : ℝ → Matrix Row Col ℝ)
    (rows : Minor → k → Row) (cols : Minor → k → Col) {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀) :
    ∃ Nonnegative Nonpositive : Minor → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ minor,
        (0 ≤ ((A x).submatrix (rows minor) (cols minor)).det ↔
            Nonnegative minor) ∧
          (((A x).submatrix (rows minor) (cols minor)).det ≤ 0 ↔
            Nonpositive minor) := by
  let square : Minor → ℝ → Matrix k k ℝ :=
    fun minor x => (A x).submatrix (rows minor) (cols minor)
  apply finite_analytic_matrix_det_sign_stabilizes square
  intro minor i j
  exact hA (rows minor i) (cols minor j)

theorem analyticAt_matrix_cramer_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (b : ℝ → n → ℝ) {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀)
    (hb : ∀ i, AnalyticAt ℝ (fun x => b x i) x₀) (i : n) :
    AnalyticAt ℝ (fun x => Matrix.cramer (A x) (b x) i) x₀ := by
  classical
  apply analyticAt_matrix_det
  intro j k
  simp only [Matrix.updateCol_apply]
  split_ifs
  · fun_prop
  · fun_prop

/-- The Cramer numerator for one coordinate of a selected square basis. -/
def cramerCoordinateNumerator
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (b : ℝ → n → ℝ)
    (i : n) (x : ℝ) : ℝ :=
  Matrix.cramer (A x) (b x) i

/-- The coordinate of a nonsingular selected square basis. -/
def cramerBasisCoordinate
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (b : ℝ → n → ℝ)
    (i : n) (x : ℝ) : ℝ :=
  cramerCoordinateNumerator A b i x / (A x).det

theorem matrix_mulVec_cramer_div_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b : n → ℝ) (hdet : A.det ≠ 0) :
    Matrix.mulVec A (fun i => Matrix.cramer A b i / A.det) = b := by
  have hcoordinate :
      (fun i => Matrix.cramer A b i / A.det) =
          A.det⁻¹ • Matrix.cramer A b := by
    funext i
    simp [div_eq_inv_mul]
  rw [hcoordinate, Matrix.mulVec_smul, Matrix.mulVec_cramer]
  ext i
  simp [hdet]

/-- The numerator of a linear objective evaluated at a Cramer basis. -/
def cramerObjectiveNumerator
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (b c : ℝ → n → ℝ)
    (x : ℝ) : ℝ :=
  ∑ i, c x i * cramerCoordinateNumerator A b i x

/-- The value of a linear objective at a nonsingular Cramer basis. -/
def cramerBasisValue
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (b c : ℝ → n → ℝ)
    (x : ℝ) : ℝ :=
  cramerObjectiveNumerator A b c x / (A x).det

theorem analyticAt_cramerCoordinateNumerator
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (b : ℝ → n → ℝ) {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀)
    (hb : ∀ i, AnalyticAt ℝ (fun x => b x i) x₀) (i : n) :
    AnalyticAt ℝ (cramerCoordinateNumerator A b i) x₀ := by
  exact analyticAt_matrix_cramer_apply A b hA hb i

theorem analyticAt_cramerObjectiveNumerator
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (b c : ℝ → n → ℝ) {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀)
    (hb : ∀ i, AnalyticAt ℝ (fun x => b x i) x₀)
    (hc : ∀ i, AnalyticAt ℝ (fun x => c x i) x₀) :
    AnalyticAt ℝ (cramerObjectiveNumerator A b c) x₀ := by
  classical
  apply Finset.univ.analyticAt_fun_sum
  intro i _
  exact (hc i).mul (analyticAt_cramerCoordinateNumerator A b hA hb i)

theorem cramerBasisCoordinate_nonneg_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (b : ℝ → n → ℝ)
    (i : n) (x : ℝ) (_hdet : (A x).det ≠ 0) :
    0 ≤ cramerBasisCoordinate A b i x ↔
      0 ≤ cramerCoordinateNumerator A b i x * (A x).det := by
  exact (div_nonneg_iff.trans mul_nonneg_iff.symm)

/-- Quotients of analytic numerators and denominators have stable pairwise
order on a punctured right neighborhood, even when the denominators vanish
at the limiting point. -/
theorem finite_analytic_quotient_family_eventually_stable
    {I : Type*} [Finite I]
    (num den : I → ℝ → ℝ) {x₀ : ℝ}
    (hnum : ∀ i, AnalyticAt ℝ (num i) x₀)
    (hden : ∀ i, AnalyticAt ℝ (den i) x₀)
    (hden_ne :
      ∀ i, ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), den i x ≠ 0) :
    ∃ R : I → I → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ i j,
        (num i x / den i x ≤ num j x / den j x ↔ R i j) := by
  let L := nhdsWithin x₀ (Set.Ioi x₀)
  let value : I → ℝ → ℝ := fun i x => num i x / den i x
  let R : I → I → Prop := fun i j => ∀ᶠ x in L, value i x ≤ value j x
  have hpair :
      ∀ i j,
        (∀ᶠ x in L, value i x = value j x) ∨
          (∀ᶠ x in L, value i x < value j x) ∨
          (∀ᶠ x in L, value j x < value i x) := by
    intro i j
    let cross : ℝ → ℝ := fun x =>
      num i x * den i x * den j x ^ 2 -
        num j x * den j x * den i x ^ 2
    have hcross : AnalyticAt ℝ cross x₀ := by
      dsimp [cross]
      fun_prop
    rcases analyticAt_eventually_eq_or_lt_or_gt
        hcross
        (analyticAt_const :
          AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) x₀) with
      heq | hlt | hgt
    · left
      filter_upwards [heq, hden_ne i, hden_ne j] with x hx hdi hdj
      dsimp [cross] at hx
      dsimp [value]
      have hi :
          num i x / den i x =
            (num i x * den i x) / den i x ^ 2 := by
        field_simp
      have hj :
          num j x / den j x =
            (num j x * den j x) / den j x ^ 2 := by
        field_simp
      rw [hi, hj]
      apply (div_eq_div_iff (sq_pos_of_ne_zero hdi).ne'
        (sq_pos_of_ne_zero hdj).ne').mpr
      exact sub_eq_zero.mp hx
    · right
      left
      filter_upwards [hlt, hden_ne i, hden_ne j] with x hx hdi hdj
      dsimp [cross] at hx
      dsimp [value]
      have hi :
          num i x / den i x =
            (num i x * den i x) / den i x ^ 2 := by
        field_simp
      have hj :
          num j x / den j x =
            (num j x * den j x) / den j x ^ 2 := by
        field_simp
      rw [hi, hj, div_lt_div_iff₀
        (sq_pos_of_ne_zero hdi) (sq_pos_of_ne_zero hdj)]
      exact sub_neg.mp hx
    · right
      right
      filter_upwards [hgt, hden_ne i, hden_ne j] with x hx hdi hdj
      dsimp [cross] at hx
      dsimp [value]
      have hi :
          num i x / den i x =
            (num i x * den i x) / den i x ^ 2 := by
        field_simp
      have hj :
          num j x / den j x =
            (num j x * den j x) / den j x ^ 2 := by
        field_simp
      rw [hi, hj, div_lt_div_iff₀
        (sq_pos_of_ne_zero hdj) (sq_pos_of_ne_zero hdi)]
      exact sub_pos.mp hx
  refine ⟨R, Filter.eventually_all.mpr fun i =>
    Filter.eventually_all.mpr fun j => ?_⟩
  rcases hpair i j with heq | hlt | hgt
  · have hR : R i j := heq.mono fun _ hx => hx.le
    filter_upwards [heq] with x hx
    simp [R, value, hR, hx]
  · have hR : R i j := hlt.mono fun _ hx => hx.le
    filter_upwards [hlt] with x hx
    simp [R, value, hR, hx.le]
  · have hR : ¬R i j := by
      intro hle
      obtain ⟨x, hgtx, hlex⟩ := (hgt.and hle).exists
      exact (not_lt_of_ge hlex) hgtx
    filter_upwards [hgt] with x hx
    simp [R, value, hR, not_le.mpr hx]

/-- A selected square Cramer system is feasible when it is nonsingular and
all of its basic coordinates are nonnegative. -/
def IsCramerBasisFeasible
    {n Basis : Type*} [Fintype n] [DecidableEq n]
    (A : Basis → ℝ → Matrix n n ℝ) (b : Basis → ℝ → n → ℝ)
    (x : ℝ) (basis : Basis) : Prop :=
  (A basis x).det ≠ 0 ∧
    ∀ i, 0 ≤ cramerBasisCoordinate (A basis) (b basis) i x

/-- For finitely many analytic square systems whose determinant germs are
nonzero on the punctured interval, Cramer feasibility stabilizes on one
common right neighborhood. -/
theorem finite_analytic_cramerBasis_feasibility_stabilizes
    {n Basis : Type*} [Fintype n] [DecidableEq n] [Finite Basis]
    (A : Basis → ℝ → Matrix n n ℝ) (b : Basis → ℝ → n → ℝ)
    {x₀ : ℝ}
    (hA : ∀ basis i j,
      AnalyticAt ℝ (fun x => A basis x i j) x₀)
    (hb : ∀ basis i,
      AnalyticAt ℝ (fun x => b basis x i) x₀)
    (hdet_ne : ∀ basis,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (A basis x).det ≠ 0) :
    ∃ Feasible : Basis → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ basis,
        (IsCramerBasisFeasible A b x basis ↔ Feasible basis) := by
  let Q := Option (Basis × n)
  let num : Q → ℝ → ℝ
    | none => fun _ => 0
    | some p => fun x =>
        cramerCoordinateNumerator (A p.1) (b p.1) p.2 x
  let den : Q → ℝ → ℝ
    | none => fun _ => 1
    | some p => fun x => (A p.1 x).det
  have hnum : ∀ q, AnalyticAt ℝ (num q) x₀ := by
    intro q
    cases q with
    | none => exact analyticAt_const
    | some p =>
      exact analyticAt_cramerCoordinateNumerator
        (A p.1) (b p.1) (hA p.1) (hb p.1) p.2
  have hden : ∀ q, AnalyticAt ℝ (den q) x₀ := by
    intro q
    cases q with
    | none => exact analyticAt_const
    | some p => exact analyticAt_matrix_det (A p.1) (hA p.1)
  have hden_ne : ∀ q,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), den q x ≠ 0 := by
    intro q
    cases q with
    | none => simp [den]
    | some p => exact hdet_ne p.1
  obtain ⟨R, hstable⟩ :=
    finite_analytic_quotient_family_eventually_stable
      num den hnum hden hden_ne
  let Feasible : Basis → Prop :=
    fun basis => ∀ i, R none (some (basis, i))
  refine ⟨Feasible, ?_⟩
  filter_upwards [hstable,
    Filter.eventually_all.mpr hdet_ne] with x hx hdet basis
  constructor
  · intro hfeasible i
    exact (hx none (some (basis, i))).mp (by
      simpa [num, den, cramerBasisCoordinate] using hfeasible.2 i)
  · intro hfeasible
    refine ⟨hdet basis, fun i => ?_⟩
    have := (hx none (some (basis, i))).mpr (hfeasible i)
    simpa [num, den, cramerBasisCoordinate] using this

/-- Objective values of finitely many moving Cramer bases have a stable
total preorder, even when their determinant germs vanish at the limiting
parameter. -/
theorem finite_analytic_cramerBasis_value_stabilizes
    {n Basis : Type*} [Fintype n] [DecidableEq n] [Finite Basis]
    (A : Basis → ℝ → Matrix n n ℝ)
    (b c : Basis → ℝ → n → ℝ) {x₀ : ℝ}
    (hA : ∀ basis i j,
      AnalyticAt ℝ (fun x => A basis x i j) x₀)
    (hb : ∀ basis i,
      AnalyticAt ℝ (fun x => b basis x i) x₀)
    (hc : ∀ basis i,
      AnalyticAt ℝ (fun x => c basis x i) x₀)
    (hdet_ne : ∀ basis,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (A basis x).det ≠ 0) :
    ∃ R : Basis → Basis → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ basis basis',
        (cramerBasisValue (A basis) (b basis) (c basis) x ≤
            cramerBasisValue
              (A basis') (b basis') (c basis') x ↔
          R basis basis') := by
  let num : Basis → ℝ → ℝ :=
    fun basis => cramerObjectiveNumerator
      (A basis) (b basis) (c basis)
  let den : Basis → ℝ → ℝ :=
    fun basis x => (A basis x).det
  have hnum : ∀ basis, AnalyticAt ℝ (num basis) x₀ := by
    intro basis
    exact analyticAt_cramerObjectiveNumerator
      (A basis) (b basis) (c basis)
      (hA basis) (hb basis) (hc basis)
  have hden : ∀ basis, AnalyticAt ℝ (den basis) x₀ := by
    intro basis
    exact analyticAt_matrix_det (A basis) (hA basis)
  obtain ⟨R, hR⟩ :=
    finite_analytic_quotient_family_eventually_stable
      num den hnum hden hdet_ne
  exact ⟨R, by
    filter_upwards [hR] with x hx
    intro basis basis'
    simpa [num, den, cramerBasisValue] using hx basis basis'⟩

/-- If one of finitely many analytic Cramer bases is feasible throughout a
punctured right neighborhood, then one fixed feasible basis eventually
maximizes the moving linear objective among all feasible bases.

This is the finite basic-solution selection step.  Applying it to a
normalized Farkas polyhedron still requires a separate static theorem saying
that its finite optimum is attained at one of the enumerated bases. -/
theorem exists_fixed_eventual_maximizing_cramerBasis
    {n Basis : Type*} [Fintype n] [DecidableEq n]
    [Finite Basis] [Nonempty Basis]
    (A : Basis → ℝ → Matrix n n ℝ)
    (b c : Basis → ℝ → n → ℝ) {x₀ : ℝ}
    (hA : ∀ basis i j,
      AnalyticAt ℝ (fun x => A basis x i j) x₀)
    (hb : ∀ basis i,
      AnalyticAt ℝ (fun x => b basis x i) x₀)
    (hc : ∀ basis i,
      AnalyticAt ℝ (fun x => c basis x i) x₀)
    (hdet_ne : ∀ basis,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (A basis x).det ≠ 0)
    (hexists :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ basis, IsCramerBasisFeasible A b x basis) :
    ∃ basisMax,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        IsCramerBasisFeasible A b x basisMax ∧
          ∀ basis, IsCramerBasisFeasible A b x basis →
            cramerBasisValue (A basis) (b basis) (c basis) x ≤
              cramerBasisValue
                (A basisMax) (b basisMax) (c basisMax) x := by
  classical
  letI := Fintype.ofFinite Basis
  obtain ⟨Feasible, hfeasible⟩ :=
    finite_analytic_cramerBasis_feasibility_stabilizes
      A b hA hb hdet_ne
  obtain ⟨R, horder⟩ :=
    finite_analytic_cramerBasis_value_stabilizes
      A b c hA hb hc hdet_ne
  obtain ⟨x, hxFeasible, hxOrder, basis₀, hbasis₀⟩ :=
    (hfeasible.and (horder.and hexists)).exists
  have hfixedNonempty :
      (Finset.univ.filter Feasible).Nonempty := by
    refine ⟨basis₀, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hxFeasible basis₀).mp hbasis₀
  obtain ⟨basisMax, hbasisMax, hmax⟩ :=
    (Finset.univ.filter Feasible).exists_max_image
      (fun basis =>
        cramerBasisValue (A basis) (b basis) (c basis) x)
      hfixedNonempty
  refine ⟨basisMax, ?_⟩
  filter_upwards [hfeasible, horder] with y hyFeasible hyOrder
  have hbasisMaxFixed : Feasible basisMax := by
    simpa using hbasisMax
  refine ⟨(hyFeasible basisMax).mpr hbasisMaxFixed, ?_⟩
  intro basis hbasis
  have hbasisFixed : Feasible basis :=
    (hyFeasible basis).mp hbasis
  have hxBasis :
      IsCramerBasisFeasible A b x basis :=
    (hxFeasible basis).mpr hbasisFixed
  have hvalueAtX :
      cramerBasisValue (A basis) (b basis) (c basis) x ≤
        cramerBasisValue
          (A basisMax) (b basisMax) (c basisMax) x := by
    apply hmax basis
    simpa using hbasisFixed
  have hR : R basis basisMax :=
    (hxOrder basis basisMax).mp hvalueAtX
  exact (hyOrder basis basisMax).mpr hR

/-- The square system cut out by one row/column choice in a rectangular
parameter-dependent matrix. -/
def selectedBasisMatrix
    {Row Col n Basis : Type*}
    (G : ℝ → Matrix Row Col ℝ)
    (rows : Basis → n → Row) (cols : Basis → n → Col)
    (basis : Basis) (x : ℝ) : Matrix n n ℝ :=
  (G x).submatrix (rows basis) (cols basis)

/-- The selected coordinates of the moving right-hand side. -/
def selectedBasisRhs
    {Row n Basis : Type*}
    (rhs : ℝ → Row → ℝ) (rows : Basis → n → Row)
    (basis : Basis) (x : ℝ) (i : n) : ℝ :=
  rhs x (rows basis i)

/-- The selected coordinates of the moving objective. -/
def selectedBasisObjective
    {Col n Basis : Type*}
    (objective : ℝ → Col → ℝ) (cols : Basis → n → Col)
    (basis : Basis) (x : ℝ) (i : n) : ℝ :=
  objective x (cols basis i)

/-- Concrete rectangular-matrix form of fixed eventual Cramer-basis
selection.  All possible row and column choices may be put in `Basis`.

The theorem freezes feasibility and objective order among those choices.  A
static vertex theorem is still needed to show that these choices cover the
optimum of the full normalized Farkas polyhedron. -/
theorem exists_fixed_eventual_maximizing_selectedBasis
    {Row Col n Basis : Type*}
    [Finite Row] [Finite Col] [Fintype n] [DecidableEq n]
    [Finite Basis] [Nonempty Basis]
    (G : ℝ → Matrix Row Col ℝ)
    (rhs : ℝ → Row → ℝ) (objective : ℝ → Col → ℝ)
    (rows : Basis → n → Row) (cols : Basis → n → Col)
    {x₀ : ℝ}
    (hG : ∀ i j, AnalyticAt ℝ (fun x => G x i j) x₀)
    (hrhs : ∀ i, AnalyticAt ℝ (fun x => rhs x i) x₀)
    (hobjective : ∀ j,
      AnalyticAt ℝ (fun x => objective x j) x₀)
    (hdet_ne : ∀ basis,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (selectedBasisMatrix G rows cols basis x).det ≠ 0)
    (hexists :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ basis,
          IsCramerBasisFeasible
            (selectedBasisMatrix G rows cols)
            (selectedBasisRhs rhs rows) x basis) :
    ∃ basisMax,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        IsCramerBasisFeasible
            (selectedBasisMatrix G rows cols)
            (selectedBasisRhs rhs rows) x basisMax ∧
          ∀ basis,
            IsCramerBasisFeasible
                (selectedBasisMatrix G rows cols)
                (selectedBasisRhs rhs rows) x basis →
              cramerBasisValue
                  (selectedBasisMatrix G rows cols basis)
                  (selectedBasisRhs rhs rows basis)
                  (selectedBasisObjective objective cols basis) x ≤
                cramerBasisValue
                  (selectedBasisMatrix G rows cols basisMax)
                  (selectedBasisRhs rhs rows basisMax)
                  (selectedBasisObjective objective cols basisMax) x := by
  apply exists_fixed_eventual_maximizing_cramerBasis
    (selectedBasisMatrix G rows cols)
    (selectedBasisRhs rhs rows)
    (selectedBasisObjective objective cols)
  · intro basis i j
    exact hG (rows basis i) (cols basis j)
  · intro basis i
    exact hrhs (rows basis i)
  · intro basis i
    exact hobjective (cols basis i)
  · exact hdet_ne
  · exact hexists

end
end LinearAlgebra
end Math
