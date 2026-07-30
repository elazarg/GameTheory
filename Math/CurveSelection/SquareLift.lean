import Math.PolynomialSignCell
import Math.AnalyticCoordinateCurve
import Math.AlgebraicSelection
import Math.CurveSelection.LexSelection
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Analytic.Polynomial

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open Math.PolynomialSignCell

namespace Math
namespace CurveSelection.SquareLiftScratch

variable {ι σ : Type*}

/-- Adjoin the requirement that one distinguished assignment coordinate is
strictly positive to a finite polynomial sign family. -/
def withPositiveCoordinatePolynomial
    (P : ι → MvPolynomial σ ℝ) (parameter : σ) :
    Option ι → MvPolynomial σ ℝ
  | none => MvPolynomial.X parameter
  | some i => P i

def withPositiveCoordinateSignPattern
    (τ : SignPattern ι) :
    SignPattern (Option ι)
  | none => 1
  | some i => τ i

theorem signCell_withPositiveCoordinate
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (parameter : σ) :
    signCell (withPositiveCoordinatePolynomial P parameter)
        (withPositiveCoordinateSignPattern τ) =
      signCell P τ ∩ {x | 0 < x parameter} := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · funext i
      exact congrFun hx (some i)
    · have h := congrFun hx none
      change 0 < x parameter
      exact sign_eq_one_iff.mp (by
        simpa [polynomialSignPattern,
          withPositiveCoordinatePolynomial,
          withPositiveCoordinateSignPattern] using h)
  · rintro ⟨hx, hparameter⟩
    funext i
    cases i with
    | none =>
        simpa [polynomialSignPattern,
          withPositiveCoordinatePolynomial,
          withPositiveCoordinateSignPattern] using
            (sign_eq_one_iff.mpr hparameter)
    | some i =>
        exact congrFun hx i

private theorem eventually_mem_signCell_of_analyticAt_of_frequently
    [Finite ι]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (γ : ℝ → Assignment σ)
    (hγ : ∀ v, AnalyticAt ℝ (fun t => γ t v) 0)
    (hfrequent :
      ∃ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ signCell P τ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      γ t ∈ signCell P τ := by
  have hcoordinate :
      ∀ i,
        AnalyticAt ℝ
          (fun t => MvPolynomial.eval (γ t) (P i)) 0 := by
    intro i
    simpa [MvPolynomial.aeval_def] using
      (AnalyticAt.aeval_mvPolynomial hγ (P i))
  have hi :
      ∀ i,
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
          SignType.sign (MvPolynomial.eval (γ t) (P i)) = τ i := by
    intro i
    rcases analyticAt_eventually_eq_or_lt_or_gt
        (hcoordinate i) analyticAt_const with hzero | hneg | hpos
    · have hsign :
          ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
            SignType.sign (MvPolynomial.eval (γ t) (P i)) = 0 := by
        filter_upwards [hzero] with t ht
        exact sign_eq_zero_iff.mpr ht
      obtain ⟨t, htcell, htsign⟩ :=
        (hfrequent.and_eventually hsign).exists
      have hτ : τ i = 0 :=
        (congrFun htcell i).symm.trans htsign
      simpa [hτ] using hsign
    · have hsign :
          ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
            SignType.sign (MvPolynomial.eval (γ t) (P i)) = -1 := by
        filter_upwards [hneg] with t ht
        exact sign_eq_neg_one_iff.mpr ht
      obtain ⟨t, htcell, htsign⟩ :=
        (hfrequent.and_eventually hsign).exists
      have hτ : τ i = -1 :=
        (congrFun htcell i).symm.trans htsign
      simpa [hτ] using hsign
    · have hsign :
          ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
            SignType.sign (MvPolynomial.eval (γ t) (P i)) = 1 := by
        filter_upwards [hpos] with t ht
        exact sign_eq_one_iff.mpr ht
      obtain ⟨t, htcell, htsign⟩ :=
        (hfrequent.and_eventually hsign).exists
      have hτ : τ i = 1 :=
        (congrFun htcell i).symm.trans htsign
      simpa [hτ] using hsign
  filter_upwards [Filter.eventually_all.mpr hi] with t ht
  exact funext ht

/-- Replace an exact sign condition by one polynomial equation using a
square slack variable. -/
def squareLiftPolynomial
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι) (i : ι) :
    MvPolynomial (σ ⊕ ι) ℝ :=
  match τ i with
  | .neg =>
      (P i).rename Sum.inl +
        MvPolynomial.X (Sum.inr i) ^ 2
  | .zero => (P i).rename Sum.inl
  | .pos =>
      (P i).rename Sum.inl -
        MvPolynomial.X (Sum.inr i) ^ 2

/-- The canonical nonnegative square slack belonging to a sign condition. -/
def squareSlack
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x : Assignment σ) (i : ι) : ℝ :=
  match τ i with
  | .neg => Real.sqrt (-MvPolynomial.eval x (P i))
  | .zero => 0
  | .pos => Real.sqrt (MvPolynomial.eval x (P i))

/-- Canonical lift of an assignment to the original and slack coordinates. -/
def squareLift
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x : Assignment σ) : Assignment (σ ⊕ ι) :=
  Sum.elim x (squareSlack P τ x)

@[simp]
theorem squareLift_inl
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x : Assignment σ) (v : σ) :
    squareLift P τ x (Sum.inl v) = x v :=
  rfl

@[simp]
theorem squareLift_inr
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x : Assignment σ) (i : ι) :
    squareLift P τ x (Sum.inr i) = squareSlack P τ x i :=
  rfl

theorem continuous_squareSlack
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι) (i : ι) :
    Continuous (fun x : Assignment σ => squareSlack P τ x i) := by
  cases hτ : τ i with
  | neg =>
      simp only [squareSlack, hτ]
      exact Real.continuous_sqrt.comp
        (MvPolynomial.continuous_eval (P i)).neg
  | zero =>
      simp only [squareSlack, hτ]
      exact continuous_const
  | pos =>
      simp only [squareSlack, hτ]
      exact Real.continuous_sqrt.comp
        (MvPolynomial.continuous_eval (P i))

theorem continuous_squareLift
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι) :
    Continuous (squareLift P τ) := by
  rw [continuous_pi_iff]
  intro v
  cases v with
  | inl v =>
      simpa using (continuous_apply v :
        Continuous (fun x : Assignment σ => x v))
  | inr i =>
      exact continuous_squareSlack P τ i

/-- Polynomial Euclidean squared radius on a finite assignment space.  Unlike
the ambient sup-metric distance, this is itself a polynomial expression and
can therefore be retained as the parameter of an algebraic germ. -/
def squaredRadius [Fintype σ]
    (x₀ x : Assignment σ) : ℝ :=
  ∑ v : σ, (x v - x₀ v) ^ 2

theorem continuous_squaredRadius [Fintype σ]
    (x₀ : Assignment σ) :
    Continuous (squaredRadius x₀) := by
  unfold squaredRadius
  fun_prop

theorem squaredRadius_nonneg [Fintype σ]
    (x₀ x : Assignment σ) :
    0 ≤ squaredRadius x₀ x := by
  unfold squaredRadius
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp]
theorem squaredRadius_self [Fintype σ]
    (x₀ : Assignment σ) :
    squaredRadius x₀ x₀ = 0 := by
  simp [squaredRadius]

theorem squaredRadius_pos [Fintype σ]
    {x₀ x : Assignment σ} (hne : x ≠ x₀) :
    0 < squaredRadius x₀ x := by
  have hcoordinate : ∃ v, x v ≠ x₀ v := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨v, hv⟩ := hcoordinate
  unfold squaredRadius
  apply Finset.sum_pos'
  · exact fun u _hu => sq_nonneg (x u - x₀ u)
  · exact ⟨v, Finset.mem_univ v,
      sq_pos_of_ne_zero (sub_ne_zero.mpr hv)⟩

/-- The multivariate polynomial representing `squaredRadius`. -/
def squaredRadiusPolynomial [Fintype σ]
    (x₀ : Assignment σ) : MvPolynomial σ ℝ :=
  ∑ v : σ,
    (MvPolynomial.X v - MvPolynomial.C (x₀ v)) ^ 2

@[simp]
theorem eval_squaredRadiusPolynomial [Fintype σ]
    (x₀ x : Assignment σ) :
    MvPolynomial.eval x (squaredRadiusPolynomial x₀) =
      squaredRadius x₀ x := by
  simp [squaredRadiusPolynomial, squaredRadius]

/-- Add one explicit algebraic parameter coordinate to a square-lift
assignment. -/
def parameterizedLiftAssignment
    (r : ℝ) (y : Assignment (σ ⊕ ι)) :
    Assignment (Option (σ ⊕ ι))
  | none => r
  | some v => y v

@[simp]
theorem parameterizedLiftAssignment_none
    (r : ℝ) (y : Assignment (σ ⊕ ι)) :
    parameterizedLiftAssignment r y none = r :=
  rfl

@[simp]
theorem parameterizedLiftAssignment_some
    (r : ℝ) (y : Assignment (σ ⊕ ι)) (v : σ ⊕ ι) :
    parameterizedLiftAssignment r y (some v) = y v :=
  rfl

/-- Polynomial squared radius of the original coordinates inside the
parameterized square-lift space. -/
def liftedSquaredRadiusPolynomial [Fintype σ] :
    (x₀ : Assignment σ) →
      MvPolynomial (Option (σ ⊕ ι)) ℝ :=
  fun x₀ =>
    ∑ v : σ,
      (MvPolynomial.X (some (Sum.inl v)) -
        MvPolynomial.C (x₀ v)) ^ 2

@[simp]
theorem eval_liftedSquaredRadiusPolynomial
    [Fintype σ]
    (x₀ : Assignment σ) (r : ℝ)
    (y : Assignment (σ ⊕ ι)) :
    MvPolynomial.eval (parameterizedLiftAssignment r y)
        (liftedSquaredRadiusPolynomial (ι := ι) x₀) =
      squaredRadius x₀ (fun v => y (Sum.inl v)) := by
  simp [liftedSquaredRadiusPolynomial, squaredRadius]

/-- The permanent polynomial equation equating the explicit parameter to
the squared radius of the original coordinates. -/
def squaredRadiusParameterEquation [Fintype σ]
    (x₀ : Assignment σ) :
    MvPolynomial (Option (σ ⊕ ι)) ℝ :=
  liftedSquaredRadiusPolynomial (ι := ι) x₀ -
    MvPolynomial.X none

@[simp]
theorem eval_squaredRadiusParameterEquation
    [Fintype σ]
    (x₀ : Assignment σ) (r : ℝ)
    (y : Assignment (σ ⊕ ι)) :
    MvPolynomial.eval (parameterizedLiftAssignment r y)
        (squaredRadiusParameterEquation (ι := ι) x₀) =
      squaredRadius x₀ (fun v => y (Sum.inl v)) - r := by
  simp [squaredRadiusParameterEquation]

/-- A polynomial squared-radius level in a finite real assignment space is
compact. -/
theorem isCompact_squaredRadius_level
    [Fintype σ]
    (x₀ : Assignment σ) (r : ℝ) :
    IsCompact {x | squaredRadius x₀ x = r} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_eq (continuous_squaredRadius x₀) continuous_const, ?_⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖x₀‖ + Real.sqrt r, ?_⟩
  intro x hx
  have hr : 0 ≤ r := by
    rw [← hx]
    exact squaredRadius_nonneg x₀ x
  have hbound_nonneg : 0 ≤ ‖x₀‖ + Real.sqrt r :=
    add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hbound_nonneg).2
  intro v
  have hterm :
      (x v - x₀ v) ^ 2 ≤ r := by
    calc
      (x v - x₀ v) ^ 2 ≤
          ∑ u : σ, (x u - x₀ u) ^ 2 := by
        exact Finset.single_le_sum
          (fun u _hu => sq_nonneg (x u - x₀ u))
          (Finset.mem_univ v)
      _ = r := hx
  have habs :
      |x v - x₀ v| ≤ Real.sqrt r := by
    apply abs_le_of_sq_le_sq
    · simpa [Real.sq_sqrt hr] using hterm
    · exact Real.sqrt_nonneg r
  have hx₀v : |x₀ v| ≤ ‖x₀‖ := by
    have h :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg x₀)).mp
        (le_refl ‖x₀‖) v
    simpa [Real.norm_eq_abs] using h
  rw [Real.norm_eq_abs]
  calc
    |x v| = |(x v - x₀ v) + x₀ v| := by ring_nf
    _ ≤ |x v - x₀ v| + |x₀ v| := abs_add_le _ _
    _ ≤ Real.sqrt r + ‖x₀‖ := add_le_add habs hx₀v
    _ = ‖x₀‖ + Real.sqrt r := add_comm _ _

/-- A point of the sign cell satisfies all square-lift equations. -/
theorem eval_squareLiftPolynomial_eq_zero
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    {x : Assignment σ} (hx : x ∈ signCell P τ) (i : ι) :
    MvPolynomial.eval (squareLift P τ x)
      (squareLiftPolynomial P τ i) = 0 := by
  have hsign := congrFun hx i
  cases hτ : τ i with
  | neg =>
      have hp : MvPolynomial.eval x (P i) < 0 := by
        exact (sign_eq_neg_one_iff.mp (hsign.trans hτ))
      simp only [squareLiftPolynomial, hτ, map_add,
        MvPolynomial.eval_rename, Function.comp_def,
        squareLift_inl, map_pow, MvPolynomial.eval_X,
        squareLift_inr, squareSlack]
      rw [Real.sq_sqrt (neg_nonneg.mpr hp.le)]
      ring
  | zero =>
      have hp : MvPolynomial.eval x (P i) = 0 := by
        exact sign_eq_zero_iff.mp (hsign.trans hτ)
      simpa [squareLiftPolynomial, hτ, MvPolynomial.eval_rename,
        Function.comp_def] using hp
  | pos =>
      have hp : 0 < MvPolynomial.eval x (P i) := by
        exact sign_eq_one_iff.mp (hsign.trans hτ)
      simp only [squareLiftPolynomial, hτ, map_sub,
        MvPolynomial.eval_rename, Function.comp_def,
        squareLift_inl, map_pow, MvPolynomial.eval_X,
        squareLift_inr, squareSlack]
      rw [Real.sq_sqrt hp.le]
      ring

/-- Every slack belonging to a strict sign is strictly positive on the cell. -/
theorem squareSlack_pos_of_ne_zero
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    {x : Assignment σ} (hx : x ∈ signCell P τ)
    (i : ι) (hi : τ i ≠ 0) :
    0 < squareSlack P τ x i := by
  have hsign := congrFun hx i
  cases hτ : τ i with
  | neg =>
      have hp : 0 < -MvPolynomial.eval x (P i) := by
        have := sign_eq_neg_one_iff.mp (hsign.trans hτ)
        linarith
      simpa [squareSlack, hτ] using Real.sqrt_pos.2 hp
  | zero => exact (hi hτ).elim
  | pos =>
      have hp : 0 < MvPolynomial.eval x (P i) :=
        sign_eq_one_iff.mp (hsign.trans hτ)
      simpa [squareSlack, hτ] using Real.sqrt_pos.2 hp

/-- The algebraic square-lift locus, retaining positivity only for the
slacks which encode strict signs. -/
def squareLiftCell
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι) :
    Set (Assignment (σ ⊕ ι)) :=
  {y |
    (∀ i, MvPolynomial.eval y (squareLiftPolynomial P τ i) = 0) ∧
    (∀ i, τ i ≠ 0 → 0 < y (Sum.inr i))}

theorem squareLift_mem_squareLiftCell
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    {x : Assignment σ} (hx : x ∈ signCell P τ) :
    squareLift P τ x ∈ squareLiftCell P τ := by
  exact
    ⟨fun i => eval_squareLiftPolynomial_eq_zero P τ hx i,
      fun i hi => squareSlack_pos_of_ne_zero P τ hx i hi⟩

/-- Projecting a square-lift point with positive strict slacks recovers the
original complete sign cell. -/
theorem project_mem_signCell_of_mem_squareLiftCell
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    {y : Assignment (σ ⊕ ι)}
    (hy : y ∈ squareLiftCell P τ) :
    (fun v => y (Sum.inl v)) ∈ signCell P τ := by
  apply funext
  intro i
  change
    SignType.sign
      (MvPolynomial.eval (fun v => y (Sum.inl v)) (P i)) = τ i
  have heq := hy.1 i
  cases hτ : τ i with
  | neg =>
      have hs : 0 < y (Sum.inr i) := hy.2 i (by simp [hτ])
      have heq' :
          MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) +
              y (Sum.inr i) ^ 2 = 0 := by
        simpa [squareLiftPolynomial, hτ, MvPolynomial.eval_rename,
          Function.comp_def] using heq
      have hp :
          MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) =
            -(y (Sum.inr i) ^ 2) := by
        linarith
      apply sign_eq_neg_one_iff.mpr
      rw [hp]
      exact neg_neg_of_pos (sq_pos_of_pos hs)
  | zero =>
      have hp :
          MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) = 0 := by
        simpa [squareLiftPolynomial, hτ, MvPolynomial.eval_rename,
          Function.comp_def] using heq
      exact sign_eq_zero_iff.mpr hp
  | pos =>
      have hs : 0 < y (Sum.inr i) := hy.2 i (by simp [hτ])
      have heq' :
          MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) -
              y (Sum.inr i) ^ 2 = 0 := by
        simpa [squareLiftPolynomial, hτ, MvPolynomial.eval_rename,
          Function.comp_def] using heq
      have hp :
          MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) =
            y (Sum.inr i) ^ 2 := by
        linarith
      apply sign_eq_one_iff.mpr
      rw [hp]
      exact sq_pos_of_pos hs

/-- The product of precisely those slack coordinates which encode strict
signs.  Its nonvanishing is equivalent to nonvanishing of every strict
slack. -/
def strictSlackProduct [Fintype ι]
    (τ : SignPattern ι) (y : Assignment (σ ⊕ ι)) : ℝ := by
  classical
  exact ∏ i : {i : ι // τ i ≠ 0}, y (Sum.inr i.1)

theorem continuous_strictSlackProduct [Fintype ι]
    (τ : SignPattern ι) :
    Continuous (strictSlackProduct (σ := σ) τ) := by
  classical
  unfold strictSlackProduct
  fun_prop

theorem strictSlackProduct_squareLift_ne_zero
    [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    {x : Assignment σ} (hx : x ∈ signCell P τ) :
    strictSlackProduct τ (squareLift P τ x) ≠ 0 := by
  classical
  apply ne_of_gt
  unfold strictSlackProduct
  apply Finset.prod_pos
  intro i _hi
  exact squareSlack_pos_of_ne_zero P τ hx i.1 i.2

/-- Permanent equations for the parameterized square lift: the original
square-lift equations, the canonical zero values of unused equality slacks,
and one polynomial squared-radius parameter equation. -/
abbrev ParameterizedSquareLiftEquation
    (τ : SignPattern ι) :=
  ι ⊕ ({i : ι // τ i = 0} ⊕ Unit)

def parameterizedSquareLiftPolynomial
    [Fintype σ]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) :
    ParameterizedSquareLiftEquation τ →
      MvPolynomial (Option (σ ⊕ ι)) ℝ
  | .inl i =>
      (squareLiftPolynomial P τ i).rename some
  | .inr (.inl i) =>
      MvPolynomial.X (some (Sum.inr i.1))
  | .inr (.inr ()) =>
      squaredRadiusParameterEquation (ι := ι) x₀

/-- The polynomial whose value is the square of the strict-slack score. -/
def parameterizedStrictScorePolynomial
    [Fintype ι]
    (τ : SignPattern ι) :
    MvPolynomial (Option (σ ⊕ ι)) ℝ := by
  classical
  exact
    (∏ i : {i : ι // τ i ≠ 0},
      MvPolynomial.X (some (Sum.inr i.1))) ^ 2

@[simp]
theorem eval_parameterizedStrictScorePolynomial
    [Fintype ι]
    (τ : SignPattern ι)
    (r : ℝ) (y : Assignment (σ ⊕ ι)) :
    MvPolynomial.eval (parameterizedLiftAssignment r y)
        (parameterizedStrictScorePolynomial (σ := σ) τ) =
      strictSlackProduct τ y ^ 2 := by
  classical
  simp [parameterizedStrictScorePolynomial, strictSlackProduct]

/-- A fixed enumeration of all square-lift coordinates. -/
def enumeratedLiftCoordinate
    [Fintype σ] [Fintype ι]
    (k : Fin (Fintype.card (σ ⊕ ι)))
    (y : Assignment (σ ⊕ ι)) : ℝ :=
  y ((Fintype.equivFin (σ ⊕ ι)).symm k)

theorem continuous_enumeratedLiftCoordinate
    [Fintype σ] [Fintype ι]
    (k : Fin (Fintype.card (σ ⊕ ι))) :
    Continuous (enumeratedLiftCoordinate (σ := σ) (ι := ι) k) := by
  exact continuous_apply _

/-- Polynomial objectives in the exact order used by compact selection:
first maximize the squared strict score, then minimize every lift coordinate.
-/
def triangularLexObjectivePolynomial
    [Fintype σ] [Fintype ι]
    (τ : SignPattern ι) :
    Fin (Fintype.card (σ ⊕ ι) + 1) →
      MvPolynomial (Option (σ ⊕ ι)) ℝ :=
  Fin.cases
    (parameterizedStrictScorePolynomial (σ := σ) τ)
    (fun k =>
      MvPolynomial.X
        (some ((Fintype.equivFin (σ ⊕ ι)).symm k)))

@[simp]
theorem eval_triangularLexObjectivePolynomial_zero
    [Fintype σ] [Fintype ι]
    (τ : SignPattern ι) (r : ℝ)
    (y : Assignment (σ ⊕ ι)) :
    MvPolynomial.eval (parameterizedLiftAssignment r y)
        (triangularLexObjectivePolynomial τ 0) =
      strictSlackProduct τ y ^ 2 := by
  simp [triangularLexObjectivePolynomial]

@[simp]
theorem eval_triangularLexObjectivePolynomial_succ
    [Fintype σ] [Fintype ι]
    (τ : SignPattern ι) (r : ℝ)
    (y : Assignment (σ ⊕ ι))
    (k : Fin (Fintype.card (σ ⊕ ι))) :
    MvPolynomial.eval (parameterizedLiftAssignment r y)
        (triangularLexObjectivePolynomial τ k.succ) =
      enumeratedLiftCoordinate k y := by
  simp [triangularLexObjectivePolynomial,
    enumeratedLiftCoordinate]

/-- Every exact sign-cell point, canonically square-lifted and equipped with
its squared radius, satisfies all permanent parameterized equations. -/
theorem eval_parameterizedSquareLiftPolynomial_eq_zero
    [Fintype σ]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ)
    {x : Assignment σ} (hx : x ∈ signCell P τ) :
    ∀ e,
      MvPolynomial.eval
          (parameterizedLiftAssignment
            (squaredRadius x₀ x) (squareLift P τ x))
          (parameterizedSquareLiftPolynomial P τ x₀ e) = 0 := by
  intro e
  rcases e with i | e
  · simpa [parameterizedSquareLiftPolynomial,
      MvPolynomial.eval_rename, Function.comp_def] using
        eval_squareLiftPolynomial_eq_zero P τ hx i
  · rcases e with i | u
    · simp [parameterizedSquareLiftPolynomial,
        squareLift, squareSlack, i.2]
    · rcases u with ⟨⟩
      simp [parameterizedSquareLiftPolynomial]

/-- Positivity of a chosen square root is not needed after taking a closure:
the equations and nonvanishing of all strict slacks already determine the
correct signs after projection. -/
theorem project_mem_signCell_of_equations_of_strictSlackProduct_ne_zero
    [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    {y : Assignment (σ ⊕ ι)}
    (hequation :
      ∀ i, MvPolynomial.eval y (squareLiftPolynomial P τ i) = 0)
    (hstrict : strictSlackProduct τ y ≠ 0) :
    (fun v => y (Sum.inl v)) ∈ signCell P τ := by
  classical
  have hslack :
      ∀ i, τ i ≠ 0 → y (Sum.inr i) ≠ 0 := by
    intro i hi
    let j : {i : ι // τ i ≠ 0} := ⟨i, hi⟩
    exact
      (Finset.prod_ne_zero_iff.mp hstrict
        j (Finset.mem_univ j))
  apply funext
  intro i
  change
    SignType.sign
      (MvPolynomial.eval (fun v => y (Sum.inl v)) (P i)) = τ i
  have heq := hequation i
  cases hτ : τ i with
  | neg =>
      have hs : y (Sum.inr i) ≠ 0 := hslack i (by simp [hτ])
      have hp :
          MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) =
            -(y (Sum.inr i) ^ 2) := by
        have heq' :
            MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) +
                y (Sum.inr i) ^ 2 = 0 := by
          simpa [squareLiftPolynomial, hτ, MvPolynomial.eval_rename,
            Function.comp_def] using heq
        exact eq_neg_of_add_eq_zero_left heq'
      apply sign_eq_neg_one_iff.mpr
      rw [hp]
      exact neg_neg_of_pos (sq_pos_of_ne_zero hs)
  | zero =>
      apply sign_eq_zero_iff.mpr
      simpa [squareLiftPolynomial, hτ, MvPolynomial.eval_rename,
        Function.comp_def] using heq
  | pos =>
      have hs : y (Sum.inr i) ≠ 0 := hslack i (by simp [hτ])
      have hp :
          MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) =
            y (Sum.inr i) ^ 2 := by
        have heq' :
            MvPolynomial.eval (fun v => y (Sum.inl v)) (P i) -
                y (Sum.inr i) ^ 2 = 0 := by
          simpa [squareLiftPolynomial, hτ, MvPolynomial.eval_rename,
            Function.comp_def] using heq
        exact sub_eq_zero.mp heq'
      apply sign_eq_one_iff.mpr
      rw [hp]
      exact sq_pos_of_ne_zero hs

/-- Closure, inside a fixed radial fiber, of canonical lifts of points of
the exact sign cell. -/
def liftedCellRadialClosure [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ) :
    Set (Assignment (σ ⊕ ι)) :=
  closure
    (squareLift P τ ''
      (signCell P τ ∩ Metric.sphere x₀ r))

theorem isCompact_liftedCellRadialClosure
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ) :
    IsCompact (liftedCellRadialClosure P τ x₀ r) := by
  let K : Set (Assignment (σ ⊕ ι)) :=
    squareLift P τ '' Metric.sphere x₀ r
  have hK : IsCompact K :=
    (isCompact_sphere _ _ :
      IsCompact (Metric.sphere x₀ r)).image
        (continuous_squareLift P τ)
  have hsubset :
      liftedCellRadialClosure P τ x₀ r ⊆ K := by
    apply closure_minimal
    · exact Set.image_mono Set.inter_subset_right
    · exact hK.isClosed
  exact hK.of_isClosed_subset isClosed_closure hsubset

theorem equations_of_mem_liftedCellRadialClosure
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ)
    {y : Assignment (σ ⊕ ι)}
    (hy : y ∈ liftedCellRadialClosure P τ x₀ r) :
    ∀ i, MvPolynomial.eval y (squareLiftPolynomial P τ i) = 0 := by
  intro i
  let Z : Set (Assignment (σ ⊕ ι)) :=
    {z | MvPolynomial.eval z (squareLiftPolynomial P τ i) = 0}
  have hZ : IsClosed Z :=
    isClosed_eq
      (MvPolynomial.continuous_eval
        (squareLiftPolynomial P τ i))
      continuous_const
  have hsub :
      squareLift P τ ''
          (signCell P τ ∩ Metric.sphere x₀ r) ⊆ Z := by
    rintro _ ⟨x, hx, rfl⟩
    exact eval_squareLiftPolynomial_eq_zero P τ hx.1 i
  exact (closure_minimal hsub hZ) hy

theorem exists_squareLift_on_sphere_of_mem_liftedCellRadialClosure
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ)
    {y : Assignment (σ ⊕ ι)}
    (hy : y ∈ liftedCellRadialClosure P τ x₀ r) :
    ∃ z ∈ Metric.sphere x₀ r, y = squareLift P τ z := by
  let K : Set (Assignment (σ ⊕ ι)) :=
    squareLift P τ '' Metric.sphere x₀ r
  have hK : IsCompact K :=
    (isCompact_sphere _ _ :
      IsCompact (Metric.sphere x₀ r)).image
        (continuous_squareLift P τ)
  have hsub :
      liftedCellRadialClosure P τ x₀ r ⊆ K := by
    apply closure_minimal
    · exact Set.image_mono Set.inter_subset_right
    · exact hK.isClosed
  obtain ⟨z, hz, hzy⟩ := hsub hy
  exact ⟨z, hz, hzy.symm⟩

/--
In the radial fiber through a sign-cell point, choose a point which maximizes
the squared strict-slack product and is then successively minimal in any
prescribed finite family of continuous coordinates.

The selected point still projects to the exact sign cell: the original lift
has nonzero score, so the maximizer does too.
-/
theorem exists_radial_lexSelected_squareLift
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ)
    (ncoord : ℕ)
    (c : Fin ncoord → Assignment (σ ⊕ ι) → ℝ)
    (hc : ∀ k, Continuous (c k))
    {x : Assignment σ} (hx : x ∈ signCell P τ) :
    ∃ (y : Assignment (σ ⊕ ι)) (z : Assignment σ),
      y ∈ liftedCellRadialClosure P τ x₀ (dist x x₀) ∧
      z ∈ Metric.sphere x₀ (dist x x₀) ∧
      y = squareLift P τ z ∧
      strictSlackProduct τ y ≠ 0 ∧
      (fun v => y (Sum.inl v)) ∈ signCell P τ ∧
      (∀ w : Assignment (σ ⊕ ι),
        w ∈ liftedCellRadialClosure P τ x₀ (dist x x₀) →
        strictSlackProduct τ w ^ 2 ≤ strictSlackProduct τ y ^ 2) ∧
      ∀ (k : Fin ncoord) (w : Assignment (σ ⊕ ι)),
        w ∈ liftedCellRadialClosure P τ x₀ (dist x x₀) →
        strictSlackProduct τ w ^ 2 =
            strictSlackProduct τ y ^ 2 →
        (∀ j : Fin ncoord, j < k → c j w = c j y) →
        c k y ≤ c k w := by
  let S :=
    liftedCellRadialClosure P τ x₀ (dist x x₀)
  have hwS : squareLift P τ x ∈ S := by
    apply subset_closure
    refine ⟨x, ?_, rfl⟩
    refine ⟨hx, ?_⟩
    rw [Metric.mem_sphere]
  obtain ⟨y, hyS, hystrict, hymax, hylex⟩ :=
    Math.CurveSelection.LexSelection.score_ne_zero_of_exists_nonzero_of_lexMinOn_maximizers
        S
        (isCompact_liftedCellRadialClosure P τ x₀ (dist x x₀))
        (strictSlackProduct τ)
        (continuous_strictSlackProduct τ)
        ncoord c hc hwS
        (strictSlackProduct_squareLift_ne_zero P τ hx)
  obtain ⟨z, hzSphere, hyEq⟩ :=
    exists_squareLift_on_sphere_of_mem_liftedCellRadialClosure
      P τ x₀ (dist x x₀) hyS
  have hycell :
      (fun v => y (Sum.inl v)) ∈ signCell P τ :=
    project_mem_signCell_of_equations_of_strictSlackProduct_ne_zero
      P τ
      (equations_of_mem_liftedCellRadialClosure
        P τ x₀ (dist x x₀) hyS)
      hystrict
  exact
    ⟨y, z, hyS, hzSphere, hyEq, hystrict, hycell, hymax, hylex⟩

/--
Perform the radial score-maximizing lexicographic selection simultaneously
along a convergent sequence.  The auxiliary square-lift assignments converge
to the canonical lift of the same endpoint.
-/
theorem exists_lexSelected_squareLift_sequence
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ)
    (x : ℕ → Assignment σ)
    (hx : ∀ m, x m ∈ signCell P τ)
    (hxlim : Tendsto x atTop (𝓝 x₀))
    (ncoord : ℕ)
    (c : Fin ncoord → Assignment (σ ⊕ ι) → ℝ)
    (hc : ∀ k, Continuous (c k)) :
    ∃ (y : ℕ → Assignment (σ ⊕ ι))
        (z : ℕ → Assignment σ),
      (∀ m,
        y m ∈ liftedCellRadialClosure
          P τ x₀ (dist (x m) x₀)) ∧
      (∀ m, z m ∈ Metric.sphere x₀ (dist (x m) x₀)) ∧
      (∀ m, y m = squareLift P τ (z m)) ∧
      (∀ m, strictSlackProduct τ (y m) ≠ 0) ∧
      (∀ m, (fun v => y m (Sum.inl v)) ∈ signCell P τ) ∧
      Tendsto z atTop (𝓝 x₀) ∧
      Tendsto y atTop (𝓝 (squareLift P τ x₀)) ∧
      (∀ m w,
        w ∈ liftedCellRadialClosure
            P τ x₀ (dist (x m) x₀) →
        strictSlackProduct τ w ^ 2 ≤
          strictSlackProduct τ (y m) ^ 2) ∧
      ∀ m (k : Fin ncoord) w,
        w ∈ liftedCellRadialClosure
            P τ x₀ (dist (x m) x₀) →
        strictSlackProduct τ w ^ 2 =
            strictSlackProduct τ (y m) ^ 2 →
        (∀ j : Fin ncoord, j < k → c j w = c j (y m)) →
        c k (y m) ≤ c k w := by
  classical
  choose y z hyS hzSphere hyEq hystrict hycell hymax hylex using
    fun m =>
      exists_radial_lexSelected_squareLift
        P τ x₀ ncoord c hc (hx m)
  have hzdist :
      ∀ m, dist (z m) x₀ = dist (x m) x₀ := by
    intro m
    exact Metric.mem_sphere.mp (hzSphere m)
  have hzlim : Tendsto z atTop (𝓝 x₀) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hxdist :=
      tendsto_iff_dist_tendsto_zero.mp hxlim
    exact hxdist.congr'
      (Filter.Eventually.of_forall fun m => (hzdist m).symm)
  have hylim :
      Tendsto y atTop (𝓝 (squareLift P τ x₀)) := by
    have hlift :
        Tendsto (fun m => squareLift P τ (z m))
          atTop (𝓝 (squareLift P τ x₀)) :=
      (continuous_squareLift P τ).continuousAt.tendsto.comp hzlim
    exact hlift.congr' (Filter.Eventually.of_forall fun m => (hyEq m).symm)
  exact
    ⟨y, z, hyS, hzSphere, hyEq, hystrict, hycell,
      hzlim, hylim, hymax, hylex⟩

/--
A nonstationary convergent sequence can be thinned so that its distance to
the limit is strictly decreasing.  This supplies an injective positive
radial parameter for the algebraic germ.
-/
theorem exists_strictAnti_distance_subsequence
    {E : Type*} [MetricSpace E]
    (x : ℕ → E) (x₀ : E)
    (hne : ∀ m, x m ≠ x₀)
    (hxlim : Tendsto x atTop (𝓝 x₀)) :
    ∃ (z : ℕ → E),
      (∀ m, z m ∈ Set.range x) ∧
      StrictAnti (fun m => dist (z m) x₀) ∧
      Tendsto z atTop (𝓝 x₀) := by
  let a : ℕ → ℝ := fun m => dist (x m) x₀
  have hapos : ∀ m, 0 < a m := by
    intro m
    change 0 < dist (x m) x₀
    exact dist_pos.mpr (hne m)
  have halim : Tendsto a atTop (𝓝 0) := by
    simpa [a] using tendsto_iff_dist_tendsto_zero.mp hxlim
  have hglb : IsGLB (Set.range a) 0 :=
    IsGLB.range_of_tendsto (fun m => (hapos m).le) halim
  have hzero_notMem : (0 : ℝ) ∉ Set.range a := by
    rintro ⟨m, hm⟩
    have hmpos := hapos m
    rw [hm] at hmpos
    exact (lt_irrefl 0 hmpos).elim
  obtain ⟨u, huanti, _hupos, _hulim, humem⟩ :=
    hglb.exists_seq_strictAnti_tendsto_of_notMem
      hzero_notMem ⟨a 0, Set.mem_range_self 0⟩
  choose φ hφ using humem
  have hφinj : Function.Injective φ := by
    intro m n hmn
    apply huanti.injective
    rw [← hφ m, ← hφ n, hmn]
  let z : ℕ → E := x ∘ φ
  have hzrange : ∀ m, z m ∈ Set.range x :=
    fun m => ⟨φ m, rfl⟩
  have hzanti : StrictAnti (fun m => dist (z m) x₀) := by
    intro m n hmn
    change a (φ n) < a (φ m)
    rw [hφ m, hφ n]
    exact huanti hmn
  exact
    ⟨z, hzrange, hzanti,
      hxlim.comp hφinj.nat_tendsto_atTop⟩

/--
A nonstationary convergent finite assignment sequence can be thinned so that
its polynomial squared radius is strictly decreasing to zero.
-/
theorem exists_strictAnti_squaredRadius_subsequence
    [Fintype σ]
    (x : ℕ → Assignment σ) (x₀ : Assignment σ)
    (hne : ∀ m, x m ≠ x₀)
    (hxlim : Tendsto x atTop (𝓝 x₀)) :
    ∃ (z : ℕ → Assignment σ),
      (∀ m, z m ∈ Set.range x) ∧
      StrictAnti (fun m => squaredRadius x₀ (z m)) ∧
      Tendsto z atTop (𝓝 x₀) := by
  let a : ℕ → ℝ := fun m => squaredRadius x₀ (x m)
  have hapos : ∀ m, 0 < a m := by
    intro m
    exact squaredRadius_pos (hne m)
  have halim : Tendsto a atTop (𝓝 0) := by
    have h :=
      (continuous_squaredRadius x₀).continuousAt.tendsto.comp hxlim
    change
      Tendsto (fun m => squaredRadius x₀ (x m))
        atTop (𝓝 (squaredRadius x₀ x₀)) at h
    simpa only [a, squaredRadius_self] using h
  have hglb : IsGLB (Set.range a) 0 :=
    IsGLB.range_of_tendsto (fun m => (hapos m).le) halim
  have hzero_notMem : (0 : ℝ) ∉ Set.range a := by
    rintro ⟨m, hm⟩
    have hmpos := hapos m
    rw [hm] at hmpos
    exact (lt_irrefl 0 hmpos).elim
  obtain ⟨u, huanti, _hupos, _hulim, humem⟩ :=
    hglb.exists_seq_strictAnti_tendsto_of_notMem
      hzero_notMem ⟨a 0, Set.mem_range_self 0⟩
  choose φ hφ using humem
  have hφinj : Function.Injective φ := by
    intro m n hmn
    apply huanti.injective
    rw [← hφ m, ← hφ n, hmn]
  let z : ℕ → Assignment σ := x ∘ φ
  have hzrange : ∀ m, z m ∈ Set.range x :=
    fun m => ⟨φ m, rfl⟩
  have hzanti :
      StrictAnti (fun m => squaredRadius x₀ (z m)) := by
    intro m n hmn
    change a (φ n) < a (φ m)
    rw [hφ m, hφ n]
    exact huanti hmn
  exact
    ⟨z, hzrange, hzanti,
      hxlim.comp hφinj.nat_tendsto_atTop⟩

/-- Closure of canonical sign-cell lifts in one polynomial
`squaredRadius` fiber. -/
def liftedCellSquaredRadiusClosure [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ) :
    Set (Assignment (σ ⊕ ι)) :=
  closure
    (squareLift P τ ''
      (signCell P τ ∩ {x | squaredRadius x₀ x = r}))

theorem isCompact_liftedCellSquaredRadiusClosure
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ) :
    IsCompact (liftedCellSquaredRadiusClosure P τ x₀ r) := by
  let K : Set (Assignment (σ ⊕ ι)) :=
    squareLift P τ '' {x | squaredRadius x₀ x = r}
  have hK : IsCompact K :=
    (isCompact_squaredRadius_level x₀ r).image
      (continuous_squareLift P τ)
  have hsubset :
      liftedCellSquaredRadiusClosure P τ x₀ r ⊆ K := by
    apply closure_minimal
    · exact Set.image_mono Set.inter_subset_right
    · exact hK.isClosed
  exact hK.of_isClosed_subset isClosed_closure hsubset

theorem equations_of_mem_liftedCellSquaredRadiusClosure
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ)
    {y : Assignment (σ ⊕ ι)}
    (hy : y ∈ liftedCellSquaredRadiusClosure P τ x₀ r) :
    ∀ i, MvPolynomial.eval y (squareLiftPolynomial P τ i) = 0 := by
  intro i
  let Z : Set (Assignment (σ ⊕ ι)) :=
    {z | MvPolynomial.eval z (squareLiftPolynomial P τ i) = 0}
  have hZ : IsClosed Z :=
    isClosed_eq
      (MvPolynomial.continuous_eval
        (squareLiftPolynomial P τ i))
      continuous_const
  have hsub :
      squareLift P τ ''
          (signCell P τ ∩
            {x | squaredRadius x₀ x = r}) ⊆ Z := by
    rintro _ ⟨x, hx, rfl⟩
    exact eval_squareLiftPolynomial_eq_zero P τ hx.1 i
  exact (closure_minimal hsub hZ) hy

theorem exists_squareLift_on_squaredRadius_of_mem_closure
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ)
    {y : Assignment (σ ⊕ ι)}
    (hy : y ∈ liftedCellSquaredRadiusClosure P τ x₀ r) :
    ∃ z, squaredRadius x₀ z = r ∧
      y = squareLift P τ z := by
  let K : Set (Assignment (σ ⊕ ι)) :=
    squareLift P τ '' {x | squaredRadius x₀ x = r}
  have hK : IsCompact K :=
    (isCompact_squaredRadius_level x₀ r).image
      (continuous_squareLift P τ)
  have hsub :
      liftedCellSquaredRadiusClosure P τ x₀ r ⊆ K := by
    apply closure_minimal
    · exact Set.image_mono Set.inter_subset_right
    · exact hK.isClosed
  obtain ⟨z, hz, hzy⟩ := hsub hy
  exact ⟨z, hz, hzy.symm⟩

/--
Near a selected lifted point whose strict slacks are nonzero, the polynomial
square-lift equations, the zero-slack equations, and the fixed-radius
equation cut out no extra local points: every such nearby solution already
belongs to the compact lifted-cell closure.

This is the Euclidean local-fiber bridge used when passing from a
lexicographic extremum on the compact selected set to an extremum on a
regular algebraic stratum.
-/
theorem eventually_mem_liftedCellSquaredRadiusClosure_of_equations
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ)
    {y : Assignment (σ ⊕ ι)}
    (hy :
      y ∈ liftedCellSquaredRadiusClosure P τ x₀ r)
    (hstrict : strictSlackProduct τ y ≠ 0) :
    ∀ᶠ w in 𝓝 y,
      (∀ i,
        MvPolynomial.eval w (squareLiftPolynomial P τ i) = 0) →
      (∀ i, τ i = 0 → w (Sum.inr i) = 0) →
      squaredRadius x₀ (fun v => w (Sum.inl v)) = r →
      w ∈ liftedCellSquaredRadiusClosure P τ x₀ r := by
  classical
  obtain ⟨z, _hzRadius, hyLift⟩ :=
    exists_squareLift_on_squaredRadius_of_mem_closure
      P τ x₀ r hy
  have hypos :
      ∀ i : {i : ι // τ i ≠ 0},
        0 < y (Sum.inr i.1) := by
    intro i
    have hine :
        y (Sum.inr i.1) ≠ 0 := by
      exact
        Finset.prod_ne_zero_iff.mp hstrict
          i (Finset.mem_univ i)
    have hinonneg :
        0 ≤ y (Sum.inr i.1) := by
      rw [hyLift, squareLift_inr]
      cases hτ : τ i.1 <;>
        simp [squareSlack, hτ]
    exact lt_of_le_of_ne hinonneg hine.symm
  have heventuallyPositive :
      ∀ᶠ w in 𝓝 y,
        ∀ i : {i : ι // τ i ≠ 0},
          0 < w (Sum.inr i.1) := by
    apply Filter.eventually_all.mpr
    intro i
    exact
      (continuous_apply (Sum.inr i.1)).continuousAt.eventually
        (Ioi_mem_nhds (hypos i))
  filter_upwards [heventuallyPositive] with w hwpos
  intro hequation hzeroSlack hradius
  have hwstrict : strictSlackProduct τ w ≠ 0 := by
    exact
      Finset.prod_ne_zero_iff.mpr fun i _hi =>
        ne_of_gt (hwpos i)
  have hwcell :
      (fun v => w (Sum.inl v)) ∈ signCell P τ :=
    project_mem_signCell_of_equations_of_strictSlackProduct_ne_zero
      P τ hequation hwstrict
  have hwLift :
      w = squareLift P τ (fun v => w (Sum.inl v)) := by
    funext v
    cases v with
    | inl v =>
        rfl
    | inr i =>
        cases hτ : τ i with
        | neg =>
            have hi : τ i ≠ 0 := by simp [hτ]
            let j : {i : ι // τ i ≠ 0} := ⟨i, hi⟩
            have hpos : 0 < w (Sum.inr i) := hwpos j
            have heq := hequation i
            have heq' :
                MvPolynomial.eval
                    (fun v => w (Sum.inl v)) (P i) +
                  w (Sum.inr i) ^ 2 = 0 := by
              simpa [squareLiftPolynomial, hτ,
                MvPolynomial.eval_rename,
                Function.comp_def] using heq
            have hsquare :
                w (Sum.inr i) ^ 2 =
                  -MvPolynomial.eval
                    (fun v => w (Sum.inl v)) (P i) := by
              linarith
            rw [squareLift_inr]
            simp only [squareSlack, hτ]
            rw [← hsquare, Real.sqrt_sq_eq_abs,
              abs_of_pos hpos]
        | zero =>
            rw [squareLift_inr]
            simp only [squareSlack, hτ]
            exact hzeroSlack i hτ
        | pos =>
            have hi : τ i ≠ 0 := by simp [hτ]
            let j : {i : ι // τ i ≠ 0} := ⟨i, hi⟩
            have hpos : 0 < w (Sum.inr i) := hwpos j
            have heq := hequation i
            have heq' :
                MvPolynomial.eval
                    (fun v => w (Sum.inl v)) (P i) -
                  w (Sum.inr i) ^ 2 = 0 := by
              simpa [squareLiftPolynomial, hτ,
                MvPolynomial.eval_rename,
                Function.comp_def] using heq
            have hsquare :
                w (Sum.inr i) ^ 2 =
                  MvPolynomial.eval
                    (fun v => w (Sum.inl v)) (P i) := by
              exact (sub_eq_zero.mp heq').symm
            rw [squareLift_inr]
            simp only [squareSlack, hτ]
            rw [← hsquare, Real.sqrt_sq_eq_abs,
              abs_of_pos hpos]
  apply subset_closure
  exact
    ⟨fun v => w (Sum.inl v),
      ⟨hwcell, hradius⟩, hwLift.symm⟩

/--
Bundled version for the permanent parameterized square-lift polynomial
family.  On the fiber where the explicit parameter equals `r`, its complete
zero locus agrees locally with the compact lifted-cell closure.
-/
theorem
    eventually_mem_liftedCellSquaredRadiusClosure_of_parameterizedEquations
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ)
    {y : Assignment (σ ⊕ ι)}
    (hy :
      y ∈ liftedCellSquaredRadiusClosure P τ x₀ r)
    (hstrict : strictSlackProduct τ y ≠ 0) :
    ∀ᶠ w in 𝓝 y,
      (∀ e : ParameterizedSquareLiftEquation τ,
        MvPolynomial.eval
          (parameterizedLiftAssignment r w)
          (parameterizedSquareLiftPolynomial P τ x₀ e) = 0) →
      w ∈ liftedCellSquaredRadiusClosure P τ x₀ r := by
  filter_upwards
    [eventually_mem_liftedCellSquaredRadiusClosure_of_equations
      P τ x₀ r hy hstrict] with w hw
  intro hpermanent
  apply hw
  · intro i
    simpa [parameterizedSquareLiftPolynomial,
      MvPolynomial.eval_rename, Function.comp_def] using
      hpermanent
        (Sum.inl i :
          ParameterizedSquareLiftEquation τ)
  · intro i hi
    let j : {i : ι // τ i = 0} := ⟨i, hi⟩
    have hj :=
      hpermanent
        (Sum.inr (Sum.inl j) :
          ParameterizedSquareLiftEquation τ)
    simpa [parameterizedSquareLiftPolynomial, j] using hj
  · have hr :=
      hpermanent
        (Sum.inr (Sum.inr ()) :
          ParameterizedSquareLiftEquation τ)
    have hr' :
        squaredRadius x₀ (fun v => w (Sum.inl v)) - r = 0 := by
      simpa [parameterizedSquareLiftPolynomial] using hr
    exact sub_eq_zero.mp hr'

/--
The compact-selection maximum of the strict-slack score is a genuine local
maximum on the fixed-parameter zero locus of all permanent square-lift
equations.  Thus the first lexicographic objective can be fed directly into
a relative (over the radius parameter) smooth-fiber Fermat or Lagrange
argument.
-/
theorem isLocalMaxOn_strictSlackProduct_sq_parameterizedEquations
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ) (r : ℝ)
    {y : Assignment (σ ⊕ ι)}
    (hy :
      y ∈ liftedCellSquaredRadiusClosure P τ x₀ r)
    (hstrict : strictSlackProduct τ y ≠ 0)
    (hmax :
      ∀ w ∈ liftedCellSquaredRadiusClosure P τ x₀ r,
        strictSlackProduct τ w ^ 2 ≤
          strictSlackProduct τ y ^ 2) :
    IsLocalMaxOn
      (fun w : Assignment (σ ⊕ ι) =>
        strictSlackProduct τ w ^ 2)
      {w |
        ∀ e : ParameterizedSquareLiftEquation τ,
          MvPolynomial.eval
            (parameterizedLiftAssignment r w)
            (parameterizedSquareLiftPolynomial P τ x₀ e) = 0}
      y := by
  change
    ∀ᶠ w in
      𝓝[
        {w |
          ∀ e : ParameterizedSquareLiftEquation τ,
            MvPolynomial.eval
              (parameterizedLiftAssignment r w)
              (parameterizedSquareLiftPolynomial P τ x₀ e) = 0}
      ] y,
      strictSlackProduct τ w ^ 2 ≤
        strictSlackProduct τ y ^ 2
  rw [eventually_nhdsWithin_iff]
  filter_upwards
    [eventually_mem_liftedCellSquaredRadiusClosure_of_parameterizedEquations
      P τ x₀ r hy hstrict] with w hw
  intro hwequations
  exact hmax w (hw hwequations)

/--
Polynomial-radius counterpart of `exists_radial_lexSelected_squareLift`.
This is the version suitable for the prime algebraic germ: the fiber
parameter is the polynomial `squaredRadius`.
-/
theorem exists_squaredRadius_lexSelected_squareLift
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ)
    (ncoord : ℕ)
    (c : Fin ncoord → Assignment (σ ⊕ ι) → ℝ)
    (hc : ∀ k, Continuous (c k))
    {x : Assignment σ} (hx : x ∈ signCell P τ) :
    ∃ (y : Assignment (σ ⊕ ι)) (z : Assignment σ),
      y ∈ liftedCellSquaredRadiusClosure
        P τ x₀ (squaredRadius x₀ x) ∧
      squaredRadius x₀ z = squaredRadius x₀ x ∧
      y = squareLift P τ z ∧
      strictSlackProduct τ y ≠ 0 ∧
      (fun v => y (Sum.inl v)) ∈ signCell P τ ∧
      (∀ w : Assignment (σ ⊕ ι),
        w ∈ liftedCellSquaredRadiusClosure
            P τ x₀ (squaredRadius x₀ x) →
        strictSlackProduct τ w ^ 2 ≤
          strictSlackProduct τ y ^ 2) ∧
      ∀ (k : Fin ncoord) (w : Assignment (σ ⊕ ι)),
        w ∈ liftedCellSquaredRadiusClosure
            P τ x₀ (squaredRadius x₀ x) →
        strictSlackProduct τ w ^ 2 =
            strictSlackProduct τ y ^ 2 →
        (∀ j : Fin ncoord, j < k → c j w = c j y) →
        c k y ≤ c k w := by
  let S :=
    liftedCellSquaredRadiusClosure
      P τ x₀ (squaredRadius x₀ x)
  have hwS : squareLift P τ x ∈ S := by
    apply subset_closure
    exact ⟨x, ⟨hx, rfl⟩, rfl⟩
  obtain ⟨y, hyS, hystrict, hymax, hylex⟩ :=
    Math.CurveSelection.LexSelection.score_ne_zero_of_exists_nonzero_of_lexMinOn_maximizers
      S
      (isCompact_liftedCellSquaredRadiusClosure
        P τ x₀ (squaredRadius x₀ x))
      (strictSlackProduct τ)
      (continuous_strictSlackProduct τ)
      ncoord c hc hwS
      (strictSlackProduct_squareLift_ne_zero P τ hx)
  obtain ⟨z, hzRadius, hyEq⟩ :=
    exists_squareLift_on_squaredRadius_of_mem_closure
      P τ x₀ (squaredRadius x₀ x) hyS
  have hycell :
      (fun v => y (Sum.inl v)) ∈ signCell P τ :=
    project_mem_signCell_of_equations_of_strictSlackProduct_ne_zero
      P τ
      (equations_of_mem_liftedCellSquaredRadiusClosure
        P τ x₀ (squaredRadius x₀ x) hyS)
      hystrict
  exact
    ⟨y, z, hyS, hzRadius, hyEq, hystrict,
      hycell, hymax, hylex⟩

/--
Simultaneous polynomial-radius lexicographic selection along a convergent
sign-cell sequence.  Both the underlying assignments and their square lifts
converge to the prescribed endpoint.
-/
theorem exists_lexSelected_squaredRadius_sequence
    [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    (x₀ : Assignment σ)
    (x : ℕ → Assignment σ)
    (hx : ∀ m, x m ∈ signCell P τ)
    (hxlim : Tendsto x atTop (𝓝 x₀))
    (ncoord : ℕ)
    (c : Fin ncoord → Assignment (σ ⊕ ι) → ℝ)
    (hc : ∀ k, Continuous (c k)) :
    ∃ (y : ℕ → Assignment (σ ⊕ ι))
        (z : ℕ → Assignment σ),
      (∀ m,
        y m ∈ liftedCellSquaredRadiusClosure
          P τ x₀ (squaredRadius x₀ (x m))) ∧
      (∀ m,
        squaredRadius x₀ (z m) =
          squaredRadius x₀ (x m)) ∧
      (∀ m, y m = squareLift P τ (z m)) ∧
      (∀ m, strictSlackProduct τ (y m) ≠ 0) ∧
      (∀ m, (fun v => y m (Sum.inl v)) ∈ signCell P τ) ∧
      Tendsto z atTop (𝓝 x₀) ∧
      Tendsto y atTop (𝓝 (squareLift P τ x₀)) ∧
      (∀ m w,
        w ∈ liftedCellSquaredRadiusClosure
            P τ x₀ (squaredRadius x₀ (x m)) →
        strictSlackProduct τ w ^ 2 ≤
          strictSlackProduct τ (y m) ^ 2) ∧
      ∀ m (k : Fin ncoord) w,
        w ∈ liftedCellSquaredRadiusClosure
            P τ x₀ (squaredRadius x₀ (x m)) →
        strictSlackProduct τ w ^ 2 =
            strictSlackProduct τ (y m) ^ 2 →
        (∀ j : Fin ncoord, j < k → c j w = c j (y m)) →
        c k (y m) ≤ c k w := by
  classical
  choose y z hyS hzRadius hyEq hystrict hycell hymax hylex using
    fun m =>
      exists_squaredRadius_lexSelected_squareLift
        P τ x₀ ncoord c hc (hx m)
  have hradius_lim :
      Tendsto (fun m => squaredRadius x₀ (x m))
        atTop (𝓝 0) := by
    have h :=
      (continuous_squaredRadius x₀).continuousAt.tendsto.comp hxlim
    change
      Tendsto (fun m => squaredRadius x₀ (x m))
        atTop (𝓝 (squaredRadius x₀ x₀)) at h
    simpa using h
  have hsqrt_lim :
      Tendsto (fun m => Real.sqrt (squaredRadius x₀ (x m)))
        atTop (𝓝 0) := by
    have h :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hradius_lim
    change
      Tendsto (fun m => Real.sqrt (squaredRadius x₀ (x m)))
        atTop (𝓝 (Real.sqrt 0)) at h
    simpa using h
  have hzlim : Tendsto z atTop (𝓝 x₀) := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero
      (fun _ => dist_nonneg)
      (fun m => ?_)
      hsqrt_lim
    have hterm :
        (z m v - x₀ v) ^ 2 ≤ squaredRadius x₀ (z m) := by
      unfold squaredRadius
      exact Finset.single_le_sum
        (fun u _hu => sq_nonneg (z m u - x₀ u))
        (Finset.mem_univ v)
    have hr : 0 ≤ squaredRadius x₀ (x m) :=
      squaredRadius_nonneg x₀ (x m)
    have hsq :
        (z m v - x₀ v) ^ 2 ≤
          (Real.sqrt (squaredRadius x₀ (x m))) ^ 2 := by
      rw [Real.sq_sqrt hr, ← hzRadius m]
      exact hterm
    have habs :=
      abs_le_of_sq_le_sq hsq
        (Real.sqrt_nonneg (squaredRadius x₀ (x m)))
    simpa [Real.dist_eq] using habs
  have hylim :
      Tendsto y atTop (𝓝 (squareLift P τ x₀)) := by
    have hlift :
        Tendsto (fun m => squareLift P τ (z m))
          atTop (𝓝 (squareLift P τ x₀)) :=
      (continuous_squareLift P τ).continuousAt.tendsto.comp hzlim
    exact hlift.congr'
      (Filter.Eventually.of_forall fun m => (hyEq m).symm)
  exact
    ⟨y, z, hyS, hzRadius, hyEq, hystrict, hycell,
      hzlim, hylim, hymax, hylex⟩

/-- Closure lifts continuously: no strict inequality is lost by first
passing to the canonical square-slack graph. -/
theorem squareLift_mem_closure_image
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    {A : Set (Assignment σ)} {x₀ : Assignment σ}
    (hx₀ : x₀ ∈ closure A) :
    squareLift P τ x₀ ∈ closure (squareLift P τ '' A) :=
  mem_closure_image (continuous_squareLift P τ).continuousAt hx₀

theorem squareLift_mem_closure_squareLiftCell
    (P : ι → MvPolynomial σ ℝ) (τ : SignPattern ι)
    {x₀ : Assignment σ}
    (hx₀ : x₀ ∈ closure (signCell P τ)) :
    squareLift P τ x₀ ∈ closure (squareLiftCell P τ) := by
  apply closure_mono ?_
    (squareLift_mem_closure_image P τ hx₀)
  rintro y ⟨x, hx, rfl⟩
  exact squareLift_mem_squareLiftCell P τ hx

/-- Forget the square-slack coordinates as a continuous linear map. -/
def leftProjection [Fintype σ] [Fintype ι] :
    Assignment (σ ⊕ ι) →L[ℝ] Assignment σ :=
  ContinuousLinearMap.pi fun v =>
    (ContinuousLinearMap.proj (R := ℝ) (Sum.inl v) :
      Assignment (σ ⊕ ι) →L[ℝ] ℝ)

@[simp]
theorem leftProjection_apply [Fintype σ] [Fintype ι]
    (y : Assignment (σ ⊕ ι)) (v : σ) :
    leftProjection y v = y (Sum.inl v) :=
  rfl

/-- Pull an original distinguished coordinate back to the square lift. -/
def liftedCoordinate [Fintype σ] [Fintype ι]
    (coordinate : Assignment σ →L[ℝ] ℝ) :
    Assignment (σ ⊕ ι) →L[ℝ] ℝ :=
  coordinate.comp leftProjection

@[simp]
theorem liftedCoordinate_apply [Fintype σ] [Fintype ι]
    (coordinate : Assignment σ →L[ℝ] ℝ)
    (y : Assignment (σ ⊕ ι)) :
    liftedCoordinate coordinate y =
      coordinate (fun v => y (Sum.inl v)) :=
  rfl

/--
An analytic ramified branch of the square-lift locus which returns
arbitrarily close through the chosen lifted cell projects to the exact
analytic power curve in the original sign cell.

Thus the remaining selection theorem may work purely with polynomial
equations; positivity of all original constraints is recovered after
projection by analytic sign stabilization.
-/
theorem hasAnalyticPowerCurveAt_of_frequent_squareLift_branch
    [Finite ι] [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : Assignment σ →L[ℝ] ℝ)
    (x₀ : Assignment σ)
    (q : ℕ)
    (γ : ℝ → Assignment (σ ⊕ ι))
    (hq : 0 < q)
    (hγ : AnalyticAt ℝ γ 0)
    (hγ0 : γ 0 = squareLift P τ x₀)
    (hfrequent :
      ∃ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ squareLiftCell P τ)
    (hpower :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        liftedCoordinate coordinate (γ t) = t ^ q) :
    HasAnalyticPowerCurveAt (signCell P τ) coordinate x₀ := by
  let δ : ℝ → Assignment σ := fun t => leftProjection (γ t)
  have hδ : AnalyticAt ℝ δ 0 := by
    change AnalyticAt ℝ (leftProjection ∘ γ) 0
    exact (leftProjection.analyticAt (γ 0)).comp hγ
  have hδ0 : δ 0 = x₀ := by
    funext v
    simp [δ, hγ0, squareLift]
  have hfrequent_projected :
      ∃ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        δ t ∈ signCell P τ := by
    apply hfrequent.mono
    intro t ht
    exact project_mem_signCell_of_mem_squareLiftCell P τ ht
  have hpower_projected :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        coordinate (δ t) = t ^ q := by
    simpa [δ, liftedCoordinate] using hpower
  have hδ_coordinate :
      ∀ v, AnalyticAt ℝ (fun t => δ t v) 0 := by
    have hδ' := hδ
    rw [analyticAt_pi_iff] at hδ'
    exact hδ'
  have hcell :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        δ t ∈ signCell P τ :=
    eventually_mem_signCell_of_analyticAt_of_frequently
      P τ δ hδ_coordinate hfrequent_projected
  have hgood :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        δ t ∈ signCell P τ ∧ coordinate (δ t) = t ^ q :=
    hcell.and hpower_projected
  obtain ⟨eta, heta, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  exact
    ⟨q, δ, eta, hq, heta, hδ, hδ0,
      fun t ht => hinterval ht⟩

end CurveSelection.SquareLiftScratch
end Math
