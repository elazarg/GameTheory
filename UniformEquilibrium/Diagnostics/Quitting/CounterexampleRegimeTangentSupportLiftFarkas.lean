/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AffineEqualityFarkas
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacketEnergy
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine

/-!
# Frozen product-root continuation lifts and Farkas certificates

An active-positive tangent packet identifies a boundary target and suggests
enlarging the support of a one-stage product root.  Choosing the simultaneous
quit probabilities is genuinely nonlinear: coalition masses and Boolean
Möbius derivatives contain products of the other owners' probabilities.
Consequently the quit probabilities are parameters here, not variables of a
spurious linear program.

Once one product root and its intended interior support are frozen, the
remaining continuation problem is exactly affine.  For joint Continue mass
`q`, opponent Continue mass `q_{-i}`, and continuation `w`, its rows are

* Bellman: `q * w_i + absorbing_i - target_i = 0`;
* mixing owner: `q_{-i} * w_i + excluded_i - sigma_i = 0`;
* pure continuer: the same residual is nonnegative;
* floor: `w_i - floor_i >= 0`;
* upper box: `upper - w_i >= 0`.

The `sigma` and `excluded` coefficients contain the actual full coalition
reward table.  The Boolean Möbius adapter identifies their difference with
the full coordinate derivative, including pair and higher collision terms.
One homogeneous coordinate fixed to one puts all of these affine clauses in
the `AffineEqualityFarkas` format.

The theorem of the alternative is pointwise in the supplied root.  Its
feasible branch decodes an exact Bellman equation, zero Möbius derivatives on
the declared support, nonpositive derivatives off support, and the requested
continuation bounds.  With an explicit interior-support/zero-pattern proof it
also gives an actual `IsQuittingNashBellmanEdge`.  Its other branch gives
finite decoded Farkas multipliers and states that no continuation lift exists
for this root.

No theorem here searches over quit probabilities, produces a support
extension, or shows that a dual certificate contradicts the tangent packet.
A uniform certificate for the simultaneous nonlinear root search would need
additional semialgebraic or monomial-consistency machinery.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset
open Math.LinearAlgebra
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Equality rows: homogenizing constant, Bellman equations, and mixing-owner
indifference equations. -/
abbrev QuittingFrozenRootLiftEqRow (ι : Type) [Fintype ι]
    (support : Finset ι) :=
  Unit ⊕ (ι ⊕ {who : ι // who ∈ support})

/-- Inequality rows: pure-continuing Nash signs, continuation floors, and
continuation upper bounds. -/
abbrev QuittingFrozenRootLiftIneqRow (ι : Type) [Fintype ι]
    (support : Finset ι) :=
  {who : ι // who ∉ support} ⊕ (ι ⊕ ι)

/-- A homogeneous coordinate is adjoined to the continuation vector. -/
abbrev QuittingFrozenRootLiftColumn (ι : Type) [Fintype ι] := Option ι

/-- Kronecker coefficient of one augmented continuation coordinate. -/
def quittingFrozenRootLiftUnitCoeff
    (coordinate : Option ι) (column : Option ι) : ℝ :=
  if column = coordinate then 1 else 0

/-- Sparse equality coefficients before reindexing columns by `Fin`. -/
def quittingFrozenRootLiftEqCoeff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (root : ι → PMF Bool) (support : Finset ι) :
    QuittingFrozenRootLiftEqRow ι support → Option ι → ℝ
  | Sum.inl _, column => quittingFrozenRootLiftUnitCoeff none column
  | Sum.inr (Sum.inl who), column =>
      quittingStationaryContinueMass root *
          quittingFrozenRootLiftUnitCoeff (some who) column +
        (quittingRootAbsorbingContribution reward root who - target who) *
          quittingFrozenRootLiftUnitCoeff none column
  | Sum.inr (Sum.inr who), column =>
      continueMassExcl (hazardOfRoot root) who *
          quittingFrozenRootLiftUnitCoeff (some (who : ι)) column +
        (excludedValue (weightOfReward reward) (hazardOfRoot root) who -
          sigmaValue (weightOfReward reward) (hazardOfRoot root) who) *
            quittingFrozenRootLiftUnitCoeff none column

/-- Sparse inequality coefficients before reindexing columns by `Fin`. -/
def quittingFrozenRootLiftIneqCoeff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι) :
    QuittingFrozenRootLiftIneqRow ι support → Option ι → ℝ
  | Sum.inl who, column =>
      continueMassExcl (hazardOfRoot root) who *
          quittingFrozenRootLiftUnitCoeff (some (who : ι)) column +
        (excludedValue (weightOfReward reward) (hazardOfRoot root) who -
          sigmaValue (weightOfReward reward) (hazardOfRoot root) who) *
            quittingFrozenRootLiftUnitCoeff none column
  | Sum.inr (Sum.inl who), column =>
      quittingFrozenRootLiftUnitCoeff (some who) column -
        floor who * quittingFrozenRootLiftUnitCoeff none column
  | Sum.inr (Sum.inr who), column =>
      upper * quittingFrozenRootLiftUnitCoeff none column -
        quittingFrozenRootLiftUnitCoeff (some who) column

/-- Equality matrix in the finite-column format consumed by affine Farkas. -/
def quittingFrozenRootLiftA
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (root : ι → PMF Bool) (support : Finset ι) :
    QuittingFrozenRootLiftEqRow ι support →
      Fin (Fintype.card (Option ι)) → ℝ :=
  fun row column => quittingFrozenRootLiftEqCoeff reward target root support row
    ((Fintype.equivFin (Option ι)).symm column)

/-- Only the homogenizing row has a nonzero equality right-hand side. -/
def quittingFrozenRootLiftB (support : Finset ι) :
    QuittingFrozenRootLiftEqRow ι support → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- Inequality matrix in the finite-column format consumed by affine Farkas. -/
def quittingFrozenRootLiftG
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι) :
    QuittingFrozenRootLiftIneqRow ι support →
      Fin (Fintype.card (Option ι)) → ℝ :=
  fun row column => quittingFrozenRootLiftIneqCoeff reward floor upper root support row
    ((Fintype.equivFin (Option ι)).symm column)

/-- Decode the physical continuation coordinates of an augmented vector. -/
def quittingFrozenRootLiftContinuation
    (h : Fin (Fintype.card (Option ι)) → ℝ) : Payoff ι :=
  fun who => h (Fintype.equivFin (Option ι) (some who))

/-- Encode a continuation together with homogeneous coordinate one. -/
def quittingFrozenRootLiftVector (continuation : Payoff ι) :
    Fin (Fintype.card (Option ι)) → ℝ :=
  fun column => match (Fintype.equivFin (Option ι)).symm column with
    | none => 1
    | some who => continuation who

omit [DecidableEq ι] in
@[simp]
theorem quittingFrozenRootLiftContinuation_vector
    (continuation : Payoff ι) :
    quittingFrozenRootLiftContinuation
      (quittingFrozenRootLiftVector continuation) = continuation := by
  funext who
  simp [quittingFrozenRootLiftContinuation, quittingFrozenRootLiftVector]

omit [DecidableEq ι] in
private theorem quittingFrozenRootLift_sum_reindex
    (C : Option ι → ℝ) (h : Fin (Fintype.card (Option ι)) → ℝ) :
    (∑ column, C ((Fintype.equivFin (Option ι)).symm column) * h column) =
      ∑ coordinate : Option ι,
        C coordinate * h (Fintype.equivFin (Option ι) coordinate) := by
  let e := Fintype.equivFin (Option ι)
  simpa [e] using
    (e.sum_comp (fun column => C (e.symm column) * h column)).symm

private theorem quittingFrozenRootLift_sum_unitCoeff
    (coordinate : Option ι)
    (h : Fin (Fintype.card (Option ι)) → ℝ) :
    (∑ column,
      quittingFrozenRootLiftUnitCoeff coordinate
          ((Fintype.equivFin (Option ι)).symm column) * h column) =
      h (Fintype.equivFin (Option ι) coordinate) := by
  rw [quittingFrozenRootLift_sum_reindex]
  simp [quittingFrozenRootLiftUnitCoeff]

theorem quittingFrozenRootLiftA_constant_row
    (target : Payoff ι) (root : ι → PMF Bool) (support : Finset ι)
    (h : Fin (Fintype.card (Option ι)) → ℝ) :
    (∑ column, quittingFrozenRootLiftA reward target root support
        (Sum.inl ()) column * h column) =
      h (Fintype.equivFin (Option ι) none) := by
  simpa [quittingFrozenRootLiftA, quittingFrozenRootLiftEqCoeff] using
    quittingFrozenRootLift_sum_unitCoeff (ι := ι) none h

theorem quittingFrozenRootLiftA_bellman_row
    (target : Payoff ι) (root : ι → PMF Bool) (support : Finset ι)
    (h : Fin (Fintype.card (Option ι)) → ℝ) (who : ι) :
    (∑ column, quittingFrozenRootLiftA reward target root support
        (Sum.inr (Sum.inl who)) column * h column) =
      quittingStationaryContinueMass root *
          quittingFrozenRootLiftContinuation h who +
        (quittingRootAbsorbingContribution reward root who - target who) *
          h (Fintype.equivFin (Option ι) none) := by
  simp only [quittingFrozenRootLiftA, quittingFrozenRootLiftEqCoeff,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [quittingFrozenRootLift_sum_unitCoeff,
    quittingFrozenRootLift_sum_unitCoeff]
  rfl

theorem quittingFrozenRootLiftA_mixing_row
    (target : Payoff ι) (root : ι → PMF Bool) (support : Finset ι)
    (h : Fin (Fintype.card (Option ι)) → ℝ)
    (who : {who : ι // who ∈ support}) :
    (∑ column, quittingFrozenRootLiftA reward target root support
        (Sum.inr (Sum.inr who)) column * h column) =
      continueMassExcl (hazardOfRoot root) who *
          quittingFrozenRootLiftContinuation h who +
        (excludedValue (weightOfReward reward) (hazardOfRoot root) who -
          sigmaValue (weightOfReward reward) (hazardOfRoot root) who) *
            h (Fintype.equivFin (Option ι) none) := by
  simp only [quittingFrozenRootLiftA, quittingFrozenRootLiftEqCoeff,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [quittingFrozenRootLift_sum_unitCoeff,
    quittingFrozenRootLift_sum_unitCoeff]
  rfl

theorem quittingFrozenRootLiftG_continuing_row
    (floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι)
    (h : Fin (Fintype.card (Option ι)) → ℝ)
    (who : {who : ι // who ∉ support}) :
    (∑ column, quittingFrozenRootLiftG reward floor upper root support
        (Sum.inl who) column * h column) =
      continueMassExcl (hazardOfRoot root) who *
          quittingFrozenRootLiftContinuation h who +
        (excludedValue (weightOfReward reward) (hazardOfRoot root) who -
          sigmaValue (weightOfReward reward) (hazardOfRoot root) who) *
            h (Fintype.equivFin (Option ι) none) := by
  simp only [quittingFrozenRootLiftG, quittingFrozenRootLiftIneqCoeff,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [quittingFrozenRootLift_sum_unitCoeff,
    quittingFrozenRootLift_sum_unitCoeff]
  rfl

theorem quittingFrozenRootLiftG_floor_row
    (floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι)
    (h : Fin (Fintype.card (Option ι)) → ℝ) (who : ι) :
    (∑ column, quittingFrozenRootLiftG reward floor upper root support
        (Sum.inr (Sum.inl who)) column * h column) =
      quittingFrozenRootLiftContinuation h who -
        floor who * h (Fintype.equivFin (Option ι) none) := by
  simp only [quittingFrozenRootLiftG, quittingFrozenRootLiftIneqCoeff,
    sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [quittingFrozenRootLift_sum_unitCoeff,
    quittingFrozenRootLift_sum_unitCoeff]
  rfl

theorem quittingFrozenRootLiftG_upper_row
    (floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι)
    (h : Fin (Fintype.card (Option ι)) → ℝ) (who : ι) :
    (∑ column, quittingFrozenRootLiftG reward floor upper root support
        (Sum.inr (Sum.inr who)) column * h column) =
      upper * h (Fintype.equivFin (Option ι) none) -
        quittingFrozenRootLiftContinuation h who := by
  simp only [quittingFrozenRootLiftG, quittingFrozenRootLiftIneqCoeff,
    sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [quittingFrozenRootLift_sum_unitCoeff,
    quittingFrozenRootLift_sum_unitCoeff]
  rfl

/-! ## Physical continuation semantics -/

/-- A continuation which lifts a frozen product root to the prescribed
current target.  The Boolean Möbius derivative retains all collision and
higher-coalition rewards. -/
def IsQuittingFrozenRootContinuationLift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι) (continuation : Payoff ι) : Prop :=
  target = quittingRootSuccessorPayoff reward continuation root ∧
    (∀ who ∈ support,
      (quittingStageCenteredCoalGame reward continuation who).coordinateDerivative
        (hazardOfRoot root) who = 0) ∧
    (∀ who ∉ support,
      (quittingStageCenteredCoalGame reward continuation who).coordinateDerivative
        (hazardOfRoot root) who ≤ 0) ∧
    (∀ who, floor who ≤ continuation who) ∧
    ∀ who, continuation who ≤ upper

/-- The concrete frozen-root affine system. -/
def IsQuittingFrozenRootLiftAffineFeasible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι) : Prop :=
  IsAffineEqualityInequalityFeasible
    (𝕜 := ℝ)
    (EqRow := QuittingFrozenRootLiftEqRow ι support)
    (IneqRow := QuittingFrozenRootLiftIneqRow ι support)
    (n := Fintype.card (Option ι))
    (quittingFrozenRootLiftA reward target root support)
    (quittingFrozenRootLiftB support)
    (quittingFrozenRootLiftG reward floor upper root support)

/-- The decoded dual certificate for failure of the frozen-root continuation
lift. -/
def IsQuittingFrozenRootLiftFarkasCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι)
    (y : QuittingFrozenRootLiftEqRow ι support → ℝ)
    (lambda : QuittingFrozenRootLiftIneqRow ι support → ℝ) : Prop :=
  IsAffineEqualityFarkasCertificate
    (𝕜 := ℝ)
    (EqRow := QuittingFrozenRootLiftEqRow ι support)
    (IneqRow := QuittingFrozenRootLiftIneqRow ι support)
    (n := Fintype.card (Option ι))
    (quittingFrozenRootLiftA reward target root support)
    (quittingFrozenRootLiftB support)
    (quittingFrozenRootLiftG reward floor upper root support) y lambda

/-- Every feasible augmented affine vector decodes to the exact Bellman,
Möbius-derivative, floor, and upper-box conditions. -/
theorem exists_continuationLift_of_affineFeasible
    (target floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι)
    (hfeasible : IsQuittingFrozenRootLiftAffineFeasible
      reward target floor upper root support) :
    ∃ continuation, IsQuittingFrozenRootContinuationLift
      reward target floor upper root support continuation := by
  rcases hfeasible with ⟨h, heq, hineq⟩
  let continuation := quittingFrozenRootLiftContinuation h
  have hconstant : h (Fintype.equivFin (Option ι) none) = 1 := by
    have hrow := heq (Sum.inl ())
    rw [quittingFrozenRootLiftA_constant_row] at hrow
    simpa [quittingFrozenRootLiftB] using hrow
  refine ⟨continuation, ?_, ?_, ?_, ?_, ?_⟩
  · funext who
    have hrow := heq (Sum.inr (Sum.inl who))
    rw [quittingFrozenRootLiftA_bellman_row, hconstant, mul_one] at hrow
    simp only [quittingFrozenRootLiftB] at hrow
    rw [quittingRootSuccessorPayoff_apply_eq_affine]
    change target who = _
    linarith
  · intro who hwho
    let owner : {who : ι // who ∈ support} := ⟨who, hwho⟩
    have hrow := heq (Sum.inr (Sum.inr owner))
    rw [quittingFrozenRootLiftA_mixing_row, hconstant, mul_one] at hrow
    simp only [quittingFrozenRootLiftB] at hrow
    rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative,
      quittingRootEndpointDifference_eq_gainValue]
    unfold gainValue gammaValue
    change continueMassExcl (hazardOfRoot root) who * continuation who +
      (excludedValue (weightOfReward reward) (hazardOfRoot root) who -
        sigmaValue (weightOfReward reward) (hazardOfRoot root) who) = 0 at hrow
    linarith
  · intro who hwho
    let owner : {who : ι // who ∉ support} := ⟨who, hwho⟩
    have hrow := hineq (Sum.inl owner)
    rw [quittingFrozenRootLiftG_continuing_row, hconstant, mul_one] at hrow
    rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative,
      quittingRootEndpointDifference_eq_gainValue]
    unfold gainValue gammaValue
    change 0 ≤ continueMassExcl (hazardOfRoot root) who * continuation who +
      (excludedValue (weightOfReward reward) (hazardOfRoot root) who -
        sigmaValue (weightOfReward reward) (hazardOfRoot root) who) at hrow
    linarith
  · intro who
    have hrow := hineq (Sum.inr (Sum.inl who))
    rw [quittingFrozenRootLiftG_floor_row, hconstant, mul_one] at hrow
    exact sub_nonneg.mp hrow
  · intro who
    have hrow := hineq (Sum.inr (Sum.inr who))
    rw [quittingFrozenRootLiftG_upper_row, hconstant, mul_one] at hrow
    linarith

/-- **Frozen-root continuation-lift alternative.**  For one supplied product
root and one supplied support, either a physical continuation satisfies the
exact game-facing system, or explicit finite Farkas multipliers certify that
no such continuation exists.  The quit probabilities themselves are not LP
variables. -/
theorem quittingFrozenRootContinuationLift_or_farkas
    (target floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι) :
    (∃ continuation, IsQuittingFrozenRootContinuationLift
      reward target floor upper root support continuation) ∨
    ((¬ ∃ continuation, IsQuittingFrozenRootContinuationLift
      reward target floor upper root support continuation) ∧
      ∃ y : QuittingFrozenRootLiftEqRow ι support → ℝ,
        ∃ lambda : QuittingFrozenRootLiftIneqRow ι support → ℝ,
          IsQuittingFrozenRootLiftFarkasCertificate
            reward target floor upper root support y lambda) := by
  by_cases hlift : ∃ continuation, IsQuittingFrozenRootContinuationLift
      reward target floor upper root support continuation
  · exact Or.inl hlift
  · right
    refine ⟨hlift, ?_⟩
    apply exists_affineEqualityFarkasCertificate_of_not_feasible
    intro hfeasible
    exact hlift (exists_continuationLift_of_affineFeasible
      target floor upper root support hfeasible)

/-! ## Exact-edge decoding -/

/-- The frozen root mixes strictly on the declared support and never quits
off it. -/
def IsQuittingRootInteriorOnSupport
    (root : ι → PMF Bool) (support : Finset ι) : Prop :=
  (∀ who ∈ support,
    0 < hazardOfRoot root who ∧ hazardOfRoot root who < 1) ∧
  ∀ who ∉ support, hazardOfRoot root who = 0

/-- Simplex coordinates of a supplied product root. -/
def quittingFrozenRootLiftSimplex (root : ι → PMF Bool) :
    QuittingRootSimplex ι :=
  fun who => stdSimplexEquiv (root who)

omit [DecidableEq ι] in
@[simp]
theorem quittingRootOfSimplex_frozenRootLiftSimplex
    (root : ι → PMF Bool) :
    quittingRootOfSimplex (quittingFrozenRootLiftSimplex root) = root := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)

/-- A decoded physical lift is an actual exact Nash--Bellman edge whenever
the frozen root has precisely the declared interior support.  The tail
simplex coordinate is arbitrary because an edge reads only its payoff. -/
theorem isQuittingNashBellmanEdge_of_frozenRootContinuationLift
    (target floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι) (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift
      reward target floor upper root support continuation)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (tailRoot : QuittingRootSimplex ι) :
    IsQuittingNashBellmanEdge reward
      (target, quittingFrozenRootLiftSimplex root)
      (continuation, tailRoot) := by
  constructor
  · simpa using hlift.1
  · intro who
    rw [quittingRootOfSimplex_frozenRootLiftSimplex]
    by_cases hwho : who ∈ support
    · have hderivative := hlift.2.1 who hwho
      rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative]
        at hderivative
      simp [hderivative]
    · have hderivative := hlift.2.2.1 who hwho
      rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative]
        at hderivative
      have hzero : (root who true).toReal = 0 := by
        exact hsupport.2 who hwho
      constructor
      · exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hderivative
      · simp [hzero]

/-- **Frozen-root exact-edge-or-Farkas alternative.**  Under an explicit
interior-support/zero-pattern hypothesis, the physical side of the affine
alternative already carries the corresponding exact Nash--Bellman edge.
The dual side still separates only this supplied root's continuation system. -/
theorem quittingFrozenRootNashBellmanEdge_or_farkas
    (target floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι) (hsupport : IsQuittingRootInteriorOnSupport root support)
    (tailRoot : QuittingRootSimplex ι) :
    (∃ continuation,
      IsQuittingFrozenRootContinuationLift
          reward target floor upper root support continuation ∧
        IsQuittingNashBellmanEdge reward
          (target, quittingFrozenRootLiftSimplex root)
          (continuation, tailRoot)) ∨
    ((¬ ∃ continuation, IsQuittingFrozenRootContinuationLift
      reward target floor upper root support continuation) ∧
      ∃ y : QuittingFrozenRootLiftEqRow ι support → ℝ,
        ∃ lambda : QuittingFrozenRootLiftIneqRow ι support → ℝ,
          IsQuittingFrozenRootLiftFarkasCertificate
            reward target floor upper root support y lambda) := by
  rcases quittingFrozenRootContinuationLift_or_farkas
      target floor upper root support with hlift | hfarkas
  · left
    rcases hlift with ⟨continuation, hcontinuation⟩
    exact ⟨continuation, hcontinuation,
      isQuittingNashBellmanEdge_of_frozenRootContinuationLift
        target floor upper root support continuation hcontinuation
          hsupport tailRoot⟩
  · exact Or.inr hfarkas

namespace QuittingChargeTangentPacket

/-- The frozen-root alternative at the canonical target, behavioral floor,
and payoff-box upper bound supplied by a charge-tangent packet.  Active
positivity selects this lane but is not needed by the pointwise affine
alternative itself. -/
theorem frozenRootContinuationLift_or_farkas
    (packet : QuittingChargeTangentPacket reward)
    (root : ι → PMF Bool) (support : Finset ι) :
    (∃ continuation, IsQuittingFrozenRootContinuationLift
      reward packet.boundary (quittingPunishmentValue reward)
        (quittingRewardBound reward) root support continuation) ∨
    ((¬ ∃ continuation, IsQuittingFrozenRootContinuationLift
      reward packet.boundary (quittingPunishmentValue reward)
        (quittingRewardBound reward) root support continuation) ∧
      ∃ y : QuittingFrozenRootLiftEqRow ι support → ℝ,
        ∃ lambda : QuittingFrozenRootLiftIneqRow ι support → ℝ,
          IsQuittingFrozenRootLiftFarkasCertificate
            reward packet.boundary (quittingPunishmentValue reward)
              (quittingRewardBound reward) root support y lambda) :=
  quittingFrozenRootContinuationLift_or_farkas
    packet.boundary (quittingPunishmentValue reward)
      (quittingRewardBound reward) root support

end QuittingChargeTangentPacket

end GameTheory
