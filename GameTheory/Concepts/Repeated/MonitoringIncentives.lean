/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import GameTheory.Concepts.Repeated.MonitoringRankInstances

/-!
# Incentive-Effect Linear Maps for Public Monitoring

Continuation transfers are mapped to their effects on pure unilateral
deviation incentives. Pure individual and pairwise full rank are exactly the
surjectivity conditions for these maps.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace KernelGame
namespace PublicMonitoring

variable {iota : Type} {G : KernelGame iota}

/-- Map a signal-contingent continuation transfer to its effect on every
nontrivial pure deviation of one player. -/
noncomputable def pureIndividualIncentiveEffectMap
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (who : iota) :
    (M.Signal → ℝ) →ₗ[ℝ] (NontrivialDeviation a who → ℝ) :=
  (M.pureDeviationSignalMatrix a who).mulVecLin

@[simp]
theorem pureIndividualIncentiveEffectMap_apply
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (who : iota) (z : M.Signal → ℝ)
    (dev : NontrivialDeviation a who) :
    M.pureIndividualIncentiveEffectMap a who z dev =
      ∑ y, M.pureDeviationSignalMatrix a who dev y * z y := by
  simp only [pureIndividualIncentiveEffectMap]
  apply Finset.sum_congr
  · ext x
    simp
  intro x _
  rfl

/-- Map a signal-contingent continuation transfer to its simultaneous effects
on the combined pure deviations of two players. -/
noncomputable def purePairwiseIncentiveEffectMap
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (i j : iota) :
    (M.Signal → ℝ) →ₗ[ℝ]
      (NontrivialDeviation a i ⊕ NontrivialDeviation a j → ℝ) :=
  (M.purePairwiseDeviationSignalFamily a i j).mulVecLin

@[simp]
theorem purePairwiseIncentiveEffectMap_apply
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (i j : iota) (z : M.Signal → ℝ)
    (dev : NontrivialDeviation a i ⊕ NontrivialDeviation a j) :
    M.purePairwiseIncentiveEffectMap a i j z dev =
      ∑ y, M.purePairwiseDeviationSignalFamily a i j dev y * z y := by
  simp only [purePairwiseIncentiveEffectMap]
  apply Finset.sum_congr
  · ext x
    simp
  intro x _
  rfl

/-- Constant continuation transfers have no effect on one player's
deviation incentives because every deviation row has coordinate sum zero. -/
@[simp]
theorem pureIndividualIncentiveEffectMap_const
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (who : iota) (c : ℝ) :
    M.pureIndividualIncentiveEffectMap a who (fun _ => c) = 0 := by
  funext dev
  rw [M.pureIndividualIncentiveEffectMap_apply]
  have hsum : ∑ y, M.pureDeviationSignalMatrix a who dev y = 0 :=
    M.sum_deviationSignalVector_eq_zero
      (G.pureMixedProfile a) who (PMF.pure dev.1)
  rw [← Finset.sum_mul, hsum, zero_mul]
  rfl

/-- Adding a constant to every signal-contingent transfer leaves individual
incentive effects unchanged. -/
theorem pureIndividualIncentiveEffectMap_add_const
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (who : iota) (z : M.Signal → ℝ) (c : ℝ) :
    M.pureIndividualIncentiveEffectMap a who (fun y => z y + c) =
      M.pureIndividualIncentiveEffectMap a who z := by
  change M.pureIndividualIncentiveEffectMap a who (z + fun _ => c) = _
  rw [map_add, M.pureIndividualIncentiveEffectMap_const, add_zero]

/-- Constant continuation transfers likewise have no simultaneous pairwise
incentive effect. -/
@[simp]
theorem purePairwiseIncentiveEffectMap_const
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (i j : iota) (c : ℝ) :
    M.purePairwiseIncentiveEffectMap a i j (fun _ => c) = 0 := by
  funext dev
  rw [M.purePairwiseIncentiveEffectMap_apply]
  have hsum : ∑ y,
      M.purePairwiseDeviationSignalFamily a i j dev y = 0 := by
    cases dev with
    | inl dev =>
        exact M.sum_deviationSignalVector_eq_zero
          (G.pureMixedProfile a) i (PMF.pure dev.1)
    | inr dev =>
        exact M.sum_deviationSignalVector_eq_zero
          (G.pureMixedProfile a) j (PMF.pure dev.1)
  rw [← Finset.sum_mul, hsum, zero_mul]
  rfl

/-- Adding a constant to every signal-contingent transfer leaves simultaneous
pairwise incentive effects unchanged. -/
theorem purePairwiseIncentiveEffectMap_add_const
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (i j : iota) (z : M.Signal → ℝ) (c : ℝ) :
    M.purePairwiseIncentiveEffectMap a i j (fun y => z y + c) =
      M.purePairwiseIncentiveEffectMap a i j z := by
  change M.purePairwiseIncentiveEffectMap a i j (z + fun _ => c) = _
  rw [map_add, M.purePairwiseIncentiveEffectMap_const, add_zero]

/-- Pure individual full rank is equivalent to the ability to prescribe an
arbitrary vector of pure-deviation incentive effects. -/
theorem pureIndividualIncentiveEffectMap_surjective_iff
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (who : iota)
    [Finite (NontrivialDeviation a who)] :
    Function.Surjective (M.pureIndividualIncentiveEffectMap a who) ↔
      M.PureIndividualFullRank a who := by
  letI := Fintype.ofFinite (NontrivialDeviation a who)
  let A : Matrix (NontrivialDeviation a who) M.Signal ℝ :=
    M.pureDeviationSignalMatrix a who
  change Function.Surjective A.mulVecLin ↔ LinearIndependent ℝ A
  constructor
  · intro hsurj
    have hrange : LinearMap.range A.mulVecLin = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (NontrivialDeviation a who) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.row))
    rw [← Matrix.rank_eq_finrank_span_row]
    rw [Matrix.rank, hrange, finrank_top,
      Module.finrank_fintype_fun_eq_card]
  · intro hli
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    dsimp [A] at hli ⊢
    have hrank : Module.finrank ℝ
        (LinearMap.range
          (M.pureDeviationSignalMatrix a who).mulVecLin) =
        Fintype.card (NontrivialDeviation a who) := by
      have hrankMatrix : (M.pureDeviationSignalMatrix a who).rank =
          Fintype.card (NontrivialDeviation a who) := hli.rank_matrix
      simpa only [Matrix.rank] using hrankMatrix
    rw [hrank, Module.finrank_fintype_fun_eq_card]

/-- Pure pairwise full rank is equivalent to the ability to prescribe an
arbitrary simultaneous vector of both players' pure-deviation effects. -/
theorem purePairwiseIncentiveEffectMap_surjective_iff
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (i j : iota)
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)] :
    Function.Surjective (M.purePairwiseIncentiveEffectMap a i j) ↔
      M.PurePairwiseFullRank a i j := by
  letI := Fintype.ofFinite (NontrivialDeviation a i)
  letI := Fintype.ofFinite (NontrivialDeviation a j)
  let A : Matrix (NontrivialDeviation a i ⊕ NontrivialDeviation a j)
      M.Signal ℝ := M.purePairwiseDeviationSignalFamily a i j
  change Function.Surjective A.mulVecLin ↔ LinearIndependent ℝ A
  constructor
  · intro hsurj
    have hrange : LinearMap.range A.mulVecLin = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card
        (NontrivialDeviation a i ⊕ NontrivialDeviation a j) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.row))
    rw [← Matrix.rank_eq_finrank_span_row]
    rw [Matrix.rank, hrange, finrank_top,
      Module.finrank_fintype_fun_eq_card]
  · intro hli
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    dsimp [A] at hli ⊢
    have hrank : Module.finrank ℝ
        (LinearMap.range
          (M.purePairwiseDeviationSignalFamily a i j).mulVecLin) =
        Fintype.card
          (NontrivialDeviation a i ⊕ NontrivialDeviation a j) := by
      have hrankMatrix :
          (M.purePairwiseDeviationSignalFamily a i j).rank =
            Fintype.card
              (NontrivialDeviation a i ⊕ NontrivialDeviation a j) :=
        hli.rank_matrix
      simpa only [Matrix.rank] using hrankMatrix
    rw [hrank, Module.finrank_fintype_fun_eq_card]

/-- Individual full rank supplies a linear right inverse selecting a
continuation transfer for every desired vector of incentive effects. -/
theorem PureIndividualFullRank.exists_incentiveEffect_rightInverse
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G} {who : iota}
    [Finite (NontrivialDeviation a who)]
    (h : M.PureIndividualFullRank a who) :
    ∃ R : (NontrivialDeviation a who → ℝ) →ₗ[ℝ] (M.Signal → ℝ),
      (M.pureIndividualIncentiveEffectMap a who).comp R = LinearMap.id := by
  letI := Fintype.ofFinite (NontrivialDeviation a who)
  exact (M.pureIndividualIncentiveEffectMap a who).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr
      ((M.pureIndividualIncentiveEffectMap_surjective_iff a who).2 h))

/-- Pairwise full rank supplies a linear right inverse selecting one public
continuation transfer for arbitrary simultaneous effects on both players. -/
theorem PurePairwiseFullRank.exists_incentiveEffect_rightInverse
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G} {i j : iota}
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)]
    (h : M.PurePairwiseFullRank a i j) :
    ∃ R :
        (NontrivialDeviation a i ⊕ NontrivialDeviation a j → ℝ) →ₗ[ℝ]
          (M.Signal → ℝ),
      (M.purePairwiseIncentiveEffectMap a i j).comp R = LinearMap.id := by
  letI := Fintype.ofFinite (NontrivialDeviation a i)
  letI := Fintype.ofFinite (NontrivialDeviation a j)
  exact (M.purePairwiseIncentiveEffectMap a i j).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr
      ((M.purePairwiseIncentiveEffectMap_surjective_iff a i j).2 h))

/-- In finite coordinates, an individual-rank right inverse can be chosen with
a finite operator-norm bound. -/
theorem PureIndividualFullRank.exists_bounded_incentiveEffect_rightInverse
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G} {who : iota}
    [Fintype (NontrivialDeviation a who)]
    (h : M.PureIndividualFullRank a who) :
    ∃ (R : (NontrivialDeviation a who → ℝ) →ₗ[ℝ] (M.Signal → ℝ))
        (C : ℝ),
      0 ≤ C ∧
        (M.pureIndividualIncentiveEffectMap a who).comp R = LinearMap.id ∧
        ∀ b, ‖R b‖ ≤ C * ‖b‖ := by
  obtain ⟨R, hR⟩ := h.exists_incentiveEffect_rightInverse
  let Rc := LinearMap.toContinuousLinearMap R
  refine ⟨R, ‖Rc‖, norm_nonneg _, hR, ?_⟩
  intro b
  exact Rc.le_opNorm b

/-- In finite coordinates, a pairwise-rank right inverse can be chosen with a
finite operator-norm bound for simultaneous incentive targets. -/
theorem PurePairwiseFullRank.exists_bounded_incentiveEffect_rightInverse
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G} {i j : iota}
    [Fintype (NontrivialDeviation a i)]
    [Fintype (NontrivialDeviation a j)]
    (h : M.PurePairwiseFullRank a i j) :
    ∃ (R :
          (NontrivialDeviation a i ⊕ NontrivialDeviation a j → ℝ) →ₗ[ℝ]
            (M.Signal → ℝ))
        (C : ℝ),
      0 ≤ C ∧
        (M.purePairwiseIncentiveEffectMap a i j).comp R = LinearMap.id ∧
        ∀ b, ‖R b‖ ≤ C * ‖b‖ := by
  obtain ⟨R, hR⟩ := h.exists_incentiveEffect_rightInverse
  let Rc := LinearMap.toContinuousLinearMap R
  refine ⟨R, ‖Rc‖, norm_nonneg _, hR, ?_⟩
  intro b
  exact Rc.le_opNorm b

/-- Over any finite family of profile-player pairs satisfying individual full
rank, the right inverses can be chosen with one common operator-norm bound.
The indexing type only needs to be finite; it need not enumerate all action
profiles or all players. -/
theorem exists_uniform_bounded_individualIncentiveEffect_rightInverses
    [Fintype iota] [DecidableEq iota]
    {K : Type*} [Finite K]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : K → Profile G) (who : K → iota)
    [∀ k, Fintype (NontrivialDeviation (a k) (who k))]
    (h : ∀ k, M.PureIndividualFullRank (a k) (who k)) :
    ∃ (R : ∀ k,
          (NontrivialDeviation (a k) (who k) → ℝ) →ₗ[ℝ]
            (M.Signal → ℝ))
        (C : ℝ),
      0 ≤ C ∧
        ∀ k,
          (M.pureIndividualIncentiveEffectMap (a k) (who k)).comp (R k) =
              LinearMap.id ∧
            ∀ b, ‖R k b‖ ≤ C * ‖b‖ := by
  letI := Fintype.ofFinite K
  have hex : ∀ k, ∃ (R :
        (NontrivialDeviation (a k) (who k) → ℝ) →ₗ[ℝ]
          (M.Signal → ℝ)) (C : ℝ),
      0 ≤ C ∧
        (M.pureIndividualIncentiveEffectMap (a k) (who k)).comp R =
            LinearMap.id ∧
          ∀ b, ‖R b‖ ≤ C * ‖b‖ := fun k =>
    (h k).exists_bounded_incentiveEffect_rightInverse
  choose R C hC using hex
  refine ⟨R, ∑ k, C k, Finset.sum_nonneg (fun k _ => (hC k).1), ?_⟩
  intro k
  refine ⟨(hC k).2.1, fun b => (hC k).2.2 b |>.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun k' _ => (hC k').1) (Finset.mem_univ k))
    (norm_nonneg b)

/-- Over any finite family of profile-player-pair triples satisfying pairwise
full rank, the simultaneous-incentive right inverses admit one common
operator-norm bound. -/
theorem exists_uniform_bounded_pairwiseIncentiveEffect_rightInverses
    [Fintype iota] [DecidableEq iota]
    {K : Type*} [Finite K]
    (M : G.mixedExtension.PublicMonitoring) [Fintype M.Signal]
    (a : K → Profile G) (i j : K → iota)
    [∀ k, Fintype (NontrivialDeviation (a k) (i k))]
    [∀ k, Fintype (NontrivialDeviation (a k) (j k))]
    (h : ∀ k, M.PurePairwiseFullRank (a k) (i k) (j k)) :
    ∃ (R : ∀ k,
          (NontrivialDeviation (a k) (i k) ⊕
              NontrivialDeviation (a k) (j k) → ℝ) →ₗ[ℝ]
            (M.Signal → ℝ))
        (C : ℝ),
      0 ≤ C ∧
        ∀ k,
          (M.purePairwiseIncentiveEffectMap (a k) (i k) (j k)).comp (R k) =
              LinearMap.id ∧
            ∀ b, ‖R k b‖ ≤ C * ‖b‖ := by
  letI := Fintype.ofFinite K
  have hex : ∀ k, ∃ (R :
        (NontrivialDeviation (a k) (i k) ⊕
            NontrivialDeviation (a k) (j k) → ℝ) →ₗ[ℝ]
          (M.Signal → ℝ)) (C : ℝ),
      0 ≤ C ∧
        (M.purePairwiseIncentiveEffectMap (a k) (i k) (j k)).comp R =
            LinearMap.id ∧
          ∀ b, ‖R b‖ ≤ C * ‖b‖ := fun k =>
    (h k).exists_bounded_incentiveEffect_rightInverse
  choose R C hC using hex
  refine ⟨R, ∑ k, C k, Finset.sum_nonneg (fun k _ => (hC k).1), ?_⟩
  intro k
  refine ⟨(hC k).2.1, fun b => (hC k).2.2 b |>.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun k' _ => (hC k').1) (Finset.mem_univ k))
    (norm_nonneg b)

/-! ## Tangent continuation transfers -/

/-- Embed a scalar signal-contingent transfer in one player's payoff
coordinate, leaving every other coordinate zero. -/
def singleCoordinateIncentiveTransfer
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) (who : iota)
    (z : M.Signal → ℝ) : M.Signal → Payoff iota :=
  fun y other => if other = who then z y else 0

@[simp]
theorem singleCoordinateIncentiveTransfer_apply_self
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) (who : iota)
    (z : M.Signal → ℝ) (y : M.Signal) :
    M.singleCoordinateIncentiveTransfer who z y who = z y := by
  simp [singleCoordinateIncentiveTransfer]

theorem singleCoordinateIncentiveTransfer_apply_of_ne
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) {who other : iota}
    (hother : other ≠ who) (z : M.Signal → ℝ) (y : M.Signal) :
    M.singleCoordinateIncentiveTransfer who z y other = 0 := by
  simp [singleCoordinateIncentiveTransfer, hother]

/-- A transfer supported on a coordinate where the normal vanishes is tangent
to that normal's hyperplane. -/
theorem singleCoordinateIncentiveTransfer_mem_normalHyperplane
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) (normal : Payoff iota)
    {who : iota} (hzero : normal who = 0)
    (z : M.Signal → ℝ) (y : M.Signal) :
    M.singleCoordinateIncentiveTransfer who z y ∈
      Math.LinearAlgebra.normalHyperplane normal := by
  simp [Math.LinearAlgebra.mem_normalHyperplane_iff,
    singleCoordinateIncentiveTransfer, hzero]

/-- Embed a scalar transfer in two coordinates with opposite normal-weighted
coefficients.  Its pointwise pairing with the normal is identically zero. -/
def pairwiseTangentIncentiveTransfer
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) (normal : Payoff iota)
    (i j : iota) (z : M.Signal → ℝ) : M.Signal → Payoff iota :=
  fun y who =>
    if who = i then normal j * z y
    else if who = j then -(normal i) * z y
    else 0

@[simp]
theorem pairwiseTangentIncentiveTransfer_apply_left
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) (normal : Payoff iota)
    (i j : iota) (z : M.Signal → ℝ) (y : M.Signal) :
    M.pairwiseTangentIncentiveTransfer normal i j z y i =
      normal j * z y := by
  simp [pairwiseTangentIncentiveTransfer]

@[simp]
theorem pairwiseTangentIncentiveTransfer_apply_right
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) (normal : Payoff iota)
    {i j : iota} (hij : i ≠ j) (z : M.Signal → ℝ) (y : M.Signal) :
    M.pairwiseTangentIncentiveTransfer normal i j z y j =
      -(normal i) * z y := by
  simp [pairwiseTangentIncentiveTransfer, hij.symm]

/-- The paired transfer lies in the normal hyperplane for every signal. -/
theorem pairwiseTangentIncentiveTransfer_mem_normalHyperplane
    [Fintype iota] [DecidableEq iota]
    (M : G.mixedExtension.PublicMonitoring) (normal : Payoff iota)
    {i j : iota} (hij : i ≠ j) (z : M.Signal → ℝ) (y : M.Signal) :
    M.pairwiseTangentIncentiveTransfer normal i j z y ∈
      Math.LinearAlgebra.normalHyperplane normal := by
  rw [Math.LinearAlgebra.mem_normalHyperplane_iff]
  simp only [pairwiseTangentIncentiveTransfer]
  calc
    (∑ x, normal x *
        (if x = i then normal j * z y
        else if x = j then -(normal i) * z y else 0)) =
        (∑ x, if x = i then normal x * (normal j * z y) else 0) +
          ∑ x, if x = j then normal x * (-(normal i) * z y) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxi : x = i
      · subst x
        simp [hij]
      · by_cases hxj : x = j
        · simp [hxj, hij.symm]
        · simp [hxi, hxj]
    _ = normal i * (normal j * z y) +
        normal j * (-(normal i) * z y) := by simp
    _ = 0 := by ring

/-- Individual full rank realizes any incentive target by a transfer supported
on the affected player's coordinate.  If the normal vanishes there, every
realized transfer remains tangent to its hyperplane. -/
theorem PureIndividualFullRank.exists_singleCoordinateIncentiveTransfer_supported
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G} {who : iota}
    [Finite (NontrivialDeviation a who)]
    (h : M.PureIndividualFullRank a who)
    (normal : Payoff iota) (hzero : normal who = 0)
    (target : NontrivialDeviation a who → ℝ) :
    ∃ w : M.Signal → Payoff iota,
      (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
        M.pureIndividualIncentiveEffectMap a who (fun y => w y who) =
          target ∧
        ∀ y other, other ≠ who → w y other = 0 := by
  have hsurj : Function.Surjective
      (M.pureIndividualIncentiveEffectMap a who) :=
    (M.pureIndividualIncentiveEffectMap_surjective_iff a who).2 h
  obtain ⟨z, hz⟩ := hsurj target
  refine ⟨M.singleCoordinateIncentiveTransfer who z,
    fun y => M.singleCoordinateIncentiveTransfer_mem_normalHyperplane
      normal hzero z y, ?_, ?_⟩
  · simpa only [singleCoordinateIncentiveTransfer_apply_self] using hz
  · intro y other hother
    exact M.singleCoordinateIncentiveTransfer_apply_of_ne hother z y

/-- Individual full rank realizes any one-player incentive target tangentially
when that player's normal coordinate vanishes. -/
theorem PureIndividualFullRank.exists_singleCoordinateIncentiveTransfer
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G} {who : iota}
    [Finite (NontrivialDeviation a who)]
    (h : M.PureIndividualFullRank a who)
    (normal : Payoff iota) (hzero : normal who = 0)
    (target : NontrivialDeviation a who → ℝ) :
    ∃ w : M.Signal → Payoff iota,
      (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
        M.pureIndividualIncentiveEffectMap a who (fun y => w y who) =
          target := by
  obtain ⟨w, htangent, heffect, _⟩ :=
    h.exists_singleCoordinateIncentiveTransfer_supported normal hzero target
  exact ⟨w, htangent, heffect⟩

/-- Pairwise full rank realizes arbitrary incentive targets for two players
with a continuation transfer that is pointwise tangent to any normal having
nonzero coordinates on those players. -/
theorem PurePairwiseFullRank.exists_pairwiseTangentIncentiveTransfer_supported
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G} {i j : iota}
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)]
    (h : M.PurePairwiseFullRank a i j) (hij : i ≠ j)
    (normal : Payoff iota) (hi : normal i ≠ 0) (hj : normal j ≠ 0)
    (targetI : NontrivialDeviation a i → ℝ)
    (targetJ : NontrivialDeviation a j → ℝ) :
    ∃ w : M.Signal → Payoff iota,
      (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
        M.pureIndividualIncentiveEffectMap a i (fun y => w y i) = targetI ∧
        M.pureIndividualIncentiveEffectMap a j (fun y => w y j) = targetJ ∧
        ∀ y who, who ≠ i → who ≠ j → w y who = 0 := by
  letI := Fintype.ofFinite (NontrivialDeviation a i)
  letI := Fintype.ofFinite (NontrivialDeviation a j)
  let target : NontrivialDeviation a i ⊕ NontrivialDeviation a j → ℝ :=
    Sum.elim (fun dev => targetI dev / normal j)
      (fun dev => -(targetJ dev) / normal i)
  obtain ⟨R, hR⟩ := h.exists_incentiveEffect_rightInverse
  let z := R target
  have hz : M.purePairwiseIncentiveEffectMap a i j z = target := by
    calc
      M.purePairwiseIncentiveEffectMap a i j z =
          ((M.purePairwiseIncentiveEffectMap a i j).comp R) target := rfl
      _ = LinearMap.id target := congrArg (fun L => L target) hR
      _ = target := rfl
  refine ⟨M.pairwiseTangentIncentiveTransfer normal i j z,
    fun y => M.pairwiseTangentIncentiveTransfer_mem_normalHyperplane
      normal hij z y, ?_, ?_, ?_⟩
  · have hzI : M.pureIndividualIncentiveEffectMap a i z =
        fun dev => targetI dev / normal j := by
      funext dev
      simpa [purePairwiseIncentiveEffectMap,
        pureIndividualIncentiveEffectMap,
        purePairwiseDeviationSignalFamily, Matrix.mulVec, dotProduct,
        target] using
          congrFun hz (Sum.inl dev)
    rw [show (fun y =>
        M.pairwiseTangentIncentiveTransfer normal i j z y i) =
          normal j • z by
      funext y
      simp [smul_eq_mul]]
    rw [map_smul, hzI]
    funext dev
    exact mul_div_cancel₀ _ hj
  · have hzJ : M.pureIndividualIncentiveEffectMap a j z =
        fun dev => -(targetJ dev) / normal i := by
      funext dev
      simpa [purePairwiseIncentiveEffectMap,
        pureIndividualIncentiveEffectMap,
        purePairwiseDeviationSignalFamily, Matrix.mulVec, dotProduct,
        target] using
          congrFun hz (Sum.inr dev)
    rw [show (fun y =>
        M.pairwiseTangentIncentiveTransfer normal i j z y j) =
          (-(normal i)) • z by
      funext y
      simp [hij, smul_eq_mul]]
    rw [map_smul, hzJ]
    funext dev
    change -(normal i) * (-(targetJ dev) / normal i) = targetJ dev
    calc
      -(normal i) * (-(targetJ dev) / normal i) =
          normal i * (targetJ dev / normal i) := by ring
      _ = targetJ dev := mul_div_cancel₀ _ hi
  · intro y who hwhoI hwhoJ
    simp [pairwiseTangentIncentiveTransfer, hwhoI, hwhoJ]

/-- Pairwise full rank realizes arbitrary two-player incentive targets by a
pointwise tangent public continuation transfer. -/
theorem PurePairwiseFullRank.exists_pairwiseTangentIncentiveTransfer
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G} {i j : iota}
    [Finite (NontrivialDeviation a i)]
    [Finite (NontrivialDeviation a j)]
    (h : M.PurePairwiseFullRank a i j) (hij : i ≠ j)
    (normal : Payoff iota) (hi : normal i ≠ 0) (hj : normal j ≠ 0)
    (targetI : NontrivialDeviation a i → ℝ)
    (targetJ : NontrivialDeviation a j → ℝ) :
    ∃ w : M.Signal → Payoff iota,
      (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
        M.pureIndividualIncentiveEffectMap a i (fun y => w y i) = targetI ∧
        M.pureIndividualIncentiveEffectMap a j (fun y => w y j) = targetJ := by
  obtain ⟨w, htangent, heffectI, heffectJ, _⟩ :=
    h.exists_pairwiseTangentIncentiveTransfer_supported hij normal hi hj
      targetI targetJ
  exact ⟨w, htangent, heffectI, heffectJ⟩

/-- Pairwise full rank for every distinct pair at a profile realizes an
arbitrary incentive target for every player while keeping every public
continuation transfer in a prescribed non-coordinate normal hyperplane. -/
theorem PurePairwiseFullRankAtProfile.exists_tangentIncentiveTransfer
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G}
    [∀ who, Finite (NontrivialDeviation a who)]
    (h : M.PurePairwiseFullRankAtProfile a)
    {normal : Payoff iota}
    (hnormal : Math.LinearAlgebra.HasTwoNonzeroCoordinates normal)
    (target : ∀ who, NontrivialDeviation a who → ℝ) :
    ∃ w : M.Signal → Payoff iota,
      (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
        ∀ who,
          M.pureIndividualIncentiveEffectMap a who (fun y => w y who) =
            target who := by
  classical
  obtain ⟨anchor, partner, hne, hanchor, hpartner⟩ := hnormal
  have hexPart (k : iota) :
      ∃ w : M.Signal → Payoff iota,
        (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
          M.pureIndividualIncentiveEffectMap a k (fun y => w y k) =
              target k ∧
            ∀ who, who ≠ k →
              M.pureIndividualIncentiveEffectMap a who
                (fun y => w y who) = 0 := by
    by_cases hk : k = anchor
    · subst k
      obtain ⟨w, htangent, heffect, hpartnerEffect, hsupport⟩ :=
        (h anchor partner hne).exists_pairwiseTangentIncentiveTransfer_supported
          hne normal hanchor hpartner (target anchor) 0
      refine ⟨w, htangent, heffect, ?_⟩
      intro who hwho
      by_cases hwhoPartner : who = partner
      · subst who
        exact hpartnerEffect
      · have hzero : (fun y => w y who) = 0 := by
          funext y
          exact hsupport y who hwho hwhoPartner
        rw [hzero, map_zero]
    · by_cases hkNormal : normal k = 0
      · have hki : M.PureIndividualFullRank a k :=
          ((M.purePairwiseFullRank_iff a k anchor).1
            (h k anchor hk)).1
        obtain ⟨w, htangent, heffect, hsupport⟩ :=
          hki.exists_singleCoordinateIncentiveTransfer_supported
            normal hkNormal (target k)
        refine ⟨w, htangent, heffect, ?_⟩
        intro who hwho
        have hzero : (fun y => w y who) = 0 := by
          funext y
          exact hsupport y who hwho
        rw [hzero, map_zero]
      · obtain ⟨w, htangent, heffect, hanchorEffect, hsupport⟩ :=
          (h k anchor hk).exists_pairwiseTangentIncentiveTransfer_supported
            hk normal hkNormal hanchor (target k) 0
        refine ⟨w, htangent, heffect, ?_⟩
        intro who hwho
        by_cases hwhoAnchor : who = anchor
        · subst who
          exact hanchorEffect
        · have hzero : (fun y => w y who) = 0 := by
            funext y
            exact hsupport y who hwho hwhoAnchor
          rw [hzero, map_zero]
  choose part hpart using hexPart
  refine ⟨fun y who => ∑ k, part k y who, ?_, ?_⟩
  · intro y
    change Math.LinearAlgebra.normalLinearMap normal
      (fun who => ∑ k, part k y who) = 0
    have hfun : (fun who => ∑ k, part k y who) = ∑ k, part k y := by
      funext who
      simp
    rw [hfun, map_sum]
    apply Finset.sum_eq_zero
    intro k _
    have hk := (hpart k).1 y
    change Math.LinearAlgebra.normalLinearMap normal (part k y) = 0 at hk
    exact hk
  · intro who
    have hfun : (fun y => ∑ k, part k y who) =
        ∑ k, (fun y => part k y who) := by
      funext y
      simp
    rw [hfun, map_sum, Finset.sum_eq_single who]
    · exact (hpart who).2.1
    · intro k _ hkwho
      exact (hpart k).2.2 who hkwho.symm
    · intro hnot
      exact (hnot (Finset.mem_univ who)).elim

/-- Individual full rank for every player realizes arbitrary targets in all
zero-normal coordinates of a coordinate hyperplane.  The distinguished
nonzero-normal coordinate remains identically zero. -/
theorem PureIndividualFullRankAtProfile.exists_coordinateTangentIncentiveTransfer
    [Fintype iota] [DecidableEq iota]
    {M : G.mixedExtension.PublicMonitoring} [Fintype M.Signal]
    {a : Profile G}
    [∀ who, Finite (NontrivialDeviation a who)]
    (h : M.PureIndividualFullRankAtProfile a)
    (normal : Payoff iota) (anchor : iota)
    (hzero : ∀ who, who ≠ anchor → normal who = 0)
    (target : ∀ who, NontrivialDeviation a who → ℝ) :
    ∃ w : M.Signal → Payoff iota,
      (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
        (∀ y, w y anchor = 0) ∧
          ∀ who, who ≠ anchor →
            M.pureIndividualIncentiveEffectMap a who (fun y => w y who) =
              target who := by
  classical
  let K := {who : iota // who ≠ anchor}
  have hexPart (k : K) :
      ∃ w : M.Signal → Payoff iota,
        (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
          M.pureIndividualIncentiveEffectMap a k.1 (fun y => w y k.1) =
              target k.1 ∧
            (∀ who, who ≠ k.1 →
              M.pureIndividualIncentiveEffectMap a who
                (fun y => w y who) = 0) ∧
            ∀ y who, who ≠ k.1 → w y who = 0 := by
    obtain ⟨w, htangent, heffect, hsupport⟩ :=
      (h k.1).exists_singleCoordinateIncentiveTransfer_supported
        normal (hzero k.1 k.2) (target k.1)
    refine ⟨w, htangent, heffect, ?_, hsupport⟩
    intro who hwho
    have hfun : (fun y => w y who) = 0 := by
      funext y
      exact hsupport y who hwho
    rw [hfun, map_zero]
  choose part hpart using hexPart
  refine ⟨fun y who => ∑ k : K, part k y who, ?_, ?_, ?_⟩
  · intro y
    change Math.LinearAlgebra.normalLinearMap normal
      (fun who => ∑ k : K, part k y who) = 0
    have hfun : (fun who => ∑ k : K, part k y who) =
        ∑ k : K, part k y := by
      funext who
      simp
    rw [hfun, map_sum]
    apply Finset.sum_eq_zero
    intro k _
    have hk := (hpart k).1 y
    change Math.LinearAlgebra.normalLinearMap normal (part k y) = 0 at hk
    exact hk
  · intro y
    apply Finset.sum_eq_zero
    intro k _
    exact (hpart k).2.2.2 y anchor k.2.symm
  · intro who hwho
    let kWho : K := ⟨who, hwho⟩
    have hfun : (fun y => ∑ k : K, part k y who) =
        ∑ k : K, (fun y => part k y who) := by
      funext y
      simp
    rw [hfun, map_sum, Finset.sum_eq_single kWho]
    · exact (hpart kWho).2.1
    · intro k _ hk
      exact (hpart k).2.2.1 who (fun heq => hk (Subtype.ext heq.symm))
    · intro hnot
      exact (hnot (Finset.mem_univ kWho)).elim

end PublicMonitoring
end KernelGame
end GameTheory
