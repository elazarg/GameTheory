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

end PublicMonitoring
end KernelGame
end GameTheory
