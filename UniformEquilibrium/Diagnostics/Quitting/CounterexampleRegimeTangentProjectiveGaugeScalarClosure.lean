/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGaugeDefect

/-!
# Scalar closure after projective gauge reduction

Solving all Bellman rows and all but one active mixing row leaves the scalar
defect isolated in `CounterexampleRegimeTangentProjectiveGaugeDefect`.  This
file records the exact first-order closure alternative on a three-coordinate
support.

If the selected three-row radial minor is nonzero, every outward tangent that
kills the retained rows has a nonzero omitted-row derivative.  Along any
differentiable reduced branch with that tangent, the scalar defect therefore
has one fixed sign on a punctured positive neighborhood.  It cannot close by
an intermediate-value argument near the packet base.

If the radial minor is zero and one reciprocal directed pair is nonzero, the
existing explicit outward solve kills all three first-order rows.  The scalar
defect then has zero first derivative and its closure is a genuinely
higher-order question.  Packet energy or pair-sign information does not by
itself decide that higher-order coefficient.

This is a local finite alternative only.  It assumes the derivative of the
scalar defect along a supplied reduced branch; it neither constructs that
branch nor asserts a global return.
-/

noncomputable section

open Filter Finset Matrix Set SignType Topology

namespace GameTheory

/-! ## One-sided sign from a nonzero scalar derivative -/

/-- A scalar germ through zero with nonzero derivative has a fixed strict
sign on the punctured positive side. -/
theorem eventually_nhdsGT_pos_or_neg_of_hasDerivAt_ne_zero
    {defect : ℝ → ℝ} {slope : ℝ}
    (hderiv : HasDerivAt defect slope 0) (hzero : defect 0 = 0)
    (hslope : slope ≠ 0) :
    (0 < slope ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < defect t) ∨
      (slope < 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), defect t < 0) := by
  rcases lt_or_gt_of_ne hslope with hslopeNeg | hslopePos
  · right
    refine ⟨hslopeNeg, ?_⟩
    have hsign :
        ∀ᶠ t in 𝓝 (0 : ℝ),
          SignType.sign (-defect t) = SignType.sign (t - 0) := by
      have hnegDeriv :
          HasDerivAt (fun t => -defect t) (-slope) 0 := hderiv.neg
      apply eventually_nhdsWithin_sign_eq_of_deriv_pos
      · rw [hnegDeriv.deriv]
        linarith
      · rw [hzero, neg_zero]
    filter_upwards
      [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with
      t ht htright
    have htSign : SignType.sign t = 1 := sign_pos htright
    rw [sub_zero, htSign] at ht
    have hnegDefect : 0 < -defect t := sign_eq_one_iff.mp ht
    linarith
  · left
    refine ⟨hslopePos, ?_⟩
    have hsign :
        ∀ᶠ t in 𝓝 (0 : ℝ),
          SignType.sign (defect t) = SignType.sign (t - 0) := by
      apply eventually_nhdsWithin_sign_eq_of_deriv_pos
      · rw [hderiv.deriv]
        exact hslopePos
      · exact hzero
    filter_upwards
      [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with
      t ht htright
    have htSign : SignType.sign t = 1 := sign_pos htright
    rw [sub_zero, htSign] at ht
    exact sign_eq_one_iff.mp ht

/-! ## Exact sign on the normalized regression family -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingChargeTangentPacket

/-- On the exact Bellman-forced normalized regression, the nonlinear omitted
scalar is exactly the parameter times its pair-join slope. -/
theorem deletedMixingRegressionPoint_omittedDefect_eq_scale_mul_pairJoinRow
    (packet : QuittingChargeTangentPacket reward)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (leadingVariation : ι → ℝ) (scale : ℝ) (who : ι) :
    quittingOmittedMixingDefect reward packet.boundary
        (packet.deletedMixingRegressionPoint leadingVariation scale).1
        (packet.deletedMixingRegressionPoint leadingVariation scale).2.1
        (packet.deletedMixingRegressionPoint leadingVariation scale).2.2
        who =
      scale * ∑ owner ∈ Finset.univ.erase who,
        leadingVariation owner *
          quittingActiveMixingPairJoinEffect reward who owner := by
  rw [quittingOmittedMixingDefect,
    packet.deletedMixingRegressionPoint_bellman_eq_zero
      leadingVariation scale who,
    zero_add]
  change (1 - 0 * _) * _ = _
  rw [zero_mul, sub_zero, one_mul,
    packet.deletedMixingRegressionPoint_mixing_eq_scale_mul_pairJoinRow
      hfullSupport hcompat leadingVariation scale who]

/-- A nonzero pair-join slope gives a fixed strict sign on the whole positive
half of the exact regression family.  Sign information therefore obstructs,
rather than forces, scalar closure on this family. -/
theorem deletedMixingRegressionPoint_omittedDefect_fixedSign
    (packet : QuittingChargeTangentPacket reward)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (leadingVariation : ι → ℝ) (who : ι)
    (hslope :
      (∑ owner ∈ Finset.univ.erase who,
        leadingVariation owner *
          quittingActiveMixingPairJoinEffect reward who owner) ≠ 0) :
    let slope := ∑ owner ∈ Finset.univ.erase who,
      leadingVariation owner *
        quittingActiveMixingPairJoinEffect reward who owner
    (0 < slope ∧ ∀ scale, 0 < scale →
      0 < quittingOmittedMixingDefect reward packet.boundary
        (packet.deletedMixingRegressionPoint leadingVariation scale).1
        (packet.deletedMixingRegressionPoint leadingVariation scale).2.1
        (packet.deletedMixingRegressionPoint leadingVariation scale).2.2
        who) ∨
      (slope < 0 ∧ ∀ scale, 0 < scale →
        quittingOmittedMixingDefect reward packet.boundary
          (packet.deletedMixingRegressionPoint leadingVariation scale).1
          (packet.deletedMixingRegressionPoint leadingVariation scale).2.1
          (packet.deletedMixingRegressionPoint leadingVariation scale).2.2
          who < 0) := by
  let slope := ∑ owner ∈ Finset.univ.erase who,
    leadingVariation owner *
      quittingActiveMixingPairJoinEffect reward who owner
  rcases lt_or_gt_of_ne hslope with hslopeNeg | hslopePos
  · right
    refine ⟨hslopeNeg, ?_⟩
    intro scale hscale
    rw [packet.deletedMixingRegressionPoint_omittedDefect_eq_scale_mul_pairJoinRow
      hfullSupport hcompat leadingVariation scale who]
    exact mul_neg_of_pos_of_neg hscale hslopeNeg
  · left
    refine ⟨hslopePos, ?_⟩
    intro scale hscale
    rw [packet.deletedMixingRegressionPoint_omittedDefect_eq_scale_mul_pairJoinRow
      hfullSupport hcompat leadingVariation scale who]
    exact mul_pos hscale hslopePos

end QuittingChargeTangentPacket

/-! ## The three-row minor decides first-order scalar closure -/

/-- If the selected radial minor is nonzero, an outward vector killing every
retained row must have nonzero omitted row.  This is the finite linear
obstruction behind the scalar sign alternative. -/
theorem quittingFinThree_omittedRow_ne_zero_of_radialMinor_ne_zero
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn direction : Fin 3 → ℝ) (omitted : Fin 3)
    (hdiag : ∀ owner, jacobian owner owner = 0)
    (hminor :
      quittingFinThreeRadialMinorObstruction jacobian radialColumn ≠ 0)
    (hradial : 0 < direction 0)
    (hretained : ∀ row, row ≠ omitted →
      (quittingFinThreeRadialMinor jacobian radialColumn *ᵥ direction) row =
        0) :
    (quittingFinThreeRadialMinor jacobian radialColumn *ᵥ direction) omitted ≠
      0 := by
  have hdet :
      Matrix.det (quittingFinThreeRadialMinor jacobian radialColumn) ≠ 0 := by
    rw [quittingFinThreeRadialMinor_det jacobian radialColumn hdiag]
    exact hminor
  have hunit : IsUnit (quittingFinThreeRadialMinor jacobian radialColumn) :=
    (quittingFinThreeRadialMinor jacobian radialColumn).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr hdet)
  have hinjective : Function.Injective
      (quittingFinThreeRadialMinor jacobian radialColumn).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  intro homitted
  have hproduct :
      quittingFinThreeRadialMinor jacobian radialColumn *ᵥ direction = 0 := by
    funext row
    by_cases hrow : row = omitted
    · subst row
      exact homitted
    · exact hretained row hrow
  have hdirection : direction = 0 := by
    apply hinjective
    simp [hproduct]
  have hzero := congrFun hdirection 0
  simp at hzero
  linarith

/-- **Nonzero-minor scalar sign obstruction.**  If a differentiable reduced
branch has an outward tangent killing the retained rows, and its omitted
scalar defect has the corresponding full-row derivative, then that defect
has a fixed nonzero sign immediately to the positive side. -/
theorem quittingFinThree_defect_fixedSign_of_radialMinor_ne_zero
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn direction : Fin 3 → ℝ) (omitted : Fin 3)
    (defect : ℝ → ℝ)
    (hdiag : ∀ owner, jacobian owner owner = 0)
    (hminor :
      quittingFinThreeRadialMinorObstruction jacobian radialColumn ≠ 0)
    (hradial : 0 < direction 0)
    (hretained : ∀ row, row ≠ omitted →
      (quittingFinThreeRadialMinor jacobian radialColumn *ᵥ direction) row =
        0)
    (hderiv : HasDerivAt defect
      ((quittingFinThreeRadialMinor jacobian radialColumn *ᵥ direction)
        omitted) 0)
    (hzero : defect 0 = 0) :
    let slope :=
      (quittingFinThreeRadialMinor jacobian radialColumn *ᵥ direction) omitted
    (0 < slope ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < defect t) ∨
      (slope < 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), defect t < 0) := by
  exact eventually_nhdsGT_pos_or_neg_of_hasDerivAt_ne_zero hderiv hzero
    (quittingFinThree_omittedRow_ne_zero_of_radialMinor_ne_zero
      jacobian radialColumn direction omitted hdiag hminor hradial hretained)

/-! ## Zero minor: honest higher-order residue -/

/-- Coordinates of the existing explicit outward solve in the selected
three-column radial minor. -/
def quittingFinThreeOutwardMinorDirection
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![1,
    (quittingFinThreeOutwardLeading jacobian radialColumn) 0,
    (quittingFinThreeOutwardLeading jacobian radialColumn) 1]

@[simp]
theorem quittingFinThreeOutwardMinorDirection_radial
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ) :
    quittingFinThreeOutwardMinorDirection jacobian radialColumn 0 = 1 := by
  simp [quittingFinThreeOutwardMinorDirection]

/-- In the zero-minor reciprocal-pair branch, the explicit outward direction
annihilates all three selected first-order rows.  Consequently the omitted
scalar has zero first derivative along this tangent; its closure cannot be
decided by an IVT sign change at first order. -/
theorem quittingFinThreeRadialMinor_mulVec_outwardDirection_eq_zero
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ)
    (hdiag : ∀ owner, jacobian owner owner = 0)
    (hforward : jacobian 0 1 ≠ 0) (hreverse : jacobian 1 0 ≠ 0)
    (hminor :
      quittingFinThreeRadialMinorObstruction jacobian radialColumn = 0) :
    quittingFinThreeRadialMinor jacobian radialColumn *ᵥ
      quittingFinThreeOutwardMinorDirection jacobian radialColumn = 0 := by
  funext row
  fin_cases row
  · simp [quittingFinThreeRadialMinor,
      quittingFinThreeOutwardMinorDirection,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      quittingFinThreeOutwardLeading, hdiag]
    field_simp [hforward]
    ring
  · simp [quittingFinThreeRadialMinor,
      quittingFinThreeOutwardMinorDirection,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      quittingFinThreeOutwardLeading, hdiag]
    field_simp [hreverse]
    ring
  · simp [quittingFinThreeRadialMinor,
      quittingFinThreeOutwardMinorDirection,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      quittingFinThreeOutwardLeading]
    field_simp [hforward, hreverse]
    unfold quittingFinThreeRadialMinorObstruction at hminor
    nlinarith

end GameTheory
