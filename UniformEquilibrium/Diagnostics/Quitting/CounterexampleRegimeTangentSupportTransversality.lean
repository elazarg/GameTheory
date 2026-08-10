/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerSupport
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Support transversality of the compatible tangent blow-up system

After the exceptional-divisor Bellman rows are eliminated, the active
leading-hazard Jacobian is the pair-join matrix

`J i j = r_i({i,j}) - r_i({i})`.

For the positive support of a compatible charge-tangent packet, its positive
mass vector lies in `ker J`.  This projective scale direction has an important
consequence for the ungauged regular-arc interface.  If the radial column is
in `range J`, there is a normalized outward solve, but adding that column
does not make the augmented derivative surjective.  If the augmented
derivative is surjective, the radial column cannot be in `range J`, so no
outward kernel direction exists.  Thus surjectivity and an outward kernel
direction cannot hold simultaneously before projective scale is gauged.

The finite augmented matrix and its full-row-rank criterion are exposed
explicitly.  Failure in the outward branch supplies a nonzero left costate
annihilating both the support Jacobian and the radial column.

For three active coordinates, a substantial solved class is given.  If one
reciprocal pair of directed pair-join effects is nonzero, a single explicit
`3 x 3` radial minor decides the exact alternative: a nonzero minor makes the
augmented system surjective and forbids outward motion; a zero minor has an
explicit outward solve and makes the augmented system singular.  Reindexing
an active support of cardinality three by `Fin 3` applies this criterion
directly.

These are first-derivative statements.  They do not supply the projective
gauge, strict outsider/floor inequalities, or a strategic realization.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Generic finite radial augmentation -/

/-- Add one distinguished radial column to a square support Jacobian. -/
def quittingRadialAugmentedMatrix
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn : α → ℝ) :
    Matrix α (Option α) ℝ
  | row, none => radialColumn row
  | row, some column => jacobian row column

/-- Surjectivity of the radial column together with the support-Jacobian
columns. -/
def QuittingRadialAugmentedSurjective
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn : α → ℝ) : Prop :=
  ∀ target : α → ℝ, ∃ radial : ℝ, ∃ leading : α → ℝ,
    radial • radialColumn + jacobian *ᵥ leading = target

/-- A positive radial solution normalized to radial speed one.  Every
solution with positive radial speed rescales to this form. -/
def QuittingHasOutwardRadialSolution
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn : α → ℝ) : Prop :=
  ∃ leading : α → ℝ, radialColumn + jacobian *ᵥ leading = 0

/-- Multiplication by the augmented matrix is the radial/support action. -/
theorem quittingRadialAugmentedMatrix_mulVec
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn : α → ℝ)
    (coordinate : Option α → ℝ) :
    quittingRadialAugmentedMatrix jacobian radialColumn *ᵥ coordinate =
      coordinate none • radialColumn +
        jacobian *ᵥ fun owner => coordinate (some owner) := by
  funext row
  simp [Matrix.mulVec, dotProduct, quittingRadialAugmentedMatrix,
    Fintype.sum_option, smul_eq_mul]
  ring

/-- The intrinsic surjectivity predicate is ordinary surjectivity of the
finite augmented matrix. -/
theorem quittingRadialAugmentedSurjective_iff_mulVec_surjective
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn : α → ℝ) :
    QuittingRadialAugmentedSurjective jacobian radialColumn ↔
      Function.Surjective
        (quittingRadialAugmentedMatrix jacobian radialColumn).mulVec := by
  constructor
  · intro hsurjective target
    obtain ⟨radial, leading, htarget⟩ := hsurjective target
    let coordinate : Option α → ℝ
      | none => radial
      | some owner => leading owner
    refine ⟨coordinate, ?_⟩
    rw [quittingRadialAugmentedMatrix_mulVec]
    exact htarget
  · intro hsurjective target
    obtain ⟨coordinate, htarget⟩ := hsurjective target
    refine ⟨coordinate none, fun owner => coordinate (some owner), ?_⟩
    rw [← quittingRadialAugmentedMatrix_mulVec]
    exact htarget

/-- Full row rank is exactly radial-augmented surjectivity. -/
theorem quittingRadialAugmentedSurjective_iff_rank_eq_card
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn : α → ℝ) :
    QuittingRadialAugmentedSurjective jacobian radialColumn ↔
      (quittingRadialAugmentedMatrix jacobian radialColumn).rank =
        Fintype.card α := by
  rw [quittingRadialAugmentedSurjective_iff_mulVec_surjective]
  constructor
  · intro hsurjective
    have hrange : LinearMap.range
        (quittingRadialAugmentedMatrix jacobian radialColumn).mulVecLin = ⊤ :=
      LinearMap.range_eq_top.mpr hsurjective
    unfold Matrix.rank
    rw [hrange, finrank_top, Module.finrank_pi]
  · intro hrank
    change Function.Surjective
      (quittingRadialAugmentedMatrix jacobian radialColumn).mulVecLin
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank, Module.finrank_pi] using hrank

/-- A normalized outward solution is exactly membership of the negative
radial column in the support-Jacobian range. -/
theorem quittingHasOutwardRadialSolution_iff_mem_range
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn : α → ℝ) :
    QuittingHasOutwardRadialSolution jacobian radialColumn ↔
      -radialColumn ∈ LinearMap.range jacobian.mulVecLin := by
  constructor
  · rintro ⟨leading, hleading⟩
    refine ⟨leading, ?_⟩
    change jacobian *ᵥ leading = -radialColumn
    funext row
    have hrow := congrFun hleading row
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hrow ⊢
    linarith
  · rintro ⟨leading, hleading⟩
    refine ⟨leading, ?_⟩
    change jacobian *ᵥ leading = -radialColumn at hleading
    rw [hleading, add_neg_cancel]

/-- A square Jacobian with a genuine kernel direction cannot be both
radial-augmented surjective and outward-solvable.  This is the finite
projective obstruction behind the compatible packet calculation. -/
theorem not_augmentedSurjective_and_outward_of_kernel
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn mass : α → ℝ)
    (hmass : mass ≠ 0) (hkernel : jacobian *ᵥ mass = 0) :
    ¬(QuittingRadialAugmentedSurjective jacobian radialColumn ∧
      QuittingHasOutwardRadialSolution jacobian radialColumn) := by
  classical
  rintro ⟨haugmented, ⟨outward, houtward⟩⟩
  have hjacobianSurjective : Function.Surjective jacobian.mulVecLin := by
    intro target
    obtain ⟨radial, leading, htarget⟩ := haugmented target
    refine ⟨leading - radial • outward, ?_⟩
    change jacobian *ᵥ (leading - radial • outward) = target
    have houtward' : jacobian *ᵥ outward = -radialColumn := by
      funext row
      have hrow := congrFun houtward row
      simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hrow ⊢
      linarith
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, houtward']
    calc
      jacobian *ᵥ leading - radial • -radialColumn =
          radial • radialColumn + jacobian *ᵥ leading := by
        funext row
        simp [smul_eq_mul]
        ring
      _ = target := htarget
  have hjacobianInjective : Function.Injective jacobian.mulVecLin :=
    LinearMap.injective_iff_surjective.mpr hjacobianSurjective
  apply hmass
  apply hjacobianInjective
  simpa using hkernel

/-- In the outward branch, singularity has an explicit finite dual witness:
a nonzero left costate annihilates both the support Jacobian and the radial
column. -/
theorem exists_nonzero_radialCostate_of_kernel_and_outward
    {α : Type} [Fintype α]
    (jacobian : Matrix α α ℝ) (radialColumn mass : α → ℝ)
    (hmass : mass ≠ 0) (hkernel : jacobian *ᵥ mass = 0)
    (houtward : QuittingHasOutwardRadialSolution jacobian radialColumn) :
    ∃ costate : α → ℝ, costate ≠ 0 ∧
      jacobian.transpose *ᵥ costate = 0 ∧
      dotProduct costate radialColumn = 0 := by
  classical
  have hdet : jacobian.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨mass, hmass, hkernel⟩
  have hdetTranspose : jacobian.transpose.det = 0 := by
    simpa using hdet
  obtain ⟨costate, hcostate, hleft⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdetTranspose
  obtain ⟨leading, hleading⟩ := houtward
  refine ⟨costate, hcostate, hleft, ?_⟩
  have hradial : radialColumn = -(jacobian *ᵥ leading) := by
    funext row
    have hrow := congrFun hleading row
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hrow ⊢
    linarith
  rw [hradial, dotProduct_neg]
  have htranspose :
      dotProduct costate (jacobian *ᵥ leading) =
        dotProduct (jacobian.transpose *ᵥ costate) leading := by
    calc
      dotProduct costate (jacobian *ᵥ leading) =
          dotProduct leading (jacobian.transpose *ᵥ costate) :=
        (Matrix.dotProduct_transpose_mulVec
          jacobian leading costate).symm
      _ = dotProduct (jacobian.transpose *ᵥ costate) leading :=
        dotProduct_comm _ _
  rw [htranspose, hleft]
  simp

/-! ## Pair-join Jacobian on a declared support -/

/-- Active support of a charge-tangent packet. -/
def QuittingChargeTangentPacket.activeSupport
    (packet : QuittingChargeTangentPacket reward) : Finset ι :=
  Finset.univ.filter fun owner => 0 < packet.mass owner

@[simp]
theorem QuittingChargeTangentPacket.mem_activeSupport_iff
    (packet : QuittingChargeTangentPacket reward) (owner : ι) :
    owner ∈ packet.activeSupport ↔ 0 < packet.mass owner := by
  simp [QuittingChargeTangentPacket.activeSupport]

/-- Extend a leading variation on a declared support by zero. -/
def quittingSupportLeadingVariation (support : Finset ι)
    (coordinate : support → ℝ) : ι → ℝ :=
  fun owner => if howner : owner ∈ support then coordinate ⟨owner, howner⟩ else 0

/-- Pair-join support Jacobian after Bellman elimination.  The diagonal is
already zero by the pair-join self identity. -/
def quittingSupportPairJoinJacobian
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (support : Finset ι) : Matrix support support ℝ :=
  fun who owner =>
    quittingActiveMixingPairJoinEffect reward who.1 owner.1

/-- Matrix form of the Bellman-eliminated support variation. -/
theorem quittingMixingFirstOrderResidual_support_eq_mulVec
    (boundary : Payoff ι) (support : Finset ι)
    (coordinate : support → ℝ) (who : support)
    (hpin : boundary who.1 =
      reward (quittingSingletonTerminal who.1) who.1) :
    quittingMixingFirstOrderResidual reward
      (quittingSupportLeadingVariation support coordinate)
      (quittingBellmanForcedLeadingDrift reward boundary
        (quittingSupportLeadingVariation support coordinate)) who.1 =
      (quittingSupportPairJoinJacobian reward support *ᵥ coordinate) who := by
  rw [quittingMixingFirstOrderResidual_forcedLeadingDrift_eq_pairJoinRow
    boundary _ who.1 hpin]
  unfold Matrix.mulVec dotProduct quittingSupportPairJoinJacobian
  have herase :
      (∑ owner ∈ Finset.univ.erase who.1,
        quittingSupportLeadingVariation support coordinate owner *
          quittingActiveMixingPairJoinEffect reward who.1 owner) =
      ∑ owner,
        quittingSupportLeadingVariation support coordinate owner *
          quittingActiveMixingPairJoinEffect reward who.1 owner := by
    rw [Finset.sum_erase]
    simp [quittingSupportLeadingVariation]
  rw [herase]
  have hsupportSum :
      (∑ owner ∈ support,
        quittingSupportLeadingVariation support coordinate owner *
          quittingActiveMixingPairJoinEffect reward who.1 owner) =
      ∑ owner,
        quittingSupportLeadingVariation support coordinate owner *
          quittingActiveMixingPairJoinEffect reward who.1 owner := by
    apply Finset.sum_subset (Finset.subset_univ support)
    intro owner _ howner
    simp [quittingSupportLeadingVariation, howner]
  rw [← hsupportSum]
  rw [Finset.sum_subtype support (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro owner _
  simp [quittingSupportLeadingVariation, owner.property]
  ring

namespace QuittingChargeTangentPacket

/-- Packet mass restricted to its positive support. -/
def activeSupportMass (packet : QuittingChargeTangentPacket reward) :
    packet.activeSupport → ℝ :=
  fun owner => packet.mass owner.1

/-- The positive support of every charge-tangent packet is nonempty. -/
theorem activeSupport_nonempty
    (packet : QuittingChargeTangentPacket reward) :
    packet.activeSupport.Nonempty := by
  by_contra hempty
  have hzero : ∀ owner, packet.mass owner = 0 := by
    intro owner
    have hnotpos : ¬0 < packet.mass owner := by
      intro hpos
      exact hempty ⟨owner, (packet.mem_activeSupport_iff owner).mpr hpos⟩
    exact le_antisymm (le_of_not_gt hnotpos) (packet.mass_nonneg owner)
  have hsumZero : (∑ owner, packet.mass owner) = 0 := by
    apply Finset.sum_eq_zero
    intro owner _
    exact hzero owner
  rw [packet.mass_sum] at hsumZero
  norm_num at hsumZero

/-- The restricted positive mass vector is nonzero. -/
theorem activeSupportMass_ne_zero
    (packet : QuittingChargeTangentPacket reward) :
    packet.activeSupportMass ≠ 0 := by
  obtain ⟨owner, howner⟩ := packet.activeSupport_nonempty
  intro hzero
  have := congrFun hzero ⟨owner, howner⟩
  have hpositive := (packet.mem_activeSupport_iff owner).mp howner
  simp [activeSupportMass] at this
  linarith

/-- Compatibility places the positive support-mass vector in the kernel of
the pair-join support Jacobian.  This is the infinitesimal projective scale
direction. -/
theorem pairJoinJacobian_mulVec_activeSupportMass_eq_zero
    (packet : QuittingChargeTangentPacket reward)
    (hcompatible : ∀ who, 0 < packet.mass who →
      quittingActivePairCompatibilityResidual packet who = 0) :
    quittingSupportPairJoinJacobian reward packet.activeSupport *ᵥ
      packet.activeSupportMass = 0 := by
  funext who
  have hpositive : 0 < packet.mass who.1 :=
    (packet.mem_activeSupport_iff who.1).mp who.property
  have hpin : packet.boundary who.1 =
      reward (quittingSingletonTerminal who.1) who.1 :=
    packet.positive_mass_pins_boundary who.1 hpositive
  rw [← quittingMixingFirstOrderResidual_support_eq_mulVec
    packet.boundary packet.activeSupport packet.activeSupportMass who hpin]
  rw [quittingMixingFirstOrderResidual_forcedLeadingDrift_eq_pairJoinRow
    packet.boundary _ who.1 hpin]
  have hextension :
      quittingSupportLeadingVariation packet.activeSupport
        packet.activeSupportMass = packet.mass := by
    funext owner
    by_cases howner : owner ∈ packet.activeSupport
    · simp [quittingSupportLeadingVariation, activeSupportMass, howner]
    · have hnotpos : ¬0 < packet.mass owner := by
        simpa [packet.mem_activeSupport_iff] using howner
      have hmassZero : packet.mass owner = 0 :=
        le_antisymm (le_of_not_gt hnotpos) (packet.mass_nonneg owner)
      simp [quittingSupportLeadingVariation, howner, hmassZero]
  rw [hextension]
  have hrow := packet.activePairCompatibilityResidual_eq_sum_pairJoinEffect
    who.1 hpositive
  rw [hcompatible who.1 hpositive] at hrow
  exact hrow.symm

/-- **Ungauged compatible transversality obstruction.**  For every radial
column, the compatible positive-support system cannot be both full-row-rank
and outward-solvable. -/
theorem not_augmentedSurjective_and_outward_on_activeSupport
    (packet : QuittingChargeTangentPacket reward)
    (hcompatible : ∀ who, 0 < packet.mass who →
      quittingActivePairCompatibilityResidual packet who = 0)
    (radialColumn : packet.activeSupport → ℝ) :
    ¬(QuittingRadialAugmentedSurjective
        (quittingSupportPairJoinJacobian reward packet.activeSupport)
        radialColumn ∧
      QuittingHasOutwardRadialSolution
        (quittingSupportPairJoinJacobian reward packet.activeSupport)
        radialColumn) :=
  not_augmentedSurjective_and_outward_of_kernel
    (quittingSupportPairJoinJacobian reward packet.activeSupport)
    radialColumn packet.activeSupportMass packet.activeSupportMass_ne_zero
    (packet.pairJoinJacobian_mulVec_activeSupportMass_eq_zero hcompatible)

/-- In the outward branch, the compatible active support exposes a nonzero
finite costate annihilating the pair-join Jacobian and radial column. -/
theorem exists_nonzero_radialCostate_on_activeSupport_of_outward
    (packet : QuittingChargeTangentPacket reward)
    (hcompatible : ∀ who, 0 < packet.mass who →
      quittingActivePairCompatibilityResidual packet who = 0)
    (radialColumn : packet.activeSupport → ℝ)
    (houtward : QuittingHasOutwardRadialSolution
      (quittingSupportPairJoinJacobian reward packet.activeSupport)
      radialColumn) :
    ∃ costate : packet.activeSupport → ℝ, costate ≠ 0 ∧
      (quittingSupportPairJoinJacobian reward packet.activeSupport).transpose *ᵥ
        costate = 0 ∧
      dotProduct costate radialColumn = 0 :=
  exists_nonzero_radialCostate_of_kernel_and_outward
    (quittingSupportPairJoinJacobian reward packet.activeSupport)
    radialColumn packet.activeSupportMass packet.activeSupportMass_ne_zero
    (packet.pairJoinJacobian_mulVec_activeSupportMass_eq_zero hcompatible)
    houtward

/-! ## Direct obstruction for the full ungauged `fderiv` -/

/-- Projective scale direction through every exceptional-divisor packet base
point. -/
def blowupScaleDirection
    (packet : QuittingChargeTangentPacket reward) :
    QuittingBlowupPoint ι :=
  (0, packet.mass, fun who => -packet.tangent who)

/-- The exceptional-divisor packet base points form the literal scale line
through the projective direction. -/
theorem blowupBasePoint_eq_smul_scaleDirection
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ) :
    packet.blowupBasePoint scale =
      scale • packet.blowupScaleDirection := by
  apply Prod.ext
  · simp [blowupBasePoint, blowupScaleDirection]
  · apply Prod.ext
    · funext owner
      simp [blowupBasePoint, blowupLeading, blowupScaleDirection,
        smul_eq_mul]
    · funext who
      simp [blowupBasePoint, blowupContinuationDrift,
        blowupScaleDirection, smul_eq_mul]

/-- The projective scale direction is nonzero because packet mass sums to
one. -/
theorem blowupScaleDirection_ne_zero
    (packet : QuittingChargeTangentPacket reward) :
    packet.blowupScaleDirection ≠ 0 := by
  intro hzero
  have hmassZero : packet.mass = 0 := by
    have := congrArg (fun point : QuittingBlowupPoint ι => point.2.1) hzero
    simpa [blowupScaleDirection] using this
  have hsum : (∑ owner, packet.mass owner) = 0 := by
    rw [hmassZero]
    simp
  rw [packet.mass_sum] at hsum
  norm_num at hsum

/-- The exact scale line makes the projective scale direction a kernel
vector of the literal full support-chart derivative. -/
theorem blowupScaleDirection_mem_fderiv_ker
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ)
    (support : Finset ι)
    (hsupport : ∀ who, who ∈ support ↔ 0 < packet.mass who)
    (hcompat : ∀ who ∈ support,
      quittingActivePairCompatibilityResidual packet who = 0) :
    packet.blowupScaleDirection ∈
      (fderiv ℝ
        (quittingSupportBlowupResidual reward packet.boundary support)
        (packet.blowupBasePoint scale)).ker := by
  let residual :=
    quittingSupportBlowupResidual reward packet.boundary support
  let base := packet.blowupBasePoint scale
  let direction := packet.blowupScaleDirection
  let derivative := fderiv ℝ residual base
  have hresidual : HasFDerivAt residual derivative base := by
    exact (analyticAt_quittingSupportBlowupResidual
      packet.boundary support base).hasStrictFDerivAt.hasFDerivAt
  have hcurve : HasFDerivAt
      (fun radial : ℝ => packet.blowupBasePoint radial)
      ((1 : ℝ →L[ℝ] ℝ).smulRight direction) scale := by
    have hsmul : HasFDerivAt
        (fun radial : ℝ => radial • direction)
        ((1 : ℝ →L[ℝ] ℝ).smulRight direction) scale :=
      (hasFDerivAt_id (𝕜 := ℝ) scale).smul_const direction
    convert hsmul using 1
    funext radial
    exact packet.blowupBasePoint_eq_smul_scaleDirection radial
  have hcomp := hresidual.comp scale hcurve
  have hzero : ∀ radial : ℝ,
      residual (packet.blowupBasePoint radial) = 0 := by
    intro radial
    exact packet.supportBlowupResidual_basePoint_eq_zero radial support
      hsupport hcompat
  have hcompZero : HasFDerivAt
      (fun _ : ℝ =>
        (0 : QuittingBlowupEqRow ι support → ℝ))
      (derivative.comp ((1 : ℝ →L[ℝ] ℝ).smulRight direction)) scale := by
    exact hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun radial => (hzero radial).symm)
  have hconst : HasFDerivAt
      (fun _ : ℝ =>
        (0 : QuittingBlowupEqRow ι support → ℝ))
      (0 : ℝ →L[ℝ] (QuittingBlowupEqRow ι support → ℝ)) scale :=
    hasFDerivAt_const (0 : QuittingBlowupEqRow ι support → ℝ) scale
  have hderivative :
      derivative.comp ((1 : ℝ →L[ℝ] ℝ).smulRight direction) = 0 :=
    HasFDerivAt.unique (𝕜 := ℝ) hcompZero hconst
  change derivative direction = 0
  have happ := congrArg
    (fun linear : ℝ →L[ℝ] (QuittingBlowupEqRow ι support → ℝ) =>
      linear 1) hderivative
  simpa [direction] using happ

omit [Fintype ι] [DecidableEq ι] in
/-- The full ungauged blow-up chart has exactly one more variable than
equality row. -/
theorem finrank_quittingBlowupPoint_eq_eqRow_add_one
    [Finite ι]
    (support : Finset ι) :
    Module.finrank ℝ (QuittingBlowupPoint ι) =
      Module.finrank ℝ (QuittingBlowupEqRow ι support → ℝ) + 1 := by
  classical
  letI := Fintype.ofFinite ι
  have hsubtypeLe :
      Fintype.card {who : ι // who ∈ support} ≤ Fintype.card ι :=
    Fintype.card_subtype_le _
  have hrowCard :
      Fintype.card (QuittingBlowupEqRow ι support) =
        2 * Fintype.card ι := by
    simp only [QuittingBlowupEqRow, Fintype.card_sum,
      Fintype.card_subtype_compl]
    omega
  rw [Module.finrank_pi, hrowCard]
  simp only [QuittingBlowupPoint, Module.finrank_prod,
    Module.finrank_pi, Module.finrank_self]
  omega

/-- A surjective linear map between finite spaces whose source has one extra
dimension has one-dimensional kernel; any nonzero kernel vector with zero
distinguished coordinate therefore rules out a positive-coordinate kernel
vector. -/
theorem not_surjective_and_positiveCoordinateKernel_of_scaleKernel
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (linear : E →L[ℝ] F) (coordinate : E →L[ℝ] ℝ) (scaleDirection : E)
    (hdimension : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (hscaleKernel : scaleDirection ∈ linear.ker)
    (hscaleNonzero : scaleDirection ≠ 0)
    (hscaleCoordinate : coordinate scaleDirection = 0) :
    ¬(linear.range = ⊤ ∧
      ∃ direction : linear.ker,
        0 < coordinate direction.1) := by
  rintro ⟨hsurjective, direction, hdirection⟩
  have hrankNullity :=
    (linear : E →ₗ[ℝ] F).finrank_range_add_finrank_ker
  have hkernelFinrank :
      Module.finrank ℝ linear.ker = 1 := by
    rw [hsurjective, finrank_top, hdimension] at hrankNullity
    omega
  have hkernelSpan :
      linear.ker = ℝ ∙ scaleDirection :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      hkernelFinrank hscaleKernel hscaleNonzero
  have hdirectionSpan : direction.1 ∈ ℝ ∙ scaleDirection := by
    rw [← hkernelSpan]
    exact direction.property
  obtain ⟨coefficient, hcoefficient⟩ :=
    (Submodule.mem_span_singleton.mp hdirectionSpan)
  have hcoordinateZero : coordinate direction.1 = 0 := by
    rw [← hcoefficient, map_smul, hscaleCoordinate, smul_zero]
  rw [hcoordinateZero] at hdirection
  exact (lt_irrefl 0) hdirection

/-- **Direct full-derivative correction to the regular-lift interface.**
Under exact positive support and compatibility, derivative surjectivity and a
positive-radial kernel vector are incompatible for the literal ungauged
support blow-up system.  A projective gauge or radial-parameter formulation
is therefore necessary before the regular analytic arc interface can be
discharged. -/
theorem not_surjective_and_positiveRadialKernel_of_compatible
    (packet : QuittingChargeTangentPacket reward) (scale : ℝ)
    (support : Finset ι)
    (hsupport : ∀ who, who ∈ support ↔ 0 < packet.mass who)
    (hcompat : ∀ who ∈ support,
      quittingActivePairCompatibilityResidual packet who = 0) :
    let derivative :=
      fderiv ℝ
        (quittingSupportBlowupResidual reward packet.boundary support)
        (packet.blowupBasePoint scale)
    ¬(derivative.range = ⊤ ∧
      ∃ direction : derivative.ker,
        0 < quittingBlowupRadialCoordinate direction.1) := by
  let derivative :=
    fderiv ℝ
      (quittingSupportBlowupResidual reward packet.boundary support)
      (packet.blowupBasePoint scale)
  exact not_surjective_and_positiveCoordinateKernel_of_scaleKernel
    derivative quittingBlowupRadialCoordinate packet.blowupScaleDirection
    (finrank_quittingBlowupPoint_eq_eqRow_add_one support)
    (packet.blowupScaleDirection_mem_fderiv_ker scale support
      hsupport hcompat)
    packet.blowupScaleDirection_ne_zero rfl

end QuittingChargeTangentPacket

/-! ## A solved three-coordinate reciprocal-pair class -/

/-- The radial/first-column/second-column `3 x 3` minor of a three-coordinate
support system. -/
def quittingFinThreeRadialMinor
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun row column => ![radialColumn row, jacobian row 0, jacobian row 1] column

/-- Explicit scalar represented by the selected radial minor. -/
def quittingFinThreeRadialMinorObstruction
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ) : ℝ :=
  radialColumn 0 * jacobian 1 0 * jacobian 2 1 +
    jacobian 0 1 * radialColumn 1 * jacobian 2 0 -
      jacobian 0 1 * jacobian 1 0 * radialColumn 2

/-- Determinant computation for the selected three-coordinate radial minor,
assuming the support-Jacobian diagonal vanishes. -/
theorem quittingFinThreeRadialMinor_det
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ)
    (hdiag : ∀ owner, jacobian owner owner = 0) :
    Matrix.det (quittingFinThreeRadialMinor jacobian radialColumn) =
      quittingFinThreeRadialMinorObstruction jacobian radialColumn := by
  rw [Matrix.det_fin_three]
  simp [quittingFinThreeRadialMinor,
    quittingFinThreeRadialMinorObstruction, hdiag]

/-- Explicit support-leading solve in the zero-minor branch. -/
def quittingFinThreeOutwardLeading
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-radialColumn 1 / jacobian 1 0,
    -radialColumn 0 / jacobian 0 1, 0]

/-- If a reciprocal directed pair is nonzero and the radial minor vanishes,
the displayed leading vector gives a normalized outward solution. -/
theorem quittingFinThree_hasOutward_of_radialMinorObstruction_eq_zero
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ)
    (hdiag : ∀ owner, jacobian owner owner = 0)
    (hforward : jacobian 0 1 ≠ 0) (hreverse : jacobian 1 0 ≠ 0)
    (hminor :
      quittingFinThreeRadialMinorObstruction jacobian radialColumn = 0) :
    QuittingHasOutwardRadialSolution jacobian radialColumn := by
  refine ⟨quittingFinThreeOutwardLeading jacobian radialColumn, ?_⟩
  funext row
  fin_cases row
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      quittingFinThreeOutwardLeading, hdiag]
    field_simp [hforward]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      quittingFinThreeOutwardLeading, hdiag]
    field_simp [hreverse]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      quittingFinThreeOutwardLeading]
    field_simp [hforward, hreverse]
    unfold quittingFinThreeRadialMinorObstruction at hminor
    nlinarith

/-- A nonzero selected radial minor makes the three-coordinate augmented
system surjective. -/
theorem quittingFinThree_augmentedSurjective_of_radialMinorObstruction_ne_zero
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn : Fin 3 → ℝ)
    (hdiag : ∀ owner, jacobian owner owner = 0)
    (hminor :
      quittingFinThreeRadialMinorObstruction jacobian radialColumn ≠ 0) :
    QuittingRadialAugmentedSurjective jacobian radialColumn := by
  have hdet :
      Matrix.det (quittingFinThreeRadialMinor jacobian radialColumn) ≠ 0 := by
    rw [quittingFinThreeRadialMinor_det jacobian radialColumn hdiag]
    exact hminor
  have hunit : IsUnit (quittingFinThreeRadialMinor jacobian radialColumn) :=
    (quittingFinThreeRadialMinor jacobian radialColumn).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr hdet)
  have hsurjective : Function.Surjective
      (quittingFinThreeRadialMinor jacobian radialColumn).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  intro target
  obtain ⟨coefficient, hcoefficient⟩ := hsurjective target
  refine ⟨coefficient 0, ![coefficient 1, coefficient 2, 0], ?_⟩
  rw [← hcoefficient]
  funext row
  fin_cases row <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      quittingFinThreeRadialMinor,
      smul_eq_mul] <;> ring

/-- **Solved three-coordinate transversality alternative.**  Suppose a
three-coordinate support Jacobian has a genuine kernel vector and one
reciprocal directed pair is nonzero.  The selected radial minor gives the
exact dichotomy: nonzero means augmented surjectivity with no outward solve;
zero means an explicit outward solve with augmented singularity. -/
theorem quittingFinThree_augmentedSurjective_xor_outward
    (jacobian : Matrix (Fin 3) (Fin 3) ℝ)
    (radialColumn mass : Fin 3 → ℝ)
    (hdiag : ∀ owner, jacobian owner owner = 0)
    (hmass : mass ≠ 0) (hkernel : jacobian *ᵥ mass = 0)
    (hforward : jacobian 0 1 ≠ 0) (hreverse : jacobian 1 0 ≠ 0) :
    (quittingFinThreeRadialMinorObstruction jacobian radialColumn ≠ 0 ∧
      QuittingRadialAugmentedSurjective jacobian radialColumn ∧
      ¬QuittingHasOutwardRadialSolution jacobian radialColumn) ∨
    (quittingFinThreeRadialMinorObstruction jacobian radialColumn = 0 ∧
      QuittingHasOutwardRadialSolution jacobian radialColumn ∧
      ¬QuittingRadialAugmentedSurjective jacobian radialColumn) := by
  by_cases hminor :
      quittingFinThreeRadialMinorObstruction jacobian radialColumn = 0
  · right
    have houtward :=
      quittingFinThree_hasOutward_of_radialMinorObstruction_eq_zero
        jacobian radialColumn hdiag hforward hreverse hminor
    refine ⟨hminor, houtward, ?_⟩
    intro hsurjective
    exact not_augmentedSurjective_and_outward_of_kernel
      jacobian radialColumn mass hmass hkernel ⟨hsurjective, houtward⟩
  · left
    have hsurjective :=
      quittingFinThree_augmentedSurjective_of_radialMinorObstruction_ne_zero
        jacobian radialColumn hdiag hminor
    refine ⟨hminor, hsurjective, ?_⟩
    intro houtward
    exact not_augmentedSurjective_and_outward_of_kernel
      jacobian radialColumn mass hmass hkernel ⟨hsurjective, houtward⟩

end GameTheory
