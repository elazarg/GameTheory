/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGaugeScalarClosure

/-!
# Second jet of the three-player projective-gauge scalar defect

In the zero-radial-minor branch the explicit outward direction kills every
first-order mixing row.  This file computes the next finite coefficient of
the omitted row `2` after passing to the sum-one gauge.

For row `2`, write `D₂₀,D₂₁` for its two pair-join effects and

`K₂ = r₂({0,1,2}) - boundary₂ - D₂₀ - D₂₁`

for the residual triple-join effect.  If `v` is the sum-one representative
of the explicit outward leading direction, the exact defect polynomial is

`s² * (Q₂ + s * C₂)`,

where

`Q₂ = (mass₀*v₁ + v₀*mass₁) * K₂`,
`C₂ = v₀*v₁*K₂`.

Thus a nonzero quadratic coefficient is a one-sided fixed-sign obstruction.
If it vanishes, the only remaining term is the displayed cubic coefficient;
if both vanish, the omitted scalar is identically zero on this affine path.

The equality with the literal blow-up residual is stated on physical points
(hazards in `[0,1]` and nonzero radial parameter).  The continuation drift is
Bellman-forced, but the omitted scalar eliminates it exactly.  No claim is
made that the affine path solves the retained nonlinear rows, or that it
returns globally.
-/

noncomputable section

open Filter Finset Matrix Set SignType Topology
open Math.PMFProduct

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Physical meaning of the omitted scalar -/

/-- On a physical hazard row, radial times the omitted blow-up defect is the
pure-Quit endpoint payoff minus the boundary. -/
theorem t_mul_quittingOmittedMixingDefect_eq_sigma_sub_boundary
    (boundary : Payoff ι) (t : ℝ) (leading drift : ι → ℝ) (who : ι)
    (hpin : boundary who = reward (quittingSingletonTerminal who) who)
    (hhazard_nonneg : ∀ owner,
      0 ≤ quittingBlowupHazard t leading owner)
    (hhazard_le_one : ∀ owner,
      quittingBlowupHazard t leading owner ≤ 1) :
    t * quittingOmittedMixingDefect reward boundary t leading drift who =
      sigmaValue (weightOfReward reward)
          (quittingBlowupHazard t leading) who - boundary who := by
  let hazard := quittingBlowupHazard t leading
  let continuation : Payoff ι :=
    fun player => boundary player + t * drift player
  let root := rootOfHazard hazard hhazard_nonneg hhazard_le_one
  have hrootHazard : hazardOfRoot root = hazard :=
    hazardOfRoot_rootOfHazard hazard hhazard_nonneg hhazard_le_one
  have habsorbing :
      (∑ S ∈ Finset.univ.erase (∅ : Finset ι),
        coalitionMass hazard S * weightOfReward reward S who) =
        quittingRootAbsorbingContribution reward root who := by
    rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
    have hrate : (fun owner => (root owner true).toReal) = hazard := by
      change hazardOfRoot root = hazard
      exact hrootHazard
    rw [hrate]
    let summand := fun S : Finset ι =>
      coalitionMass (fun owner => (root owner true).toReal) S *
        quittingProjectiveCoalitionReward reward S who
    have hsplit := Finset.add_sum_erase Finset.univ summand
      (Finset.mem_univ (∅ : Finset ι))
    have hempty : summand ∅ = 0 := by
      simp [summand, quittingProjectiveCoalitionReward]
    rw [hempty, zero_add] at hsplit
    simpa only [summand, hrate, quittingProjectiveCoalitionReward,
      weightOfReward] using hsplit
  have hcontinue : quittingStationaryContinueMass root =
      continueMass hazard := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    unfold continueMass
    apply Finset.prod_congr rfl
    intro owner _
    have hsum := quittingRoot_continueProbability_add_quitProbability root owner
    have hquit : (root owner true).toReal = hazard owner :=
      congrFun hrootHazard owner
    linarith
  have hbellmanPhysical :
      continueMass hazard * continuation who +
          (∑ S ∈ Finset.univ.erase (∅ : Finset ι),
            coalitionMass hazard S * weightOfReward reward S who) -
            boundary who =
        quittingRootSuccessorPayoff reward continuation root who -
          boundary who := by
    rw [habsorbing, quittingRootSuccessorPayoff_apply_eq_affine,
      hcontinue]
    ring
  rw [quittingOmittedMixingDefect, mul_add]
  rw [t_mul_quittingBellmanBlowupResidual]
  rw [← mul_assoc t (1 - t * leading who),
    mul_comm t (1 - t * leading who), mul_assoc,
    t_mul_quittingMixingBlowupResidual boundary t leading drift who hpin]
  change continueMass hazard * continuation who + _ - boundary who +
      (1 - hazard who) * gainValue _ hazard who (continuation who) = _
  rw [hbellmanPhysical, quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue, hrootHazard]
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hquit : (root who true).toReal = hazard who :=
    congrFun hrootHazard who
  have hcontinueWho : (root who false).toReal = 1 - hazard who := by
    linarith
  rw [hquit, hcontinueWho]
  unfold gainValue
  ring

/-! ## Literal three-player row-two polynomial -/

variable {rewardThree :
  {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)}

/-- Residual triple-join effect in the omitted row `2`. -/
def quittingFinThreeRowTwoTripleJoinRemainder
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (boundary : Payoff (Fin 3)) : ℝ :=
  weightOfReward reward ({0, 1, 2} : Finset (Fin 3)) 2 - boundary 2 -
    quittingActiveMixingPairJoinEffect reward 2 0 -
    quittingActiveMixingPairJoinEffect reward 2 1

/-- Explicit pure-Quit scalar after division by the radial parameter for row
`2` of a three-player blow-up chart. -/
def quittingFinThreeRowTwoJoinDefect
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (boundary : Payoff (Fin 3)) (t : ℝ) (leading : Fin 3 → ℝ) : ℝ :=
  leading 0 * (1 - t * leading 1) *
      quittingActiveMixingPairJoinEffect reward 2 0 +
    leading 1 * (1 - t * leading 0) *
      quittingActiveMixingPairJoinEffect reward 2 1 +
    t * leading 0 * leading 1 *
      (weightOfReward reward ({0, 1, 2} : Finset (Fin 3)) 2 - boundary 2)

/-- Exact expansion of the row-two pure-Quit boundary defect. -/
theorem sigma_sub_boundary_eq_t_mul_finThreeRowTwoJoinDefect
    (boundary : Payoff (Fin 3)) (t : ℝ) (leading : Fin 3 → ℝ)
    (hpin : boundary 2 = rewardThree (quittingSingletonTerminal 2) 2) :
    sigmaValue (weightOfReward rewardThree)
        (quittingBlowupHazard t leading) 2 - boundary 2 =
      t * quittingFinThreeRowTwoJoinDefect rewardThree boundary t leading := by
  have hplayers : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    decide
  have herase : ({0, 1, 2} : Finset (Fin 3)).erase 2 = {0, 1} := by
    decide
  have hpowerset :
      (({0, 1} : Finset (Fin 3)).powerset : Finset (Finset (Fin 3))) =
        {∅, {0}, {1}, {0, 1}} := by
    decide
  have hdiff : ({0, 1} : Finset (Fin 3)) \ {0} = {1} := by
    decide
  have htriple :
      ({2, 0, 1} : Finset (Fin 3)) = {0, 1, 2} := by
    decide
  have hsingleton :
      rewardThree
          ⟨({2} : Finset (Fin 3)), Finset.singleton_nonempty 2⟩ 2 =
        boundary 2 := by
    simpa [quittingSingletonTerminal] using hpin.symm
  unfold sigmaValue quittingBlowupHazard
  rw [hplayers, herase, hpowerset]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  norm_num [quittingFinThreeRowTwoJoinDefect,
    quittingActiveMixingPairJoinEffect, quittingPairJoinTerminal,
    weightOfReward, hpin, hdiff, htriple, hsingleton]
  ring

/-- At a nonzero physical radial parameter, the literal omitted residual is
the explicit three-player join polynomial and is independent of the supplied
continuation drift. -/
theorem quittingOmittedMixingDefect_eq_finThreeRowTwoJoinDefect
    (boundary : Payoff (Fin 3)) (t : ℝ) (leading drift : Fin 3 → ℝ)
    (hpin : boundary 2 = rewardThree (quittingSingletonTerminal 2) 2)
    (ht : t ≠ 0)
    (hhazard_nonneg : ∀ owner,
      0 ≤ quittingBlowupHazard t leading owner)
    (hhazard_le_one : ∀ owner,
      quittingBlowupHazard t leading owner ≤ 1) :
    quittingOmittedMixingDefect rewardThree boundary t leading drift 2 =
      quittingFinThreeRowTwoJoinDefect rewardThree boundary t leading := by
  have hphysical :=
    t_mul_quittingOmittedMixingDefect_eq_sigma_sub_boundary
      boundary t leading drift 2 hpin hhazard_nonneg hhazard_le_one
  rw [sigma_sub_boundary_eq_t_mul_finThreeRowTwoJoinDefect
    boundary t leading hpin] at hphysical
  exact mul_left_cancel₀ ht hphysical

/-! ## The sum-one representative of the explicit outward direction -/

/-- Literal pair-join Jacobian on the three player coordinates. -/
def quittingFinThreePairJoinJacobian
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun who owner => quittingActiveMixingPairJoinEffect reward who owner

/-- Triple-join remainder in each of the three active rows. -/
def quittingFinThreeTripleJoinRemainder
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (boundary : Payoff (Fin 3)) : Fin 3 → ℝ :=
  ![
    weightOfReward reward ({0, 1, 2} : Finset (Fin 3)) 0 - boundary 0 -
      quittingActiveMixingPairJoinEffect reward 0 1 -
      quittingActiveMixingPairJoinEffect reward 0 2,
    weightOfReward reward ({0, 1, 2} : Finset (Fin 3)) 1 - boundary 1 -
      quittingActiveMixingPairJoinEffect reward 1 0 -
      quittingActiveMixingPairJoinEffect reward 1 2,
    quittingFinThreeRowTwoTripleJoinRemainder reward boundary]

/-- Actual radial derivative of the three omitted-row defects at the packet
mass.  Each coordinate is the product of the two opponent masses times its
triple-join remainder. -/
def QuittingChargeTangentPacket.finThreeDefectRadialColumn
    (packet : QuittingChargeTangentPacket rewardThree) : Fin 3 → ℝ :=
  ![
    packet.mass 1 * packet.mass 2 *
      quittingFinThreeTripleJoinRemainder rewardThree packet.boundary 0,
    packet.mass 0 * packet.mass 2 *
      quittingFinThreeTripleJoinRemainder rewardThree packet.boundary 1,
    packet.mass 0 * packet.mass 1 *
      quittingFinThreeTripleJoinRemainder rewardThree packet.boundary 2]

namespace QuittingChargeTangentPacket

/-- Sum-one representative of the explicit zero-minor outward leading
direction.  Subtracting its total times the packet mass changes only the
projective scale representative. -/
def finThreeGaugedOutwardLeading
    (packet : QuittingChargeTangentPacket rewardThree) : Fin 3 → ℝ :=
  let leading := quittingFinThreeOutwardLeading
    (quittingFinThreePairJoinJacobian rewardThree)
    packet.finThreeDefectRadialColumn
  let total := ∑ owner, leading owner
  leading - total • packet.mass

/-- Affine radial path with the sum-one outward leading representative and
Bellman-forced continuation drift. -/
def finThreeSecondJetPath
    (packet : QuittingChargeTangentPacket rewardThree)
    (scale : ℝ) : QuittingBlowupPoint (Fin 3) :=
  let leading := packet.mass + scale • packet.finThreeGaugedOutwardLeading
  (scale, leading,
    quittingBellmanForcedLeadingDrift rewardThree packet.boundary leading)

/-- The gauged outward leading direction is zero-sum. -/
theorem sum_finThreeGaugedOutwardLeading_eq_zero
    (packet : QuittingChargeTangentPacket rewardThree) :
    ∑ owner, packet.finThreeGaugedOutwardLeading owner = 0 := by
  unfold finThreeGaugedOutwardLeading
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, packet.mass_sum, smul_eq_mul,
    mul_one, sub_self]

/-- The second-jet path stays in the global sum-one projective slice. -/
theorem finThreeSecondJetPath_leadingTotal
    (packet : QuittingChargeTangentPacket rewardThree) (scale : ℝ) :
    quittingBlowupLeadingTotal (packet.finThreeSecondJetPath scale).2.1 = 1 := by
  change quittingBlowupLeadingTotal
    (packet.mass + scale • packet.finThreeGaugedOutwardLeading) = 1
  rw [map_add, map_smul, quittingBlowupLeadingTotal_apply,
    packet.mass_sum, quittingBlowupLeadingTotal_apply,
    packet.sum_finThreeGaugedOutwardLeading_eq_zero,
    smul_zero, add_zero]

/-- At parameter zero the second-jet path is the unit-scale packet base. -/
@[simp]
theorem finThreeSecondJetPath_zero
    (packet : QuittingChargeTangentPacket rewardThree) :
    packet.finThreeSecondJetPath 0 = packet.blowupBasePoint 1 := by
  rw [finThreeSecondJetPath, zero_smul, add_zero,
    packet.bellmanForcedLeadingDrift_mass_eq]
  ext owner <;> simp [blowupBasePoint, blowupLeading]

/-- Compatibility puts the packet mass in the literal three-player pair-join
kernel. -/
theorem finThreePairJoinJacobian_mulVec_mass_eq_zero
    (packet : QuittingChargeTangentPacket rewardThree)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0) :
    quittingFinThreePairJoinJacobian rewardThree *ᵥ packet.mass = 0 := by
  funext who
  have hrow := packet.activePairCompatibilityResidual_eq_sum_pairJoinEffect
    who (hfullSupport who)
  rw [hcompat who] at hrow
  unfold quittingFinThreePairJoinJacobian Matrix.mulVec dotProduct
  change (∑ owner,
    quittingActiveMixingPairJoinEffect rewardThree who owner *
      packet.mass owner) = 0
  calc
    (∑ owner,
        quittingActiveMixingPairJoinEffect rewardThree who owner *
          packet.mass owner) =
        ∑ owner, packet.mass owner *
          quittingActiveMixingPairJoinEffect rewardThree who owner := by
      apply Finset.sum_congr rfl
      intro owner _
      ring
    _ = ∑ owner ∈ Finset.univ.erase who,
        packet.mass owner *
          quittingActiveMixingPairJoinEffect rewardThree who owner := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
      simp [quittingActiveMixingPairJoinEffect_self]
    _ = 0 := hrow.symm

/-- In the zero-radial-minor branch, the sum-one representative satisfies the
same full first-order outward equation as the explicit projective
representative. -/
theorem finThreeDefectRadialColumn_add_pairJoin_mulVec_gaugedOutward_eq_zero
    (packet : QuittingChargeTangentPacket rewardThree)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (hforward : quittingFinThreePairJoinJacobian rewardThree 0 1 ≠ 0)
    (hreverse : quittingFinThreePairJoinJacobian rewardThree 1 0 ≠ 0)
    (hminor : quittingFinThreeRadialMinorObstruction
      (quittingFinThreePairJoinJacobian rewardThree)
      packet.finThreeDefectRadialColumn = 0) :
    packet.finThreeDefectRadialColumn +
        quittingFinThreePairJoinJacobian rewardThree *ᵥ
          packet.finThreeGaugedOutwardLeading = 0 := by
  let jacobian := quittingFinThreePairJoinJacobian rewardThree
  let radial := packet.finThreeDefectRadialColumn
  let leading := quittingFinThreeOutwardLeading jacobian radial
  let total := ∑ owner, leading owner
  have hminorDirection :=
    quittingFinThreeRadialMinor_mulVec_outwardDirection_eq_zero
      jacobian radial
      (fun owner =>
        quittingActiveMixingPairJoinEffect_self (reward := rewardThree) owner)
      hforward hreverse hminor
  have houtward : radial + jacobian *ᵥ leading = 0 := by
    funext row
    have hrow := congrFun hminorDirection row
    fin_cases row <;>
      simp [quittingFinThreeRadialMinor,
        quittingFinThreeOutwardMinorDirection,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, leading,
        quittingFinThreeOutwardLeading, jacobian, radial] at hrow ⊢ <;>
      linarith
  have hkernel : jacobian *ᵥ packet.mass = 0 :=
    packet.finThreePairJoinJacobian_mulVec_mass_eq_zero
      hfullSupport hcompat
  have hgauge : packet.finThreeGaugedOutwardLeading =
      leading - total • packet.mass := by
    rfl
  rw [hgauge, Matrix.mulVec_sub, Matrix.mulVec_smul, hkernel,
    smul_zero, sub_zero]
  exact houtward

/-! ## Exact second and third coefficients -/

/-- Quadratic coefficient of the omitted row-two scalar. -/
def finThreeRowTwoQuadraticCoefficient
    (packet : QuittingChargeTangentPacket rewardThree) : ℝ :=
  let variation := packet.finThreeGaugedOutwardLeading
  (packet.mass 0 * variation 1 + variation 0 * packet.mass 1) *
    quittingFinThreeRowTwoTripleJoinRemainder rewardThree packet.boundary

/-- Cubic coefficient, which is the entire remainder after a vanishing
quadratic coefficient. -/
def finThreeRowTwoCubicCoefficient
    (packet : QuittingChargeTangentPacket rewardThree) : ℝ :=
  packet.finThreeGaugedOutwardLeading 0 *
    packet.finThreeGaugedOutwardLeading 1 *
      quittingFinThreeRowTwoTripleJoinRemainder rewardThree packet.boundary

/-- **Exact second-jet computation.**  In the compatible zero-minor branch,
the explicit row-two join defect is exactly quadratic plus cubic. -/
theorem finThreeRowTwoJoinDefect_secondJet
    (packet : QuittingChargeTangentPacket rewardThree)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (hforward : quittingFinThreePairJoinJacobian rewardThree 0 1 ≠ 0)
    (hreverse : quittingFinThreePairJoinJacobian rewardThree 1 0 ≠ 0)
    (hminor : quittingFinThreeRadialMinorObstruction
      (quittingFinThreePairJoinJacobian rewardThree)
      packet.finThreeDefectRadialColumn = 0)
    (scale : ℝ) :
    quittingFinThreeRowTwoJoinDefect rewardThree packet.boundary scale
        (packet.finThreeSecondJetPath scale).2.1 =
      scale ^ 2 * (packet.finThreeRowTwoQuadraticCoefficient +
        scale * packet.finThreeRowTwoCubicCoefficient) := by
  let variation := packet.finThreeGaugedOutwardLeading
  let pairZero := quittingActiveMixingPairJoinEffect rewardThree 2 0
  let pairOne := quittingActiveMixingPairJoinEffect rewardThree 2 1
  let triple :=
    quittingFinThreeRowTwoTripleJoinRemainder rewardThree packet.boundary
  have hconstant :
      packet.mass 0 * pairZero + packet.mass 1 * pairOne = 0 := by
    have hkernel := congrFun
      (packet.finThreePairJoinJacobian_mulVec_mass_eq_zero
        hfullSupport hcompat) 2
    have hkernel' :
        quittingActiveMixingPairJoinEffect rewardThree 2 0 * packet.mass 0 +
          quittingActiveMixingPairJoinEffect rewardThree 2 1 * packet.mass 1 =
            0 := by
      simpa [quittingFinThreePairJoinJacobian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three,
        quittingActiveMixingPairJoinEffect_self] using hkernel
    calc
      packet.mass 0 * pairZero + packet.mass 1 * pairOne =
          pairZero * packet.mass 0 + pairOne * packet.mass 1 := by ring
      _ = 0 := hkernel'
  have hlinear :
      variation 0 * pairZero + variation 1 * pairOne +
        packet.mass 0 * packet.mass 1 * triple = 0 := by
    have houtward := congrFun
      (packet.finThreeDefectRadialColumn_add_pairJoin_mulVec_gaugedOutward_eq_zero
        hfullSupport hcompat hforward hreverse hminor) 2
    have houtward' :
        packet.mass 0 * packet.mass 1 *
            quittingFinThreeRowTwoTripleJoinRemainder rewardThree
              packet.boundary +
          (quittingActiveMixingPairJoinEffect rewardThree 2 0 *
              packet.finThreeGaugedOutwardLeading 0 +
            quittingActiveMixingPairJoinEffect rewardThree 2 1 *
              packet.finThreeGaugedOutwardLeading 1) = 0 := by
      simpa [finThreeDefectRadialColumn,
        quittingFinThreeTripleJoinRemainder,
        quittingFinThreePairJoinJacobian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three,
        quittingActiveMixingPairJoinEffect_self] using houtward
    calc
      variation 0 * pairZero + variation 1 * pairOne +
          packet.mass 0 * packet.mass 1 * triple =
        packet.mass 0 * packet.mass 1 * triple +
          (pairZero * variation 0 + pairOne * variation 1) := by ring
      _ = 0 := houtward'
  have htripleIdentity :
      weightOfReward rewardThree ({0, 1, 2} : Finset (Fin 3)) 2 -
          packet.boundary 2 = triple + pairZero + pairOne := by
    dsimp only [triple, pairZero, pairOne,
      quittingFinThreeRowTwoTripleJoinRemainder]
    ring
  unfold quittingFinThreeRowTwoJoinDefect finThreeSecondJetPath
    finThreeRowTwoQuadraticCoefficient finThreeRowTwoCubicCoefficient
    quittingFinThreeRowTwoTripleJoinRemainder
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination hconstant + scale * hlinear +
    scale * packet.mass 0 * packet.mass 1 * htripleIdentity

/-- On every nonzero physical point of the second-jet path, the literal
omitted blow-up defect has exactly the computed quadratic--cubic value. -/
theorem omittedMixingDefect_secondJet_of_physical
    (packet : QuittingChargeTangentPacket rewardThree)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (hforward : quittingFinThreePairJoinJacobian rewardThree 0 1 ≠ 0)
    (hreverse : quittingFinThreePairJoinJacobian rewardThree 1 0 ≠ 0)
    (hminor : quittingFinThreeRadialMinorObstruction
      (quittingFinThreePairJoinJacobian rewardThree)
      packet.finThreeDefectRadialColumn = 0)
    (scale : ℝ) (hscale : scale ≠ 0)
    (hhazard_nonneg : ∀ owner,
      0 ≤ quittingBlowupHazard scale
        (packet.finThreeSecondJetPath scale).2.1 owner)
    (hhazard_le_one : ∀ owner,
      quittingBlowupHazard scale
        (packet.finThreeSecondJetPath scale).2.1 owner ≤ 1) :
    quittingOmittedMixingDefect rewardThree packet.boundary scale
        (packet.finThreeSecondJetPath scale).2.1
        (packet.finThreeSecondJetPath scale).2.2 2 =
      scale ^ 2 * (packet.finThreeRowTwoQuadraticCoefficient +
        scale * packet.finThreeRowTwoCubicCoefficient) := by
  have hpin : packet.boundary 2 =
      rewardThree (quittingSingletonTerminal 2) 2 :=
    packet.positive_mass_pins_boundary 2 (hfullSupport 2)
  rw [quittingOmittedMixingDefect_eq_finThreeRowTwoJoinDefect
    packet.boundary scale (packet.finThreeSecondJetPath scale).2.1
    (packet.finThreeSecondJetPath scale).2.2 hpin hscale
    hhazard_nonneg hhazard_le_one]
  exact packet.finThreeRowTwoJoinDefect_secondJet hfullSupport hcompat
    hforward hreverse hminor scale

/-! ## Finite second-jet classification -/

/-- A nonzero quadratic coefficient fixes the one-sided sign of a
quadratic--cubic polynomial. -/
theorem eventually_sq_mul_affine_pos_or_neg
    {quadratic cubic : ℝ} (hquadratic : quadratic ≠ 0) :
    (0 < quadratic ∧
      ∀ᶠ scale in 𝓝[>] (0 : ℝ),
        0 < scale ^ 2 * (quadratic + scale * cubic)) ∨
      (quadratic < 0 ∧
        ∀ᶠ scale in 𝓝[>] (0 : ℝ),
          scale ^ 2 * (quadratic + scale * cubic) < 0) := by
  have htend : Tendsto (fun scale : ℝ => quadratic + scale * cubic)
      (𝓝 0) (𝓝 quadratic) := by
    have hcontinuous : ContinuousAt
        (fun scale : ℝ => quadratic + scale * cubic) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  rcases lt_or_gt_of_ne hquadratic with hquadraticNeg | hquadraticPos
  · right
    refine ⟨hquadraticNeg, ?_⟩
    have heventually :
        ∀ᶠ scale in 𝓝 (0 : ℝ), quadratic + scale * cubic < 0 :=
      htend.eventually (Iio_mem_nhds hquadraticNeg)
    filter_upwards
      [heventually.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with scale htail hscale
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hscale) htail
  · left
    refine ⟨hquadraticPos, ?_⟩
    have heventually :
        ∀ᶠ scale in 𝓝 (0 : ℝ), 0 < quadratic + scale * cubic :=
      htend.eventually (Ioi_mem_nhds hquadraticPos)
    filter_upwards
      [heventually.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with scale htail hscale
    exact mul_pos (sq_pos_of_pos hscale) htail

/-- A nonzero quadratic coefficient is a fixed-sign local obstruction for
the explicit omitted join defect. -/
theorem finThreeRowTwoJoinDefect_fixedSign_of_quadratic_ne_zero
    (packet : QuittingChargeTangentPacket rewardThree)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (hforward : quittingFinThreePairJoinJacobian rewardThree 0 1 ≠ 0)
    (hreverse : quittingFinThreePairJoinJacobian rewardThree 1 0 ≠ 0)
    (hminor : quittingFinThreeRadialMinorObstruction
      (quittingFinThreePairJoinJacobian rewardThree)
      packet.finThreeDefectRadialColumn = 0)
    (hquadratic : packet.finThreeRowTwoQuadraticCoefficient ≠ 0) :
    (0 < packet.finThreeRowTwoQuadraticCoefficient ∧
      ∀ᶠ scale in 𝓝[>] (0 : ℝ),
        0 < quittingFinThreeRowTwoJoinDefect rewardThree packet.boundary scale
          (packet.finThreeSecondJetPath scale).2.1) ∨
      (packet.finThreeRowTwoQuadraticCoefficient < 0 ∧
        ∀ᶠ scale in 𝓝[>] (0 : ℝ),
          quittingFinThreeRowTwoJoinDefect rewardThree packet.boundary scale
            (packet.finThreeSecondJetPath scale).2.1 < 0) := by
  have hsign := eventually_sq_mul_affine_pos_or_neg
    (cubic := packet.finThreeRowTwoCubicCoefficient) hquadratic
  rcases hsign with ⟨hpositive, heventually⟩ |
      ⟨hnegative, heventually⟩
  · left
    refine ⟨hpositive, ?_⟩
    filter_upwards [heventually] with scale hscale
    rw [packet.finThreeRowTwoJoinDefect_secondJet hfullSupport hcompat
      hforward hreverse hminor scale]
    exact hscale
  · right
    refine ⟨hnegative, ?_⟩
    filter_upwards [heventually] with scale hscale
    rw [packet.finThreeRowTwoJoinDefect_secondJet hfullSupport hcompat
      hforward hreverse hminor scale]
    exact hscale

/-- If the quadratic coefficient vanishes, the entire remaining polynomial
is the explicit cubic term. -/
theorem finThreeRowTwoJoinDefect_eq_scale_cubed_mul_of_quadratic_eq_zero
    (packet : QuittingChargeTangentPacket rewardThree)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (hforward : quittingFinThreePairJoinJacobian rewardThree 0 1 ≠ 0)
    (hreverse : quittingFinThreePairJoinJacobian rewardThree 1 0 ≠ 0)
    (hminor : quittingFinThreeRadialMinorObstruction
      (quittingFinThreePairJoinJacobian rewardThree)
      packet.finThreeDefectRadialColumn = 0)
    (hquadratic : packet.finThreeRowTwoQuadraticCoefficient = 0)
    (scale : ℝ) :
    quittingFinThreeRowTwoJoinDefect rewardThree packet.boundary scale
        (packet.finThreeSecondJetPath scale).2.1 =
      scale ^ 3 * packet.finThreeRowTwoCubicCoefficient := by
  rw [packet.finThreeRowTwoJoinDefect_secondJet hfullSupport hcompat
    hforward hreverse hminor scale, hquadratic]
  ring

/-- With zero quadratic but nonzero cubic coefficient, the omitted scalar
still has one fixed sign for every positive parameter. -/
theorem finThreeRowTwoJoinDefect_fixedSign_of_quadratic_eq_zero
    (packet : QuittingChargeTangentPacket rewardThree)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (hforward : quittingFinThreePairJoinJacobian rewardThree 0 1 ≠ 0)
    (hreverse : quittingFinThreePairJoinJacobian rewardThree 1 0 ≠ 0)
    (hminor : quittingFinThreeRadialMinorObstruction
      (quittingFinThreePairJoinJacobian rewardThree)
      packet.finThreeDefectRadialColumn = 0)
    (hquadratic : packet.finThreeRowTwoQuadraticCoefficient = 0)
    (hcubic : packet.finThreeRowTwoCubicCoefficient ≠ 0) :
    (0 < packet.finThreeRowTwoCubicCoefficient ∧
      ∀ scale, 0 < scale →
        0 < quittingFinThreeRowTwoJoinDefect rewardThree packet.boundary scale
          (packet.finThreeSecondJetPath scale).2.1) ∨
      (packet.finThreeRowTwoCubicCoefficient < 0 ∧
        ∀ scale, 0 < scale →
          quittingFinThreeRowTwoJoinDefect rewardThree packet.boundary scale
            (packet.finThreeSecondJetPath scale).2.1 < 0) := by
  rcases lt_or_gt_of_ne hcubic with hcubicNeg | hcubicPos
  · right
    refine ⟨hcubicNeg, ?_⟩
    intro scale hscale
    rw [packet.finThreeRowTwoJoinDefect_eq_scale_cubed_mul_of_quadratic_eq_zero
      hfullSupport hcompat hforward hreverse hminor hquadratic scale]
    exact mul_neg_of_pos_of_neg (pow_pos hscale 3) hcubicNeg
  · left
    refine ⟨hcubicPos, ?_⟩
    intro scale hscale
    rw [packet.finThreeRowTwoJoinDefect_eq_scale_cubed_mul_of_quadratic_eq_zero
      hfullSupport hcompat hforward hreverse hminor hquadratic scale]
    exact mul_pos (pow_pos hscale 3) hcubicPos

/-- If both finite coefficients vanish, the omitted scalar is identically
zero on the whole affine second-jet path. -/
theorem finThreeRowTwoJoinDefect_eq_zero_of_coefficients_eq_zero
    (packet : QuittingChargeTangentPacket rewardThree)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (hforward : quittingFinThreePairJoinJacobian rewardThree 0 1 ≠ 0)
    (hreverse : quittingFinThreePairJoinJacobian rewardThree 1 0 ≠ 0)
    (hminor : quittingFinThreeRadialMinorObstruction
      (quittingFinThreePairJoinJacobian rewardThree)
      packet.finThreeDefectRadialColumn = 0)
    (hquadratic : packet.finThreeRowTwoQuadraticCoefficient = 0)
    (hcubic : packet.finThreeRowTwoCubicCoefficient = 0)
    (scale : ℝ) :
    quittingFinThreeRowTwoJoinDefect rewardThree packet.boundary scale
      (packet.finThreeSecondJetPath scale).2.1 = 0 := by
  rw [packet.finThreeRowTwoJoinDefect_eq_scale_cubed_mul_of_quadratic_eq_zero
    hfullSupport hcompat hforward hreverse hminor hquadratic scale,
    hcubic, mul_zero]

end QuittingChargeTangentPacket

end GameTheory
