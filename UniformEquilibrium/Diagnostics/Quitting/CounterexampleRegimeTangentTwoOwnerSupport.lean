/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentRegularArcLift

/-!
# Two-owner support Jacobian of the tangent blow-up system

Eliminate the exceptional-divisor Bellman rows by letting a leading-hazard
variation choose its forced continuation drift.  On a pinned active owner,
the remaining mixing row is exactly the pair-join row.  For two distinct
owners `first, second`, its support Jacobian is therefore

`[[0, D first second], [D second first, 0]]`,

where `D i j = r_i({i,j}) - r_i({i})`.  Its determinant is
`-D first second * D second first`.  A directed signed pivot is consequently
regular precisely when its reciprocal directed effect is nonzero.  In that
case every radial column has an explicit outward solution with radial
coordinate one.

There is also a decisive singular branch.  If `first, second` are the entire
positive-mass support of a compatible tangent packet, each compatibility row
has only one positive-mass outsider.  Both directed effects must vanish, so
the reduced Jacobian is the zero matrix.  A negative reciprocal collision
increment then says exactly that the reciprocal singleton solo effect is
positive; it does not restore regularity of this chart.

These are support-linearization results.  The regular case supplies the
finite Jacobian and outward solve needed by the regular arc interface, but
does not by itself verify the strict outsider/floor cell.  The singular case
does not imply a pure or sure-exit solution.
-/

noncomputable section

namespace GameTheory

open Finset Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The continuation drift forced by the exceptional-divisor Bellman rows
for a supplied leading-hazard variation. -/
def quittingBellmanForcedLeadingDrift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : Payoff ι) (leadingVariation : ι → ℝ) : ι → ℝ :=
  fun who => -∑ owner, leadingVariation owner *
    (reward (quittingSingletonTerminal owner) who - boundary who)

omit [DecidableEq ι] in
/-- The forced drift kills every linear exceptional-divisor Bellman row. -/
theorem quittingBellmanFirstOrderResidual_forcedLeadingDrift_eq_zero
    (boundary : Payoff ι) (leadingVariation : ι → ℝ) (who : ι) :
    quittingBellmanFirstOrderResidual reward boundary leadingVariation
      (quittingBellmanForcedLeadingDrift reward boundary leadingVariation)
      who = 0 := by
  unfold quittingBellmanFirstOrderResidual
    quittingBellmanForcedLeadingDrift
  simp

/-- After Bellman elimination, a pinned active mixing row is exactly the
linear pair-join row.  This is the reduced support Jacobian formula before a
support is chosen. -/
theorem quittingMixingFirstOrderResidual_forcedLeadingDrift_eq_pairJoinRow
    (boundary : Payoff ι) (leadingVariation : ι → ℝ) (who : ι)
    (hpin : boundary who = reward (quittingSingletonTerminal who) who) :
    quittingMixingFirstOrderResidual reward leadingVariation
      (quittingBellmanForcedLeadingDrift reward boundary leadingVariation)
      who =
        ∑ owner ∈ Finset.univ.erase who,
          leadingVariation owner *
            quittingActiveMixingPairJoinEffect reward who owner := by
  unfold quittingMixingFirstOrderResidual
    quittingBellmanForcedLeadingDrift
  rw [sub_neg_eq_add]
  have hsingletonErase :
      (∑ owner, leadingVariation owner *
        (reward (quittingSingletonTerminal owner) who - boundary who)) =
      ∑ owner ∈ Finset.univ.erase who,
        leadingVariation owner *
          (reward (quittingSingletonTerminal owner) who - boundary who) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
    simp [hpin]
  rw [hsingletonErase, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro owner howner
  have hpairWeight :
      weightOfReward reward ({who, owner} : Finset ι) who =
        reward (quittingPairJoinTerminal who owner) who := by
    simp [weightOfReward, quittingPairJoinTerminal]
  have hsingletonWeight :
      weightOfReward reward ({owner} : Finset ι) who =
        reward (quittingSingletonTerminal owner) who := by
    simp only [weightOfReward, quittingSingletonTerminal]
    congr
  rw [hpairWeight, hsingletonWeight]
  rw [← mul_add]
  unfold quittingActiveMixingPairJoinEffect
  rw [hpin]
  ring

/-- The two owners indexed in the order used by the support Jacobian. -/
def quittingTwoOwnerIndex (first second : ι) : Fin 2 → ι :=
  ![first, second]

/-- The reduced two-owner support Jacobian after Bellman elimination. -/
def quittingTwoOwnerSupportJacobian
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun row column =>
    if row = column then 0 else
      quittingActiveMixingPairJoinEffect reward
        (quittingTwoOwnerIndex first second row)
        (quittingTwoOwnerIndex first second column)

omit [Fintype ι] in
@[simp]
theorem quittingTwoOwnerSupportJacobian_zero_zero
    (first second : ι) :
    quittingTwoOwnerSupportJacobian reward first second 0 0 = 0 := by
  simp [quittingTwoOwnerSupportJacobian]

omit [Fintype ι] in
@[simp]
theorem quittingTwoOwnerSupportJacobian_zero_one
    (first second : ι) :
    quittingTwoOwnerSupportJacobian reward first second 0 1 =
      quittingActiveMixingPairJoinEffect reward first second := by
  simp [quittingTwoOwnerSupportJacobian, quittingTwoOwnerIndex]

omit [Fintype ι] in
@[simp]
theorem quittingTwoOwnerSupportJacobian_one_zero
    (first second : ι) :
    quittingTwoOwnerSupportJacobian reward first second 1 0 =
      quittingActiveMixingPairJoinEffect reward second first := by
  simp [quittingTwoOwnerSupportJacobian, quittingTwoOwnerIndex]

omit [Fintype ι] in
@[simp]
theorem quittingTwoOwnerSupportJacobian_one_one
    (first second : ι) :
    quittingTwoOwnerSupportJacobian reward first second 1 1 = 0 := by
  simp [quittingTwoOwnerSupportJacobian]

omit [Fintype ι] in
/-- Exact determinant of the reduced two-owner support Jacobian. -/
theorem quittingTwoOwnerSupportJacobian_det
    (first second : ι) :
    Matrix.det (quittingTwoOwnerSupportJacobian reward first second) =
      -(quittingActiveMixingPairJoinEffect reward first second *
        quittingActiveMixingPairJoinEffect reward second first) := by
  rw [Matrix.det_fin_two]
  simp

omit [Fintype ι] in
/-- The two-owner support Jacobian is regular exactly when both directed
pair-join effects are nonzero. -/
theorem quittingTwoOwnerSupportJacobian_det_ne_zero_iff
    (first second : ι) :
    Matrix.det (quittingTwoOwnerSupportJacobian reward first second) ≠ 0 ↔
      quittingActiveMixingPairJoinEffect reward first second ≠ 0 ∧
        quittingActiveMixingPairJoinEffect reward second first ≠ 0 := by
  rw [quittingTwoOwnerSupportJacobian_det]
  simp

/-- Leading-hazard variation supported on two declared owners. -/
def quittingTwoOwnerLeadingVariation
    (first second : ι) (coordinate : Fin 2 → ℝ) : ι → ℝ :=
  fun owner =>
    if owner = first then coordinate 0
    else if owner = second then coordinate 1
    else 0

omit [Fintype ι] in
@[simp]
theorem quittingTwoOwnerLeadingVariation_first
    (first second : ι) (coordinate : Fin 2 → ℝ) :
    quittingTwoOwnerLeadingVariation first second coordinate first =
      coordinate 0 := by
  simp [quittingTwoOwnerLeadingVariation]

omit [Fintype ι] in
@[simp]
theorem quittingTwoOwnerLeadingVariation_second
    (first second : ι) (coordinate : Fin 2 → ℝ)
    (hne : first ≠ second) :
  quittingTwoOwnerLeadingVariation first second coordinate second =
      coordinate 1 := by
  simp [quittingTwoOwnerLeadingVariation, hne.symm]

/-- First reduced mixing row for a two-owner leading variation. -/
theorem quittingMixingFirstOrderResidual_twoOwner_first
    (boundary : Payoff ι) (first second : ι) (coordinate : Fin 2 → ℝ)
    (hne : first ≠ second)
    (hpin : boundary first =
      reward (quittingSingletonTerminal first) first) :
    quittingMixingFirstOrderResidual reward
      (quittingTwoOwnerLeadingVariation first second coordinate)
      (quittingBellmanForcedLeadingDrift reward boundary
        (quittingTwoOwnerLeadingVariation first second coordinate)) first =
      coordinate 1 *
        quittingActiveMixingPairJoinEffect reward first second := by
  rw [quittingMixingFirstOrderResidual_forcedLeadingDrift_eq_pairJoinRow
    boundary _ first hpin]
  rw [Finset.sum_eq_single second]
  · simp [quittingTwoOwnerLeadingVariation, hne.symm]
  · intro owner howner hownerSecond
    have hownerFirst : owner ≠ first := (Finset.mem_erase.mp howner).1
    simp [quittingTwoOwnerLeadingVariation, hownerFirst, hownerSecond]
  · intro hsecond
    exact (hsecond (by simp [hne.symm])).elim

/-- Second reduced mixing row for a two-owner leading variation. -/
theorem quittingMixingFirstOrderResidual_twoOwner_second
    (boundary : Payoff ι) (first second : ι) (coordinate : Fin 2 → ℝ)
    (hne : first ≠ second)
    (hpin : boundary second =
      reward (quittingSingletonTerminal second) second) :
    quittingMixingFirstOrderResidual reward
      (quittingTwoOwnerLeadingVariation first second coordinate)
      (quittingBellmanForcedLeadingDrift reward boundary
        (quittingTwoOwnerLeadingVariation first second coordinate)) second =
      coordinate 0 *
        quittingActiveMixingPairJoinEffect reward second first := by
  rw [quittingMixingFirstOrderResidual_forcedLeadingDrift_eq_pairJoinRow
    boundary _ second hpin]
  rw [Finset.sum_eq_single first]
  · simp [quittingTwoOwnerLeadingVariation]
  · intro owner howner hownerFirst
    have hownerSecond : owner ≠ second := (Finset.mem_erase.mp howner).1
    simp [quittingTwoOwnerLeadingVariation, hownerFirst, hownerSecond]
  · intro hfirst
    exact (hfirst (by simp [hne])).elim

/-- Vector form: the reduced exceptional-divisor variation is multiplication
by the displayed two-owner support Jacobian. -/
theorem quittingMixingFirstOrderResidual_twoOwner_eq_mulVec
    (boundary : Payoff ι) (first second : ι) (coordinate : Fin 2 → ℝ)
    (hne : first ≠ second)
    (hpinFirst : boundary first =
      reward (quittingSingletonTerminal first) first)
    (hpinSecond : boundary second =
      reward (quittingSingletonTerminal second) second) :
    (fun row => quittingMixingFirstOrderResidual reward
      (quittingTwoOwnerLeadingVariation first second coordinate)
      (quittingBellmanForcedLeadingDrift reward boundary
        (quittingTwoOwnerLeadingVariation first second coordinate))
      (quittingTwoOwnerIndex first second row)) =
      (quittingTwoOwnerSupportJacobian reward first second).mulVec coordinate := by
  funext row
  fin_cases row
  · change quittingMixingFirstOrderResidual reward
        (quittingTwoOwnerLeadingVariation first second coordinate)
        (quittingBellmanForcedLeadingDrift reward boundary
          (quittingTwoOwnerLeadingVariation first second coordinate)) first =
      (quittingTwoOwnerSupportJacobian reward first second).mulVec coordinate 0
    rw [quittingMixingFirstOrderResidual_twoOwner_first
      boundary first second coordinate hne hpinFirst]
    simp [Matrix.mulVec, dotProduct]
    ring
  · change quittingMixingFirstOrderResidual reward
        (quittingTwoOwnerLeadingVariation first second coordinate)
        (quittingBellmanForcedLeadingDrift reward boundary
          (quittingTwoOwnerLeadingVariation first second coordinate)) second =
      (quittingTwoOwnerSupportJacobian reward first second).mulVec coordinate 1
    rw [quittingMixingFirstOrderResidual_twoOwner_second
      boundary first second coordinate hne hpinSecond]
    simp [Matrix.mulVec, dotProduct]
    ring

/-- Explicit active-leading component of an outward kernel direction for an
arbitrary reduced radial column. -/
def quittingTwoOwnerOutwardLeadingDirection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι) (radialColumn : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-radialColumn 1 /
      quittingActiveMixingPairJoinEffect reward second first,
    -radialColumn 0 /
      quittingActiveMixingPairJoinEffect reward first second]

omit [Fintype ι] in
/-- In the regular branch, radial coordinate one together with the explicit
leading direction kills every reduced active row. -/
theorem quittingTwoOwnerSupportJacobian_mulVec_outwardLeadingDirection
    (first second : ι) (radialColumn : Fin 2 → ℝ)
    (hforward :
      quittingActiveMixingPairJoinEffect reward first second ≠ 0)
    (hreverse :
      quittingActiveMixingPairJoinEffect reward second first ≠ 0) :
    (quittingTwoOwnerSupportJacobian reward first second).mulVec
        (quittingTwoOwnerOutwardLeadingDirection reward first second
          radialColumn) + radialColumn = 0 := by
  funext row
  fin_cases row
  · simp [quittingTwoOwnerOutwardLeadingDirection]
    field_simp [hforward]
    ring
  · simp [quittingTwoOwnerOutwardLeadingDirection]
    field_simp [hreverse]
    ring

omit [Fintype ι] in
/-- A positive directed pair-join pivot has a sharp reciprocal
classification: zero reciprocal effect is the singular residue, positive
reciprocal effect gives negative determinant, and negative reciprocal effect
gives positive determinant. -/
theorem quittingTwoOwnerSupportJacobian_trichotomy_of_forward_pos
    (first second : ι)
    (hforward :
      0 < quittingActiveMixingPairJoinEffect reward first second) :
    (quittingActiveMixingPairJoinEffect reward second first = 0 ∧
      Matrix.det (quittingTwoOwnerSupportJacobian reward first second) = 0) ∨
    (0 < quittingActiveMixingPairJoinEffect reward second first ∧
      Matrix.det (quittingTwoOwnerSupportJacobian reward first second) < 0) ∨
    (quittingActiveMixingPairJoinEffect reward second first < 0 ∧
      0 < Matrix.det
        (quittingTwoOwnerSupportJacobian reward first second)) := by
  rw [quittingTwoOwnerSupportJacobian_det]
  rcases lt_trichotomy
      (quittingActiveMixingPairJoinEffect reward second first) 0 with
    hnegative | hzero | hpositive
  · exact Or.inr (Or.inr ⟨hnegative, by nlinarith⟩)
  · exact Or.inl ⟨hzero, by simp [hzero]⟩
  · exact Or.inr (Or.inl ⟨hpositive, by nlinarith⟩)

namespace QuittingChargeTangentPacket

/-- In a literal two-owner positive support, compatibility forces the forward
pair-join effect to vanish. -/
theorem pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_first
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst :
      quittingActivePairCompatibilityResidual packet first = 0) :
    quittingActiveMixingPairJoinEffect reward first second = 0 := by
  have hcollapse :=
    packet.activePairCompatibilityResidual_eq_sum_pairJoinEffect first hfirst
  rw [hcompatFirst] at hcollapse
  have hsum :
      (∑ owner ∈ Finset.univ.erase first,
        packet.mass owner *
          quittingActiveMixingPairJoinEffect reward first owner) =
        packet.mass second *
          quittingActiveMixingPairJoinEffect reward first second := by
    apply Finset.sum_eq_single second
    · intro owner howner hownerSecond
      have hownerFirst : owner ≠ first := (Finset.mem_erase.mp howner).1
      simp [houtside owner hownerFirst hownerSecond]
    · intro hsecondMem
      exact (hsecondMem (by simp [hne.symm])).elim
  rw [hsum] at hcollapse
  exact (mul_eq_zero.mp hcollapse.symm).resolve_left hsecond.ne'

/-- In a literal two-owner positive support, compatibility forces the reverse
pair-join effect to vanish as well. -/
theorem pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_second
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatSecond :
      quittingActivePairCompatibilityResidual packet second = 0) :
    quittingActiveMixingPairJoinEffect reward second first = 0 := by
  exact packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_first
    second first hne.symm hsecond hfirst
      (fun owner hownerSecond hownerFirst =>
        houtside owner hownerFirst hownerSecond) hcompatSecond

/-- **Two-owner compatible singularity.**  If two distinct owners are the
entire positive support and both active rows are compatible, the reduced
support Jacobian is the zero matrix. -/
theorem twoOwnerSupportJacobian_eq_zero_of_compatible
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst :
      quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond :
      quittingActivePairCompatibilityResidual packet second = 0) :
    quittingTwoOwnerSupportJacobian reward first second = 0 := by
  have hforward :=
    packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_first
      first second hne hfirst hsecond houtside hcompatFirst
  have hreverse :=
    packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_second
      first second hne hfirst hsecond houtside hcompatSecond
  funext row column
  fin_cases row <;> fin_cases column <;> simp [hforward, hreverse]

/-- In particular, the compatible two-owner reduced support Jacobian is
singular, so the regular first-blow-up arc theorem cannot be discharged from
this chart. -/
theorem twoOwnerSupportJacobian_det_eq_zero_of_compatible
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst :
      quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond :
      quittingActivePairCompatibilityResidual packet second = 0) :
    Matrix.det (quittingTwoOwnerSupportJacobian reward first second) = 0 := by
  rw [packet.twoOwnerSupportJacobian_eq_zero_of_compatible first second hne
    hfirst hsecond houtside hcompatFirst hcompatSecond]
  simp

omit [Fintype ι] in
/-- When both pair-join effects vanish, reciprocal collision increment is
the negative of reciprocal singleton solo effect. -/
theorem reciprocalCollisionIncrement_eq_neg_reciprocalSoloEffect_of_pairJoin_zero
    (first second : ι)
    (hforward :
      quittingActiveMixingPairJoinEffect reward first second = 0)
    (hreverse :
      quittingActiveMixingPairJoinEffect reward second first = 0) :
    quittingActiveMixingCollisionIncrement reward first second +
        quittingActiveMixingCollisionIncrement reward second first =
      -(quittingSingletonSoloEffect reward first second +
        quittingSingletonSoloEffect reward second first) := by
  have hfirstDecompose :=
    quittingActiveMixingPairJoinEffect_eq_solo_add_collisionIncrement
      (reward := reward) first second
  have hsecondDecompose :=
    quittingActiveMixingPairJoinEffect_eq_solo_add_collisionIncrement
      (reward := reward) second first
  rw [hforward] at hfirstDecompose
  rw [hreverse] at hsecondDecompose
  linarith

/-- The negative reciprocal-collision dispatch on a compatible literal
two-owner support is exactly positive reciprocal singleton energy together
with a zero support Jacobian; it is a singular residue, not a regular arc. -/
theorem twoOwner_singular_and_reciprocalSoloEffect_pos_of_compatible_collision_neg
    (packet : QuittingChargeTangentPacket reward) (first second : ι)
    (hne : first ≠ second)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst :
      quittingActivePairCompatibilityResidual packet first = 0)
    (hcompatSecond :
      quittingActivePairCompatibilityResidual packet second = 0)
    (hcollision :
      quittingActiveMixingCollisionIncrement reward first second +
        quittingActiveMixingCollisionIncrement reward second first < 0) :
    quittingTwoOwnerSupportJacobian reward first second = 0 ∧
      0 < quittingSingletonSoloEffect reward first second +
        quittingSingletonSoloEffect reward second first := by
  have hforward :=
    packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_first
      first second hne hfirst hsecond houtside hcompatFirst
  have hreverse :=
    packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_second
      first second hne hfirst hsecond houtside hcompatSecond
  refine ⟨packet.twoOwnerSupportJacobian_eq_zero_of_compatible first second hne
      hfirst hsecond houtside hcompatFirst hcompatSecond, ?_⟩
  have hidentity :=
    reciprocalCollisionIncrement_eq_neg_reciprocalSoloEffect_of_pairJoin_zero
      (reward := reward) first second hforward hreverse
  linarith

end QuittingChargeTangentPacket

end GameTheory
