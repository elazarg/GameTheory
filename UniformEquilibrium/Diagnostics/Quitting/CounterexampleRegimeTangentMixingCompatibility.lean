/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacketEnergy

/-!
# First-order active-mixing compatibility of a tangent packet

For the first-order ansatz with quit hazards `x = t * a` and continuation
value `boundary + t * u`, the active mixing row for receiver `who` contains

`tangent who + sum_{owner != who} mass owner *
  (r_who({who, owner}) - r_who({owner}))`.

On positive mass, packet pinning turns the tangent into the singleton
solo-effect average.  The displayed row therefore collapses exactly to the
mass-weighted pair-join effect

`sum_{owner != who} mass owner *
  (r_who({who, owner}) - r_who({who}))`.

Thus the singleton packet identities do not make the first-order mixing rows
vanish.  If they do vanish, singleton energy must instead be cancelled by the
collision-increment energy.  Under an active positive tangent this forces a
negative reciprocal collision-increment pair.  If a row does not vanish, a
supported directed pair has the same strict sign, and the canonical finite
sign functional strictly separates the active residual vector from zero.

All results here are finite algebraic identities.  They neither construct a
product-root arc nor assert that the separating functional satisfies the
additional annihilation and sign conditions of a strategic Farkas
certificate.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The terminal coalition in which `who` and `owner` quit. -/
def quittingPairJoinTerminal (who owner : ι) :
    {S : Finset ι // S.Nonempty} :=
  ⟨{who, owner}, by simp⟩

omit [Fintype ι] in
@[simp]
theorem quittingPairJoinTerminal_self (who : ι) :
    quittingPairJoinTerminal who who = quittingSingletonTerminal who := by
  apply Subtype.ext
  simp [quittingPairJoinTerminal, quittingSingletonTerminal]

/-- The collision marginal in the literal first-order active-mixing row:
adding receiver `who` to owner `owner`'s singleton exit. -/
def quittingActiveMixingCollisionIncrement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  reward (quittingPairJoinTerminal who owner) who -
    reward (quittingSingletonTerminal owner) who

/-- The pair-join effect isolated after the packet tangent identity is used:
the `{who, owner}` payoff relative to `who`'s own singleton payoff. -/
def quittingActiveMixingPairJoinEffect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  reward (quittingPairJoinTerminal who owner) who -
    reward (quittingSingletonTerminal who) who

omit [Fintype ι] in
@[simp]
theorem quittingActiveMixingPairJoinEffect_self (who : ι) :
    quittingActiveMixingPairJoinEffect reward who who = 0 := by
  simp [quittingActiveMixingPairJoinEffect]

omit [Fintype ι] in
/-- Adding a receiver to its own singleton exit has zero collision
increment. -/
@[simp]
theorem quittingActiveMixingCollisionIncrement_self (who : ι) :
    quittingActiveMixingCollisionIncrement reward who who = 0 := by
  simp [quittingActiveMixingCollisionIncrement]

omit [Fintype ι] in
/-- A pair-join effect is singleton solo motion plus the literal collision
increment. -/
theorem quittingActiveMixingPairJoinEffect_eq_solo_add_collisionIncrement
    (who owner : ι) :
    quittingActiveMixingPairJoinEffect reward who owner =
      quittingSingletonSoloEffect reward who owner +
        quittingActiveMixingCollisionIncrement reward who owner := by
  unfold quittingActiveMixingPairJoinEffect
    quittingSingletonSoloEffect quittingActiveMixingCollisionIncrement
  ring

/-- The unscaled first-order active-mixing compatibility row of a tangent
packet. -/
def quittingActivePairCompatibilityResidual
    (packet : QuittingChargeTangentPacket reward) (who : ι) : ℝ :=
  packet.tangent who +
    ∑ owner ∈ Finset.univ.erase who,
      packet.mass owner *
        quittingActiveMixingCollisionIncrement reward who owner

namespace QuittingChargeTangentPacket

/-- At a positive-mass receiver, the packet tangent is exactly its
mass-weighted singleton solo-effect row. -/
theorem tangent_eq_sum_mass_mul_soloEffect
    (packet : QuittingChargeTangentPacket reward) (who : ι)
    (hmass : 0 < packet.mass who) :
    packet.tangent who =
      ∑ owner, packet.mass owner *
        quittingSingletonSoloEffect reward who owner := by
  rw [sum_mass_mul_quittingSingletonSoloEffect_eq
    reward packet.mass packet.mass_sum who]
  rw [packet.tangent_eq who,
    packet.positive_mass_pins_boundary who hmass]

/-- **Active-row collapse.**  On positive support, the first-order
compatibility row is precisely the mass-weighted pair-join effect. -/
theorem activePairCompatibilityResidual_eq_sum_pairJoinEffect
    (packet : QuittingChargeTangentPacket reward) (who : ι)
    (hmass : 0 < packet.mass who) :
    quittingActivePairCompatibilityResidual packet who =
      ∑ owner ∈ Finset.univ.erase who,
        packet.mass owner *
          quittingActiveMixingPairJoinEffect reward who owner := by
  rw [quittingActivePairCompatibilityResidual,
    packet.tangent_eq_sum_mass_mul_soloEffect who hmass]
  have hsoloErase :
      (∑ owner, packet.mass owner *
          quittingSingletonSoloEffect reward who owner) =
        ∑ owner ∈ Finset.univ.erase who,
          packet.mass owner *
            quittingSingletonSoloEffect reward who owner := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
    simp
  rw [hsoloErase, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro owner howner
  rw [← mul_add,
    ← quittingActiveMixingPairJoinEffect_eq_solo_add_collisionIncrement]

/-- A strictly positive active row has a positive supported outsider
pair-join effect. -/
theorem exists_supported_outsider_pos_pairJoinEffect_of_residual_pos
    (packet : QuittingChargeTangentPacket reward) (who : ι)
    (hmass : 0 < packet.mass who)
    (hresidual : 0 < quittingActivePairCompatibilityResidual packet who) :
    ∃ owner, owner ≠ who ∧ 0 < packet.mass owner ∧
      0 < quittingActiveMixingPairJoinEffect reward who owner := by
  rw [packet.activePairCompatibilityResidual_eq_sum_pairJoinEffect who hmass]
    at hresidual
  by_contra hno
  push Not at hno
  have hnonpos :
      (∑ owner ∈ Finset.univ.erase who,
        packet.mass owner *
          quittingActiveMixingPairJoinEffect reward who owner) ≤ 0 := by
    apply Finset.sum_nonpos
    intro owner howner
    have hne : owner ≠ who := by
      simpa using (Finset.mem_erase.mp howner).1
    by_cases hownerMass : 0 < packet.mass owner
    · exact mul_nonpos_of_nonneg_of_nonpos (packet.mass_nonneg owner)
        (hno owner hne hownerMass)
    · have hzero : packet.mass owner = 0 :=
        le_antisymm (le_of_not_gt hownerMass) (packet.mass_nonneg owner)
      simp [hzero]
  linarith

/-- A strictly negative active row has a negative supported outsider
pair-join effect. -/
theorem exists_supported_outsider_neg_pairJoinEffect_of_residual_neg
    (packet : QuittingChargeTangentPacket reward) (who : ι)
    (hmass : 0 < packet.mass who)
    (hresidual : quittingActivePairCompatibilityResidual packet who < 0) :
    ∃ owner, owner ≠ who ∧ 0 < packet.mass owner ∧
      quittingActiveMixingPairJoinEffect reward who owner < 0 := by
  rw [packet.activePairCompatibilityResidual_eq_sum_pairJoinEffect who hmass]
    at hresidual
  by_contra hno
  push Not at hno
  have hnonneg :
      0 ≤ ∑ owner ∈ Finset.univ.erase who,
        packet.mass owner *
          quittingActiveMixingPairJoinEffect reward who owner := by
    apply Finset.sum_nonneg
    intro owner howner
    have hne : owner ≠ who := by
      simpa using (Finset.mem_erase.mp howner).1
    by_cases hownerMass : 0 < packet.mass owner
    · exact mul_nonneg (packet.mass_nonneg owner)
        (hno owner hne hownerMass)
    · have hzero : packet.mass owner = 0 :=
        le_antisymm (le_of_not_gt hownerMass) (packet.mass_nonneg owner)
      simp [hzero]
  linarith

end QuittingChargeTangentPacket

/-- Quadratic energy of the literal collision-increment matrix. -/
def quittingActiveMixingCollisionEnergy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) : ℝ :=
  ∑ who, mass who * ∑ owner, mass owner *
    quittingActiveMixingCollisionIncrement reward who owner

/-- Quadratic energy of the pair-join matrix isolated by active-row
collapse. -/
def quittingActiveMixingPairJoinEnergy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) : ℝ :=
  ∑ who, mass who * ∑ owner, mass owner *
    quittingActiveMixingPairJoinEffect reward who owner

/-- Pair-join energy splits into singleton packet energy and literal
collision-increment energy. -/
theorem quittingActiveMixingPairJoinEnergy_eq_singleton_add_collision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) :
    quittingActiveMixingPairJoinEnergy reward mass =
      quittingSingletonPacketQuadraticEnergy reward mass +
        quittingActiveMixingCollisionEnergy reward mass := by
  unfold quittingActiveMixingPairJoinEnergy
    quittingSingletonPacketQuadraticEnergy
    quittingActiveMixingCollisionEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro who _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro owner _
  rw [← mul_add,
    ← quittingActiveMixingPairJoinEffect_eq_solo_add_collisionIncrement]

namespace QuittingChargeTangentPacket

/-- Complementarity weighted by packet mass: the packet tangent and its
singleton quadratic energy have the same total pairing, without any sign
assumption on the tangent. -/
theorem sum_mass_mul_tangent_eq_singletonEnergy
    (packet : QuittingChargeTangentPacket reward) :
    (∑ who, packet.mass who * packet.tangent who) =
      quittingSingletonPacketQuadraticEnergy reward packet.mass := by
  unfold quittingSingletonPacketQuadraticEnergy
  apply Finset.sum_congr rfl
  intro who _
  by_cases hmass : 0 < packet.mass who
  · rw [packet.tangent_eq_sum_mass_mul_soloEffect who hmass]
  · have hzero : packet.mass who = 0 :=
      le_antisymm (le_of_not_gt hmass) (packet.mass_nonneg who)
    simp [hzero]

/-- The mass-weighted sum of the first-order compatibility rows is exactly
the pair-join energy. -/
theorem sum_mass_mul_activePairCompatibilityResidual_eq_pairJoinEnergy
    (packet : QuittingChargeTangentPacket reward) :
    (∑ who, packet.mass who *
      quittingActivePairCompatibilityResidual packet who) =
        quittingActiveMixingPairJoinEnergy reward packet.mass := by
  calc
    (∑ who, packet.mass who *
      quittingActivePairCompatibilityResidual packet who) =
        (∑ who, packet.mass who * packet.tangent who) +
          quittingActiveMixingCollisionEnergy reward packet.mass := by
      unfold quittingActivePairCompatibilityResidual
        quittingActiveMixingCollisionEnergy
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro who _
      rw [mul_add]
      congr 1
      rw [Finset.sum_erase]
      simp
    _ = quittingSingletonPacketQuadraticEnergy reward packet.mass +
          quittingActiveMixingCollisionEnergy reward packet.mass := by
      rw [packet.sum_mass_mul_tangent_eq_singletonEnergy]
    _ = quittingActiveMixingPairJoinEnergy reward packet.mass := by
      rw [quittingActiveMixingPairJoinEnergy_eq_singleton_add_collision]

/-- If every positive-mass first-order row is compatible, pair-join energy
vanishes. -/
theorem pairJoinEnergy_eq_zero_of_active_compatible
    (packet : QuittingChargeTangentPacket reward)
    (hcompatible : ∀ who, 0 < packet.mass who →
      quittingActivePairCompatibilityResidual packet who = 0) :
    quittingActiveMixingPairJoinEnergy reward packet.mass = 0 := by
  rw [← packet.sum_mass_mul_activePairCompatibilityResidual_eq_pairJoinEnergy]
  apply Finset.sum_eq_zero
  intro who _
  by_cases hmass : 0 < packet.mass who
  · simp [hcompatible who hmass]
  · have hzero : packet.mass who = 0 :=
      le_antisymm (le_of_not_gt hmass) (packet.mass_nonneg who)
    simp [hzero]

/-- Exact weighted cancellation forced by active compatibility: collision
increments pay the negative of the singleton packet energy. -/
theorem collisionEnergy_eq_neg_singletonEnergy_of_active_compatible
    (packet : QuittingChargeTangentPacket reward)
    (hcompatible : ∀ who, 0 < packet.mass who →
      quittingActivePairCompatibilityResidual packet who = 0) :
    quittingActiveMixingCollisionEnergy reward packet.mass =
      -quittingSingletonPacketQuadraticEnergy reward packet.mass := by
  have hzero := packet.pairJoinEnergy_eq_zero_of_active_compatible hcompatible
  rw [quittingActiveMixingPairJoinEnergy_eq_singleton_add_collision] at hzero
  linarith

end QuittingChargeTangentPacket

omit [DecidableEq ι] in
/-- A negative quadratic energy of a finite matrix with zero diagonal forces
a negative reciprocal pair in the positive support.  This generic finite
lemma is the sign-reversed counterpart of the singleton packet energy
argument. -/
theorem exists_supported_pair_neg_reciprocal_of_quadraticEnergy_neg
    (mass : ι → ℝ) (matrix : ι → ι → ℝ)
    (hmass : ∀ who, 0 ≤ mass who)
    (hdiag : ∀ who, matrix who who = 0)
    (henergy :
      (∑ who, mass who * ∑ owner, mass owner * matrix who owner) < 0) :
    ∃ who owner, 0 < mass who ∧ 0 < mass owner ∧ who ≠ owner ∧
      matrix who owner + matrix owner who < 0 := by
  classical
  by_contra hno
  push Not at hno
  have henergy' :
      (∑ who, ∑ owner,
        mass who * mass owner * matrix who owner) < 0 := by
    simpa only [Finset.mul_sum, mul_assoc] using henergy
  have henergyNonneg :
      0 ≤ ∑ who, ∑ owner,
        mass who * mass owner *
          (matrix who owner + matrix owner who) := by
    apply Finset.sum_nonneg
    intro who _
    by_cases hwho : 0 < mass who
    · apply Finset.sum_nonneg
      intro owner _
      by_cases howner : 0 < mass owner
      · apply mul_nonneg (mul_nonneg (hmass who) (hmass owner))
        by_cases heq : who = owner
        · subst owner
          simp [hdiag]
        · exact hno who owner hwho howner heq
      · have hzero : mass owner = 0 :=
          le_antisymm (le_of_not_gt howner) (hmass owner)
        simp [hzero]
    · have hzero : mass who = 0 :=
        le_antisymm (le_of_not_gt hwho) (hmass who)
      simp [hzero]
  have hswap :
      (∑ who, ∑ owner,
        mass who * mass owner * matrix owner who) =
        ∑ who, ∑ owner,
          mass who * mass owner * matrix who owner := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro who _
    apply Finset.sum_congr rfl
    intro owner _
    ring
  have htwice :
      (∑ who, ∑ owner,
        mass who * mass owner *
          (matrix who owner + matrix owner who)) =
        2 * ∑ who, ∑ owner,
          mass who * mass owner * matrix who owner := by
    calc
      (∑ who, ∑ owner,
        mass who * mass owner *
          (matrix who owner + matrix owner who)) =
          (∑ who, ∑ owner,
            mass who * mass owner * matrix who owner) +
          (∑ who, ∑ owner,
            mass who * mass owner * matrix owner who) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      _ = (∑ who, ∑ owner,
            mass who * mass owner * matrix who owner) +
          (∑ who, ∑ owner,
            mass who * mass owner * matrix who owner) := by
        rw [hswap]
      _ = 2 * ∑ who, ∑ owner,
          mass who * mass owner * matrix who owner := by ring
  rw [htwice] at henergyNonneg
  linarith

/-- Under active compatibility, an active positive tangent forces a
supported pair whose reciprocal literal collision increment is negative. -/
theorem QuittingChargeTangentPacket.exists_supported_pair_neg_reciprocalCollisionIncrement
    (packet : QuittingChargeTangentPacket reward)
    (htangent : ∀ who, 0 ≤ packet.tangent who)
    (active : ι) (hmass : 0 < packet.mass active)
    (hactive : 0 < packet.tangent active)
    (hcompatible : ∀ who, 0 < packet.mass who →
      quittingActivePairCompatibilityResidual packet who = 0) :
    ∃ who owner,
      0 < packet.mass who ∧ 0 < packet.mass owner ∧ who ≠ owner ∧
        quittingActiveMixingCollisionIncrement reward who owner +
          quittingActiveMixingCollisionIncrement reward owner who < 0 := by
  have hterm : 0 < packet.mass active * packet.tangent active :=
    mul_pos hmass hactive
  have hweighted : 0 < ∑ who, packet.mass who * packet.tangent who :=
    hterm.trans_le <| Finset.single_le_sum
      (fun who _ => mul_nonneg (packet.mass_nonneg who) (htangent who))
      (Finset.mem_univ active)
  have hsingleton :
      0 < quittingSingletonPacketQuadraticEnergy reward packet.mass := by
    rw [← packet.sum_mass_mul_tangent_eq_singletonEnergy]
    exact hweighted
  have hcollision :
      quittingActiveMixingCollisionEnergy reward packet.mass < 0 := by
    rw [packet.collisionEnergy_eq_neg_singletonEnergy_of_active_compatible
      hcompatible]
    linarith
  exact exists_supported_pair_neg_reciprocal_of_quadraticEnergy_neg
    packet.mass (quittingActiveMixingCollisionIncrement reward)
      packet.mass_nonneg
        (quittingActiveMixingCollisionIncrement_self (reward := reward))
        hcollision

/-- The canonical finite sign functional on the active compatibility rows.
Its coefficients lie in `{-1, 0, 1}`; inactive coordinates receive zero. -/
def quittingActiveCompatibilitySignFunctional
    (packet : QuittingChargeTangentPacket reward) : ι → ℝ :=
  fun who =>
    if 0 < packet.mass who then
      if 0 ≤ quittingActivePairCompatibilityResidual packet who then 1 else -1
    else 0

/-- Pairing the canonical sign functional with the residual vector is the
active-support `L1` defect. -/
theorem quittingActiveCompatibilitySignFunctional_pairing_eq
    (packet : QuittingChargeTangentPacket reward) :
    (∑ who, quittingActiveCompatibilitySignFunctional packet who *
      quittingActivePairCompatibilityResidual packet who) =
      ∑ who, if 0 < packet.mass who then
        |quittingActivePairCompatibilityResidual packet who| else 0 := by
  apply Finset.sum_congr rfl
  intro who _
  by_cases hmass : 0 < packet.mass who
  · simp only [quittingActiveCompatibilitySignFunctional, hmass, if_true]
    by_cases hresidual :
        0 ≤ quittingActivePairCompatibilityResidual packet who
    · simp [hresidual, abs_of_nonneg hresidual]
    · have hnegative :
          quittingActivePairCompatibilityResidual packet who < 0 :=
        lt_of_not_ge hresidual
      simp [hresidual, abs_of_neg hnegative]
  · simp [quittingActiveCompatibilitySignFunctional, hmass]

/-- Failure of active compatibility is strictly separated from zero by the
canonical finite sign functional. -/
theorem quittingActiveCompatibilitySignFunctional_pairing_pos_iff
    (packet : QuittingChargeTangentPacket reward) :
    0 < ∑ who, quittingActiveCompatibilitySignFunctional packet who *
      quittingActivePairCompatibilityResidual packet who ↔
      ∃ who, 0 < packet.mass who ∧
        quittingActivePairCompatibilityResidual packet who ≠ 0 := by
  rw [quittingActiveCompatibilitySignFunctional_pairing_eq]
  constructor
  · contrapose!
    intro hzero
    have hsumZero :
        (∑ who, if 0 < packet.mass who then
          |quittingActivePairCompatibilityResidual packet who| else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro who _
      by_cases hmass : 0 < packet.mass who
      · simp [hmass, hzero who hmass]
      · simp [hmass]
    rw [hsumZero]
  · rintro ⟨who, hmass, hresidual⟩
    apply Finset.sum_pos'
    · intro owner _
      split_ifs
      · exact abs_nonneg _
      · exact le_rfl
    · exact ⟨who, Finset.mem_univ who, by
        simp [hmass, abs_pos.mpr hresidual]⟩

/-- **Sharp finite active-mixing alternative.**  Either all active rows are
compatible, or a positive row exposes a positive supported pair-join pivot,
or a negative row exposes a negative supported pair-join pivot. -/
theorem QuittingChargeTangentPacket.activeMixingCompatibility_or_signedPivot
    (packet : QuittingChargeTangentPacket reward) :
    (∀ who, 0 < packet.mass who →
      quittingActivePairCompatibilityResidual packet who = 0) ∨
    (∃ who owner, 0 < packet.mass who ∧ owner ≠ who ∧
      0 < packet.mass owner ∧
      0 < quittingActivePairCompatibilityResidual packet who ∧
      0 < quittingActiveMixingPairJoinEffect reward who owner) ∨
    ∃ who owner, 0 < packet.mass who ∧ owner ≠ who ∧
      0 < packet.mass owner ∧
      quittingActivePairCompatibilityResidual packet who < 0 ∧
      quittingActiveMixingPairJoinEffect reward who owner < 0 := by
  by_cases hcompatible : ∀ who, 0 < packet.mass who →
      quittingActivePairCompatibilityResidual packet who = 0
  · exact Or.inl hcompatible
  · right
    push Not at hcompatible
    obtain ⟨who, hmass, hresidual⟩ := hcompatible
    rcases lt_or_gt_of_ne hresidual with hnegative | hpositive
    · right
      obtain ⟨owner, hne, hownerMass, hpair⟩ :=
        packet.exists_supported_outsider_neg_pairJoinEffect_of_residual_neg
          who hmass hnegative
      exact ⟨who, owner, hmass, hne, hownerMass, hnegative, hpair⟩
    · left
      obtain ⟨owner, hne, hownerMass, hpair⟩ :=
        packet.exists_supported_outsider_pos_pairJoinEffect_of_residual_pos
          who hmass hpositive
      exact ⟨who, owner, hmass, hne, hownerMass, hpositive, hpair⟩

end GameTheory
