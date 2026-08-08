/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.SupportWitnessPathCompiler
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium

/-!
# Periodic support-witness cycles

This file supplies the finite-to-infinite adapter needed to consume Simon's
periodic alternative.  A finite cycle retains, at every phase,

* the product root witnessing the `Fδ` step;
* the exact cyclic policy-evaluation value;
* support-local `δ` optimality of the actions actually used; and
* approximate individual rationality.

If one phase has positive absorption, exact cyclic policy evaluation is
uniquely selected by the terminal payoff of the periodically repeated roots.
Starting the infinite path at that absorbing phase then has a positive total
absorption charge once every cycle, so the charge series diverges.  The finite
cycle therefore produces exactly the witness-retaining divergent path
consumed by `QuittingSupportWitnessPathCompiler`.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite witness-retaining version of a periodic `Fδ` cycle.

`value phase` is the payoff entering `phase`; `cycle phase` is the root played
there.  The next continuation is read at `finRotate K phase`. -/
def IsQuittingFiniteSupportRationalCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (supportError rationalityError : ℝ) : Prop :=
  (∀ phase,
    value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase)) ∧
  (∀ phase,
    IsQuittingRootSupportApproxNash reward
      (value (finRotate K phase)) supportError (cycle phase)) ∧
  ∀ target phase,
    quittingPunishmentValue reward target - rationalityError ≤
      value phase target

omit [DecidableEq ι] in
/-- A periodically repeated root cycle with one positive-absorption phase has
nonsummable total absorption charge.  The path is started at that phase, so
the same positive charge appears at every multiple of the period. -/
theorem
    not_summable_quittingTotalAbsorptionCharge_cyclicRootSequence_of_pos
    (cycle : Fin K → ι → PMF Bool) (absorbingPhase : Fin K)
    (habsorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)) :
    ¬Summable (quittingTotalAbsorptionCharge
      (quittingCyclicRootSequence cycle absorbingPhase)) := by
  intro hsummable
  have htendsto := hsummable.tendsto_atTop_zero
  have hhalf : 0 < quittingRootAbsorptionMass (cycle absorbingPhase) / 2 := by
    linarith
  have heventually : ∀ᶠ time : ℕ in atTop,
      quittingTotalAbsorptionCharge
          (quittingCyclicRootSequence cycle absorbingPhase) time <
        quittingRootAbsorptionMass (cycle absorbingPhase) / 2 :=
    (tendsto_order.1 htendsto).2 _ hhalf
  obtain ⟨threshold, hthreshold⟩ :=
    Filter.eventually_atTop.1 heventually
  have hK : 1 ≤ K := Nat.succ_le_iff.mpr absorbingPhase.pos
  have htime : threshold ≤ threshold * K := by
    simpa using Nat.mul_le_mul_left threshold hK
  have hsmall := hthreshold (threshold * K) htime
  have hperiod :
      quittingTotalAbsorptionCharge
          (quittingCyclicRootSequence cycle absorbingPhase) (threshold * K) =
        quittingRootAbsorptionMass (cycle absorbingPhase) := by
    simp [quittingTotalAbsorptionCharge, quittingCyclicRootSequence,
      quittingCyclicOrbit_mul_card]
  rw [hperiod] at hsmall
  linarith

/-- **Finite periodic cycle to divergent infinite path.**

One positive-absorption phase pins the finite cyclic values to the terminal
values selected by periodic repetition.  The repeated roots then preserve the
support witness and individual-rationality inequalities at every chronological
continuation, while their total absorption charge diverges. -/
theorem exists_supportRationalDivergentPath_of_finiteSupportRationalCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    {supportError rationalityError : ℝ}
    (hcycle : IsQuittingFiniteSupportRationalCycle reward cycle value
      supportError rationalityError)
    (absorbingPhase : Fin K)
    (habsorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan supportError ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      ∀ target time,
        quittingPunishmentValue reward target - rationalityError ≤
          quittingRootSequenceTerminalValue reward plan target time := by
  rcases hcycle with ⟨hpolicy, hsupport, hir⟩
  have hcontract :
      (∏ phase : Fin K,
        quittingStationaryContinueMass (cycle phase)) < 1 :=
    prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
      cycle absorbingPhase habsorbing
  have hselected :
      value = quittingCyclicTerminalValue reward cycle :=
    eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
      reward cycle value hpolicy hcontract
  let plan : ℕ → ι → PMF Bool :=
    quittingCyclicRootSequence cycle absorbingPhase
  refine ⟨plan, ?_, ?_, ?_⟩
  · intro stage
    have htail :
        quittingRootSequenceTailVector reward plan (stage + 1) =
          value (finRotate K
            (quittingCyclicOrbit absorbingPhase stage)) := by
      funext who
      change quittingRootSequenceTerminalValue reward
        (quittingCyclicRootSequence cycle absorbingPhase) who (stage + 1) = _
      rw [quittingRootSequenceTerminalValue_cyclic_eq]
      rw [← hselected]
      rw [quittingCyclicOrbit_succ]
    have hphase := hsupport (quittingCyclicOrbit absorbingPhase stage)
    simpa only [plan, quittingCyclicRootSequence, htail] using hphase
  · exact
      not_summable_quittingTotalAbsorptionCharge_cyclicRootSequence_of_pos
        cycle absorbingPhase habsorbing
  · intro target time
    change quittingPunishmentValue reward target - rationalityError ≤
      quittingRootSequenceTerminalValue reward
        (quittingCyclicRootSequence cycle absorbingPhase) target time
    rw [quittingRootSequenceTerminalValue_cyclic_eq]
    rw [← hselected]
    exact hir target (quittingCyclicOrbit absorbingPhase time)

/-- A finite support-rational cycle directly yields Simon's `3ε` conclusion
under the same two-tolerance overhead condition as the infinite-path
compiler. -/
theorem
    exists_isThreeEpsilonAsymptoticNash_of_finiteSupportRationalCycle
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hcycle : IsQuittingFiniteSupportRationalCycle reward cycle value δ ε)
    (absorbingPhase : Fin K)
    (habsorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase))
    (hoverhead :
      2 * δ + Real.sqrt δ *
        (2 + 7 * quittingRewardBound reward) ≤ 2 * ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (3 * ε) profile := by
  obtain ⟨plan, hsupport, hdiverges, hir⟩ :=
    exists_supportRationalDivergentPath_of_finiteSupportRationalCycle
      reward cycle value hcycle absorbingPhase habsorbing
  exact
    exists_isThreeEpsilonAsymptoticNash_of_divergentAbsorption_supportRationalPath
      reward plan hδ hε hsupport hdiverges hir hoverhead

/-- **Uniform payoff from finite periodic witness cycles.**

If every positive support tolerance admits a finite witness-retaining cycle
which is rational to the same tolerance and has one positive-absorption phase,
then the periodic adapter supplies the divergent paths consumed by the path
compiler at every accuracy. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_finiteSupportRationalCycles
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcycles : ∀ δ : ℝ, 0 < δ →
      ∃ K : ℕ,
        ∃ cycle : Fin K → ι → PMF Bool,
          ∃ value : Fin K → Payoff ι,
            ∃ absorbingPhase : Fin K,
              IsQuittingFiniteSupportRationalCycle reward cycle value δ δ ∧
              0 < quittingRootAbsorptionMass (cycle absorbingPhase)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths
    reward
  intro δ hδ
  obtain ⟨K, cycle, value, absorbingPhase, hcycle, habsorbing⟩ :=
    hcycles δ hδ
  exact exists_supportRationalDivergentPath_of_finiteSupportRationalCycle
    reward cycle value hcycle absorbingPhase habsorbing

end GameTheory
