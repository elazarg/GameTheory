/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCyclePinnedDebt
import GameTheory.Concepts.Stochastic.QuittingPeriodicCompiler
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformPayoffSelection

/-!
# An admissible absorbing cycle carries a terminal approximate equilibrium

`QuittingCyclePinnedDebt` isolates the carrier of the absorbing-cycle program:
an `IsQuittingCyclicContinuationBlock`, i.e. a finite exact Nash--Bellman block
which reproduces its own value at its origin and absorbs at some stage.
This file closes the remaining arrow of the conditional: *an admissible
absorbing block generates a behavior profile which is a terminal approximate
equilibrium at every accuracy*, in exactly the sense the landed
terminal-to-uniform consumer
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
requires, namely
`(quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε`.
That predicate quantifies over **all** behavioral deviations of the deviating
player, so nothing below is restricted to stopping-time deviations.

The infinite object is supplied at the *profile* level rather than at the
prescribed-value level: `quittingCyclicRootSequence` reads the block's rows
forever and `quittingCyclicBehaviorProfile` turns them into a behavior profile,
whose `quittingTerminalPayoff` is by definition `quittingCyclicTerminalValue`.
`QuittingCyclicPeriodicExtension`'s value-level extension is the same
construction read on prescribed values, and is not needed here.

## The two hypotheses

**(H1) absorbing cyclic continuation block.**  `IsQuittingCyclicContinuationBlock
reward terminal (period + 1) block`.  This is the carrier itself.

**(H2) zero deviation mismatch at every coordinate.**  This is supplied as an
explicit hypothesis and is *not* derived from (H1).  It is stated as
`IsQuittingCycleAdmissible`: for every coordinate `who`, either the deleted
(opponent) survival product around the cycle is strictly below one, or the solo
reward `r_who({who})` is nonnegative.

That disjunction is exactly the repository's own deviation-machinery branch
condition -- it is the `hbranch` argument of the umbrella local-to-global bound
`quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_zero_or_nonnegativeSolo`
-- and it is exactly the characterization of vanishing deviation mismatch
recorded in the program notes: the deleted survival product `P_who` of an
absorbing cycle is `1` only in the *isolated* configuration where every opponent
of `who` is silent at every phase, and there the mismatch is `[-r_who({who})]₊`,
so it vanishes precisely when `r_who({who}) ≥ 0`.

**(H2) is not redundant** -- *hand check, not formalized here.*  Take two
players, let player `1` quit with probability `1/2` at the single block stage
and player `2` never quit, and set `r_1({1}) = -1`, `r_1({2}) = r_1({1,2})` and
player `2`'s entries all `0`.  Every clause of
`IsQuittingCyclicContinuationBlock` holds: the endpoint difference vanishes at
player `1` (both his pure Quit and pure Continue pay `-1`) and player `2`'s
pure Quit pays `0`, which is his displayed value; the absorption mass is `1/2`.
The block's value at coordinate `1` is `-1`.  But player `1` can continue
forever, in which case nobody ever absorbs and he collects `0`, a gain of `1`.
Here `P_1 = 1` and `r_1({1}) < 0`, so (H2) fails at coordinate `1`, and the
periodic profile is *not* terminal `ε`-Nash for `ε < 1`.  So no theorem of this
shape can drop (H2), and (H2) is not derivable from (H1).

## What absorption alone does buy

The block's displayed value is pinned to the *realized* terminal payoff of the
generated profile by absorption alone: `quittingRootSuccessorPayoff` is affine
in the continuation with scalar linear part the joint all-continue mass, and one
absorbing stage makes the product of those masses around the cycle strictly less
than one.  This is
`eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing`, a strict
strengthening of the existing
`eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff`, whose hypothesis is the
*playerwise* contraction (the deleted masses dominate the joint mass, so the
playerwise hypothesis is the stronger one).

## Relation to the existing periodic compiler

`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate_finite`
already compiles a cyclic certificate to a terminal Nash profile, but under
playerwise contraction at *every* coordinate.  That hypothesis fails on the
program's own running example (the stationary row of the surgery table, where
the row's quitter has a silent opponent).  The results below replace it by
(H1) + (H2), which that example does satisfy.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Absorption alone selects the realized cyclic value -/

omit [DecidableEq ι] in
/-- One absorbing stage makes the product of the *joint* all-continue masses
around the cycle strictly below one.  This is the `Fin`-indexed companion of
`prod_quittingStationaryContinueMass_lt_one_of_absorbing`. -/
theorem prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
    (cycle : Fin K → ι → PMF Bool) (stage : Fin K)
    (habsorb : 0 < quittingRootAbsorptionMass (cycle stage)) :
    (∏ cyclePhase : Fin K, quittingStationaryContinueMass (cycle cyclePhase)) < 1 := by
  have hsplit := Finset.mul_prod_erase Finset.univ
    (fun cyclePhase ↦ quittingStationaryContinueMass (cycle cyclePhase))
    (Finset.mem_univ stage)
  have hle : (∏ cyclePhase ∈ Finset.univ.erase stage,
      quittingStationaryContinueMass (cycle cyclePhase)) ≤ 1 :=
    Finset.prod_le_one
      (fun cyclePhase _ ↦ quittingStationaryContinueMass_nonneg (cycle cyclePhase))
      (fun cyclePhase _ ↦ quittingStationaryContinueMass_le_one (cycle cyclePhase))
  have hnonneg : 0 ≤ quittingStationaryContinueMass (cycle stage) :=
    quittingStationaryContinueMass_nonneg (cycle stage)
  have hlt : quittingStationaryContinueMass (cycle stage) < 1 := by
    rw [quittingRootAbsorptionMass] at habsorb; linarith
  calc (∏ cyclePhase : Fin K, quittingStationaryContinueMass (cycle cyclePhase)) =
      quittingStationaryContinueMass (cycle stage) *
        ∏ cyclePhase ∈ Finset.univ.erase stage,
          quittingStationaryContinueMass (cycle cyclePhase) := hsplit.symm
    _ ≤ quittingStationaryContinueMass (cycle stage) * 1 :=
        mul_le_mul_of_nonneg_left hle hnonneg
    _ = quittingStationaryContinueMass (cycle stage) := mul_one _
    _ < 1 := hlt

omit [DecidableEq ι] in
/-- One cyclic step of the difference between a certified cyclic value and the
realized cyclic terminal value multiplies it by the joint all-continue mass. -/
theorem quittingCyclicValue_sub_terminalValue_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (hpolicy : ∀ cyclePhase, value cyclePhase = quittingRootSuccessorPayoff reward
      (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (who : ι) (cyclePhase : Fin K) :
    value cyclePhase who -
        quittingCyclicTerminalValue reward cycle cyclePhase who =
      quittingStationaryContinueMass (cycle cyclePhase) *
        (value (finRotate K cyclePhase) who -
          quittingCyclicTerminalValue reward cycle (finRotate K cyclePhase) who) := by
  have hvalue := congrFun (hpolicy cyclePhase) who
  have hterminal := congrFun
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward cycle cyclePhase) who
  rw [hvalue, hterminal, quittingRootSuccessorPayoff_sub_eq_continueMass_mul]

omit [DecidableEq ι] in
/-- Iterating the cyclic step: the phase difference is the joint prefix weight
times the difference at the rotated phase. -/
theorem quittingCyclicValue_sub_terminalValue_eq_prefixWeight_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (hpolicy : ∀ cyclePhase, value cyclePhase = quittingRootSuccessorPayoff reward
      (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (who : ι) (phase : Fin K) (fuel : ℕ) :
    value phase who - quittingCyclicTerminalValue reward cycle phase who =
      quittingCyclicPrefixWeight
          (fun cyclePhase ↦ quittingStationaryContinueMass (cycle cyclePhase))
          phase fuel *
        (value (quittingCyclicOrbit phase fuel) who -
          quittingCyclicTerminalValue reward cycle
            (quittingCyclicOrbit phase fuel) who) := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [ih, quittingCyclicPrefixWeight_succ, quittingCyclicOrbit_succ, mul_assoc]
      congr 1
      exact quittingCyclicValue_sub_terminalValue_step reward cycle value hpolicy who
        (quittingCyclicOrbit phase fuel)

omit [DecidableEq ι] in
/-- **Absorption alone pins the certified cyclic value to the realized one.**
The backward Bellman step is affine in the continuation with scalar linear part
the *joint* all-continue mass, so a single absorbing stage already makes the
one-turn composite a strict contraction.  Contrast
`eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff`, whose hypothesis is
playerwise contraction; the joint mass is dominated by every deleted mass
(`quittingStationaryContinueMass_le_fixedOpponentsContinueMass`), so the
hypothesis used here is the weaker one. -/
theorem eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (hpolicy : ∀ cyclePhase, value cyclePhase = quittingRootSuccessorPayoff reward
      (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (habsorb : (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1) :
    value = quittingCyclicTerminalValue reward cycle := by
  funext phase who
  have hkey := quittingCyclicValue_sub_terminalValue_eq_prefixWeight_mul
    reward cycle value hpolicy who phase K
  rw [quittingCyclicPrefixWeight_card, quittingCyclicOrbit_card] at hkey
  have hfactor : (value phase who -
        quittingCyclicTerminalValue reward cycle phase who) *
      (1 - ∏ cyclePhase : Fin K,
        quittingStationaryContinueMass (cycle cyclePhase)) = 0 := by
    have hexpand : (value phase who -
          quittingCyclicTerminalValue reward cycle phase who) *
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryContinueMass (cycle cyclePhase)) =
        (value phase who - quittingCyclicTerminalValue reward cycle phase who) -
          (∏ cyclePhase : Fin K,
            quittingStationaryContinueMass (cycle cyclePhase)) *
            (value phase who -
              quittingCyclicTerminalValue reward cycle phase who) := by ring
    rw [hexpand, ← hkey, sub_self]
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · exact absurd hzero (by linarith)

/-! ## Admissibility: zero deviation mismatch at a coordinate -/

/-- **Zero deviation mismatch at coordinate `who`.**  Either the deleted
(opponent) survival product around the cycle is strictly below one, or the solo
reward of `who` is nonnegative.

This is the branch condition of the repository's umbrella local-to-global bound
`quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_zero_or_nonnegativeSolo`,
and it is the characterization of vanishing deviation mismatch on an absorbing
cycle: the deleted product equals one only when every opponent of `who` is
silent at every phase, and in that isolated configuration the mismatch is
`max {0, r_who({who})} - r_who({who}) = [-r_who({who})]₊`. -/
def IsQuittingCycleZeroDeviationMismatchAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (who : ι) : Prop :=
  (∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1 ∨
    0 ≤ reward (quittingSingletonTerminal who) who

/-- **Admissible cycle.**  The deviation mismatch vanishes at every
coordinate. -/
def IsQuittingCycleAdmissible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) : Prop :=
  ∀ who : ι, IsQuittingCycleZeroDeviationMismatchAt reward cycle who

/-- Playerwise contraction is a sufficient, strictly stronger condition for
admissibility, so every certificate accepted by the existing periodic compiler
is accepted here. -/
theorem isQuittingCycleAdmissible_of_contracts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (hcontracts : ∀ who : ι, (∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1) :
    IsQuittingCycleAdmissible reward cycle :=
  fun who ↦ Or.inl (hcontracts who)

/-- On the non-contracting branch every deleted phase mass is one, so opponent
survival along the cyclic live path is identically one. -/
theorem quittingOpponentSurvivalWeight_cyclicRootSequence_eq_one_of_not_contracts
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (hcontracts : ¬ (∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1)
    (fuel : ℕ) :
    quittingOpponentSurvivalWeight
      (quittingCyclicRootSequence cycle phase) who 0 fuel = 1 := by
  set coefficient : Fin K → ℝ := fun cyclePhase ↦
    quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who with hcoef
  have hnonneg : ∀ cyclePhase, 0 ≤ coefficient cyclePhase := fun cyclePhase ↦
    quittingStationaryFixedOpponentsContinueMass_nonneg (cycle cyclePhase) who
  have hle : ∀ cyclePhase, coefficient cyclePhase ≤ 1 := fun cyclePhase ↦
    quittingStationaryContinueMass_le_one
      (Function.update (cycle cyclePhase) who (PMF.pure false))
  have hall : ∀ cyclePhase, coefficient cyclePhase = 1 := by
    intro cyclePhase
    by_contra hne
    have hlt : coefficient cyclePhase < 1 := lt_of_le_of_ne (hle cyclePhase) hne
    have hsplit := Finset.mul_prod_erase Finset.univ coefficient
      (Finset.mem_univ cyclePhase)
    have herase : (∏ other ∈ Finset.univ.erase cyclePhase, coefficient other) ≤ 1 :=
      Finset.prod_le_one (fun other _ ↦ hnonneg other) (fun other _ ↦ hle other)
    have hprod : (∏ other : Fin K, coefficient other) < 1 := by
      calc (∏ other : Fin K, coefficient other) =
          coefficient cyclePhase *
            ∏ other ∈ Finset.univ.erase cyclePhase, coefficient other := hsplit.symm
        _ ≤ coefficient cyclePhase * 1 :=
            mul_le_mul_of_nonneg_left herase (hnonneg cyclePhase)
        _ = coefficient cyclePhase := mul_one _
        _ < 1 := hlt
    exact hcontracts hprod
  rw [quittingOpponentSurvivalWeight_cyclicRootSequence, quittingCyclicPrefixWeight]
  rw [Finset.prod_congr rfl (fun offset _ ↦ hall _)]
  simp

/-! ## The admissible cyclic deviation bound -/

/-- **No unilateral hazard beats an admissible exactly-Nash cycle.**  This is
`quittingCyclicHazardTerminalValue_le_of_isZeroRootNash` with the playerwise
contraction hypothesis replaced by admissibility at the deviating coordinate.
The contracting branch is the existing one; the non-contracting branch is the
positive-survival branch of the umbrella bound, which needs the solo reward to
be nonnegative. -/
theorem quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (deviation : ℕ → PMF Bool)
    (hnash : ∀ cyclePhase, IsεQuittingRootNash reward
      (quittingCyclicTerminalValue reward cycle (finRotate K cyclePhase)) 0
      (cycle cyclePhase))
    (hadmissible : IsQuittingCycleZeroDeviationMismatchAt reward cycle who) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingCyclicRootSequence cycle phase) who deviation 0 ≤
      quittingCyclicTerminalValue reward cycle phase who := by
  set roots := quittingCyclicRootSequence cycle phase with hroots
  set prescribed := quittingRootSequenceTerminalValue reward roots who with hprescribed
  have hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0 :=
    fun time ↦ quittingPrescribedOneStepResidual_cyclic_eq_zero
      reward cycle phase who hnash time
  have hsummable : Summable (fun time ↦
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time) := by
    simpa only [hresidual, mul_zero] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  obtain ⟨limit, hlimit, hbranch⟩ :
      ∃ limit : ℝ,
        Tendsto (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit) ∧
          (limit = 0 ∨ 0 ≤ reward (quittingSingletonTerminal who) who) := by
    by_cases hcontracts : (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1
    · exact ⟨0, tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
        cycle phase who hcontracts, Or.inl rfl⟩
    · refine ⟨1, ?_, Or.inr (hadmissible.resolve_left hcontracts)⟩
      have hone : quittingOpponentSurvivalWeight roots who 0 = fun _ : ℕ ↦ (1 : ℝ) :=
        funext (quittingOpponentSurvivalWeight_cyclicRootSequence_eq_one_of_not_contracts
          cycle phase who hcontracts)
      rw [hone]
      exact tendsto_const_nhds
  have hgap :=
    quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_zero_or_nonnegativeSolo
      reward roots who deviation (quittingRewardBound reward) limit
      (quittingRewardBound_nonneg reward) (abs_reward_le_quittingRewardBound reward)
      hlimit hbranch hsummable
  have hsum : (∑' time, quittingOpponentSurvivalWeight roots who 0 time *
      quittingPrescribedOneStepResidual reward roots who prescribed time) = 0 := by
    simp only [hresidual, mul_zero, tsum_zero]
  rw [hsum] at hgap
  have hbase : quittingRootSequenceTerminalValue reward roots who 0 =
      quittingCyclicTerminalValue reward cycle phase who := by
    rw [hroots, quittingRootSequenceTerminalValue_cyclic_eq]
    simp
  linarith [hgap, hbase]

/-! ## The behavioral compiler under admissibility -/

/-- **Exact terminal Nash from an admissible absorbing cyclic certificate.**
Exact policy recursion, exact local root Nash, one absorbing stage, and
admissibility at every coordinate compile to an exactly terminal Nash behavior
profile against *all* behavioral deviations. -/
theorem isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_admissible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι) (phase : Fin K)
    (hpolicy : ∀ cyclePhase, value cyclePhase = quittingRootSuccessorPayoff reward
      (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (hnash : ∀ cyclePhase, IsεQuittingRootNash reward
      (value (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (habsorb : (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1)
    (hadmissible : IsQuittingCycleAdmissible reward cycle) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
    reward cycle value hpolicy habsorb
  have hnashTerminal : ∀ cyclePhase, IsεQuittingRootNash reward
      (quittingCyclicTerminalValue reward cycle (finRotate K cyclePhase)) 0
      (cycle cyclePhase) := by
    rw [← hvalue]; exact hnash
  intro who deviation
  have hhazard := quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible
    reward cycle phase who (quittingBehaviorLiveHazard reward deviation)
    hnashTerminal (hadmissible who)
  rw [← quittingTerminalPayoff_cyclicBehaviorProfile reward cycle phase] at hhazard
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingCyclicBehaviorProfile reward cycle phase) who deviation
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile] at hdeviation
  rw [hdeviation]
  simpa using hhazard

/-! ## From a cyclic continuation block to its periodic profile -/

/-- The cycle of rows played by a cyclic continuation block. -/
def quittingCyclicContinuationBlockCycle (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1)) :
    Fin (period + 1) → ι → PMF Bool :=
  fun stage ↦ quittingRootOfSimplex (block (Fin.castSucc stage)).2

/-- The cycle of displayed values of a cyclic continuation block. -/
def quittingCyclicContinuationBlockValue (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1)) :
    Fin (period + 1) → Payoff ι :=
  fun stage ↦ (block (Fin.castSucc stage)).1

omit [Fintype ι] [DecidableEq ι] in
/-- `finRotate` is one step of the cyclic orbit. -/
theorem finRotate_eq_quittingCyclicOrbit_one (phase : Fin K) :
    finRotate K phase = quittingCyclicOrbit phase 1 := by
  rw [quittingCyclicOrbit_succ, quittingCyclicOrbit_zero]

/-- The value at the rotated stage of a cyclic continuation block is the
block's next displayed value.  At the last stage this is where the block's
self-reproduction is consumed. -/
theorem quittingCyclicContinuationBlockValue_finRotate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (stage : Fin (period + 1)) :
    quittingCyclicContinuationBlockValue period block
        (finRotate (period + 1) stage) =
      (block (Fin.succ stage)).1 := by
  have hval : (finRotate (period + 1) stage).val = (stage.val + 1) % (period + 1) := by
    rw [finRotate_eq_quittingCyclicOrbit_one]
    rfl
  by_cases hlast : stage.val + 1 < period + 1
  · have hidx : Fin.castSucc (finRotate (period + 1) stage) = Fin.succ stage := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ, hval, Nat.mod_eq_of_lt hlast]
    rw [quittingCyclicContinuationBlockValue, hidx]
  · have heq : stage.val + 1 = period + 1 := by omega
    have hidx : Fin.castSucc (finRotate (period + 1) stage) = (0 : Fin (period + 2)) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_zero, hval, heq, Nat.mod_self]
    have hsucc : Fin.succ stage = Fin.last (period + 1) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last, heq]
    rw [quittingCyclicContinuationBlockValue, hidx, hsucc, hblock.2.1, hblock.1.2.1]

/-- The block's rows and values satisfy the exact cyclic policy recursion. -/
theorem quittingCyclicContinuationBlock_policy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (stage : Fin (period + 1)) :
    quittingCyclicContinuationBlockValue period block stage =
      quittingRootSuccessorPayoff reward
        (quittingCyclicContinuationBlockValue period block
          (finRotate (period + 1) stage))
        (quittingCyclicContinuationBlockCycle period block stage) := by
  rw [quittingCyclicContinuationBlockValue_finRotate reward terminal period block
    hblock stage]
  exact (hblock.1.2.2 stage).1

/-- The block's rows are exactly Nash against the block's next displayed
values, read cyclically. -/
theorem quittingCyclicContinuationBlock_rootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (stage : Fin (period + 1)) :
    IsεQuittingRootNash reward
      (quittingCyclicContinuationBlockValue period block
        (finRotate (period + 1) stage)) 0
      (quittingCyclicContinuationBlockCycle period block stage) := by
  rw [quittingCyclicContinuationBlockValue_finRotate reward terminal period block
    hblock stage]
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  exact (hblock.1.2.2 stage).2

/-- The joint all-continue product of a cyclic continuation block is strictly
below one: this is exactly its absorption clause. -/
theorem quittingCyclicContinuationBlock_prod_continueMass_lt_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    (∏ stage : Fin (period + 1), quittingStationaryContinueMass
      (quittingCyclicContinuationBlockCycle period block stage)) < 1 := by
  obtain ⟨stage, habsorb⟩ := hblock.2.2
  exact prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
    (quittingCyclicContinuationBlockCycle period block) stage habsorb

/-- The periodic behavior profile generated by a cyclic continuation block,
started at a supplied phase of the block. -/
def quittingCyclicContinuationBlockProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (phase : Fin (period + 1)) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward
    (quittingCyclicContinuationBlockCycle period block) phase

/-! ## The conditional theorem -/

/-- **(H1) + (H2) give an exact terminal equilibrium.**  If `terminal` admits an
absorbing cyclic continuation block whose deviation mismatch vanishes at every
coordinate, then the periodic profile generated by the block is exactly
terminal Nash against every behavioral deviation.

Hypothesis honesty: `hadmissible` is an explicit hypothesis; nothing below
derives it from `hblock`, and it cannot be derived (see the module docstring for
a two-player absorbing exact block violating it). -/
theorem isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (hadmissible : IsQuittingCycleAdmissible reward
      (quittingCyclicContinuationBlockCycle period block))
    (phase : Fin (period + 1)) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicContinuationBlockProfile reward period block phase) :=
  isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_admissible reward
    (quittingCyclicContinuationBlockCycle period block)
    (quittingCyclicContinuationBlockValue period block) phase
    (quittingCyclicContinuationBlock_policy reward terminal period block hblock)
    (quittingCyclicContinuationBlock_rootNash reward terminal period block hblock)
    (quittingCyclicContinuationBlock_prod_continueMass_lt_one reward terminal
      period block hblock)
    hadmissible

/-- **The conditional theorem, accuracy form.**  An admissible absorbing cyclic
continuation block yields a terminal `ε`-Nash behavior profile at every positive
accuracy -- the exact predicate consumed by
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`. -/
theorem exists_isεAsymptoticNash_of_admissible_quittingCyclicContinuationBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (hadmissible : IsQuittingCycleAdmissible reward
      (quittingCyclicContinuationBlockCycle period block))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile :=
  ⟨quittingCyclicContinuationBlockProfile reward period block 0,
    (isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile reward terminal
      period block hblock hadmissible 0).mono hε.le⟩

/-- The periodic profile started at the block's origin realizes the block's own
terminal vector.  Absorption is what pins this. -/
theorem quittingTerminalPayoff_quittingCyclicContinuationBlockProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    quittingTerminalPayoff reward
      (quittingCyclicContinuationBlockProfile reward period block 0) = terminal := by
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
    reward (quittingCyclicContinuationBlockCycle period block)
    (quittingCyclicContinuationBlockValue period block)
    (quittingCyclicContinuationBlock_policy reward terminal period block hblock)
    (quittingCyclicContinuationBlock_prod_continueMass_lt_one reward terminal
      period block hblock)
  have horigin : quittingCyclicContinuationBlockValue period block 0 = terminal :=
    hblock.2.1
  rw [quittingCyclicContinuationBlockProfile,
    quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue, horigin]

/-- **The chain to a uniform equilibrium payoff.**  Composing the conditional
theorem with the landed terminal-to-uniform selection
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`:
a weight admitting an admissible absorbing cyclic continuation block has a
uniform equilibrium payoff.

`HEADLINE` — the conditional half of the finite-quitting reduction. Together
with the zero-solo disjunct this is the whole path from a cycle to the
conjecture. The deviation class is *all* behavior strategies, not stopping
times. -/
theorem exists_uniformEquilibriumPayoff_of_admissible_quittingCyclicContinuationBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (hadmissible : IsQuittingCycleAdmissible reward
      (quittingCyclicContinuationBlockCycle period block)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors reward
    (fun ε hε ↦ exists_isεAsymptoticNash_of_admissible_quittingCyclicContinuationBlock
      reward terminal period block hblock hadmissible ε hε)

namespace QuittingBoundedSurgeryDescentCounterexample

/-! ## A worked instance: the surgery table's stationary block

The stationary row of the surgery table is an absorbing cyclic continuation
block (`stationaryBlock_isQuittingCyclicContinuationBlock`).  It is admissible,
but it does **not** satisfy the playerwise contraction hypothesis of the
existing periodic compiler: player one's only opponent never quits, so the
deleted survival product at player one is exactly `1`.  Admissibility survives
there only through the second branch, `0 ≤ r_1({1}) = a`.  So the theorems above
are a genuine generalization on this program's own running example, and not a
restatement. -/

theorem quittingCyclicContinuationBlockCycle_stationaryBlock (a : ℝ)
    (stage : Fin 1) :
    quittingCyclicContinuationBlockCycle 0 (stationaryBlock a) stage =
      stationaryRoot a := by
  rw [quittingCyclicContinuationBlockCycle]
  exact quittingRootOfSimplex_stationarySimplexRoot a

/-- Player two's opponent survives with probability `1/2`: player one quits
half the time. -/
theorem quittingStationaryFixedOpponentsContinueMass_stationaryRoot_true (a : ℝ) :
    quittingStationaryFixedOpponentsContinueMass (stationaryRoot a) true = 1 / 2 := by
  change quittingStationaryContinueMass
    (Function.update (stationaryRoot a) true (PMF.pure false)) = 1 / 2
  have htrue : Function.update (stationaryRoot a) true (PMF.pure false) true =
      PMF.pure false := by simp
  have hfalse : Function.update (stationaryRoot a) true (PMF.pure false) false =
      stationaryRoot a false := by simp
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, Fintype.prod_bool,
    htrue, hfalse, stationaryRoot_false_false]
  simp

/-- **Playerwise contraction fails.**  Player one's opponent never quits, so the
deleted survival product at player one is exactly one. -/
theorem quittingStationaryFixedOpponentsContinueMass_stationaryRoot_false (a : ℝ) :
    quittingStationaryFixedOpponentsContinueMass (stationaryRoot a) false = 1 := by
  change quittingStationaryContinueMass
    (Function.update (stationaryRoot a) false (PMF.pure false)) = 1
  have hfalse : Function.update (stationaryRoot a) false (PMF.pure false) false =
      PMF.pure false := by simp
  have htrue : Function.update (stationaryRoot a) false (PMF.pure false) true =
      stationaryRoot a true := by simp
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, Fintype.prod_bool,
    htrue, hfalse]
  simp [stationaryRoot]

/-- The existing periodic compiler does not apply: playerwise contraction fails
at player one. -/
theorem not_contracts_stationaryBlockCycle (a : ℝ) :
    ¬ (∀ who : Bool, (∏ stage : Fin 1,
      quittingStationaryFixedOpponentsContinueMass
        (quittingCyclicContinuationBlockCycle 0 (stationaryBlock a) stage) who) < 1) := by
  intro hcontracts
  have hfalse := hcontracts false
  rw [Fin.prod_univ_one, quittingCyclicContinuationBlockCycle_stationaryBlock,
    quittingStationaryFixedOpponentsContinueMass_stationaryRoot_false] at hfalse
  exact lt_irrefl 1 hfalse

/-- **The stationary block is admissible.**  At player two the deleted survival
product is `1/2 < 1`; at player one it is `1`, and the second branch applies
because the solo reward `r_1({1}) = a` is positive. -/
theorem isQuittingCycleAdmissible_stationaryBlockCycle (a : ℝ) (ha0 : 0 < a) :
    IsQuittingCycleAdmissible (reward a)
      (quittingCyclicContinuationBlockCycle 0 (stationaryBlock a)) := by
  intro who
  cases who
  · refine Or.inr ?_
    rw [show reward a (quittingSingletonTerminal false) false = a by
      simp [reward, quittingSingletonTerminal]]
    exact ha0.le
  · refine Or.inl ?_
    rw [Fin.prod_univ_one, quittingCyclicContinuationBlockCycle_stationaryBlock,
      quittingStationaryFixedOpponentsContinueMass_stationaryRoot_true]
    norm_num

/-- The stationary periodic profile is an exact terminal Nash profile of the
surgery table. -/
theorem isZeroAsymptoticNash_stationaryBlockProfile (a : ℝ) (ha0 : 0 < a) :
    (quittingGame (reward a)).IsεAsymptoticNash
      (quittingTerminalPayoff (reward a)) 0
      (quittingCyclicContinuationBlockProfile (reward a) 0 (stationaryBlock a) 0) :=
  isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile (reward a)
    (stationaryValue a) 0 (stationaryBlock a)
    (stationaryBlock_isQuittingCyclicContinuationBlock a ha0)
    (isQuittingCycleAdmissible_stationaryBlockCycle a ha0) 0

/-- Its terminal payoff is the stationary value `(a, 0)`. -/
theorem quittingTerminalPayoff_stationaryBlockProfile (a : ℝ) (ha0 : 0 < a) :
    quittingTerminalPayoff (reward a)
        (quittingCyclicContinuationBlockProfile (reward a) 0 (stationaryBlock a) 0) =
      stationaryValue a :=
  quittingTerminalPayoff_quittingCyclicContinuationBlockProfile (reward a)
    (stationaryValue a) 0 (stationaryBlock a)
    (stationaryBlock_isQuittingCyclicContinuationBlock a ha0)

/-- The surgery table has a uniform equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_reward (a : ℝ) (ha0 : 0 < a) :
    ∃ payoff : Payoff Bool,
      (quittingGame (reward a)).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_admissible_quittingCyclicContinuationBlock
    (reward a) (stationaryValue a) 0 (stationaryBlock a)
    (stationaryBlock_isQuittingCyclicContinuationBlock a ha0)
    (isQuittingCycleAdmissible_stationaryBlockCycle a ha0)

end QuittingBoundedSurgeryDescentCounterexample

end GameTheory
