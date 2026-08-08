/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.PhaseSwitchDeviationCap

/-!
# Survival-window landing by continuation lifting

A global near-equilibrium plan cannot cross a multiplicative survival window
in one stage.  The chain has three links, each stated here at its own
generality.

## (1) The reached-stage transfer lemma

A deviation that follows the plan strictly before a stage, deviates at that
stage, and resumes afterwards leaves the prefix untouched, so its *global*
gain is the joint survival through the stage times its *conditional* gain.
Hence a globally `ε`-optimal root sequence is, at every stage reached with
positive joint survival `S`, one-stage `(ε / S)`-Nash against its own
continuation vector.  This is the quitting one-shot-deviation principle with
reach-probability scaling.

The global cap is taken at the **root-sequence** level
(`IsεQuittingRootSequenceNash`), matching the hypothesis shape the
phase-switch deviation cap already consumes;
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash` identifies it with the
tree's `IsεAsymptoticNash` for the terminal payoff, so nothing is lost.

## (2) The continuation lift

The transfer lemma alone does not certify that the plan's continuation is
individually rational: rationality by the same scaling would cost the reach
probability `S * c`, which is small precisely at the jump one is trying to
exclude.  The repair replaces the continuation coordinatewise by

> `quittingLiftedContinuation _ = max (continuation value) (reservation)`,

which dominates the reservation vector by construction, at no cost in reach
probability.  The row is still one-stage `(ε / S)`-Nash against the lift:
the deviation side is carried by the securing tail response
(`IsQuittingConditionalReservation`), the prescribed side by monotonicity of
`quittingRootSuccessorPayoff` in the tail — the recursion is affine with
slope the (nonnegative) continue mass.

The reservation vector is a **parameter**.  The hypothesis actually consumed
is that each player has a *conditional* tail response securing it against
the plan's opponent tail; a min-max level taken as an infimum over profiles
implies that hypothesis, but the two are not interchanged here.

## (3) The no-large-jump lemma and the landing

The published per-stage bound — every row that is one-stage `ρ`-endpoint-Nash
against a `ρ`-rational continuation keeps continue mass at least `ρ` — is
**not** proved here; it is a hypothesis of the theorems that use it.  Granted
it, `S_i ≥ ε / ρ` forces `c(p_i) ≥ ρ`, and the elementary sequence lemma
`exists_mem_survivalWindow_of_ratio_ge` lands the survival product in the
closed window `[ρ * T, T]`.

## Main results

* `exists_mem_survivalWindow_of_ratio_ge` — the pure sequence lemma
* `isεQuittingRootNash_tailVector_of_isεQuittingRootSequenceNash` — (1)
* `isεQuittingRootNash_quittingLiftedContinuation` — (2)
* `le_quittingStationaryContinueMass_of_le_jointSurvivalWeight` — (3), the
  no-large-jump lemma
* `exists_jointSurvivalWeight_mem_survivalWindow` — the landing
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

/-! ## The pure sequence lemma -/

/-- **The window-landing sequence lemma.**  A real sequence that starts at or
above `ratio * window`, never loses more than the factor `ratio` at a stage
where it is still strictly above `window`, and reaches a value at most
`window`, has some term in the closed window `[ratio * window, window]`.

The sequence is not assumed monotone and no upper bound on `ratio` is
needed: the first crossing index does all the work. -/
theorem exists_mem_survivalWindow_of_ratio_ge
    {survival : ℕ → ℝ} {ratio window : ℝ} (hratio : 0 < ratio)
    (hstart : ratio * window ≤ survival 0)
    (hstep : ∀ stage, window < survival stage →
      ratio * survival stage ≤ survival (stage + 1))
    {below : ℕ} (hbelow : survival below ≤ window) :
    ∃ stage, ratio * window ≤ survival stage ∧ survival stage ≤ window := by
  classical
  have hexists : ∃ stage, survival stage ≤ window := ⟨below, hbelow⟩
  refine ⟨Nat.find hexists, ?_, Nat.find_spec hexists⟩
  rcases Nat.eq_zero_or_pos (Nat.find hexists) with hzero | hpos
  · rw [hzero]
    exact hstart
  · obtain ⟨prev, hprev⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hlt : prev < Nat.find hexists := by omega
    have hnot := Nat.find_min hexists hlt
    have habove : window < survival prev := lt_of_not_ge hnot
    have hscaled : ratio * window < ratio * survival prev :=
      mul_lt_mul_of_pos_left habove hratio
    have hstepprev := hstep prev habove
    rw [hprev]
    linarith

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Reading a root sequence from a stage on -/

omit [DecidableEq ι] in
/-- The terminal value from a stage sees only the roots from that stage on. -/
theorem quittingRootSequenceTerminalValue_congr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x y : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (hagree : ∀ offset, x (start + offset) = y (start + offset)) :
    quittingRootSequenceTerminalValue reward x who start =
      quittingRootSequenceTerminalValue reward y who start := by
  have hprofile : quittingRootSequenceProfile reward x start =
      quittingRootSequenceProfile reward y start := by
    funext player time history
    rw [quittingRootSequenceProfile, quittingRootSequenceProfile, hagree time]
  rw [quittingRootSequenceTerminalValue, quittingRootSequenceTerminalValue,
    hprofile]

omit [Fintype ι] [DecidableEq ι] in
/-- Truncation at a cutoff sees only the roots strictly before it. -/
theorem quittingTruncatedRoots_congr
    (x y : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (hagree : ∀ time, time < cutoff → x time = y time) :
    quittingTruncatedRoots x cutoff = quittingTruncatedRoots y cutoff := by
  funext time
  by_cases htime : time < cutoff
  · rw [quittingTruncatedRoots_of_lt _ htime, quittingTruncatedRoots_of_lt _ htime,
      hagree time htime]
  · rw [quittingTruncatedRoots_of_le _ (Nat.not_lt.mp htime),
      quittingTruncatedRoots_of_le _ (Nat.not_lt.mp htime)]

omit [DecidableEq ι] in
/-- The empty survival window carries weight one. -/
@[simp] theorem quittingJointSurvivalWeight_zero_fuel
    (x : ℕ → ι → PMF Bool) (start : ℕ) :
    quittingJointSurvivalWeight x start 0 = 1 := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simp

omit [DecidableEq ι] in
/-- **Prefix scaling.**  Two root sequences agreeing strictly before a stage
differ at stage zero by exactly the joint survival through the stage times
their difference from the stage on.  This is the whole content of "the
prefix is unchanged, so the global gain is `S_i` times the conditional
gain". -/
theorem quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x y : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ)
    (hagree : ∀ time, time < stage → x time = y time) :
    quittingRootSequenceTerminalValue reward x who 0 -
        quittingRootSequenceTerminalValue reward y who 0 =
      quittingJointSurvivalWeight y 0 stage *
        (quittingRootSequenceTerminalValue reward x who stage -
          quittingRootSequenceTerminalValue reward y who stage) := by
  have hx := quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    reward x who stage
  have hy := quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    reward y who stage
  have htrunc : quittingTruncatedRoots x stage = quittingTruncatedRoots y stage :=
    quittingTruncatedRoots_congr x y stage hagree
  have hsurvival : quittingJointSurvivalWeight x 0 stage =
      quittingJointSurvivalWeight y 0 stage := by
    refine quittingJointSurvivalWeight_congr x y 0 stage fun offset hoffset => ?_
    rw [Nat.zero_add]
    exact hagree offset hoffset
  rw [hx, hy, htrunc, hsurvival]
  ring

/-! ## The one-stage deviation with a supplied tail -/

/-- The unilateral hazard that follows the plan's own marginals strictly
before a stage, plays `dev` at that stage, and plays `tail` afterwards. -/
def quittingStageDeviationHazard
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ)
    (dev : PMF Bool) (tail : ℕ → PMF Bool) : ℕ → PMF Bool :=
  fun time =>
    if time < stage then roots time who
    else if time = stage then dev else tail (time - (stage + 1))

omit [Fintype ι] [DecidableEq ι] in
/-- Before the deviation stage the hazard is the plan's own marginal. -/
theorem quittingStageDeviationHazard_of_lt
    (roots : ℕ → ι → PMF Bool) (who : ι) {stage time : ℕ}
    (dev : PMF Bool) (tail : ℕ → PMF Bool) (htime : time < stage) :
    quittingStageDeviationHazard roots who stage dev tail time = roots time who :=
  if_pos htime

omit [Fintype ι] [DecidableEq ι] in
/-- At the deviation stage the hazard is the supplied action. -/
@[simp] theorem quittingStageDeviationHazard_self
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ)
    (dev : PMF Bool) (tail : ℕ → PMF Bool) :
    quittingStageDeviationHazard roots who stage dev tail stage = dev := by
  rw [quittingStageDeviationHazard, if_neg (lt_irrefl stage), if_pos rfl]

omit [Fintype ι] [DecidableEq ι] in
/-- After the deviation stage the hazard is the supplied tail, read at its
own offsets. -/
@[simp] theorem quittingStageDeviationHazard_add
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage offset : ℕ)
    (dev : PMF Bool) (tail : ℕ → PMF Bool) :
    quittingStageDeviationHazard roots who stage dev tail (stage + 1 + offset) =
      tail offset := by
  have hlt : ¬ stage + 1 + offset < stage := by omega
  have heq : ¬ stage + 1 + offset = stage := by omega
  rw [quittingStageDeviationHazard, if_neg hlt, if_neg heq]
  congr 1
  omega

omit [Fintype ι] in
/-- Before the deviation stage the deviated sequence is the plan. -/
theorem quittingRootSequenceUpdate_stageDeviationHazard_of_lt
    (roots : ℕ → ι → PMF Bool) (who : ι) {stage time : ℕ}
    (dev : PMF Bool) (tail : ℕ → PMF Bool) (htime : time < stage) :
    quittingRootSequenceUpdate roots who
        (quittingStageDeviationHazard roots who stage dev tail) time =
      roots time := by
  rw [quittingRootSequenceUpdate,
    quittingStageDeviationHazard_of_lt roots who dev tail htime]
  exact Function.update_eq_self who (roots time)

omit [Fintype ι] in
/-- At the deviation stage the deviated sequence is the plan's row with the
deviator's coordinate replaced. -/
theorem quittingRootSequenceUpdate_stageDeviationHazard_self
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ)
    (dev : PMF Bool) (tail : ℕ → PMF Bool) :
    quittingRootSequenceUpdate roots who
        (quittingStageDeviationHazard roots who stage dev tail) stage =
      Function.update (roots stage) who dev := by
  rw [quittingRootSequenceUpdate, quittingStageDeviationHazard_self]

omit [Fintype ι] in
/-- From one stage past the deviation on, the deviated sequence is the
shifted plan with the supplied tail substituted. -/
theorem quittingRootSequenceUpdate_stageDeviationHazard_shift
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ)
    (dev : PMF Bool) (tail : ℕ → PMF Bool) :
    (fun offset => quittingRootSequenceUpdate roots who
        (quittingStageDeviationHazard roots who stage dev tail)
        (stage + 1 + offset)) =
      quittingRootSequenceUpdate (fun time => roots (stage + 1 + time)) who tail := by
  funext offset
  rw [quittingRootSequenceUpdate, quittingRootSequenceUpdate,
    quittingStageDeviationHazard_add]

/-- Following the plan's own marginals is a tail response worth exactly the
plan's continuation value. -/
theorem quittingRootSequenceHazardTerminalValue_self_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward
        (fun time => roots (start + time)) who
        (fun time => roots (start + time) who) 0 =
      quittingRootSequenceTerminalValue reward roots who start := by
  have hupdate : quittingRootSequenceUpdate (fun time => roots (start + time)) who
      (fun time => roots (start + time) who) = fun time => roots (start + time) :=
    funext fun time => Function.update_eq_self who (roots (start + time))
  rw [quittingRootSequenceHazardTerminalValue, hupdate]
  exact (quittingRootSequenceTerminalValue_eq_shift reward roots who start).symm

/-! ## The successor payoff reads one coordinate of the tail -/

omit [DecidableEq ι] in
/-- The successor payoff at a coordinate is that coordinate's root expected
payoff. -/
theorem quittingRootSuccessorPayoff_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      quittingRootExpectedPayoff reward tail root who :=
  rfl

omit [DecidableEq ι] in
/-- The successor payoff at a coordinate reads only that coordinate of the
tail. -/
theorem quittingRootSuccessorPayoff_congr_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail tail' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (htail : tail who = tail' who) :
    quittingRootSuccessorPayoff reward tail root who =
      quittingRootSuccessorPayoff reward tail' root who := by
  rw [quittingRootSuccessorPayoff_apply_eq_affine,
    quittingRootSuccessorPayoff_apply_eq_affine, htail]

omit [DecidableEq ι] in
/-- **Monotonicity in the tail.**  Raising the continuation at a coordinate
can only raise that coordinate's successor payoff: the recursion is affine
with slope the nonnegative continue mass. -/
theorem quittingRootSuccessorPayoff_mono_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail tail' : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (htail : tail who ≤ tail' who) :
    quittingRootSuccessorPayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail' root who := by
  rw [quittingRootSuccessorPayoff_apply_eq_affine,
    quittingRootSuccessorPayoff_apply_eq_affine]
  have hslope := mul_le_mul_of_nonneg_left htail
    (quittingStationaryContinueMass_nonneg root)
  linarith

/-! ## The global cap -/

/-- **The global cap, at the root-sequence level.**  No player gains more
than `ε` by replacing their own root marginals by an arbitrary time-indexed
hazard sequence.  This is the hypothesis shape the phase-switch deviation cap
already consumes, and by
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash` it is exactly the tree's
terminal `ε`-Nash property of the generated profile. -/
def IsεQuittingRootSequenceNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ε : ℝ) (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ (who : ι) (hazard : ℕ → PMF Bool),
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
      quittingRootSequenceTerminalValue reward roots who 0 + ε

/-- **The two global cap notions agree.**  The root-sequence cap is the
terminal `ε`-Nash property of the profile the sequence generates: the
live-hazard collapse turns an arbitrary behaviour deviation into a hazard
sequence, and every hazard sequence is itself a behaviour strategy. -/
theorem isεQuittingRootSequenceNash_iff_isεAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ε : ℝ) (roots : ℕ → ι → PMF Bool) :
    IsεQuittingRootSequenceNash reward ε roots ↔
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        (quittingRootSequenceProfile reward roots 0) := by
  constructor
  · intro hcap who deviation
    have hcollapse := quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingRootSequenceProfile reward roots 0) who deviation
    rw [quittingProfileLiveRoot_quittingRootSequenceProfile_zero] at hcollapse
    have hhazard := hcap who (quittingBehaviorLiveHazard reward deviation)
    rw [← hcollapse] at hhazard
    exact hhazard
  · intro hnash who hazard
    have hcollapse := quittingRootSequenceHazardTerminalValue_eq_terminalPayoff_update
      reward roots who hazard
    have hdev := hnash who (fun time _history => hazard time)
    rw [hcollapse]
    exact hdev

/-! ## (1) The reached-stage transfer lemma -/

/-- The plan's continuation vector at a stage: coordinate `who` is that
player's own terminal value from the stage on. -/
def quittingRootSequenceTailVector
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) : Payoff ι :=
  fun who => quittingRootSequenceTerminalValue reward roots who start

omit [DecidableEq ι] in
/-- The plan's own value at a stage is the successor payoff of its row
against its own continuation vector. -/
theorem quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    quittingRootSequenceTerminalValue reward roots who start =
      quittingRootSuccessorPayoff reward
        (quittingRootSequenceTailVector reward roots (start + 1)) (roots start) who := by
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff reward roots who start]
  exact quittingRootSuccessorPayoff_congr_apply reward _ _ (roots start) who rfl

/-- **The transfer lemma with a supplied tail, in multiplied-through form.**
For a globally `ε`-optimal plan, the joint survival through a stage times the
conditional gain of a one-stage deviation resumed by an arbitrary tail hazard
is at most `ε`.  The prefix is unchanged, so the global cap applies verbatim;
no division by a survival weight occurs. -/
theorem quittingJointSurvivalWeight_mul_stageDeviationGain_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {ε : ℝ}
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (who : ι) (stage : ℕ) (dev : PMF Bool) (tail : ℕ → PMF Bool) :
    quittingJointSurvivalWeight roots 0 stage *
        (quittingRootSuccessorPayoff reward
            (fun _ => quittingRootSequenceHazardTerminalValue reward
              (fun time => roots (stage + 1 + time)) who tail 0)
            (Function.update (roots stage) who dev) who -
          quittingRootSequenceTerminalValue reward roots who stage) ≤ ε := by
  set hazard := quittingStageDeviationHazard roots who stage dev tail with hhazard
  set deviated := quittingRootSequenceUpdate roots who hazard with hdeviated
  have hagree : ∀ time, time < stage → deviated time = roots time := by
    intro time htime
    rw [hdeviated, hhazard]
    exact quittingRootSequenceUpdate_stageDeviationHazard_of_lt roots who dev tail htime
  have hscaling := quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
    reward deviated roots who stage hagree
  have hglobal : quittingRootSequenceTerminalValue reward deviated who 0 ≤
      quittingRootSequenceTerminalValue reward roots who 0 + ε := hnash who hazard
  have hstage : quittingRootSequenceTerminalValue reward deviated who stage =
      quittingRootSuccessorPayoff reward
        (fun _ => quittingRootSequenceHazardTerminalValue reward
          (fun time => roots (stage + 1 + time)) who tail 0)
        (Function.update (roots stage) who dev) who := by
    have htailValue : quittingRootSequenceTerminalValue reward deviated who (stage + 1) =
        quittingRootSequenceHazardTerminalValue reward
          (fun time => roots (stage + 1 + time)) who tail 0 := by
      rw [quittingRootSequenceTerminalValue_eq_shift reward deviated who (stage + 1),
        hdeviated, hhazard,
        quittingRootSequenceUpdate_stageDeviationHazard_shift roots who stage dev tail,
        quittingRootSequenceHazardTerminalValue]
    rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff reward deviated who stage,
      htailValue, hdeviated, hhazard,
      quittingRootSequenceUpdate_stageDeviationHazard_self roots who stage dev tail]
  rw [hstage] at hscaling
  linarith

/-- **(1) The reached-stage transfer lemma.**  A globally `ε`-optimal plan is,
at every stage reached with positive joint survival `S`, one-stage
`(ε / S)`-Nash against its own continuation vector.

This is the quitting one-shot-deviation principle with reach-probability
scaling: the deviation follows the plan before the stage, deviates at it and
resumes after, so its global gain is `S` times its conditional gain. -/
theorem isεQuittingRootNash_tailVector_of_isεQuittingRootSequenceNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {ε : ℝ}
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (stage : ℕ) (hsurvival : 0 < quittingJointSurvivalWeight roots 0 stage) :
    IsεQuittingRootNash reward
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (ε / quittingJointSurvivalWeight roots 0 stage) (roots stage) := by
  intro who dev
  have htransfer := quittingJointSurvivalWeight_mul_stageDeviationGain_le
    reward roots hnash who stage dev (fun time => roots (stage + 1 + time) who)
  rw [quittingRootSequenceHazardTerminalValue_self_tail reward roots who (stage + 1)]
    at htransfer
  have hdeviation : quittingRootSuccessorPayoff reward
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (Function.update (roots stage) who dev) who =
      quittingRootSuccessorPayoff reward
        (fun _ => quittingRootSequenceTerminalValue reward roots who (stage + 1))
        (Function.update (roots stage) who dev) who :=
    quittingRootSuccessorPayoff_congr_apply reward _ _ _ who rfl
  have hgain : quittingRootSuccessorPayoff reward
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (Function.update (roots stage) who dev) who -
      quittingRootSequenceTerminalValue reward roots who stage ≤
      ε / quittingJointSurvivalWeight roots 0 stage := by
    rw [le_div_iff₀ hsurvival, hdeviation]
    linarith [htransfer]
  rw [← quittingRootSuccessorPayoff_apply, ← quittingRootSuccessorPayoff_apply,
    ← quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
  linarith

/-- **(1), endpoint form.**  The same conclusion read through the endpoint
inequalities.  The one-stage payoff is affine in the deviating coordinate, so
comparing against the two pure endpoints is equivalent to comparing against
every mixed deviation; that equivalence is
`isεQuittingRootEndpointNash_iff_isεQuittingRootNash`. -/
theorem isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {ε : ℝ}
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (stage : ℕ) (hsurvival : 0 < quittingJointSurvivalWeight roots 0 stage) :
    IsεQuittingRootEndpointNash reward
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (ε / quittingJointSurvivalWeight roots 0 stage) (roots stage) :=
  (isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward _ _ _).mpr
    (isεQuittingRootNash_tailVector_of_isεQuittingRootSequenceNash reward roots
      hnash stage hsurvival)

/-! ## (2) The continuation lift -/

/-- **A conditional reservation vector.**  From every stage on and for every
positive slack, each player has a *tail hazard against the plan's opponent
tail* securing `reservation` up to that slack.

The conditionality is essential: an unconditional min-max level, an infimum
over all opponent profiles, implies this hypothesis, but the implication is
one-directional and is not used in the other sense anywhere below. -/
def IsQuittingConditionalReservation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (reservation : Payoff ι) : Prop :=
  ∀ (who : ι) (start : ℕ) (slack : ℝ), 0 < slack →
    ∃ tail : ℕ → PMF Bool,
      reservation who - slack ≤
        quittingRootSequenceHazardTerminalValue reward
          (fun time => roots (start + time)) who tail 0

/-- **The reservation interface is inhabited.**  Under a uniform reward bound
the constant vector `-bound` is a conditional reservation vector: every tail
response secures it.  This is a vacuity check on
`IsQuittingConditionalReservation`, not a useful reservation level — the
granted per-stage bound below is what forces `reservation` to be sharp, since
it restricts to continuations dominating `reservation`. -/
theorem isQuittingConditionalReservation_const_neg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound) :
    IsQuittingConditionalReservation reward roots (fun _ => -bound) := by
  intro who start slack hslack
  refine ⟨fun _ => PMF.pure false, ?_⟩
  rw [quittingRootSequenceHazardTerminalValue]
  have habs := abs_quittingRootSequenceTerminalValue_le reward
    (quittingRootSequenceUpdate (fun time => roots (start + time)) who
      (fun _ => PMF.pure false)) who 0 hbound hreward
  have hlower := neg_abs_le (quittingRootSequenceTerminalValue reward
    (quittingRootSequenceUpdate (fun time => roots (start + time)) who
      (fun _ => PMF.pure false)) who 0)
  linarith

/-- **The lifted continuation.**  Each coordinate of the plan's continuation
vector is raised to the reservation level.  The lift dominates the
reservation vector by construction — it is `0`-rational for free — and costs
no reach probability at all, which is exactly why the circle at a jump stage
never closes. -/
def quittingLiftedContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (reservation : Payoff ι) (start : ℕ) : Payoff ι :=
  fun who => max (quittingRootSequenceTerminalValue reward roots who start)
    (reservation who)

omit [DecidableEq ι] in
/-- **(2a) The lift dominates the actual continuation.** -/
theorem quittingRootSequenceTailVector_le_quittingLiftedContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (reservation : Payoff ι) (start : ℕ) (who : ι) :
    quittingRootSequenceTailVector reward roots start who ≤
      quittingLiftedContinuation reward roots reservation start who :=
  le_max_left _ _

omit [DecidableEq ι] in
/-- **The lift is `0`-rational.**  Every coordinate dominates the reservation
level, by construction and at no cost in reach probability. -/
theorem le_quittingLiftedContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (reservation : Payoff ι) (start : ℕ) (who : ι) :
    reservation who ≤ quittingLiftedContinuation reward roots reservation start who :=
  le_max_right _ _

/-- Every coordinate of the lift is secured, up to any positive slack, by a
tail hazard: by the reservation response where the reservation wins, by
following the plan where the plan's own continuation wins. -/
theorem exists_tail_quittingLiftedContinuation_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι}
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (who : ι) (start : ℕ) {slack : ℝ} (hslack : 0 < slack) :
    ∃ tail : ℕ → PMF Bool,
      quittingLiftedContinuation reward roots reservation start who - slack ≤
        quittingRootSequenceHazardTerminalValue reward
          (fun time => roots (start + time)) who tail 0 := by
  rcases le_total (reservation who)
      (quittingRootSequenceTerminalValue reward roots who start) with hle | hle
  · refine ⟨fun time => roots (start + time) who, ?_⟩
    rw [quittingRootSequenceHazardTerminalValue_self_tail reward roots who start,
      quittingLiftedContinuation, max_eq_left hle]
    linarith
  · obtain ⟨tail, htail⟩ := hreserve who start slack hslack
    refine ⟨tail, ?_⟩
    rw [quittingLiftedContinuation, max_eq_right hle]
    exact htail

/-- **(2) The continuation lift.**  A globally `ε`-optimal plan's row at a
stage reached with positive joint survival `S` is still one-stage
`(ε / S)`-Nash against the *lifted* continuation.

The deviation side is carried by the securing tail response: the deviator
plays `dev` at the stage and then a response worth at least the lift minus a
slack, and the whole deviation conditions on reaching the stage — probability
`S`, not `S * c`.  The prescribed side is monotonicity of the one-stage
payoff in the tail. -/
theorem isεQuittingRootNash_quittingLiftedContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι} {ε : ℝ}
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (stage : ℕ) (hsurvival : 0 < quittingJointSurvivalWeight roots 0 stage) :
    IsεQuittingRootNash reward
      (quittingLiftedContinuation reward roots reservation (stage + 1))
      (ε / quittingJointSurvivalWeight roots 0 stage) (roots stage) := by
  intro who dev
  set lifted := quittingLiftedContinuation reward roots reservation (stage + 1)
    with hlifted
  set deviated := quittingRootSuccessorPayoff reward lifted
    (Function.update (roots stage) who dev) who with hdeviated
  set prescribed := quittingRootSequenceTerminalValue reward roots who stage
    with hprescribed
  -- The deviation side, with a slack that is then sent to zero.
  have hslackbound : ∀ slack : ℝ, 0 < slack →
      deviated ≤ prescribed + ε / quittingJointSurvivalWeight roots 0 stage + slack := by
    intro slack hslack
    obtain ⟨tail, htail⟩ := exists_tail_quittingLiftedContinuation_sub_le reward roots
      hreserve who (stage + 1) hslack
    set tailValue := quittingRootSequenceHazardTerminalValue reward
      (fun time => roots (stage + 1 + time)) who tail 0 with htailValue
    set root := Function.update (roots stage) who dev with hroot
    have htransfer := quittingJointSurvivalWeight_mul_stageDeviationGain_le
      reward roots hnash who stage dev tail
    have hmass := quittingStationaryContinueMass_nonneg root
    have hmassOne := quittingStationaryContinueMass_le_one root
    have hscaled : quittingStationaryContinueMass root * (lifted who - slack) ≤
        quittingStationaryContinueMass root * tailValue :=
      mul_le_mul_of_nonneg_left htail hmass
    rw [mul_sub] at hscaled
    have hslackMass : quittingStationaryContinueMass root * slack ≤ slack :=
      mul_le_of_le_one_left hslack.le hmassOne
    have hcompare : deviated ≤
        quittingRootSuccessorPayoff reward (fun _ => tailValue) root who + slack := by
      rw [hdeviated, quittingRootSuccessorPayoff_apply_eq_affine,
        quittingRootSuccessorPayoff_apply_eq_affine]
      linarith
    have hcap : quittingRootSuccessorPayoff reward (fun _ => tailValue) root who -
        prescribed ≤ ε / quittingJointSurvivalWeight roots 0 stage := by
      rw [le_div_iff₀ hsurvival]
      linarith [htransfer]
    linarith
  have hdeviationSide :
      deviated ≤ prescribed + ε / quittingJointSurvivalWeight roots 0 stage :=
    le_of_forall_pos_le_add hslackbound
  -- The prescribed side: raising the continuation can only raise the row.
  have hprescribedSide : prescribed ≤
      quittingRootSuccessorPayoff reward lifted (roots stage) who := by
    rw [hprescribed,
      quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector reward roots who stage]
    exact quittingRootSuccessorPayoff_mono_apply reward _ _ (roots stage) who
      (quittingRootSequenceTailVector_le_quittingLiftedContinuation reward roots
        reservation (stage + 1) who)
  rw [← quittingRootSuccessorPayoff_apply, ← quittingRootSuccessorPayoff_apply]
  linarith

/-- **(2), endpoint form.** -/
theorem isεQuittingRootEndpointNash_quittingLiftedContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι} {ε : ℝ}
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (stage : ℕ) (hsurvival : 0 < quittingJointSurvivalWeight roots 0 stage) :
    IsεQuittingRootEndpointNash reward
      (quittingLiftedContinuation reward roots reservation (stage + 1))
      (ε / quittingJointSurvivalWeight roots 0 stage) (roots stage) :=
  (isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward _ _ _).mpr
    (isεQuittingRootNash_quittingLiftedContinuation reward roots hnash hreserve
      stage hsurvival)

/-! ## (3) The no-large-jump lemma and the landing -/

/-- **The granted per-stage bound.**  Every row that is one-stage
`ratio`-endpoint-Nash against a `ratio`-rational continuation keeps continue
mass at least `ratio`.

This is the published Lemma 5(2)(b).  It is **not** proved here: it is a
hypothesis, packaged as a predicate on the reward so that the theorems below
say exactly what they consume. -/
def IsQuittingGrantedContinueMassBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (reservation : Payoff ι) (ratio : ℝ) : Prop :=
  ∀ (continuation : Payoff ι) (root : ι → PMF Bool),
    (∀ player, reservation player - ratio ≤ continuation player) →
    IsεQuittingRootEndpointNash reward continuation ratio root →
      ratio ≤ quittingStationaryContinueMass root

/-- **(3) The no-large-jump lemma.**  Granted the per-stage bound, a globally
`ε`-optimal plan cannot lose more than the factor `ratio` at a stage whose
joint survival is at least `ε / ratio`.

The lifted continuation is what makes the granted bound applicable: it is
`0`-rational, hence `ratio`-rational, at no cost in reach probability, so the
circle "the jump destroys the reach probability that would forbid the jump"
never closes. -/
theorem le_quittingStationaryContinueMass_of_le_jointSurvivalWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι} {ε ratio : ℝ}
    (hε : 0 < ε) (hratio : 0 < ratio)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (hgranted : IsQuittingGrantedContinueMassBound reward reservation ratio)
    (stage : ℕ) (hstage : ε / ratio ≤ quittingJointSurvivalWeight roots 0 stage) :
    ratio ≤ quittingStationaryContinueMass (roots stage) := by
  have hpos : 0 < ε / ratio := div_pos hε hratio
  have hsurvival : 0 < quittingJointSurvivalWeight roots 0 stage := lt_of_lt_of_le hpos hstage
  have htolerance : ε / quittingJointSurvivalWeight roots 0 stage ≤ ratio := by
    rw [div_le_iff₀ hsurvival, mul_comm]
    exact (div_le_iff₀ hratio).mp hstage
  have hlift := isεQuittingRootNash_quittingLiftedContinuation reward roots hnash
    hreserve stage hsurvival
  have hratioNash : IsεQuittingRootNash reward
      (quittingLiftedContinuation reward roots reservation (stage + 1)) ratio
      (roots stage) := by
    intro player deviation
    have := hlift player deviation
    linarith
  refine hgranted _ (roots stage) (fun player => ?_)
    ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward _ _ _).mpr hratioNash)
  have hdominates := le_quittingLiftedContinuation reward roots reservation (stage + 1) player
  linarith

/-- **The survival-window landing.**  Granted the per-stage bound, a globally
`ε`-optimal plan whose joint survival ever drops to `window` — with accuracy
`ε ≤ ratio * window` and `ratio * window ≤ 1` — has some stage whose joint
survival lies in the closed window `[ratio * window, window]`.

With `window = θ/3` and `ratio = ρ` this is the published window; the
accuracy requirement is only `ε ≤ ρθ/3`. -/
theorem exists_jointSurvivalWeight_mem_survivalWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι} {ε ratio window : ℝ}
    (hε : 0 < ε) (hratio : 0 < ratio)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (hgranted : IsQuittingGrantedContinueMassBound reward reservation ratio)
    (hwindow : ratio * window ≤ 1) (haccuracy : ε ≤ ratio * window)
    {below : ℕ} (hbelow : quittingJointSurvivalWeight roots 0 below ≤ window) :
    ∃ stage, ratio * window ≤ quittingJointSurvivalWeight roots 0 stage ∧
      quittingJointSurvivalWeight roots 0 stage ≤ window := by
  refine exists_mem_survivalWindow_of_ratio_ge hratio ?_ (fun stage hstage => ?_) hbelow
  · rw [quittingJointSurvivalWeight_zero_fuel]
    exact hwindow
  · have hthreshold : ε / ratio ≤ quittingJointSurvivalWeight roots 0 stage := by
      rw [div_le_iff₀ hratio]
      nlinarith [hstage, haccuracy]
    have hmass := le_quittingStationaryContinueMass_of_le_jointSurvivalWeight reward
      roots hε hratio hnash hreserve hgranted stage hthreshold
    have hsucc := quittingJointSurvivalWeight_succ roots 0 stage
    rw [Nat.zero_add] at hsucc
    have hnonneg := quittingJointSurvivalWeight_nonneg roots 0 stage
    rw [hsucc]
    nlinarith [hmass, hnonneg]

/-- **The landing from a vanishing survival limit.**  If the joint survival
converges below the window, it lands in it.  This is the form the published
argument uses: `S_∞ < ρT ≤ T` is supplied, and the landing follows. -/
theorem exists_jointSurvivalWeight_mem_survivalWindow_of_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι} {ε ratio window limit : ℝ}
    (hε : 0 < ε) (hratio : 0 < ratio)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (hgranted : IsQuittingGrantedContinueMassBound reward reservation ratio)
    (hwindow : ratio * window ≤ 1) (haccuracy : ε ≤ ratio * window)
    (hlimit : Tendsto (quittingJointSurvivalWeight roots 0) atTop (nhds limit))
    (hbelow : limit < window) :
    ∃ stage, ratio * window ≤ quittingJointSurvivalWeight roots 0 stage ∧
      quittingJointSurvivalWeight roots 0 stage ≤ window := by
  obtain ⟨below, hbelowStage⟩ := ((tendsto_order.1 hlimit).2 window hbelow).exists
  exact exists_jointSurvivalWeight_mem_survivalWindow reward roots hε hratio hnash
    hreserve hgranted hwindow haccuracy hbelowStage.le

end GameTheory
