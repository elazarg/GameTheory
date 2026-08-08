/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Boundary.Analytic.SeamPriceResidual
import UniformEquilibrium.Quitting.Terminal.TargetTail.FiniteChainTerminalCompiler
import UniformEquilibrium.Quitting.Paths.PlannedSurvivalStoppingIndex

/-!
# The phase-switch combinator for quitting games

Every profile grammar in this tree is stationary, cyclic, or a pinned chain:
what a player does at stage `t` never depends on what happened before.  This
file adds the first combinator whose behaviour genuinely changes after an
event, namely a **phase switch in time**: play one time-indexed plan until a
switch stage, then play a punishment plan from its own stage zero forever.

That this is enough adaptivity for a quitting game is the content of
`quittingBehaviorLiveHazard` (`QuittingBehaviorPureTimeExtremality.lean`):
before absorption a quitting game has a *unique* public history, so any
behaviour strategy's active-path behaviour is already a deterministic
function of the stage count, and the only public signal a deviation can emit
is survival itself.  A phase switch in calendar time is therefore not a
restriction of history dependence along the active path -- it is all of it.
The switch stage here is a **fixed** natural number; the random,
history-measurable switch of the literature is not claimed.

## Main definitions

* `quittingPhaseSwitchRoots` -- the combinator on time-indexed product roots
* `quittingPhaseSwitchProfile` -- the behaviour profile it generates
* `quittingTruncatedRoots` -- a root sequence frozen to all-Continue from a
  cutoff, i.e. the *truncated* plan
* `quittingTruncatedHazard` -- a deviator's hazard frozen to sure Continue
  from a cutoff

## Main results

* `quittingBehaviorLiveHazard_quittingPhaseSwitchProfile` -- the profile's
  live-path hazard at stage `t` is the switched root's marginal at `t`
* `quittingJointSurvivalWeight_quittingPhaseSwitchRoots_add` -- the survival
  product factors as plan-phase survival times punishment-phase survival
* `quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul` --
  the exact payoff decomposition at an arbitrary cutoff: truncated-prefix
  value plus survival-weighted continuation value
* `quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots` and
  `quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots` -- that
  decomposition specialised to the switch stage, for the prescribed profile
  and for an arbitrary unilateral hazard deviation
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The combinator -/

/-- Play `plan` at every stage strictly before `switch`, then `punish`,
restarted at its own stage zero, from `switch` on. -/
def quittingPhaseSwitchRoots
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) :
    ℕ → ι → PMF Bool :=
  fun time => if time < switch then plan time else punish (time - switch)

omit [Fintype ι] [DecidableEq ι] in
/-- Before the switch stage the phase-switch roots are the plan's. -/
theorem quittingPhaseSwitchRoots_of_lt
    (plan punish : ℕ → ι → PMF Bool) {switch time : ℕ} (htime : time < switch) :
    quittingPhaseSwitchRoots plan punish switch time = plan time :=
  if_pos htime

omit [Fintype ι] [DecidableEq ι] in
/-- From the switch stage on the phase-switch roots are the punishment's,
re-indexed to start at its own stage zero. -/
theorem quittingPhaseSwitchRoots_of_le
    (plan punish : ℕ → ι → PMF Bool) {switch time : ℕ} (htime : switch ≤ time) :
    quittingPhaseSwitchRoots plan punish switch time = punish (time - switch) :=
  if_neg (Nat.not_lt.mpr htime)

omit [Fintype ι] [DecidableEq ι] in
/-- The punishment phase read at its own offsets. -/
@[simp] theorem quittingPhaseSwitchRoots_add
    (plan punish : ℕ → ι → PMF Bool) (switch offset : ℕ) :
    quittingPhaseSwitchRoots plan punish switch (switch + offset) =
      punish offset := by
  rw [quittingPhaseSwitchRoots_of_le plan punish (Nat.le_add_right switch offset),
    Nat.add_sub_cancel_left]

omit [Fintype ι] [DecidableEq ι] in
/-- The punishment phase, read from the switch stage on, is exactly the
punishment plan. -/
theorem quittingPhaseSwitchRoots_comp_add
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) :
    (fun offset => quittingPhaseSwitchRoots plan punish switch (switch + offset)) =
      punish :=
  funext fun offset => quittingPhaseSwitchRoots_add plan punish switch offset

/-- A root sequence frozen to all-Continue from a cutoff on: the *truncated*
plan, whose whole payoff is generated strictly before the cutoff. -/
def quittingTruncatedRoots (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    ℕ → ι → PMF Bool :=
  quittingPhaseSwitchRoots roots (fun _ => quittingAllContinueRoot) cutoff

omit [Fintype ι] [DecidableEq ι] in
/-- Before the cutoff the truncated roots are the original ones. -/
theorem quittingTruncatedRoots_of_lt
    (roots : ℕ → ι → PMF Bool) {cutoff time : ℕ} (htime : time < cutoff) :
    quittingTruncatedRoots roots cutoff time = roots time :=
  quittingPhaseSwitchRoots_of_lt roots _ htime

omit [Fintype ι] [DecidableEq ι] in
/-- From the cutoff on the truncated roots are all-Continue. -/
theorem quittingTruncatedRoots_of_le
    (roots : ℕ → ι → PMF Bool) {cutoff time : ℕ} (htime : cutoff ≤ time) :
    quittingTruncatedRoots roots cutoff time =
      (quittingAllContinueRoot : ι → PMF Bool) :=
  quittingPhaseSwitchRoots_of_le roots _ htime

omit [Fintype ι] [DecidableEq ι] in
/-- Truncating a phase switch at its own switch stage forgets the punishment
phase entirely. -/
theorem quittingTruncatedRoots_quittingPhaseSwitchRoots
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) :
    quittingTruncatedRoots (quittingPhaseSwitchRoots plan punish switch) switch =
      quittingTruncatedRoots plan switch := by
  funext time
  by_cases htime : time < switch
  · rw [quittingTruncatedRoots_of_lt _ htime, quittingTruncatedRoots_of_lt _ htime,
      quittingPhaseSwitchRoots_of_lt plan punish htime]
  · rw [quittingTruncatedRoots_of_le _ (Nat.not_lt.mp htime),
      quittingTruncatedRoots_of_le _ (Nat.not_lt.mp htime)]

/-- A deviator's hazard frozen to sure Continue from the cutoff on. -/
def quittingTruncatedHazard (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    ℕ → PMF Bool :=
  fun time => if time < cutoff then hazard time else PMF.pure false

/-- Before the cutoff the truncated hazard is the original one. -/
theorem quittingTruncatedHazard_of_lt
    (hazard : ℕ → PMF Bool) {cutoff time : ℕ} (htime : time < cutoff) :
    quittingTruncatedHazard hazard cutoff time = hazard time :=
  if_pos htime

/-- From the cutoff on the truncated hazard continues for sure. -/
theorem quittingTruncatedHazard_of_le
    (hazard : ℕ → PMF Bool) {cutoff time : ℕ} (htime : cutoff ≤ time) :
    quittingTruncatedHazard hazard cutoff time = PMF.pure false :=
  if_neg (Nat.not_lt.mpr htime)

omit [Fintype ι] in
/-- Truncating the plan and the deviator together is the same as deviating
inside the truncated plan. -/
theorem quittingRootSequenceUpdate_quittingTruncatedRoots
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingRootSequenceUpdate (quittingTruncatedRoots roots cutoff) who
        (quittingTruncatedHazard hazard cutoff) =
      quittingTruncatedRoots (quittingRootSequenceUpdate roots who hazard) cutoff := by
  funext time
  by_cases htime : time < cutoff
  · rw [quittingRootSequenceUpdate, quittingTruncatedRoots_of_lt _ htime,
      quittingTruncatedHazard_of_lt _ htime, quittingTruncatedRoots_of_lt _ htime,
      quittingRootSequenceUpdate]
  · have hle := Nat.not_lt.mp htime
    rw [quittingRootSequenceUpdate, quittingTruncatedRoots_of_le _ hle,
      quittingTruncatedHazard_of_le _ hle, quittingTruncatedRoots_of_le _ hle]
    exact Function.update_eq_self who (quittingAllContinueRoot : ι → PMF Bool)

/-! ## The generated profile and its live hazard -/

/-- The behaviour profile generated by a phase switch: it plays `plan` until
the switch stage and `punish` afterwards. -/
def quittingPhaseSwitchProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward
    (quittingPhaseSwitchRoots plan punish switch) 0

omit [DecidableEq ι] in
/-- A root-sequence profile started at stage zero has exactly its own roots
as canonical live roots.  This is the elementary half of the live-hazard
collapse: reading a history-free profile along the unique live history
returns the sequence it was built from. -/
@[simp] theorem quittingProfileLiveRoot_quittingRootSequenceProfile_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) :
    quittingProfileLiveRoot reward
        (quittingRootSequenceProfile reward roots 0) = roots := by
  funext time player
  rw [quittingProfileLiveRoot, quittingRootSequenceProfile, Nat.zero_add]

omit [DecidableEq ι] in
/-- The canonical live roots of a phase-switch profile are the phase-switch
roots. -/
@[simp] theorem quittingProfileLiveRoot_quittingPhaseSwitchProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) :
    quittingProfileLiveRoot reward
        (quittingPhaseSwitchProfile reward plan punish switch) =
      quittingPhaseSwitchRoots plan punish switch :=
  quittingProfileLiveRoot_quittingRootSequenceProfile_zero reward _

omit [DecidableEq ι] in
/-- **The hazard at stage `t`.**  Along the unique live public history the
phase-switch profile hands player `who` the plan's marginal before the
switch stage and the punishment's marginal after it. -/
theorem quittingBehaviorLiveHazard_quittingPhaseSwitchProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι) (time : ℕ) :
    quittingBehaviorLiveHazard reward
        (quittingPhaseSwitchProfile reward plan punish switch who) time =
      quittingPhaseSwitchRoots plan punish switch time who := by
  rw [quittingBehaviorLiveHazard, quittingPhaseSwitchProfile,
    quittingRootSequenceProfile, Nat.zero_add]

/-! ## Shifting a root sequence -/

omit [DecidableEq ι] in
/-- Starting a root-sequence profile at a later stage is the same as
restarting the shifted sequence at stage zero. -/
theorem quittingRootSequenceProfile_eq_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    quittingRootSequenceProfile reward roots start =
      quittingRootSequenceProfile reward (fun time => roots (start + time)) 0 := by
  funext player time history
  rw [quittingRootSequenceProfile, quittingRootSequenceProfile, Nat.zero_add]

omit [DecidableEq ι] in
/-- The terminal value of a root sequence at a later start is the terminal
value of the shifted sequence at stage zero. -/
theorem quittingRootSequenceTerminalValue_eq_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    quittingRootSequenceTerminalValue reward roots who start =
      quittingRootSequenceTerminalValue reward
        (fun time => roots (start + time)) who 0 := by
  rw [quittingRootSequenceTerminalValue, quittingRootSequenceTerminalValue,
    quittingRootSequenceProfile_eq_shift]

omit [DecidableEq ι] in
/-- At the switch stage the phase-switch sequence is worth exactly the
punishment plan restarted at its own stage zero. -/
theorem quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_switch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι) :
    quittingRootSequenceTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who switch =
      quittingRootSequenceTerminalValue reward punish who 0 := by
  rw [quittingRootSequenceTerminalValue_eq_shift,
    quittingPhaseSwitchRoots_comp_add]

/-- Deviating inside a phase switch and then reading the punishment phase is
the same as deviating, with the shifted hazard, inside the punishment plan
alone. -/
theorem quittingRootSequenceTerminalValue_update_quittingPhaseSwitchRoots_switch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceTerminalValue reward
        (quittingRootSequenceUpdate
          (quittingPhaseSwitchRoots plan punish switch) who hazard) who switch =
      quittingRootSequenceHazardTerminalValue reward punish who
        (fun offset => hazard (switch + offset)) 0 := by
  rw [quittingRootSequenceTerminalValue_eq_shift,
    quittingRootSequenceHazardTerminalValue]
  congr 1
  funext offset
  rw [quittingRootSequenceUpdate, quittingRootSequenceUpdate,
    quittingPhaseSwitchRoots_add]

/-! ## Survival products -/

omit [DecidableEq ι] in
/-- Joint survival from a later start is joint survival of the shifted
sequence from stage zero. -/
theorem quittingJointSurvivalWeight_eq_shift
    (x : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight x start fuel =
      quittingJointSurvivalWeight (fun time => x (start + time)) 0 fuel := by
  rw [quittingJointSurvivalWeight_eq_prod, quittingJointSurvivalWeight_eq_prod]
  exact Finset.prod_congr rfl fun offset _ => by rw [Nat.zero_add]

omit [DecidableEq ι] in
/-- Joint survival over a window only sees the roots inside that window. -/
theorem quittingJointSurvivalWeight_congr
    (x y : ℕ → ι → PMF Bool) (start fuel : ℕ)
    (hagree : ∀ offset, offset < fuel → x (start + offset) = y (start + offset)) :
    quittingJointSurvivalWeight x start fuel =
      quittingJointSurvivalWeight y start fuel := by
  rw [quittingJointSurvivalWeight_eq_prod, quittingJointSurvivalWeight_eq_prod]
  exact Finset.prod_congr rfl fun offset hoffset => by
    rw [hagree offset (Finset.mem_range.mp hoffset)]

omit [DecidableEq ι] in
/-- Over the plan phase the phase-switch sequence has the plan's joint
survival. -/
@[simp] theorem quittingJointSurvivalWeight_quittingPhaseSwitchRoots_plan
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) :
    quittingJointSurvivalWeight (quittingPhaseSwitchRoots plan punish switch) 0
        switch =
      quittingJointSurvivalWeight plan 0 switch := by
  refine quittingJointSurvivalWeight_congr _ _ 0 switch fun offset hoffset => ?_
  rw [Nat.zero_add]
  exact quittingPhaseSwitchRoots_of_lt plan punish hoffset

omit [DecidableEq ι] in
/-- Over any window inside the plan phase the truncated plan has the plan's
joint survival. -/
theorem quittingJointSurvivalWeight_quittingTruncatedRoots
    (roots : ℕ → ι → PMF Bool) (cutoff fuel : ℕ) (hfuel : fuel ≤ cutoff) :
    quittingJointSurvivalWeight (quittingTruncatedRoots roots cutoff) 0 fuel =
      quittingJointSurvivalWeight roots 0 fuel := by
  refine quittingJointSurvivalWeight_congr _ _ 0 fuel fun offset hoffset => ?_
  rw [Nat.zero_add]
  exact quittingTruncatedRoots_of_lt roots (lt_of_lt_of_le hoffset hfuel)

omit [DecidableEq ι] in
/-- **The survival product of a phase switch factors.**  Surviving the plan
phase and then `fuel` further punishment stages is surviving the plan phase
times surviving the punishment phase. -/
theorem quittingJointSurvivalWeight_quittingPhaseSwitchRoots_add
    (plan punish : ℕ → ι → PMF Bool) (switch fuel : ℕ) :
    quittingJointSurvivalWeight (quittingPhaseSwitchRoots plan punish switch) 0
        (switch + fuel) =
      quittingJointSurvivalWeight plan 0 switch *
        quittingJointSurvivalWeight punish 0 fuel := by
  rw [quittingJointSurvivalWeight_add,
    quittingJointSurvivalWeight_quittingPhaseSwitchRoots_plan]
  congr 1
  rw [quittingJointSurvivalWeight_eq_shift, Nat.zero_add,
    quittingPhaseSwitchRoots_comp_add]

/-! ## The payoff decomposition -/

omit [DecidableEq ι] in
/-- **The exact finite telescope.**  Any sequence obeying the live
prescribed-value recursion splits, at every horizon, into the
survival-weighted absorbing contributions collected inside the window plus
the survival-weighted value at the far end of the window. -/
theorem eq_sum_jointSurvivalWeight_mul_absorbingContribution_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → ℝ)
    (hvalue : IsQuittingLivePrescribedValue reward x who value)
    (start fuel : ℕ) :
    value start =
      (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight x start offset *
          quittingRootAbsorbingContribution reward (x (start + offset)) who) +
        quittingJointSurvivalWeight x start fuel * value (start + fuel) := by
  induction fuel with
  | zero =>
      simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ fuel ih =>
      have hstep : value (start + fuel) =
          quittingRootAbsorbingContribution reward (x (start + fuel)) who +
            quittingStationaryContinueMass (x (start + fuel)) *
              value (start + fuel + 1) := by
        rw [hvalue (start + fuel), quittingRootSuccessorPayoff_apply_eq_affine]
      rw [Finset.sum_range_succ, quittingJointSurvivalWeight_succ,
        show start + (fuel + 1) = start + fuel + 1 from rfl, ih, hstep]
      ring

omit [DecidableEq ι] in
/-- The truncated plan's whole terminal value is collected strictly before
the cutoff. -/
theorem quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequenceTerminalValue reward
        (quittingTruncatedRoots roots cutoff) who 0 =
      ∑ offset ∈ Finset.range cutoff,
        quittingJointSurvivalWeight roots 0 offset *
          quittingRootAbsorbingContribution reward (roots offset) who := by
  have hzero : quittingRootSequenceTerminalValue reward
      (quittingTruncatedRoots roots cutoff) who cutoff = 0 :=
    quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from reward _ who
      cutoff fun time htime => quittingTruncatedRoots_of_le roots htime
  have htelescope := eq_sum_jointSurvivalWeight_mul_absorbingContribution_add
    reward (quittingTruncatedRoots roots cutoff) who
    (quittingRootSequenceTerminalValue reward
      (quittingTruncatedRoots roots cutoff) who)
    (isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue reward _ who)
    0 cutoff
  simp only [Nat.zero_add] at htelescope
  rw [htelescope, hzero, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun offset hoffset => ?_
  have hlt : offset < cutoff := Finset.mem_range.mp hoffset
  rw [quittingJointSurvivalWeight_quittingTruncatedRoots roots cutoff offset hlt.le,
    quittingTruncatedRoots_of_lt roots hlt]

omit [DecidableEq ι] in
/-- **The payoff decomposition at an arbitrary cutoff.**  The value of a root
sequence is the value of its truncation at the cutoff plus the joint survival
through the cutoff times the value from the cutoff on.  Every phase-switch
decomposition below is this identity read at the switch stage. -/
theorem quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots roots cutoff) who 0 +
        quittingJointSurvivalWeight roots 0 cutoff *
          quittingRootSequenceTerminalValue reward roots who cutoff := by
  have htelescope := eq_sum_jointSurvivalWeight_mul_absorbingContribution_add
    reward roots who (quittingRootSequenceTerminalValue reward roots who)
    (isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue reward roots who)
    0 cutoff
  simp only [Nat.zero_add] at htelescope
  rw [quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
  exact htelescope

omit [DecidableEq ι] in
/-- **The prescribed phase-switch payoff decomposition.**  The switched
profile pays the truncated plan's value plus, weighted by the probability
that the plan phase is survived, the punishment plan's own value. -/
theorem quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι) :
    quittingRootSequenceTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who 0 =
      quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan switch) who 0 +
        quittingJointSurvivalWeight plan 0 switch *
          quittingRootSequenceTerminalValue reward punish who 0 := by
  rw [quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
      reward (quittingPhaseSwitchRoots plan punish switch) who switch,
    quittingTruncatedRoots_quittingPhaseSwitchRoots,
    quittingJointSurvivalWeight_quittingPhaseSwitchRoots_plan,
    quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_switch]

/-- **The deviated phase-switch payoff decomposition.**  A unilateral hazard
deviation against the switched profile pays exactly its value against the
*truncated* plan -- with its own hazard truncated too -- plus, weighted by
the joint survival of the deviated plan phase, its value against the
punishment plan alone. -/
theorem quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who hazard 0 =
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who
          (quittingTruncatedHazard hazard switch) 0 +
        quittingJointSurvivalWeight
            (quittingRootSequenceUpdate plan who hazard) 0 switch *
          quittingRootSequenceHazardTerminalValue reward punish who
            (fun offset => hazard (switch + offset)) 0 := by
  have hdeviated :
      quittingRootSequenceUpdate
        (quittingTruncatedRoots (quittingPhaseSwitchRoots plan punish switch)
          switch) who (quittingTruncatedHazard hazard switch) =
      quittingTruncatedRoots
        (quittingRootSequenceUpdate
          (quittingPhaseSwitchRoots plan punish switch) who hazard) switch :=
    quittingRootSequenceUpdate_quittingTruncatedRoots _ who hazard switch
  rw [quittingTruncatedRoots_quittingPhaseSwitchRoots] at hdeviated
  have hsurvival :
      quittingJointSurvivalWeight
          (quittingRootSequenceUpdate
            (quittingPhaseSwitchRoots plan punish switch) who hazard) 0 switch =
        quittingJointSurvivalWeight
          (quittingRootSequenceUpdate plan who hazard) 0 switch := by
    refine quittingJointSurvivalWeight_congr _ _ 0 switch fun offset hoffset => ?_
    rw [Nat.zero_add, quittingRootSequenceUpdate, quittingRootSequenceUpdate,
      quittingPhaseSwitchRoots_of_lt plan punish hoffset]
  rw [quittingRootSequenceHazardTerminalValue,
    quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
      reward (quittingRootSequenceUpdate
        (quittingPhaseSwitchRoots plan punish switch) who hazard) who switch,
    hsurvival,
    quittingRootSequenceTerminalValue_update_quittingPhaseSwitchRoots_switch,
    ← hdeviated]
  rfl

end GameTheory
