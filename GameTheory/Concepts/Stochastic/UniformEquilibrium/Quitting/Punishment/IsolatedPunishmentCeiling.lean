/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.Isolated.AnchorMaxAffine
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Stationary.FullRateStationaryVerifier
import GameTheory.Concepts.Stochastic.Models.Quitting.PunishmentLevel
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.ThreeBranchDisjunction

/-!
# The punishment ceiling is one quantity, seen four ways

Four objects, built in four different files for four different reasons, all
reduce to the same formula `max 0 (reward (quittingSingletonTerminal who) who)`
-- `quittingPositiveSingletonDebtCap reward who`:

1. **the positive singleton debt cap** itself
   (`quittingPositiveSingletonDebtCap`, `QuittingDebtAugmentedEdge.lean`);
2. **the isolated-coordinate anchored value**, the `P = 1`, `T = 0` regime of
   `Math.MaxAffineStopping.System.anchoredValue` at anchor `0`
   (`quittingPositiveSingletonDebtCap_eq_anchoredValue`,
   `QuittingIsolatedAnchorMaxAffine.lean` -- already proved there, not
   reproved here);
3. **the saturated branch of the stationary full-rate unilateral cap**
   (`quittingStationaryFullRateUnilateralCap`, taken on the face where the
   fixed opponents' continuation mass is exactly one,
   `QuittingFullRateStationaryVerifier.lean`); and
4. **the right-hand side of the quitting punishment ceiling**
   (`punishmentLevel_quittingGame_le_max`, `QuittingPunishmentLevel.lean`).

Both new identifications below (2 was already landed) are literally `rfl`
once the saturated/ceiling side is unfolded: every one of these files
independently wrote `max 0 (reward (quittingSingletonTerminal who) who)`, not
a lookalike expression, so there is no `max`-versus-`sup` or
inequality-versus-equality mismatch to paper over -- the coincidence really
is exact.

**What stays an inequality.** `punishmentLevel_quittingGame_le_max` is a
`≤`, not a `=`: the punishment level quantifies over *every* opponent
behavior profile, of which the all-continue profile behind objects 2/3/4's
regime is only one. Nothing here upgrades that ceiling to an equality for
`punishmentLevel` itself -- see the negative finding below.

## The payoff: mismatch is ceiling minus honest value

`QuittingThreeBranchDisjunction.lean`'s isolated-negative branch proves the
anchored companion mismatch at an isolated coordinate of negative solo
weight is exactly `-reward (quittingSingletonTerminal who) who`
(`quittingIsolatedNegativeCycle_mismatch_eq`), leaving the limit `anchorLimit`
as a free parameter satisfying a `Tendsto` hypothesis. Combined with
`QuittingIsolatedAnchorMaxAffine.lean`'s
`tendsto_iterate_soloQuitAnchor_of_isolated_via_anchoredValue`, that limit is
not free at all: it is uniquely `quittingPositiveSingletonDebtCap reward who`,
by uniqueness of limits in `ℝ`. Substituting gives the folk-theorem reading
promised by the review:

    mismatch = ceiling - honest value

(`quittingIsolatedNegativeCycle_mismatch_eq_ceiling_sub_honestValue`), and
chaining through the punishment ceiling itself gives a genuine (if, on this
branch, numerically trivial) individual-rationality-flavored bound
(`punishmentLevel_quittingGame_le_honestValue_add_mismatch`).

## What does not close: no matching lower bound

The review also asks whether the ceiling can be turned into a lower bound at
the isolated configuration, which would let the no-go generator
(`not_isUniformEquilibriumPayoff_of_punishmentLevel_gt`) reject a table
outright. **It cannot, and this is a theorem, not a gap.**
`punishmentLevel` infimizes over *every* opponent behavior profile, including
profiles where the opponent quits deterministically and drags the deviator
onto a terminal state that does not contain them -- a coordinate `reward`
is entirely unconstrained on. `punishmentLevel_lt_quittingPositiveSingletonDebtCap`
below exhibits a two-player reward table and horizon at which the punishment
level sits *strictly below* the very ceiling objects 1-4 agree on: the
"opponents are silent" regime that saturates objects 2/3/4 is only *one*
profile in `punishmentLevel`'s infimum, never forced to be the minimizing
one.

## Main results

* `quittingStationaryFullRateUnilateralCap_eq_quittingPositiveSingletonDebtCap_of_eq_one` --
  object 3 (saturated branch) `=` object 1.
* `punishmentLevel_quittingGame_le_quittingPositiveSingletonDebtCap` --
  object 4's ceiling restated with object 1 on the right.
* `quittingIsolatedNegativeCycle_mismatch_eq_ceiling_sub_honestValue` --
  deliverable (2): mismatch `=` ceiling `-` honest value.
* `punishmentLevel_quittingGame_le_honestValue_add_mismatch` -- the
  punishment ceiling read through that identity.
* `QuittingIsolatedPunishmentLowerBoundCounterexample.
  punishmentLevel_lt_quittingPositiveSingletonDebtCap` -- deliverable (3)
  does not hold in general: a witness reward table and horizon driving
  `punishmentLevel` strictly below the ceiling.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct Filter StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Objects 1 and 3: the saturated stationary cap is the debt cap -/

/-- **Object 3 (saturated branch) `=` object 1.** On the face where the
fixed opponents' continuation mass is exactly one, the stationary full-rate
unilateral cap is *syntactically* `quittingPositiveSingletonDebtCap`: both
sides are `max 0 (reward (quittingSingletonTerminal who) who)`. -/
theorem quittingStationaryFullRateUnilateralCap_eq_quittingPositiveSingletonDebtCap_of_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1) :
    quittingStationaryFullRateUnilateralCap reward root who =
      quittingPositiveSingletonDebtCap reward who :=
  quittingStationaryFullRateUnilateralCap_of_eq_one reward root who hmass

/-! ## Objects 1 and 4: the punishment ceiling's bound is the debt cap -/

/-- **Object 4's ceiling, restated with object 1 on the right.** Purely a
rewrite of `punishmentLevel_quittingGame_le_max`: its bound `max 0 (reward
(quittingSingletonTerminal who) who)` already *is*
`quittingPositiveSingletonDebtCap reward who`. -/
theorem punishmentLevel_quittingGame_le_quittingPositiveSingletonDebtCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ) :
    (quittingGame reward).punishmentLevel none T who ≤
      quittingPositiveSingletonDebtCap reward who :=
  punishmentLevel_quittingGame_le_max reward who hC T

/-! ## Deliverable (2): mismatch is ceiling minus honest value -/

/-- **The anchor limit is not free: it is the debt cap.** Whenever the
`quittingCompanionComposite` iterates from `quittingPositiveSingletonDebtCap`
converge along an isolated window, they converge to that same cap --
`tendsto_iterate_soloQuitAnchor_of_isolated_via_anchoredValue` names the
limit, uniqueness of limits in `ℝ` pins any other named limit to it. -/
theorem quittingCompanionComposite_iterate_anchorLimit_eq_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (hiso : IsQuittingIsolatedWindow roots who period)
    {anchorLimit : ℝ}
    (hanchor : Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward roots who 0 period)^[N]
          (quittingPositiveSingletonDebtCap reward who))
      atTop (nhds anchorLimit)) :
    anchorLimit = quittingPositiveSingletonDebtCap reward who :=
  tendsto_nhds_unique hanchor
    (tendsto_iterate_soloQuitAnchor_of_isolated_via_anchoredValue reward roots who period hiso)

/-- **Deliverable (2), the payoff.** At an isolated coordinate of negative
solo weight, the anchored companion mismatch is exactly the punishment
ceiling (object 1, the isolated debt cap `=` object 2 the anchored value `=`
the saturated branch of object 3) minus the block's honest value at that
coordinate -- a folk-theorem reading of the obstruction found in
`QuittingThreeBranchDisjunction.lean`. -/
theorem quittingIsolatedNegativeCycle_mismatch_eq_ceiling_sub_honestValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    {who : ι}
    (hiso : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period)
    (hneg : reward (quittingSingletonTerminal who) who < 0) :
    quittingPositiveSingletonDebtCap reward who - terminal who =
      -reward (quittingSingletonTerminal who) who :=
  quittingIsolatedNegativeCycle_mismatch_eq reward terminal period block hblock hiso hneg
    (quittingPositiveSingletonDebtCap reward who)
    (tendsto_iterate_soloQuitAnchor_of_isolated_via_anchoredValue reward
      (quittingFiniteNashBellmanPathRoots period block) who period hiso)

/-- **The punishment ceiling, read through the mismatch identity.** At every
finite horizon, the punishment level is at most the block's honest value at
the isolated coordinate plus the mismatch -- the individually-rational shape
the review asked for, even though on this branch (`hneg`) both sides collapse
to `0`: the ceiling itself is `max 0 (negative) = 0`, and
`quittingIsolatedNegativeCycle_value_eq` identifies `terminal who` with that
same negative solo weight the mismatch cancels. The content is the shape,
not the numeral: elsewhere, off this branch, the two summands stop being
negatives of each other. -/
theorem punishmentLevel_quittingGame_le_honestValue_add_mismatch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    (hiso : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period)
    (hneg : reward (quittingSingletonTerminal who) who < 0) :
    (quittingGame reward).punishmentLevel none T who ≤
      terminal who + -reward (quittingSingletonTerminal who) who := by
  have hceiling := punishmentLevel_quittingGame_le_quittingPositiveSingletonDebtCap reward who hC T
  have hmismatch := quittingIsolatedNegativeCycle_mismatch_eq_ceiling_sub_honestValue reward
    terminal period block hblock hiso hneg
  linarith

/-! ## Deliverable (3): no matching lower bound, in general

The two lemmas below are the mirror image of `QuittingSimpleBranches.lean`'s
all-continue machinery, with `false` (quit) in place of `true` (continue).
They exist only to power the counterexample at the end of this section. -/

/-- The stationary profile under which every player always quits: the
mirror image of `quittingAlwaysContinueProfile`. -/
def quittingAlwaysQuitProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).BehaviorProfile :=
  (quittingGame reward).stationaryBehaviorProfile fun _ => PMF.pure true

/-- The root action law after a unilateral deviation from all-quit: the
mirror image of `stageActionDist_update_quittingAlwaysContinueProfile`. -/
theorem stageActionDist_update_quittingAlwaysQuitProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {t : ℕ} (h : (quittingGame reward).Hist t) :
    (quittingGame reward).stageActionDist
        (Function.update (quittingAlwaysQuitProfile reward) who deviation) h =
      pmfPi (Function.update (fun _ : ι => PMF.pure true) who (deviation t h)) := by
  change (quittingGame reward).stageActionDist
      (Function.update ((quittingGame reward).stationaryBehaviorProfile
        fun _ : ι => PMF.pure true) who deviation) h = _
  exact (quittingGame reward).stageActionDist_update_stationaryBehaviorProfile
    (fun _ : ι => PMF.pure true) who deviation h

/-- Under a unilateral deviation from all-quit, every supported joint action
keeps every opponent quitting: the mirror image of
`action_eq_false_of_mem_support_update_quittingAlwaysContinue`. -/
theorem action_eq_true_of_mem_support_update_quittingAlwaysQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {t : ℕ} (h : (quittingGame reward).Hist t)
    (action : ι → Bool)
    (haction : action ∈ ((quittingGame reward).stageActionDist
      (Function.update (quittingAlwaysQuitProfile reward) who deviation)
      h).support)
    (other : ι) (hother : other ≠ who) : action other = true := by
  have hdist := stageActionDist_update_quittingAlwaysQuitProfile reward who deviation h
  rw [hdist] at haction
  let factors : ι → PMF Bool :=
    Function.update (fun _ : ι => PMF.pure true) who (deviation t h)
  have hcoord : action other ∈
      (Math.ProbabilityMassFunction.pushforward (pmfPi factors)
        (fun joint => joint other)).support := by
    rw [Math.ProbabilityMassFunction.pushforward, PMF.mem_support_map_iff]
    exact ⟨action, haction, rfl⟩
  rw [pmfPi_push_coord factors other] at hcoord
  have hfactor : factors other = PMF.pure true := by
    simp [factors, Function.update_of_ne hother]
  rw [hfactor] at hcoord
  exact (PMF.mem_support_pure_iff _ _).mp (by simpa [hfactor] using hcoord)

/-- **One step of all-quit absorbs, at every opponent.** A unilateral
deviation from all-quit reaches, after one stage, a terminal state
containing some designated opponent `other`. Only the first step is proved
-- all the counterexample below needs -- rather than the full "stays
absorbed forever" induction of
`state_eq_none_or_singleton_of_mem_support_update_quittingAlwaysContinue`. -/
theorem exists_state_containsOther_of_mem_support_update_quittingAlwaysQuit_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who other : ι) (hother : other ≠ who)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (h' : (quittingGame reward).Hist 1)
    (hh' : h' ∈ ((quittingGame reward).histDist
      (Function.update (quittingAlwaysQuitProfile reward) who deviation) none 1).support) :
    ∃ S : {S : Finset ι // S.Nonempty}, h'.2 = some S ∧ other ∈ (S : Finset ι) := by
  classical
  obtain ⟨h, hh, action, haction, next, hnext, hEq⟩ :=
    ((quittingGame reward).mem_support_histDist_succ
      (Function.update (quittingAlwaysQuitProfile reward) who deviation) none 0 h').mp hh'
  change (ι → Bool) at action
  have hstate : h.2 = none := by
    have heq : h = (quittingGame reward).emptyHist none := by simpa using hh
    rw [heq]; rfl
  have hact_other : action other = true :=
    action_eq_true_of_mem_support_update_quittingAlwaysQuit reward who deviation h action
      haction other hother
  have hmem : other ∈ ({player | action player = true} : Finset ι) := by
    simpa using hact_other
  have hnonempty : ({player | action player = true} : Finset ι).Nonempty := ⟨other, hmem⟩
  rw [hstate, quittingGame_transition_none, dif_pos hnonempty] at hnext
  refine ⟨⟨_, hnonempty⟩, ?_, hmem⟩
  rw [hEq]
  simpa using hnext

/-! ## Negative finding: no reward table makes `punishmentLevel` match the
ceiling from below, in general

A two-player witness table and horizon at which the punishment level sits
strictly below `quittingPositiveSingletonDebtCap` -- the very quantity
objects 1-4 agree on. Opponent `false` quits with certainty every stage; by
`exists_state_containsOther_of_mem_support_update_quittingAlwaysQuit_one`
this forces absorption, after one stage, onto a terminal state that always
contains `false`, hence is never the deviator's own singleton `{true}` --
and the table scores every such state a ruinous `-1000` for `true`,
regardless of what `true` does. -/
namespace QuittingIsolatedPunishmentLowerBoundCounterexample

/-- The witness reward table: the isolated singleton quit by `true` is
harmless (`0`), but every terminal configuration in which the opponent
`false` has also quit -- the only ones reachable once `false` commits to
quitting -- costs `true` a ruinous `-1000`. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S i => if i = true then (if (S : Finset Bool) = {true} then (0 : ℝ) else -1000) else 0

/-- `reward`'s value at `true`, unfolded. -/
theorem reward_true (S : {S : Finset Bool // S.Nonempty}) :
    reward S true = if (S : Finset Bool) = {true} then (0 : ℝ) else -1000 := by
  simp [reward]

/-- The witness table is bounded, as `punishmentLevel_quittingGame_le_max`
and its ilk require. -/
theorem abs_reward_true_le (S : {S : Finset Bool // S.Nonempty}) :
    |reward S true| ≤ 1000 := by
  rw [reward_true]; split <;> norm_num

/-- The witness table's stage payoffs are bounded, feeding
`abs_bestResponseAverageAgainstProfile_le`. -/
theorem abs_stagePayoff_true_le (s : (quittingGame reward).State) (a : Bool → Bool) :
    |(quittingGame reward).stagePayoff s a true| ≤ 1000 := by
  cases s with
  | none => simp [quittingGame]
  | some S => exact abs_reward_true_le S

/-- The singleton-quit reward is `0`, so the punishment ceiling here is `0`. -/
theorem quittingPositiveSingletonDebtCap_reward_eq :
    quittingPositiveSingletonDebtCap reward true = 0 := by
  unfold quittingPositiveSingletonDebtCap
  rw [reward_true, quittingSingletonTerminal]
  simp

/-- Every deviation of `true` against the all-quit profile lands, after one
stage, on a terminal state other than the harmless singleton `{true}`. -/
theorem exists_state_ne_singleton_true
    (deviation : (quittingGame reward).BehaviorStrategy true)
    (h' : (quittingGame reward).Hist 1)
    (hh' : h' ∈ ((quittingGame reward).histDist
      (Function.update (quittingAlwaysQuitProfile reward) true deviation) none 1).support) :
    ∃ S : {S : Finset Bool // S.Nonempty}, h'.2 = some S ∧ (S : Finset Bool) ≠ {true} := by
  obtain ⟨S, hS, hmem⟩ :=
    exists_state_containsOther_of_mem_support_update_quittingAlwaysQuit_one
      reward true false (by decide) deviation h' hh'
  refine ⟨S, hS, fun hcontra => ?_⟩
  rw [hcontra] at hmem
  simp at hmem

/-- The expected stage payoff at epoch `1` is exactly `-1000`, for any
deviation of `true`: every reachable terminal state at that epoch scores
`-1000` (`exists_state_ne_singleton_true`, `reward_true`). -/
theorem expectedStagePayoff_update_quittingAlwaysQuit_one
    (deviation : (quittingGame reward).BehaviorStrategy true) :
    (quittingGame reward).expectedStagePayoff
        (Function.update (quittingAlwaysQuitProfile reward) true deviation) none 1 true =
      -1000 := by
  unfold StochasticGame.expectedStagePayoff
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ (fun _ => (-1000 : ℝ))
    (fun h hh => by
      rw [stageEUAt_quittingGame_eq_stateReward]
      obtain ⟨S, hS, hne⟩ := exists_state_ne_singleton_true deviation h hh
      rw [hS]
      change reward S true = -1000
      rw [reward_true, if_neg hne]),
    expect_const]

/-- The expected stage payoff at epoch `0` is `0`: play has not yet left the
active state. -/
theorem expectedStagePayoff_update_quittingAlwaysQuit_zero
    (deviation : (quittingGame reward).BehaviorStrategy true) :
    (quittingGame reward).expectedStagePayoff
        (Function.update (quittingAlwaysQuitProfile reward) true deviation) none 0 true = 0 := by
  unfold StochasticGame.expectedStagePayoff
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ (fun _ => (0 : ℝ))
    (fun h hh => by
      have heq : h = (quittingGame reward).emptyHist none := by simpa using hh
      rw [stageEUAt_quittingGame_eq_stateReward, heq]; rfl),
    expect_const]

/-- The finite-horizon-`2` average payoff against the all-quit profile is
exactly `-500` for every deviation of `true`: the Cesàro average of a `0`
followed by a `-1000`. -/
theorem finiteAveragePayoff_update_quittingAlwaysQuit_two
    (deviation : (quittingGame reward).BehaviorStrategy true) :
    (quittingGame reward).finiteAveragePayoff none 2
        (Function.update (quittingAlwaysQuitProfile reward) true deviation) true = -500 := by
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset Bool // S.Nonempty}))
  letI : ∀ player : Bool, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  rw [(quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff,
    show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
    expectedStagePayoff_update_quittingAlwaysQuit_zero,
    expectedStagePayoff_update_quittingAlwaysQuit_one]
  norm_num

/-- The best response against the all-quit profile at horizon `2` is `-500`:
every deviation gives the same value, so the supremum is that constant. -/
theorem bestResponseAverageAgainstProfile_eq :
    (quittingGame reward).bestResponseAverageAgainstProfile none 2 true
        (quittingAlwaysQuitProfile reward) = -500 := by
  haveI : Nonempty ((quittingGame reward).Act true) := inferInstanceAs (Nonempty Bool)
  haveI := (quittingGame reward).nonempty_behaviorStrategy true
  unfold StochasticGame.bestResponseAverageAgainstProfile
  simp only [finiteAveragePayoff_update_quittingAlwaysQuit_two]
  exact ciSup_const

/-- **The counterexample.** At horizon `2`, the punishment level of this
table is strictly below `quittingPositiveSingletonDebtCap reward true = 0`
-- objects 1-4's shared ceiling -- witnessed by the all-quit opponent
profile. So no identification in this file, however uniform, upgrades to a
matching *lower* bound on `punishmentLevel` in general: deliverable (3)
does not close. -/
theorem punishmentLevel_lt_quittingPositiveSingletonDebtCap :
    (quittingGame reward).punishmentLevel none 2 true <
      quittingPositiveSingletonDebtCap reward true := by
  haveI : Nonempty ((quittingGame reward).Act true) := inferInstanceAs (Nonempty Bool)
  rw [quittingPositiveSingletonDebtCap_reward_eq]
  have hbdd : BddBelow (Set.range
      ((quittingGame reward).bestResponseAverageAgainstProfile none 2 true)) :=
    ⟨-1000, by
      rintro _ ⟨τ, rfl⟩
      exact (abs_le.mp ((quittingGame reward).abs_bestResponseAverageAgainstProfile_le
        (by norm_num : (0 : ℝ) ≤ 1000) abs_stagePayoff_true_le none 2 τ)).1⟩
  calc (quittingGame reward).punishmentLevel none 2 true
      ≤ (quittingGame reward).bestResponseAverageAgainstProfile none 2 true
          (quittingAlwaysQuitProfile reward) := by
        unfold StochasticGame.punishmentLevel
        exact ciInf_le hbdd (quittingAlwaysQuitProfile reward)
    _ = -500 := bestResponseAverageAgainstProfile_eq
    _ < 0 := by norm_num

end QuittingIsolatedPunishmentLowerBoundCounterexample

end GameTheory
