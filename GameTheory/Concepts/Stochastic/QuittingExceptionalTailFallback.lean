/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingStationaryBestResponse
import GameTheory.Concepts.Stochastic.QuittingOpponentActionMass
import GameTheory.Concepts.Stochastic.QuittingRootPerturbation
import GameTheory.Concepts.Stochastic.QuittingNonSoloTail

/-!
# Exceptional-tail stationary fallback

This file formalizes the deterministic assembly at the exceptional seam.
A solo stationary root, at which only one player has positive quit hazard,
has terminal payoff equal to the corresponding singleton reward.  Its exact
unilateral caps are Quit versus Never for the exceptional player and Quit-now
versus waiting for solo absorption for every other player.

The capstone exposes the two probabilistic inputs as hypotheses: concentration
of the tail payoff near the singleton reward, and stability of an immediate-
Quit payoff after deleting the other current hazards.  Together with tail
Nash inequalities, the resulting stationary profile is a terminal
`β + 4Mη`-Nash profile.  A filter-level corollary selects errors approaching
`β` when `η` tends to zero.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Mapping a finite law through a deterministic retraction can only move
total-variation mass carried by points that the retraction changes. -/
theorem pmfTV_self_map_le_expect_moved
    {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (distribution : PMF Ω) (retraction : Ω → Ω) :
    pmfTV distribution (distribution.map retraction) ≤
      expect distribution (fun outcome =>
        if retraction outcome ≠ outcome then 1 else 0) := by
  change
    (∑ outcome : Ω,
        max ((distribution outcome).toReal -
          ((distribution.map retraction) outcome).toReal) 0) ≤ _
  rw [expect_eq_sum]
  apply Finset.sum_le_sum
  intro outcome _
  change
    max ((distribution outcome).toReal -
      ((distribution.map retraction) outcome).toReal) 0 ≤
        (distribution outcome).toReal *
          (if retraction outcome ≠ outcome then 1 else 0)
  by_cases hmoved : retraction outcome = outcome
  · have hmass : distribution outcome ≤
        distribution.map retraction outcome := by
      have hmass' := Math.ProbabilityMassFunction.le_pushforward_apply
        distribution retraction outcome
      change distribution outcome ≤
        distribution.map retraction (retraction outcome) at hmass'
      rwa [hmoved] at hmass'
    have hmassReal : (distribution outcome).toReal ≤
        ((distribution.map retraction) outcome).toReal :=
      ENNReal.toReal_mono (PMF.apply_ne_top _ _) hmass
    rw [max_eq_right (sub_nonpos.mpr hmassReal)]
    simp [hmoved]
  · have hdistribution : 0 ≤ (distribution outcome).toReal :=
      ENNReal.toReal_nonneg
    have hmapped : 0 ≤ ((distribution.map retraction) outcome).toReal :=
      ENNReal.toReal_nonneg
    rw [if_pos hmoved, mul_one]
    exact max_le (by linarith) hdistribution

/-- A bounded expectation changes by at most twice its bound times the
probability that a deterministic retraction changes the sampled point. -/
theorem abs_expect_sub_expect_map_le_moved
    {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (distribution : PMF Ω) (retraction : Ω → Ω)
    (value : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hvalue : ∀ outcome, |value outcome| ≤ M) :
    |expect distribution value -
        expect (distribution.map retraction) value| ≤
      2 * M * expect distribution (fun outcome =>
        if retraction outcome ≠ outcome then 1 else 0) := by
  calc
    _ ≤ (2 * M) * pmfTV distribution (distribution.map retraction) :=
      abs_expect_sub_le_two_mul_pmfTV distribution
        (distribution.map retraction) value hvalue
    _ ≤ (2 * M) * expect distribution (fun outcome =>
          if retraction outcome ≠ outcome then 1 else 0) :=
      mul_le_mul_of_nonneg_left
        (pmfTV_self_map_le_expect_moved distribution retraction) (by positivity)
    _ = 2 * M * expect distribution (fun outcome =>
          if retraction outcome ≠ outcome then 1 else 0) := by ring

/-- A stationary root at which only `owner` may quit. -/
def quittingSoloStationaryRoot (owner : ι) (hazard : PMF Bool) :
    ι → PMF Bool :=
  Function.update (fun _ => PMF.pure false) owner hazard

/-- Joint action at which only `owner` may take the supplied action. -/
def quittingSoloAction (owner : ι) (action : Bool) : ι → Bool :=
  Function.update (fun _ => false) owner action

/-- Delete every coordinate except `first` and `second` from a joint action. -/
def quittingKeepPairAction (first second : ι) (action : ι → Bool) :
    ι → Bool :=
  fun player =>
    if player = first then action player
    else if player = second then action player
    else false

/-- Some coordinate outside the distinguished pair quits. -/
def quittingSomeOutsidePairQuits
    (first second : ι) (action : ι → Bool) : Prop :=
  ∃ player, player ≠ first ∧ player ≠ second ∧ action player = true

/-- Boolean flag for a quitter outside the distinguished pair. -/
noncomputable def quittingOutsidePairQuitFlag
    (first second : ι) (action : ι → Bool) : Bool := by
  classical
  exact decide (quittingSomeOutsidePairQuits first second action)

/-- Real indicator for a quitter outside the distinguished pair. -/
def quittingOutsidePairQuitIndicator
    (first second : ι) (action : ι → Bool) : ℝ :=
  if quittingOutsidePairQuitFlag first second action = true then 1 else 0

omit [Fintype ι] in
/-- The keep-pair retraction moves exactly the actions with a quitter outside
the pair. -/
theorem quittingKeepPairAction_ne_iff
    (first second : ι) (action : ι → Bool) :
    quittingKeepPairAction first second action ≠ action ↔
      quittingSomeOutsidePairQuits first second action := by
  classical
  constructor
  · intro hmoved
    by_contra houtside
    apply hmoved
    funext player
    by_cases hfirst : player = first
    · simp [quittingKeepPairAction, hfirst]
    · by_cases hsecond : player = second
      · simp [quittingKeepPairAction, hsecond]
      · cases haction : action player with
        | false => simp [quittingKeepPairAction, hfirst, hsecond]
        | true =>
            exact (houtside ⟨player, hfirst, hsecond, haction⟩).elim
  · rintro ⟨player, hfirst, hsecond, hquit⟩ heq
    have hcoordinate := congrFun heq player
    simp [quittingKeepPairAction, hfirst, hsecond, hquit] at hcoordinate

omit [Fintype ι] [DecidableEq ι] in
theorem quittingOutsidePairQuitFlag_eq_true_iff
    (first second : ι) (action : ι → Bool) :
    quittingOutsidePairQuitFlag first second action = true ↔
      quittingSomeOutsidePairQuits first second action := by
  classical
  simp [quittingOutsidePairQuitFlag]

omit [Fintype ι] in
theorem quittingSomeOutsidePairQuits_update_second_iff
    (first second : ι) (action : ι → Bool) (secondAction : Bool) :
    quittingSomeOutsidePairQuits first second
        (Function.update action second secondAction) ↔
      quittingSomeOutsidePairQuits first second action := by
  constructor
  · rintro ⟨player, hfirst, hsecond, hquit⟩
    refine ⟨player, hfirst, hsecond, ?_⟩
    simpa [Function.update_of_ne hsecond] using hquit
  · rintro ⟨player, hfirst, hsecond, hquit⟩
    refine ⟨player, hfirst, hsecond, ?_⟩
    simpa [Function.update_of_ne hsecond] using hquit

omit [Fintype ι] in
/-- The outside-pair flag ignores either coordinate that the retraction
keeps; this orientation is the one used when forcing `second` to quit. -/
theorem quittingOutsidePairQuitFlag_ignores_second
    (first second : ι) :
    Ignores (A := fun _ : ι => Bool) second
      (fun action => PMF.pure
        (quittingOutsidePairQuitFlag first second action)) := by
  intro action secondAction
  apply congrArg PMF.pure
  rw [Bool.eq_iff_iff,
    quittingOutsidePairQuitFlag_eq_true_iff,
    quittingOutsidePairQuitFlag_eq_true_iff]
  exact quittingSomeOutsidePairQuits_update_second_iff
    first second action secondAction

/-- Changing `second`'s marginal does not change the probability of a quitter
outside the distinguished pair. -/
theorem expect_pmfPi_outsidePairQuits_update_invariant
    (root : ι → PMF Bool) (first second : ι) (marginal : PMF Bool) :
    expect (pmfPi (Function.update root second marginal))
        (quittingOutsidePairQuitIndicator first second) =
      expect (pmfPi root)
        (quittingOutsidePairQuitIndicator first second) := by
  have hbind := pmfPi_bind_ignores_coord
    (A := fun _ : ι => Bool) root second marginal
    (fun action => PMF.pure
      (quittingOutsidePairQuitFlag first second action))
    (quittingOutsidePairQuitFlag_ignores_second first second)
  have hexpect := congrArg (fun distribution : PMF Bool =>
    expect distribution (fun flag => if flag = true then (1 : ℝ) else 0))
    hbind
  change expect (pmfPi (Function.update root second marginal))
      (fun action =>
        if quittingOutsidePairQuitFlag first second action = true
        then 1 else 0) =
    expect (pmfPi root) (fun action =>
      if quittingOutsidePairQuitFlag first second action = true
      then 1 else 0)
  simpa [expect_bind, expect_pure] using hexpect

omit [Fintype ι] [DecidableEq ι] in
/-- A quitter outside `{first, second}` is in particular an opponent of
`first`. -/
theorem quittingOutsidePairQuitIndicator_le_opponentQuitIndicator
    (first second : ι) (action : ι → Bool) :
    quittingOutsidePairQuitIndicator first second action ≤
      quittingSomeOpponentQuitsIndicator first action := by
  by_cases houtside :
      quittingSomeOutsidePairQuits first second action
  · have houtsideFlag :=
      (quittingOutsidePairQuitFlag_eq_true_iff first second action).2 houtside
    obtain ⟨player, hfirst, _hsecond, hquit⟩ := houtside
    have hopponent : quittingSomeOpponentQuits first action :=
      ⟨player, hfirst, hquit⟩
    have hopponentFlag :=
      (quittingOpponentQuitFlag_eq_true_iff first action).2 hopponent
    simp [quittingOutsidePairQuitIndicator,
      quittingSomeOpponentQuitsIndicator, houtsideFlag, hopponentFlag]
  · have houtsideFlag :
        quittingOutsidePairQuitFlag first second action ≠ true :=
      fun h => houtside
        ((quittingOutsidePairQuitFlag_eq_true_iff first second action).1 h)
    cases hflag : quittingOutsidePairQuitFlag first second action
    · unfold quittingOutsidePairQuitIndicator
      rw [hflag]
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold quittingSomeOpponentQuitsIndicator
      split_ifs <;> norm_num
    · exact (houtsideFlag hflag).elim

/-- The outside-pair probability after forcing `second` is bounded by the
original one-stage probability that some opponent of `first` quits. -/
theorem expect_pmfPi_outsidePairQuits_le_one_sub_continueMass
    (root : ι → PMF Bool) (first second : ι) (marginal : PMF Bool) :
    expect (pmfPi (Function.update root second marginal))
        (quittingOutsidePairQuitIndicator first second) ≤
      1 - quittingStationaryFixedOpponentsContinueMass root first := by
  rw [expect_pmfPi_outsidePairQuits_update_invariant]
  calc
    expect (pmfPi root)
          (quittingOutsidePairQuitIndicator first second) ≤
        expect (pmfPi root)
          (quittingSomeOpponentQuitsIndicator first) :=
      expect_mono (pmfPi root) _ _
        (quittingOutsidePairQuitIndicator_le_opponentQuitIndicator
          first second)
    _ = 1 - quittingStationaryFixedOpponentsContinueMass root first := by
      have hmass := expect_pmfPi_someOpponentQuits_eq_one_sub_continueMass
        root first (root first)
      have hroot : Function.update root first (root first) = root := by
        funext player
        by_cases hp : player = first
        · subst player
          simp
        · simp [Function.update_of_ne hp]
      simpa [hroot, quittingStationaryFixedOpponentsContinueMass,
        quittingFixedOpponentsContinueMass,
        quittingStationaryContinueMass] using hmass

/-- Keeping only `first` and a surely-quitting `second` pushes the original
product law to the corresponding solo-root law. -/
theorem map_pmfPi_update_pure_true_keepPair
    (root : ι → PMF Bool) {first second : ι} (hne : second ≠ first) :
    (pmfPi (Function.update root second (PMF.pure true))).map
        (quittingKeepPairAction first second) =
      pmfPi (Function.update
        (quittingSoloStationaryRoot first (root first)) second
        (PMF.pure true)) := by
  have hpush := pmfPi_push_coordwise
    (A := fun _ : ι => Bool) (B := fun _ : ι => Bool)
    (Function.update root second (PMF.pure true))
    (fun player action =>
      if player = first then action
      else if player = second then action
      else false)
  change
    (pmfPi (Function.update root second (PMF.pure true))).map
        (quittingKeepPairAction first second) =
      pmfPi (fun player =>
        ((Function.update root second (PMF.pure true)) player).map
          (fun action =>
            if player = first then action
            else if player = second then action
            else false)) at hpush
  rw [hpush]
  apply congrArg pmfPi
  funext player
  by_cases hfirst : player = first
  · subst player
    simp [quittingSoloStationaryRoot, Ne.symm hne]
    exact PMF.map_id _
  · by_cases hsecond : player = second
    · subst player
      simp [hfirst, quittingSoloStationaryRoot]
      exact PMF.map_id _
    · simp [hfirst, hsecond, quittingSoloStationaryRoot]
      exact PMF.map_const _ _

/-- Deleting every current hazard except `owner`'s changes another player's
immediate-Quit payoff by at most `2M` times the current probability that some
opponent of `owner` quits. -/
theorem abs_quittingStationaryFixedOpponentsQuitValue_sub_solo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {owner who : ι} (hne : who ≠ owner)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingStationaryFixedOpponentsQuitValue reward root who -
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner (root owner)) who| ≤
      2 * M *
        (1 - quittingStationaryFixedOpponentsContinueMass root owner) := by
  let distribution :=
    pmfPi (Function.update root who (PMF.pure true))
  let retraction := quittingKeepPairAction owner who
  let value : (ι → Bool) → ℝ := fun action =>
    quittingRootPayoff reward (0 : Payoff ι) action who
  have hvalue : ∀ action, |value action| ≤ M := by
    intro action
    dsimp only [value]
    exact abs_quittingRootPayoff_le reward (0 : Payoff ι)
      hreward (fun player => by simpa using hM) action who
  have hmap : distribution.map retraction =
      pmfPi (Function.update
        (quittingSoloStationaryRoot owner (root owner)) who
        (PMF.pure true)) := by
    simpa [distribution, retraction] using
      map_pmfPi_update_pure_true_keepPair root hne
  have hmoved :
      expect distribution (fun action =>
          if retraction action ≠ action then 1 else 0) =
        expect distribution
          (quittingOutsidePairQuitIndicator owner who) := by
    apply congrArg (expect distribution)
    funext action
    change
      (if quittingKeepPairAction owner who action ≠ action then 1 else 0) =
        (if quittingOutsidePairQuitFlag owner who action = true then 1 else 0)
    by_cases houtside :
        quittingSomeOutsidePairQuits owner who action
    · have hmoved :=
        (quittingKeepPairAction_ne_iff owner who action).2 houtside
      have hflag :=
        (quittingOutsidePairQuitFlag_eq_true_iff owner who action).2 houtside
      simp [hmoved, hflag]
    · have hmoved :
          ¬quittingKeepPairAction owner who action ≠ action :=
        fun h => houtside
          ((quittingKeepPairAction_ne_iff owner who action).1 h)
      have hflag :
          quittingOutsidePairQuitFlag owner who action ≠ true :=
        fun h => houtside
          ((quittingOutsidePairQuitFlag_eq_true_iff owner who action).1 h)
      simp [hmoved, hflag]
  have hprob :
      expect distribution
          (quittingOutsidePairQuitIndicator owner who) ≤
        1 - quittingStationaryFixedOpponentsContinueMass root owner := by
    simpa [distribution] using
      expect_pmfPi_outsidePairQuits_le_one_sub_continueMass
        root owner who (PMF.pure true)
  have hestimate := abs_expect_sub_expect_map_le_moved
    distribution retraction value hM hvalue
  calc
    |quittingStationaryFixedOpponentsQuitValue reward root who -
          quittingStationaryFixedOpponentsQuitValue reward
            (quittingSoloStationaryRoot owner (root owner)) who| =
        |expect distribution value -
          expect (distribution.map retraction) value| := by
      simp only [quittingStationaryFixedOpponentsQuitValue,
        quittingFixedOpponentsQuitValue,
        quittingRootAbsorbingContribution,
        quittingRootExpectedPayoff, distribution, value]
      rw [hmap]
    _ ≤ 2 * M * expect distribution (fun action =>
          if retraction action ≠ action then 1 else 0) := hestimate
    _ = 2 * M * expect distribution
          (quittingOutsidePairQuitIndicator owner who) := by rw [hmoved]
    _ ≤ 2 * M *
          (1 - quittingStationaryFixedOpponentsContinueMass root owner) :=
      mul_le_mul_of_nonneg_left hprob (by positivity)

/-- Tail-error form of the root-deletion estimate. -/
theorem abs_quittingStationaryFixedOpponentsQuitValue_sub_solo_le_of_hazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {owner who : ι} (hne : who ≠ owner)
    {M η : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hhazard :
      1 - quittingStationaryFixedOpponentsContinueMass root owner ≤ η) :
    |quittingStationaryFixedOpponentsQuitValue reward root who -
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner (root owner)) who| ≤
      2 * M * η := by
  calc
    _ ≤ 2 * M *
          (1 - quittingStationaryFixedOpponentsContinueMass root owner) :=
      abs_quittingStationaryFixedOpponentsQuitValue_sub_solo_le
        reward root hne hM hreward
    _ ≤ 2 * M * η := mul_le_mul_of_nonneg_left hhazard (by positivity)

/-- Terminal reward when `owner` is the unique quitter. -/
def quittingSoloReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) : Payoff ι :=
  reward ⟨{owner}, Finset.singleton_nonempty owner⟩

omit [DecidableEq ι] in
/-- Every finite-time absorbed-state mass is nonnegative. -/
theorem quittingAbsorbedMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingAbsorbedMass reward profile time terminal := by
  unfold quittingAbsorbedMass StochasticGame.expectedStateValue
  apply expect_nonneg
  intro history
  unfold quittingAbsorbedIndicator
  split_ifs <;> norm_num

omit [DecidableEq ι] in
/-- Every limiting absorbed-state mass is nonnegative. -/
theorem quittingAbsorbedMassLimit_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingAbsorbedMassLimit reward profile terminal :=
  (quittingAbsorbedMass_nonneg reward profile 0 terminal).trans
    (quittingAbsorbedMass_le_limit reward profile 0 terminal)

/-- Under almost-sure absorption, terminal payoff is within `2M` times the
non-solo absorption probability of the singleton reward owned by `owner`. -/
theorem abs_quittingTerminalPayoff_sub_soloReward_le_nonSoloMassLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorbs : quittingLiveMassLimit reward profile = 0) :
    |quittingTerminalPayoff reward profile who -
        quittingSoloReward reward owner who| ≤
      2 * M * quittingNonSoloMassLimit reward profile owner := by
  classical
  let singleton := quittingSingletonTerminal owner
  let mass := fun terminal =>
    quittingAbsorbedMassLimit reward profile terminal
  let solo := quittingSoloReward reward owner who
  have htotal : (∑ terminal, mass terminal) = 1 := by
    have hconservation :=
      quittingLiveMassLimit_add_sum_absorbedMassLimit reward profile
    rw [habsorbs, zero_add] at hconservation
    exact hconservation
  have hsolo : reward singleton who = solo := by
    rfl
  have hidentity :
      quittingTerminalPayoff reward profile who - solo =
        ∑ terminal,
          if terminal = singleton then 0
          else mass terminal * (reward terminal who - solo) := by
    calc
      quittingTerminalPayoff reward profile who - solo =
          (∑ terminal, mass terminal * reward terminal who) - solo := by
        rfl
      _ = (∑ terminal, mass terminal * reward terminal who) -
          (∑ terminal, mass terminal) * solo := by rw [htotal, one_mul]
      _ = ∑ terminal, mass terminal * (reward terminal who - solo) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro terminal _
        ring
      _ = ∑ terminal,
          if terminal = singleton then 0
          else mass terminal * (reward terminal who - solo) := by
        apply Finset.sum_congr rfl
        intro terminal _
        by_cases hterminal : terminal = singleton
        · subst terminal
          simp [hsolo]
        · simp [hterminal]
  rw [hidentity]
  calc
    |∑ terminal,
        if terminal = singleton then 0
        else mass terminal * (reward terminal who - solo)| ≤
      ∑ terminal,
        |if terminal = singleton then 0
        else mass terminal * (reward terminal who - solo)| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun terminal =>
          if terminal = singleton then 0
          else mass terminal * (reward terminal who - solo))
        Finset.univ
    _ = ∑ terminal,
        if terminal = singleton then 0
        else mass terminal * |reward terminal who - solo| := by
      apply Finset.sum_congr rfl
      intro terminal _
      by_cases hterminal : terminal = singleton
      · simp [hterminal]
      · simp only [hterminal, ↓reduceIte, abs_mul]
        rw [abs_of_nonneg]
        exact quittingAbsorbedMassLimit_nonneg reward profile terminal
    _ ≤ ∑ terminal,
        if terminal = singleton then 0
        else mass terminal * (2 * M) := by
      apply Finset.sum_le_sum
      intro terminal _
      by_cases hterminal : terminal = singleton
      · simp [hterminal]
      · simp only [hterminal, ↓reduceIte]
        apply mul_le_mul_of_nonneg_left
        · calc
            |reward terminal who - solo| ≤
                |reward terminal who| + |solo| := abs_sub _ _
            _ ≤ M + M := add_le_add (hreward terminal who) (by
              rw [← hsolo]
              exact hreward singleton who)
            _ = 2 * M := by ring
        · exact quittingAbsorbedMassLimit_nonneg reward profile terminal
    _ = 2 * M * quittingNonSoloMassLimit reward profile owner := by
      unfold quittingNonSoloMassLimit
      dsimp only [mass, singleton]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro terminal _
      by_cases hterminal : terminal = quittingSingletonTerminal owner
      · simp [hterminal]
      · simp [hterminal, mul_comm]

/-- Non-solo terminal absorption is bounded by the probability that some
opponent of `owner` eventually quits. -/
theorem quittingNonSoloMassLimit_le_one_sub_opponentLiveMassLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι) :
    quittingNonSoloMassLimit reward profile owner ≤
      1 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward profile owner) := by
  have htail := quittingNonSoloMassLimit_update_sub_le_opponentLiveTail
    reward profile owner (profile owner) 0
  have hupdate : Function.update profile owner (profile owner) = profile := by
    funext player
    by_cases hp : player = owner
    · subst player
      simp
    · simp [Function.update_of_ne hp]
  have hzero : quittingNonSoloMass reward profile owner 0 = 0 := by
    unfold quittingNonSoloMass
    rw [(quittingGame reward).expectedStateValue_zero]
    simp [quittingNonSoloIndicator]
  rw [hupdate, hzero, quittingLiveMass_zero, sub_zero] at htail
  exact htail

/-- Semantic form of tail concentration: almost-sure absorption and an
opponent-live-tail bound imply the `2Mη` estimate used by the exceptional
fallback. -/
theorem abs_quittingTerminalPayoff_sub_soloReward_le_of_opponentLiveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner who : ι) {M η : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorbs : quittingLiveMassLimit reward profile = 0)
    (htail : 1 - quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile owner) ≤ η) :
    |quittingTerminalPayoff reward profile who -
        quittingSoloReward reward owner who| ≤
      2 * M * η := by
  calc
    _ ≤ 2 * M * quittingNonSoloMassLimit reward profile owner :=
      abs_quittingTerminalPayoff_sub_soloReward_le_nonSoloMassLimit
        reward profile owner who hreward habsorbs
    _ ≤ 2 * M *
          (1 - quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile owner)) :=
      mul_le_mul_of_nonneg_left
        (quittingNonSoloMassLimit_le_one_sub_opponentLiveMassLimit
          reward profile owner) (by positivity)
    _ ≤ 2 * M * η := mul_le_mul_of_nonneg_left htail (by positivity)

omit [Fintype ι] in
@[simp] theorem update_quittingSoloStationaryRoot_owner
    (owner : ι) (first second : PMF Bool) :
    Function.update (quittingSoloStationaryRoot owner first) owner second =
      quittingSoloStationaryRoot owner second := by
  simp [quittingSoloStationaryRoot]

omit [Fintype ι] in
@[simp] theorem update_quittingSoloStationaryRoot_other
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    Function.update (quittingSoloStationaryRoot owner hazard) other
        (PMF.pure false) =
      quittingSoloStationaryRoot owner hazard := by
  funext player
  by_cases hp : player = other
  · subst player
    simp [quittingSoloStationaryRoot, hne]
  · simp [Function.update_of_ne hp]

theorem pmfPi_quittingSoloStationaryRoot
    (owner : ι) (hazard : PMF Bool) :
    pmfPi (quittingSoloStationaryRoot owner hazard) =
      hazard.bind (fun action => PMF.pure (quittingSoloAction owner action)) := by
  rw [quittingSoloStationaryRoot, pmfPi_update_bind]
  apply congrArg (PMF.bind hazard)
  funext action
  rw [show Function.update (fun _ : ι => PMF.pure false) owner
      (PMF.pure action) =
      fun player => PMF.pure (quittingSoloAction owner action player) by
        funext player
        by_cases hp : player = owner
        · subst player
          simp [quittingSoloAction]
        · simp [quittingSoloAction, Function.update_of_ne hp]]
  exact pmfPi_pure _

theorem expect_quittingSoloStationaryRoot
    (owner : ι) (hazard : PMF Bool) (value : (ι → Bool) → ℝ) :
    expect (pmfPi (quittingSoloStationaryRoot owner hazard)) value =
      (hazard false).toReal * value (quittingSoloAction owner false) +
        (hazard true).toReal * value (quittingSoloAction owner true) := by
  rw [pmfPi_quittingSoloStationaryRoot, expect_bind]
  simp only [expect_pure]
  rw [expect_eq_sum, Fintype.sum_bool]
  ring

omit [Fintype ι] in
@[simp] theorem quittingSoloAction_false (owner : ι) :
    quittingSoloAction owner false = quittingAllContinueAction := by
  funext player
  simp [quittingSoloAction, quittingAllContinueAction]

@[simp] theorem quittingQuitters_soloAction_true (owner : ι) :
    quittingQuitters (quittingSoloAction owner true) = {owner} := by
  ext player
  by_cases hp : player = owner
  · subst player
    simp [quittingSoloAction, quittingQuitters]
  · simp [quittingSoloAction, quittingQuitters, hp]

@[simp] theorem quittingStationaryContinueMass_solo
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryContinueMass
        (quittingSoloStationaryRoot owner hazard) =
      (hazard false).toReal := by
  have hne : quittingAllContinueAction ≠
      quittingSoloAction owner true := by
    intro h
    have howner := congrFun h owner
    simp [quittingAllContinueAction, quittingSoloAction] at howner
  unfold quittingStationaryContinueMass
  rw [pmfPi_quittingSoloStationaryRoot]
  simp [quittingSoloAction_false, hne]

theorem quittingRootAbsorbingContribution_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) (hazard : PMF Bool) :
    quittingRootAbsorbingContribution reward
        (quittingSoloStationaryRoot owner hazard) who =
      (hazard true).toReal * quittingSoloReward reward owner who := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_quittingSoloStationaryRoot]
  simp [quittingRootPayoff, quittingSoloReward]

theorem quittingTerminalPayoff_soloStationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner hazard)) who =
      quittingSoloReward reward owner who := by
  have hsum : (hazard false).toReal + (hazard true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one hazard
  have hcontracts : quittingStationaryContinueMass
      (quittingSoloStationaryRoot owner hazard) < 1 := by
    rw [quittingStationaryContinueMass_solo]
    linarith
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward _ who hcontracts,
    quittingRootAbsorbingContribution_solo,
    quittingStationaryContinueMass_solo]
  have hne : (hazard true).toReal ≠ 0 := ne_of_gt hpositive
  have hden : 1 - (hazard false).toReal = (hazard true).toReal := by
    linarith
  rw [hden]
  field_simp [hne]

@[simp] theorem quittingStationaryFixedOpponentsQuitValue_solo_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingSoloStationaryRoot owner hazard) owner =
      quittingSoloReward reward owner owner := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
  rw [update_quittingSoloStationaryRoot_owner,
    quittingRootAbsorbingContribution_solo]
  simp [quittingSoloReward]

@[simp] theorem quittingStationaryFixedOpponentsContinueReward_solo_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingSoloStationaryRoot owner hazard) owner = 0 := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  rw [update_quittingSoloStationaryRoot_owner,
    quittingRootAbsorbingContribution_solo]
  simp

@[simp] theorem quittingStationaryFixedOpponentsContinueMass_solo_owner
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSoloStationaryRoot owner hazard) owner = 1 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_quittingSoloStationaryRoot_owner,
    quittingStationaryContinueMass_solo]
  simp

@[simp] theorem quittingStationaryUnilateralCap_solo_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    quittingStationaryUnilateralCap reward
        (quittingSoloStationaryRoot owner hazard) owner =
      max (quittingSoloReward reward owner owner) 0 := by
  simp [quittingStationaryUnilateralCap,
    quittingStationarySelectedCap, quittingStationaryNeverValue]

@[simp] theorem quittingStationaryFixedOpponentsContinueReward_solo_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard true).toReal * quittingSoloReward reward owner other := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  rw [update_quittingSoloStationaryRoot_other hne,
    quittingRootAbsorbingContribution_solo]

@[simp] theorem quittingStationaryFixedOpponentsContinueMass_solo_other
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard false).toReal := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_quittingSoloStationaryRoot_other hne,
    quittingStationaryContinueMass_solo]

theorem quittingStationaryUnilateralCap_solo_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal) :
    quittingStationaryUnilateralCap reward
        (quittingSoloStationaryRoot owner hazard) other =
      max
        (quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner hazard) other)
        (quittingSoloReward reward owner other) := by
  have hsum : (hazard false).toReal + (hazard true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one hazard
  have hneHazard : (hazard true).toReal ≠ 0 := ne_of_gt hpositive
  unfold quittingStationaryUnilateralCap
  rw [quittingStationaryFixedOpponentsContinueReward_solo_other
      reward hne hazard,
    quittingStationaryFixedOpponentsContinueMass_solo_other hne hazard]
  unfold quittingStationarySelectedCap quittingStationaryNeverValue
  congr 1
  have hden : 1 - (hazard false).toReal = (hazard true).toReal := by
    linarith
  rw [hden]
  field_simp [hneHazard]

theorem quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSoloStationaryRoot owner hazard) other < 1 := by
  rw [quittingStationaryFixedOpponentsContinueMass_solo_other hne]
  have hsum : (hazard false).toReal + (hazard true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one hazard
  linarith

/-- When the prescribed stationary root only lets `owner` quit, arbitrary
deviations by `owner` face all-continuing opponents and hence are bounded by
Quit-versus-Never. -/
theorem quittingTerminalPayoff_update_solo_owner_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingStationaryProfile reward
            (quittingSoloStationaryRoot owner hazard)) owner deviation) owner ≤
      max 0 (quittingSoloReward reward owner owner) := by
  have hprofiles :
      Function.update
          (quittingStationaryProfile reward
            (quittingSoloStationaryRoot owner hazard)) owner deviation =
        Function.update (quittingAlwaysContinueProfile reward) owner
          deviation := by
    funext player time history
    by_cases hp : player = owner
    · subst player
      simp
    · simp [quittingStationaryProfile, quittingSoloStationaryRoot,
        quittingAlwaysContinueProfile, hp,
        StochasticGame.stationaryBehaviorProfile]
      rfl
  rw [hprofiles]
  exact quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
    reward owner deviation

/-- The two `2Mη` estimates and the tail Nash inequalities assemble into the
stationary `β + 4Mη` exceptional fallback.  The concentration and root-
deletion estimates are explicit hypotheses so their probabilistic adapters
can be proved independently. -/
theorem isεAsymptoticNash_soloStationary_of_tail_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (originalRoot : ι → PMF Bool) (tailValue : Payoff ι)
    (owner : ι) {β M η : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hpositive : 0 < (originalRoot owner true).toReal)
    (hconcentration : ∀ who,
      |tailValue who - quittingSoloReward reward owner who| ≤ 2 * M * η)
    (hneverNash : -M * η ≤ tailValue owner + β)
    (hquitNash : ∀ who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward originalRoot who ≤
        tailValue who + β)
    (hdelete : ∀ who, who ≠ owner →
      |quittingStationaryFixedOpponentsQuitValue reward originalRoot who -
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner (originalRoot owner)) who| ≤
        2 * M * η) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (β + 4 * M * η)
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner (originalRoot owner))) := by
  let soloRoot := quittingSoloStationaryRoot owner (originalRoot owner)
  let error := β + 4 * M * η
  have hMη : 0 ≤ M * η := mul_nonneg hM hη
  have herror : 0 ≤ error := by
    dsimp only [error]
    positivity
  have hsoloOwnerLower :
      -β - 3 * M * η ≤ quittingSoloReward reward owner owner := by
    have hcloseUpper := (abs_le.mp (hconcentration owner)).2
    linarith
  have hsoloQuitUpper : ∀ who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward soloRoot who ≤
        quittingSoloReward reward owner who + error := by
    intro who hne
    have hdeleteLower := (abs_le.mp (hdelete who hne)).1
    have htailUpper := (abs_le.mp (hconcentration who)).2
    have hquit := hquitNash who hne
    dsimp only [soloRoot, error] at hdeleteLower ⊢
    linarith
  intro who deviation
  by_cases hwho : who = owner
  · subst who
    have hcap := quittingTerminalPayoff_update_solo_owner_le
      reward owner (originalRoot owner) deviation
    rw [quittingTerminalPayoff_soloStationary reward owner owner
      (originalRoot owner) hpositive]
    apply hcap.trans
    apply max_le
    · nlinarith [hMη]
    · exact le_add_of_nonneg_right herror
  · have hcap :=
      quittingTerminalPayoff_update_stationary_le_unilateralCap
        reward soloRoot who deviation
        (quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
          hwho (originalRoot owner) hpositive)
    rw [quittingTerminalPayoff_soloStationary reward owner who
      (originalRoot owner) hpositive]
    apply hcap.trans
    rw [quittingStationaryUnilateralCap_solo_other reward hwho
      (originalRoot owner) hpositive]
    apply max_le
    · exact hsoloQuitUpper who hwho
    · exact le_add_of_nonneg_right herror

/-- The exceptional fallback with root deletion discharged from the current
opponent-hazard bound. -/
theorem isεAsymptoticNash_soloStationary_of_tail_bounds_of_hazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (originalRoot : ι → PMF Bool) (tailValue : Payoff ι)
    (owner : ι) {β M η : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hhazard :
      1 - quittingStationaryFixedOpponentsContinueMass originalRoot owner ≤ η)
    (hpositive : 0 < (originalRoot owner true).toReal)
    (hconcentration : ∀ who,
      |tailValue who - quittingSoloReward reward owner who| ≤ 2 * M * η)
    (hneverNash : -M * η ≤ tailValue owner + β)
    (hquitNash : ∀ who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward originalRoot who ≤
        tailValue who + β) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (β + 4 * M * η)
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner (originalRoot owner))) := by
  apply isεAsymptoticNash_soloStationary_of_tail_bounds
    reward originalRoot tailValue owner hβ hM hη hpositive
      hconcentration hneverNash hquitNash
  intro who hne
  exact
    abs_quittingStationaryFixedOpponentsQuitValue_sub_solo_le_of_hazard
      reward originalRoot hne hM hreward hhazard

/-- The one-tail exceptional fallback with both probabilistic estimates
discharged semantically: absorption gives concentration, and the current
opponent hazard gives root-deletion stability. -/
theorem isεAsymptoticNash_soloStationary_of_absorbing_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (originalRoot : ι → PMF Bool)
    (tailProfile : (quittingGame reward).BehaviorProfile)
    (owner : ι) {β M η : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorbs : quittingLiveMassLimit reward tailProfile = 0)
    (htail : 1 - quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward tailProfile owner) ≤ η)
    (hhazard :
      1 - quittingStationaryFixedOpponentsContinueMass originalRoot owner ≤ η)
    (hpositive : 0 < (originalRoot owner true).toReal)
    (hneverNash : -M * η ≤
      quittingTerminalPayoff reward tailProfile owner + β)
    (hquitNash : ∀ who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward originalRoot who ≤
        quittingTerminalPayoff reward tailProfile who + β) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (β + 4 * M * η)
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner (originalRoot owner))) := by
  apply isεAsymptoticNash_soloStationary_of_tail_bounds_of_hazard
    reward originalRoot (quittingTerminalPayoff reward tailProfile) owner
      hβ hM hη hreward hhazard hpositive
  · intro who
    exact
      abs_quittingTerminalPayoff_sub_soloReward_le_of_opponentLiveTail
        reward tailProfile owner who hM hreward habsorbs htail
  · exact hneverNash
  · exact hquitNash

/-- If the opponent-tail error tends to zero and positive owner hazards occur
arbitrarily late, the stationary solo fallbacks can be selected with error
arbitrarily close to `β`. -/
theorem exists_isεAsymptoticNash_soloStationary_of_tendsto_tail_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (tailValue : ℕ → Payoff ι)
    (owner : ι) (η : ℕ → ℝ) {β M : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hη : ∀ time, 0 ≤ η time)
    (hηzero : Tendsto η atTop (nhds 0))
    (hpositiveLate : ∀ threshold,
      ∃ time ≥ threshold, 0 < (roots time owner true).toReal)
    (hconcentration : ∀ time who,
      |tailValue time who - quittingSoloReward reward owner who| ≤
        2 * M * η time)
    (hneverNash : ∀ time,
      -M * η time ≤ tailValue time owner + β)
    (hquitNash : ∀ time who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
        tailValue time who + β)
    (hdelete : ∀ time who, who ≠ owner →
      |quittingStationaryFixedOpponentsQuitValue reward (roots time) who -
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingSoloStationaryRoot owner (roots time owner)) who| ≤
        2 * M * η time) :
    ∀ ζ > 0, ∃ time,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (β + ζ)
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner (roots time owner))) := by
  intro ζ hζ
  have hscaled : Tendsto (fun time => 4 * M * η time)
      atTop (nhds 0) := by
    simpa using hηzero.const_mul (4 * M)
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hscaled) ζ hζ
  obtain ⟨time, htime, hpositive⟩ := hpositiveLate threshold
  have hclose := hthreshold time htime
  rw [Real.dist_eq, sub_zero] at hclose
  have herror : 4 * M * η time ≤ ζ :=
    (le_abs_self (4 * M * η time)).trans hclose.le
  refine ⟨time, ?_⟩
  have hnash := isεAsymptoticNash_soloStationary_of_tail_bounds
    reward (roots time) (tailValue time) owner hβ hM (hη time)
      hpositive (hconcentration time) (hneverNash time)
      (hquitNash time) (hdelete time)
  intro who deviation
  have herror' : β + 4 * M * η time ≤ β + ζ := by linarith
  exact (hnash who deviation).trans (add_le_add_right herror' _)

/-- Limit selection with the root-deletion premise replaced by the semantic
one-stage opponent-hazard bound. -/
theorem exists_isεAsymptoticNash_soloStationary_of_tendsto_hazard_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (tailValue : ℕ → Payoff ι)
    (owner : ι) (η : ℕ → ℝ) {β M : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hη : ∀ time, 0 ≤ η time)
    (hηzero : Tendsto η atTop (nhds 0))
    (hhazard : ∀ time,
      1 - quittingStationaryFixedOpponentsContinueMass
        (roots time) owner ≤ η time)
    (hpositiveLate : ∀ threshold,
      ∃ time ≥ threshold, 0 < (roots time owner true).toReal)
    (hconcentration : ∀ time who,
      |tailValue time who - quittingSoloReward reward owner who| ≤
        2 * M * η time)
    (hneverNash : ∀ time,
      -M * η time ≤ tailValue time owner + β)
    (hquitNash : ∀ time who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
        tailValue time who + β) :
    ∀ ζ > 0, ∃ time,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (β + ζ)
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner (roots time owner))) := by
  apply exists_isεAsymptoticNash_soloStationary_of_tendsto_tail_bounds
    reward roots tailValue owner η hβ hM hη hηzero hpositiveLate
      hconcentration hneverNash hquitNash
  intro time who hne
  exact
    abs_quittingStationaryFixedOpponentsQuitValue_sub_solo_le_of_hazard
      reward (roots time) hne hM hreward (hhazard time)

/-- Limit selection from a sequence of absorbing tails.  Both `2Mη`
estimates are derived from live-mass bounds rather than supplied as abstract
payoff inequalities. -/
theorem exists_isεAsymptoticNash_soloStationary_of_absorbing_tails
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : ι) (η : ℕ → ℝ) {β M : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hη : ∀ time, 0 ≤ η time)
    (hηzero : Tendsto η atTop (nhds 0))
    (habsorbs : ∀ time,
      quittingLiveMassLimit reward (tails time) = 0)
    (htail : ∀ time,
      1 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward (tails time) owner) ≤ η time)
    (hhazard : ∀ time,
      1 - quittingStationaryFixedOpponentsContinueMass
        (roots time) owner ≤ η time)
    (hpositiveLate : ∀ threshold,
      ∃ time ≥ threshold, 0 < (roots time owner true).toReal)
    (hneverNash : ∀ time,
      -M * η time ≤
        quittingTerminalPayoff reward (tails time) owner + β)
    (hquitNash : ∀ time who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
        quittingTerminalPayoff reward (tails time) who + β) :
    ∀ ζ > 0, ∃ time,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (β + ζ)
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner (roots time owner))) := by
  apply exists_isεAsymptoticNash_soloStationary_of_tendsto_hazard_bounds
    reward roots (fun time => quittingTerminalPayoff reward (tails time))
      owner η hβ hM hreward hη hηzero hhazard hpositiveLate
  · intro time who
    exact
      abs_quittingTerminalPayoff_sub_soloReward_le_of_opponentLiveTail
        reward (tails time) owner who hM hreward
          (habsorbs time) (htail time)
  · exact hneverNash
  · exact hquitNash

end GameTheory
