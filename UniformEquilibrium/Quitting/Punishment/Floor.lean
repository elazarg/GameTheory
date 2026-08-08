/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.Quitting.Punishment.IsolatedPunishmentCeiling

/-!
# Punishment floors in quitting games

`QuittingPunishmentLevel.lean` bounds a quitting game's punishment level from
*above* by `max 0 (reward (quittingSingletonTerminal who) who)`.  A ceiling
alone refutes nothing: `not_isUniformEquilibriumPayoff_of_punishmentLevel_gt`
needs the punishment level bounded from *below*.  This file supplies the
matching floors and the first payoff vector they refute.

## What is and is not true

The naive floor `max 0 (reward (quittingSingletonTerminal who) who) ≤
punishmentLevel` is **false**;
`QuittingIsolatedPunishmentLowerBoundCounterexample` refutes it.  Both halves
fail for the same reason: the punishment level infimizes over *every* opponent
profile, and opponents who quit drag `who` onto terminal states the reward
table constrains nowhere.

* the `0` half needs `0 ≤ reward S who` whenever `who ∉ S`;
* the solo half needs `reward (quittingSingletonTerminal who) who ≤ reward S who`
  whenever `who ∈ S`, because `who`'s own quitting move is simultaneous with
  the opponents' and can land on a larger quitter set.

What holds unconditionally is one floor per pure guarantee, each carrying the
horizon factor `horizonTailWeight T = (T - 1) / T` that accounts for the one
stage of active play (which pays `0`) that precedes any absorption:

* quitting at once secures `horizonTailWeight T * mIn` for any `mIn` below every
  reward at a terminal set containing `who`;
* never quitting secures any nonpositive `mOut` below every reward at a
  terminal set avoiding `who`.

Their maximum, `max_le_punishmentLevel_quittingGame`, is the unconditional
floor, and it is **sharp**: on the counterexample table it meets the all-quit
opponent profile's value exactly, pinning `punishmentLevel none 2 true = -500`
(`punishmentLevel_quittingGame_alwaysQuitCounterexample_eq`).  Nothing here
claims the floor is sharp on every table — that would need the infimum over
*mixed* opponent hazard rows, not the two pure profiles used here.

Under the two hypotheses above the floors and the ceiling close up: the
punishment level is sandwiched and converges to `max 0 (reward
(quittingSingletonTerminal who) who)`.  Both hypotheses are finitely
checkable — one comparison per coalition — and when the solo reward is already
nonnegative the second is not needed at all.

## Main definitions

* `horizonTailWeight` — the share `(T - 1) / T` of a horizon-`T` average
  carried by the stages after the first

## Main results

* `StochasticGame.horizonTailWeight_mul_le_finiteAveragePayoff` and
  `StochasticGame.finiteAveragePayoff_le_horizonTailWeight_mul` — a bound on
  every stage after the first, plus the sign of the first, bounds the average
* `horizonTailWeight_mul_le_punishmentLevel_quittingGame` — the quit-at-once
  punishment floor
* `le_punishmentLevel_quittingGame_of_forall_notMem` — the never-quit
  punishment floor
* `max_le_punishmentLevel_quittingGame` — the unconditional floor
* `punishmentLevel_quittingGame_alwaysQuitCounterexample_eq` — the floor is
  attained: an exact punishment level on the table that refutes the ceiling
* `punishmentLevel_quittingGame_sandwich`,
  `punishmentLevel_quittingGame_sandwich_of_nonneg_solo` and
  `tendsto_punishmentLevel_quittingGame` — the conditional identity: under
  finitely checkable hypotheses the ceiling is attained in the horizon limit
* `QuittingQuitBonus.not_isUniformEquilibriumPayoff_zero` — a worked
  refutation: on the quit-bonus table the all-continue payoff `0` is not a
  uniform equilibrium payoff
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The horizon tail weight -/

/-- The share of a horizon-`T` Cesàro average carried by the stages after the
first, `(T - 1) / T`.  At `T = 0` division by zero makes this `0`, matching
`finiteAveragePayoff`'s own degenerate value there. -/
def horizonTailWeight (T : ℕ) : ℝ := ((T : ℝ) - 1) / T

/-- The tail weight is never negative. -/
theorem horizonTailWeight_nonneg (T : ℕ) : 0 ≤ horizonTailWeight T := by
  unfold horizonTailWeight
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  · have h1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    exact div_nonneg (by linarith) (by linarith)

/-- The tail weight tends to one: one wasted stage out of `T` is asymptotically
free. -/
theorem tendsto_horizonTailWeight :
    Tendsto horizonTailWeight atTop (nhds 1) := by
  have hbase : Tendsto (fun T : ℕ => 1 - 1 / (T : ℝ)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [sub_zero] at hbase
  refine hbase.congr' ?_
  refine eventually_atTop.2 ⟨1, fun T hT => ?_⟩
  have hT0 : (T : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  unfold horizonTailWeight
  field_simp

/-! ## Averaging with one wasted stage -/

omit [DecidableEq ι] in
/-- If the first stage pays nonnegatively and every later stage below the
horizon pays at least `m`, the horizon-`T` average is at least
`horizonTailWeight T * m`. -/
theorem StochasticGame.horizonTailWeight_mul_le_finiteAveragePayoff
    (G : StochasticGame ι) [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) (T : ℕ) {m : ℝ}
    (hzero : 0 ≤ G.expectedStagePayoff σ s₀ 0 who)
    (htail : ∀ t, t + 1 < T → m ≤ G.expectedStagePayoff σ s₀ (t + 1) who) :
    horizonTailWeight T * m ≤ G.finiteAveragePayoff s₀ T σ who := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp [horizonTailWeight]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT.ne'
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff, Finset.sum_range_succ']
    have hsum : (n : ℝ) * m ≤
        (∑ i ∈ Finset.range n, G.expectedStagePayoff σ s₀ (i + 1) who)
          + G.expectedStagePayoff σ s₀ 0 who := by
      have h1 : (n : ℝ) * m ≤
          ∑ i ∈ Finset.range n, G.expectedStagePayoff σ s₀ (i + 1) who := by
        calc (n : ℝ) * m = ∑ _i ∈ Finset.range n, m := by
              simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum fun i hi =>
              htail i (Nat.succ_lt_succ (Finset.mem_range.mp hi))
      linarith
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hrw : horizonTailWeight (n + 1) * m = ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * m) := by
      unfold horizonTailWeight
      rw [hcast]
      field_simp
      ring
    rw [hrw, hcast]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)

omit [DecidableEq ι] in
/-- If the first stage pays nonpositively and every later stage below the
horizon pays at most `M`, the horizon-`T` average is at most
`horizonTailWeight T * M`. -/
theorem StochasticGame.finiteAveragePayoff_le_horizonTailWeight_mul
    (G : StochasticGame ι) [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) (T : ℕ) {M : ℝ}
    (hzero : G.expectedStagePayoff σ s₀ 0 who ≤ 0)
    (htail : ∀ t, t + 1 < T → G.expectedStagePayoff σ s₀ (t + 1) who ≤ M) :
    G.finiteAveragePayoff s₀ T σ who ≤ horizonTailWeight T * M := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp [horizonTailWeight]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT.ne'
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff, Finset.sum_range_succ']
    have hsum : (∑ i ∈ Finset.range n, G.expectedStagePayoff σ s₀ (i + 1) who)
          + G.expectedStagePayoff σ s₀ 0 who ≤ (n : ℝ) * M := by
      have h1 : (∑ i ∈ Finset.range n, G.expectedStagePayoff σ s₀ (i + 1) who)
          ≤ (n : ℝ) * M := by
        calc (∑ i ∈ Finset.range n, G.expectedStagePayoff σ s₀ (i + 1) who)
            ≤ ∑ _i ∈ Finset.range n, M := Finset.sum_le_sum fun i hi =>
              htail i (Nat.succ_lt_succ (Finset.mem_range.mp hi))
          _ = (n : ℝ) * M := by
              simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hrw : horizonTailWeight (n + 1) * M = ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * M) := by
      unfold horizonTailWeight
      rw [hcast]
      field_simp
      ring
    rw [hrw, hcast]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)

omit [DecidableEq ι] in
/-- If every stage below the horizon pays at least a nonpositive `M`, so does
the horizon-`T` average.  The mirror of
`finiteAveragePayoff_le_of_forall_expectedStagePayoff_le`. -/
theorem StochasticGame.le_finiteAveragePayoff_of_forall_le_expectedStagePayoff
    (G : StochasticGame ι) [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) (T : ℕ) {M : ℝ}
    (hM0 : M ≤ 0)
    (hbound : ∀ t < T, M ≤ G.expectedStagePayoff σ s₀ t who) :
    M ≤ G.finiteAveragePayoff s₀ T σ who := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · subst hT0
    simpa using hM0
  · have hsum : (T : ℝ) * M ≤
        ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who := by
      calc (T : ℝ) * M = ∑ _t ∈ Finset.range T, M := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun t ht => hbound t (Finset.mem_range.mp ht)
    have hT' : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
    calc M = (T : ℝ)⁻¹ * ((T : ℝ) * M) := by field_simp
      _ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who :=
          mul_le_mul_of_nonneg_left hsum (by positivity)

/-! ## Reading one player's coordinate out of a joint action -/

omit [DecidableEq ι] in
/-- Players randomize independently, so every supported joint action has every
coordinate supported by that player's own mixed action. -/
theorem StochasticGame.coord_mem_support_stageActionDist
    (G : StochasticGame ι) [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) {action : G.JointAct}
    (haction : action ∈ (G.stageActionDist σ h).support) (i : ι) :
    action i ∈ (σ i t h).support := by
  have hdist : G.stageActionDist σ h = pmfPi (fun j => σ j t h) := rfl
  rw [hdist] at haction
  have hcoord : action i ∈ (Math.ProbabilityMassFunction.pushforward
      (pmfPi (fun j => σ j t h)) (fun joint => joint i)).support := by
    rw [Math.ProbabilityMassFunction.pushforward, PMF.mem_support_map_iff]
    exact ⟨action, haction, rfl⟩
  rwa [pmfPi_push_coord (fun j => σ j t h) i] at hcoord

/-! ## Where the two pure guarantees lead -/

omit [DecidableEq ι] in
/-- Active play pays nothing, so the epoch-zero expected stage payoff from the
active state vanishes under every profile. -/
theorem expectedStagePayoff_quittingGame_none_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingGame reward).expectedStagePayoff σ none 0 who = 0 := by
  unfold StochasticGame.expectedStagePayoff
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ (fun _ => (0 : ℝ))
    (fun h hh => by
      have heq : h = (quittingGame reward).emptyHist none := by simpa using hh
      rw [stageEUAt_quittingGame_eq_stateReward, heq]
      rfl),
    expect_const]

/-- **Quitting at once absorbs onto a set containing the quitter.**  Whatever
the opponents do, once `who` quits at every history every supported history
after at least one completed stage sits at a terminal state that contains
`who`. -/
theorem exists_state_mem_of_mem_support_update_quittingAlwaysQuitStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (τ : (quittingGame reward).BehaviorProfile) :
    ∀ (t : ℕ) (h : (quittingGame reward).Hist (t + 1)),
      h ∈ ((quittingGame reward).histDist
        (Function.update τ who (quittingAlwaysQuitStrategy reward who))
        none (t + 1)).support →
      ∃ S : {S : Finset ι // S.Nonempty}, h.2 = some S ∧ who ∈ (S : Finset ι) := by
  classical
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  intro t
  induction t with
  | zero =>
      intro h' hh'
      rw [(quittingGame reward).mem_support_histDist_succ] at hh'
      obtain ⟨h, hh, action, haction, next, hnext, rfl⟩ := hh'
      change (ι → Bool) at action
      have hstate : h.2 = none := by
        have heq : h = (quittingGame reward).emptyHist none := by simpa using hh
        rw [heq]; rfl
      have hwho : action who = true := by
        have hcoord := (quittingGame reward).coord_mem_support_stageActionDist
          (Function.update τ who (quittingAlwaysQuitStrategy reward who)) h haction who
        rw [Function.update_self] at hcoord
        exact (PMF.mem_support_pure_iff _ _).mp hcoord
      have hmem : who ∈ ({player | action player = true} : Finset ι) := by
        simpa using hwho
      have hnonempty : ({player | action player = true} : Finset ι).Nonempty :=
        ⟨who, hmem⟩
      rw [hstate, quittingGame_transition_none, dif_pos hnonempty] at hnext
      exact ⟨⟨_, hnonempty⟩, by simpa using hnext, hmem⟩
  | succ t ih =>
      intro h' hh'
      rw [(quittingGame reward).mem_support_histDist_succ] at hh'
      obtain ⟨h, hh, action, haction, next, hnext, rfl⟩ := hh'
      change (ι → Bool) at action
      obtain ⟨S, hS, hmem⟩ := ih h hh
      rw [hS, show (quittingGame reward).transition (some S) action =
        PMF.pure (show (quittingGame reward).State from some S) from rfl] at hnext
      exact ⟨S, by simpa using hnext, hmem⟩

/-- **Never quitting keeps the quitter out of every terminal set.**  Whatever
the opponents do, once `who` continues at every history every supported
history is still active or sits at a terminal state avoiding `who`. -/
theorem state_eq_none_or_notMem_of_mem_support_update_quittingAlwaysContinueStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (τ : (quittingGame reward).BehaviorProfile) :
    ∀ (t : ℕ) (h : (quittingGame reward).Hist t),
      h ∈ ((quittingGame reward).histDist
        (Function.update τ who (quittingAlwaysContinueStrategy reward who))
        none t).support →
      h.2 = none ∨
        ∃ S : {S : Finset ι // S.Nonempty}, h.2 = some S ∧ who ∉ (S : Finset ι) := by
  classical
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  intro t
  induction t with
  | zero =>
      intro h hh
      left
      have heq : h = (quittingGame reward).emptyHist none := by simpa using hh
      rw [heq]; rfl
  | succ t ih =>
      intro h' hh'
      rw [(quittingGame reward).mem_support_histDist_succ] at hh'
      obtain ⟨h, hh, action, haction, next, hnext, rfl⟩ := hh'
      change (ι → Bool) at action
      rcases ih h hh with hnone | ⟨S, hS, hnot⟩
      · have hwho : action who = false := by
          have hcoord := (quittingGame reward).coord_mem_support_stageActionDist
            (Function.update τ who (quittingAlwaysContinueStrategy reward who)) h
            haction who
          rw [Function.update_self] at hcoord
          exact (PMF.mem_support_pure_iff _ _).mp hcoord
        by_cases hne : ({player | action player = true} : Finset ι).Nonempty
        · rw [hnone, quittingGame_transition_none, dif_pos hne] at hnext
          exact Or.inr ⟨⟨_, hne⟩, by simpa using hnext, by simp [hwho]⟩
        · rw [hnone, quittingGame_transition_none, dif_neg hne] at hnext
          exact Or.inl (by simpa using hnext)
      · rw [hS, show (quittingGame reward).transition (some S) action =
          PMF.pure (show (quittingGame reward).State from some S) from rfl] at hnext
        exact Or.inr ⟨S, by simpa using hnext, hnot⟩

/-! ## The two punishment floors -/

/-- Quitting at once secures the tail-weighted worst reward over terminal sets
containing `who`, against every opponent profile. -/
theorem horizonTailWeight_mul_le_finiteAveragePayoff_update_quittingAlwaysQuitStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (τ : (quittingGame reward).BehaviorProfile) (T : ℕ) {m : ℝ}
    (hm : ∀ S : {S : Finset ι // S.Nonempty}, who ∈ (S : Finset ι) →
      m ≤ reward S who) :
    horizonTailWeight T * m ≤
      (quittingGame reward).finiteAveragePayoff none T
        (Function.update τ who (quittingAlwaysQuitStrategy reward who)) who := by
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  refine (quittingGame reward).horizonTailWeight_mul_le_finiteAveragePayoff _ none who T
    (le_of_eq (expectedStagePayoff_quittingGame_none_zero reward _ who).symm) ?_
  intro t _ht
  unfold StochasticGame.expectedStagePayoff
  apply Math.ProbabilityMassFunction.le_expect_of_le_on_support
  intro h hh
  rw [stageEUAt_quittingGame_eq_stateReward]
  obtain ⟨S, hS, hmem⟩ :=
    exists_state_mem_of_mem_support_update_quittingAlwaysQuitStrategy reward who τ t h hh
  rw [hS]
  exact hm S hmem

/-- Never quitting secures any nonpositive `m` that is below every reward at a
terminal set avoiding `who`, against every opponent profile.  Nonpositivity is
needed because a never-quitting `who` may never absorb at all, and active play
pays `0`. -/
theorem le_finiteAveragePayoff_update_quittingAlwaysContinueStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (τ : (quittingGame reward).BehaviorProfile) (T : ℕ) {m : ℝ} (hm0 : m ≤ 0)
    (hout : ∀ S : {S : Finset ι // S.Nonempty}, who ∉ (S : Finset ι) →
      m ≤ reward S who) :
    m ≤ (quittingGame reward).finiteAveragePayoff none T
      (Function.update τ who (quittingAlwaysContinueStrategy reward who)) who := by
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  refine (quittingGame reward).le_finiteAveragePayoff_of_forall_le_expectedStagePayoff
    _ none who T hm0 ?_
  intro t _ht
  unfold StochasticGame.expectedStagePayoff
  apply Math.ProbabilityMassFunction.le_expect_of_le_on_support
  intro h hh
  rw [stageEUAt_quittingGame_eq_stateReward]
  rcases state_eq_none_or_notMem_of_mem_support_update_quittingAlwaysContinueStrategy
      reward who τ t h hh with hnone | ⟨S, hS, hnot⟩
  · rw [hnone]; exact hm0
  · rw [hS]; exact hout S hnot

omit [DecidableEq ι] in
/-- A uniform bound on `who`'s rewards bounds every stage payoff. -/
theorem abs_stagePayoff_quittingGame_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C)
    (s : (quittingGame reward).State) (a : ι → Bool) :
    |(quittingGame reward).stagePayoff s a who| ≤ max 0 C := by
  cases s with
  | none =>
      show |(quittingGame reward).stagePayoff none a who| ≤ max 0 C
      rw [show (quittingGame reward).stagePayoff none a who = 0 from rfl, abs_zero]
      exact le_max_left 0 C
  | some S => exact (hC S).trans (le_max_right 0 C)

/-- **The quit-at-once punishment floor.**  If `m` is below every reward at a
terminal set containing `who`, then `who`'s punishment level at horizon `T` is
at least `horizonTailWeight T * m`: the one stage of active play that precedes
absorption is the entire loss. -/
theorem horizonTailWeight_mul_le_punishmentLevel_quittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ) {m : ℝ}
    (hm : ∀ S : {S : Finset ι // S.Nonempty}, who ∈ (S : Finset ι) →
      m ≤ reward S who) :
    horizonTailWeight T * m ≤ (quittingGame reward).punishmentLevel none T who := by
  haveI : ∀ i : ι, Nonempty ((quittingGame reward).Act i) :=
    fun _ => inferInstanceAs (Nonempty Bool)
  haveI : Nonempty (quittingGame reward).BehaviorProfile :=
    (quittingGame reward).nonempty_behaviorProfile
  unfold StochasticGame.punishmentLevel StochasticGame.bestResponseAverageAgainstProfile
  refine le_ciInf fun τ => ?_
  have hbdd : BddAbove (Set.range fun dev : (quittingGame reward).BehaviorStrategy who =>
      (quittingGame reward).finiteAveragePayoff none T (Function.update τ who dev) who) :=
    ⟨max 0 C, by
      rintro _ ⟨dev, rfl⟩
      exact (abs_le.mp ((quittingGame reward).abs_finiteAveragePayoff_le
        (le_max_left 0 C) (abs_stagePayoff_quittingGame_le reward who hC) none T _)).2⟩
  refine le_trans ?_ (le_ciSup hbdd (quittingAlwaysQuitStrategy reward who))
  exact horizonTailWeight_mul_le_finiteAveragePayoff_update_quittingAlwaysQuitStrategy
    reward who τ T hm

/-- **The never-quit punishment floor.**  If a nonpositive `m` is below every
reward at a terminal set avoiding `who`, then `who`'s punishment level is at
least `m` at every horizon. -/
theorem le_punishmentLevel_quittingGame_of_forall_notMem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ) {m : ℝ} (hm0 : m ≤ 0)
    (hout : ∀ S : {S : Finset ι // S.Nonempty}, who ∉ (S : Finset ι) →
      m ≤ reward S who) :
    m ≤ (quittingGame reward).punishmentLevel none T who := by
  haveI : ∀ i : ι, Nonempty ((quittingGame reward).Act i) :=
    fun _ => inferInstanceAs (Nonempty Bool)
  haveI : Nonempty (quittingGame reward).BehaviorProfile :=
    (quittingGame reward).nonempty_behaviorProfile
  unfold StochasticGame.punishmentLevel StochasticGame.bestResponseAverageAgainstProfile
  refine le_ciInf fun τ => ?_
  have hbdd : BddAbove (Set.range fun dev : (quittingGame reward).BehaviorStrategy who =>
      (quittingGame reward).finiteAveragePayoff none T (Function.update τ who dev) who) :=
    ⟨max 0 C, by
      rintro _ ⟨dev, rfl⟩
      exact (abs_le.mp ((quittingGame reward).abs_finiteAveragePayoff_le
        (le_max_left 0 C) (abs_stagePayoff_quittingGame_le reward who hC) none T _)).2⟩
  refine le_trans ?_ (le_ciSup hbdd (quittingAlwaysContinueStrategy reward who))
  exact le_finiteAveragePayoff_update_quittingAlwaysContinueStrategy reward who τ T hm0 hout

/-- **The never-quit punishment floor at zero.**  If no terminal set avoiding
`who` is bad for `who`, then `who`'s punishment level is nonnegative at every
horizon. -/
theorem zero_le_punishmentLevel_quittingGame_of_forall_notMem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ)
    (hout : ∀ S : {S : Finset ι // S.Nonempty}, who ∉ (S : Finset ι) →
      0 ≤ reward S who) :
    0 ≤ (quittingGame reward).punishmentLevel none T who :=
  le_punishmentLevel_quittingGame_of_forall_notMem reward who hC T le_rfl hout

/-- **The unconditional punishment floor.**  With no hypothesis on the reward
table beyond boundedness, `who` secures the better of the two pure guarantees:
quitting at once is worth `horizonTailWeight T * mIn` for any `mIn` below the
rewards at terminal sets containing `who`, and never quitting is worth any
nonpositive `mOut` below the rewards at terminal sets avoiding `who`.

Taking `mIn` and `mOut` to be the actual minima over the finitely many
coalitions makes this the sharpest bound available from pure play; it is
attained — see `punishmentLevel_quittingGame_alwaysQuitCounterexample_eq`. -/
theorem max_le_punishmentLevel_quittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ) {mIn mOut : ℝ}
    (hin : ∀ S : {S : Finset ι // S.Nonempty}, who ∈ (S : Finset ι) →
      mIn ≤ reward S who)
    (hmOut0 : mOut ≤ 0)
    (hout : ∀ S : {S : Finset ι // S.Nonempty}, who ∉ (S : Finset ι) →
      mOut ≤ reward S who) :
    max (horizonTailWeight T * mIn) mOut ≤
      (quittingGame reward).punishmentLevel none T who :=
  max_le
    (horizonTailWeight_mul_le_punishmentLevel_quittingGame reward who hC T hin)
    (le_punishmentLevel_quittingGame_of_forall_notMem reward who hC T hmOut0 hout)

/-! ## The conditional identity at the punishment corner -/

/-- **The punishment level is sandwiched.**  Assume no terminal set avoiding
`who` is bad for `who` (`hout`) and no terminal set containing `who` is worse
for `who` than quitting alone (`hin`).  Then the punishment level lies between
`horizonTailWeight T` times the ceiling and the ceiling itself. -/
theorem punishmentLevel_quittingGame_sandwich
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ)
    (hout : ∀ S : {S : Finset ι // S.Nonempty}, who ∉ (S : Finset ι) →
      0 ≤ reward S who)
    (hin : ∀ S : {S : Finset ι // S.Nonempty}, who ∈ (S : Finset ι) →
      reward (quittingSingletonTerminal who) who ≤ reward S who) :
    horizonTailWeight T * max 0 (reward (quittingSingletonTerminal who) who) ≤
        (quittingGame reward).punishmentLevel none T who ∧
      (quittingGame reward).punishmentLevel none T who ≤
        max 0 (reward (quittingSingletonTerminal who) who) := by
  refine ⟨?_, punishmentLevel_quittingGame_le_max reward who hC T⟩
  rcases le_or_gt (reward (quittingSingletonTerminal who) who) 0 with hsolo | hsolo
  · rw [max_eq_left hsolo, mul_zero]
    exact zero_le_punishmentLevel_quittingGame_of_forall_notMem reward who hC T hout
  · rw [max_eq_right hsolo.le]
    exact horizonTailWeight_mul_le_punishmentLevel_quittingGame reward who hC T hin

/-- **The conditional identity.**  Under the same two hypotheses the ceiling
is exact in the horizon limit: the punishment level converges to
`max 0 (reward (quittingSingletonTerminal who) who)`.  Without them the ceiling
is not attained — the punishment level infimizes over opponents who quit, and
the reward table is unconstrained at the terminal sets they force. -/
theorem tendsto_punishmentLevel_quittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C)
    (hout : ∀ S : {S : Finset ι // S.Nonempty}, who ∉ (S : Finset ι) →
      0 ≤ reward S who)
    (hin : ∀ S : {S : Finset ι // S.Nonempty}, who ∈ (S : Finset ι) →
      reward (quittingSingletonTerminal who) who ≤ reward S who) :
    Tendsto (fun T : ℕ => (quittingGame reward).punishmentLevel none T who) atTop
      (nhds (max 0 (reward (quittingSingletonTerminal who) who))) := by
  have hlow : Tendsto
      (fun T : ℕ => horizonTailWeight T *
        max 0 (reward (quittingSingletonTerminal who) who)) atTop
      (nhds (max 0 (reward (quittingSingletonTerminal who) who))) := by
    simpa using tendsto_horizonTailWeight.mul_const
      (max 0 (reward (quittingSingletonTerminal who) who))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun T => (punishmentLevel_quittingGame_sandwich reward who hC T hout hin).1)
    (fun T => (punishmentLevel_quittingGame_sandwich reward who hC T hout hin).2)

/-- **Tightness needs only `hin` once quitting alone pays.**  When `who`'s solo
quitting reward is already nonnegative the ceiling is `reward
(quittingSingletonTerminal who) who` itself, and the quit-at-once floor alone
brackets the punishment level: no hypothesis at all is needed on the terminal
sets avoiding `who`, since `who` never lets the opponents pick one.  This is
the weakest of the tightness hypotheses proved here — `hin` is `2 ^ card ι`
comparisons and nothing else. -/
theorem punishmentLevel_quittingGame_sandwich_of_nonneg_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who)
    (hin : ∀ S : {S : Finset ι // S.Nonempty}, who ∈ (S : Finset ι) →
      reward (quittingSingletonTerminal who) who ≤ reward S who) :
    horizonTailWeight T * reward (quittingSingletonTerminal who) who ≤
        (quittingGame reward).punishmentLevel none T who ∧
      (quittingGame reward).punishmentLevel none T who ≤
        reward (quittingSingletonTerminal who) who := by
  refine ⟨horizonTailWeight_mul_le_punishmentLevel_quittingGame reward who hC T hin, ?_⟩
  have hceiling := punishmentLevel_quittingGame_le_max reward who hC T
  rwa [max_eq_right hsolo] at hceiling

/-! ## The floor is attained -/

open QuittingIsolatedPunishmentLowerBoundCounterexample in
/-- **The unconditional floor is sharp.**  On
`QuittingIsolatedPunishmentLowerBoundCounterexample.reward` — the two-player
table whose singleton quit by `true` pays `0` while every coalition containing
`false` pays `-1000` — the quit-at-once floor and the all-quit opponent profile
meet exactly, pinning the punishment level at horizon `2` to `-500`.

That table is precisely the one on which the ceiling `max 0 (reward
(quittingSingletonTerminal true) true) = 0` fails to be a lower bound
(`punishmentLevel_lt_quittingPositiveSingletonDebtCap`); here the punishment
level is computed outright, so the gap to the ceiling is exactly `500`, and
`horizonTailWeight 2 * (-1000)` is not merely a bound but the value. -/
theorem punishmentLevel_quittingGame_alwaysQuitCounterexample_eq :
    (quittingGame reward).punishmentLevel none 2 true = -500 := by
  classical
  haveI : Nonempty ((quittingGame reward).Act true) := inferInstanceAs (Nonempty Bool)
  have hbdd : BddBelow
      (Set.range ((quittingGame reward).bestResponseAverageAgainstProfile none 2 true)) :=
    ⟨-1000, by
      rintro _ ⟨τ, rfl⟩
      exact (abs_le.mp ((quittingGame reward).abs_bestResponseAverageAgainstProfile_le
        (by norm_num : (0 : ℝ) ≤ 1000) abs_stagePayoff_true_le none 2 τ)).1⟩
  refine le_antisymm ?_ ?_
  · calc (quittingGame reward).punishmentLevel none 2 true
        ≤ (quittingGame reward).bestResponseAverageAgainstProfile none 2 true
            (quittingAlwaysQuitProfile reward) := by
          unfold StochasticGame.punishmentLevel
          exact ciInf_le hbdd (quittingAlwaysQuitProfile reward)
      _ = -500 := bestResponseAverageAgainstProfile_eq
  · have hfloor := horizonTailWeight_mul_le_punishmentLevel_quittingGame reward true
      abs_reward_true_le 2 (m := -1000) (fun S _ => by
        rw [reward_true]
        split <;> norm_num)
    have hweight : horizonTailWeight 2 * (-1000 : ℝ) = -500 := by
      norm_num [horizonTailWeight]
    rwa [hweight] at hfloor

/-! ## A worked refutation: the quit-bonus table -/

namespace QuittingQuitBonus

/-- The quit-bonus table: every player in the quitter set is paid `1`, every
other player `0`.  Quitting is strictly worth doing whatever the opponents
do, so no opponent coalition can hold anybody down. -/
def quitBonusReward : {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun S i => if i ∈ (S : Finset ι) then 1 else 0

omit [Fintype ι] in
/-- Rewards in the quit-bonus table are bounded by one. -/
theorem abs_quitBonusReward_le (S : {S : Finset ι // S.Nonempty}) (i : ι) :
    |quitBonusReward S i| ≤ 1 := by
  unfold quitBonusReward
  split <;> norm_num

omit [Fintype ι] in
/-- A player in the quitter set is paid exactly one. -/
theorem one_le_quitBonusReward (who : ι) (S : {S : Finset ι // S.Nonempty})
    (hmem : who ∈ (S : Finset ι)) : (1 : ℝ) ≤ quitBonusReward S who := by
  simp [quitBonusReward, hmem]

/-- Under the quit-bonus table, every player's punishment level is at least
the horizon tail weight: quitting at stage zero is paid `1` forever after,
whatever the opponents do. -/
theorem horizonTailWeight_le_punishmentLevel (who : ι) (T : ℕ) :
    horizonTailWeight T ≤
      (quittingGame (quitBonusReward (ι := ι))).punishmentLevel none T who := by
  have hfloor := horizonTailWeight_mul_le_punishmentLevel_quittingGame
    (quitBonusReward (ι := ι)) who (fun S => abs_quitBonusReward_le S who) T
    (m := 1) (fun S hS => one_le_quitBonusReward who S hS)
  simpa using hfloor

/-- Every stage payoff of the quit-bonus table is bounded by one. -/
theorem abs_stagePayoff_le (who : ι)
    (s : (quittingGame (quitBonusReward (ι := ι))).State) (a : ι → Bool) :
    |(quittingGame (quitBonusReward (ι := ι))).stagePayoff s a who| ≤ 1 := by
  cases s with
  | none =>
      show |(quittingGame (quitBonusReward (ι := ι))).stagePayoff none a who| ≤ 1
      rw [show (quittingGame (quitBonusReward (ι := ι))).stagePayoff none a who = 0
        from rfl, abs_zero]
      norm_num
  | some S => exact abs_quitBonusReward_le S who

/-- **A worked refutation.**  On the quit-bonus table the all-continue payoff
vector `0` is not a uniform equilibrium payoff: from horizon `4` on, every
player's punishment floor `horizonTailWeight T ≥ 3/4` exceeds `0 + 1/4`, so
the individual-rationality no-go generator
`not_isUniformEquilibriumPayoff_of_punishmentLevel_gt` rejects it. -/
theorem not_isUniformEquilibriumPayoff_zero (who : ι) :
    ¬ (quittingGame (quitBonusReward (ι := ι))).IsUniformEquilibriumPayoff none
      (fun _ => 0) := by
  haveI : Nonempty ((quittingGame (quitBonusReward (ι := ι))).Act who) :=
    inferInstanceAs (Nonempty Bool)
  refine StochasticGame.not_isUniformEquilibriumPayoff_of_punishmentLevel_gt
    (quittingGame (quitBonusReward (ι := ι))) none (fun _ => 0) who
    (by norm_num : (0 : ℝ) ≤ 1) (abs_stagePayoff_le who)
    (by norm_num : (0 : ℝ) < 1 / 4) 4 ?_
  intro T hT
  have hT4 : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hT0 : (T : ℝ) ≠ 0 := by intro h; rw [h] at hT4; linarith
  have hinv : 1 / (T : ℝ) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num) hT4
  have hweight : horizonTailWeight T = 1 - 1 / (T : ℝ) := by
    unfold horizonTailWeight
    field_simp
  have hfloor := horizonTailWeight_le_punishmentLevel (ι := ι) who T
  rw [hweight] at hfloor
  change (0 : ℝ) + 1 / 4 < _
  linarith

end QuittingQuitBonus

end GameTheory
