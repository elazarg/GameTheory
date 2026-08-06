/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingTargetAnchoredTail
import GameTheory.Concepts.Stochastic.QuittingFiniteEndpointNashBellmanFactory
import GameTheory.Concepts.Stochastic.QuittingCertifiedBoundaryReinsertion
import GameTheory.Concepts.Stochastic.QuittingSurvivalPrefixBridge

/-!
# Diagonal target-tail reinsertion

This module assembles finite exact Nash--Bellman prefixes with player-indexed
closed tails.  Its first layer records the finite semantic identities needed
for the assembly: decomposition at a finite boundary, monotonicity in the
boundary value, exact policy evaluation, and propagation of a terminal
best-response debt through opponent survival.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Finite decomposition of an infinite tail -/

/-- An infinite hazard payoff factors through any finite boundary, with the
actual suffix payoff used as the terminal value of the finite recursion. -/
theorem quittingRootSequenceHazardTerminalValue_eq_finiteTerminalHazardValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      quittingRootSequenceHazardTerminalValue reward roots who hazard start =
        quittingFiniteTerminalHazardValue reward roots who hazard
          (quittingRootSequenceHazardTerminalValue reward roots who hazard
            (start + fuel)) start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
        quittingFiniteTerminalHazardValue]
      have hindex : start + (fuel + 1) = (start + 1) + fuel := by omega
      rw [hindex, ih (start + 1)]

/-- Replacing a root sequence's own coordinate by itself changes nothing. -/
theorem quittingRootSequenceHazardTerminalValue_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who
        (fun time => roots time who) start =
      quittingRootSequenceTerminalValue reward roots who start := by
  unfold quittingRootSequenceHazardTerminalValue
  apply congrArg
    (fun sequence => quittingRootSequenceTerminalValue reward sequence who start)
  funext time player
  simp [quittingRootSequenceUpdate]

/-- The prescribed root-sequence payoff has the same finite-boundary
factorization, using the player's prescribed marginal as its hazard. -/
theorem quittingRootSequenceTerminalValue_eq_finiteTerminalHazardValue_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingRootSequenceTerminalValue reward roots who start =
      quittingFiniteTerminalHazardValue reward roots who
        (fun time => roots time who)
        (quittingRootSequenceTerminalValue reward roots who (start + fuel))
        start fuel := by
  simpa only [quittingRootSequenceHazardTerminalValue_self] using
    quittingRootSequenceHazardTerminalValue_eq_finiteTerminalHazardValue
      reward roots who (fun time => roots time who) start fuel

/-- The finite hazard recursion is monotone in its terminal boundary. -/
theorem quittingFiniteTerminalHazardValue_mono_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) {first second : ℝ}
    (hterminal : first ≤ second) :
    ∀ start fuel,
      quittingFiniteTerminalHazardValue reward roots who hazard first
          start fuel ≤
        quittingFiniteTerminalHazardValue reward roots who hazard second
          start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simpa using hterminal
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalHazardValue]
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left (ih (start + 1))
        (quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false)))

/-! ## Exact finite-prefix Bellman bounds -/

/-- Exact one-root Nash together with policy evaluation bounds both pure
unilateral endpoints by the displayed current value. -/
theorem quittingFinitePrefix_endpointBounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (time : ℕ)
    (hpolicy : value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time))
    (hnash : IsεQuittingRootNash reward (value (time + 1)) 0
      (roots time)) :
    quittingFixedOpponentsQuitValue reward roots who time ≤ value time who ∧
      quittingFixedOpponentsContinueReward reward roots who time +
          quittingFixedOpponentsContinueMass roots who time *
            value (time + 1) who ≤
        value time who := by
  have hcurrent := congrFun hpolicy who
  have hquitNash := hnash who (PMF.pure true)
  have hcontinueNash := hnash who (PMF.pure false)
  constructor
  · rw [hcurrent,
      ← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward roots who (value (time + 1)) time]
    unfold quittingRootQuitPayoff quittingRootSuccessorPayoff
    simpa only [add_zero] using hquitNash
  · rw [hcurrent,
      ← quittingRootContinuePayoff_eq_fixedOpponents
        reward roots who (value (time + 1)) time]
    unfold quittingRootContinuePayoff quittingRootSuccessorPayoff
    simpa only [add_zero] using hcontinueNash

/-- A nonnegative terminal debt at the end of an exact finite Nash--Bellman
prefix is multiplied by opponent-only survival through the prefix. -/
theorem quittingFiniteTerminalBestResponseValue_le_declared_add_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (cutoff : ℕ) {terminalDebt : ℝ}
    (hterminalDebt : 0 ≤ terminalDebt)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) :
    ∀ start fuel, start + fuel ≤ cutoff →
      quittingFiniteTerminalBestResponseValue reward roots who
          (value (start + fuel) who + terminalDebt) start fuel ≤
        value start who +
          quittingOpponentSurvivalWeight roots who start fuel * terminalDebt := by
  intro start fuel hcutoff
  induction fuel generalizing start with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hstart : start < cutoff := by omega
      have htailCutoff : (start + 1) + fuel ≤ cutoff := by omega
      have htail := ih (start + 1) htailCutoff
      obtain ⟨hquit, hcontinue⟩ :=
        quittingFinitePrefix_endpointBounds reward roots value who start
          (hpolicy start hstart) (hnash start hstart)
      let mass := quittingFixedOpponentsContinueMass roots who start
      let tailWeight := quittingOpponentSurvivalWeight roots who (start + 1) fuel
      have hmass : 0 ≤ mass :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have htailWeight : 0 ≤ tailWeight :=
        quittingOpponentSurvivalWeight_nonneg roots who (start + 1) fuel
      have hsurvival :
          quittingOpponentSurvivalWeight roots who start (fuel + 1) =
            mass * tailWeight := by
        rw [show fuel + 1 = 1 + fuel by omega,
          quittingOpponentSurvivalWeight_add]
        simp [quittingOpponentSurvivalWeight, mass, tailWeight]
      rw [quittingFiniteTerminalBestResponseValue]
      apply max_le
      · calc
          quittingFixedOpponentsQuitValue reward roots who start ≤
              value start who := hquit
          _ ≤ value start who + mass * tailWeight * terminalDebt := by
            positivity
          _ = value start who +
              quittingOpponentSurvivalWeight roots who start (fuel + 1) *
                terminalDebt := by rw [hsurvival]
      · have hscaled := mul_le_mul_of_nonneg_left htail hmass
        calc
          quittingFixedOpponentsContinueReward reward roots who start +
                mass *
                  quittingFiniteTerminalBestResponseValue reward roots who
                    (value (start + 1 + fuel) who + terminalDebt)
                    (start + 1) fuel ≤
              quittingFixedOpponentsContinueReward reward roots who start +
                mass * (value (start + 1) who + tailWeight * terminalDebt) := by
                  exact add_le_add_left hscaled _
          _ = (quittingFixedOpponentsContinueReward reward roots who start +
                mass * value (start + 1) who) +
                mass * tailWeight * terminalDebt := by ring
          _ ≤ value start who + mass * tailWeight * terminalDebt :=
            add_le_add_right hcontinue _
          _ = value start who +
              quittingOpponentSurvivalWeight roots who start (fuel + 1) *
                terminalDebt := by rw [hsurvival]

/-- Following the prescribed root marginal through an exact policy-evaluation
prefix returns the displayed initial value when the finite terminal boundary
is the displayed endpoint. -/
theorem quittingFiniteTerminalHazardValue_self_eq_declared
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (cutoff : ℕ)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) :
    ∀ start fuel, start + fuel ≤ cutoff →
      quittingFiniteTerminalHazardValue reward roots who
          (fun time => roots time who) (value (start + fuel) who)
          start fuel = value start who := by
  intro start fuel hcutoff
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      have hstart : start < cutoff := by omega
      have htailCutoff : (start + 1) + fuel ≤ cutoff := by omega
      rw [quittingFiniteTerminalHazardValue, ih (start + 1) htailCutoff]
      rw [congrFun (hpolicy start hstart) who,
        quittingRootSuccessorPayoff_eq_endpointMix,
        quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
        quittingRootContinuePayoff_eq_fixedOpponents]

/-! ## Prefix--tail splicing -/

/-- Use `prefix` before `cutoff` and the time-zero-based `tail` afterward. -/
def quittingPrefixThenTailRoots
    (prefix tail : ℕ → ι → PMF Bool) (cutoff time : ℕ) : ι → PMF Bool :=
  if time < cutoff then prefix time else tail (time - cutoff)

@[simp] theorem quittingPrefixThenTailRoots_of_lt
    (prefix tail : ℕ → ι → PMF Bool) (cutoff time : ℕ)
    (htime : time < cutoff) :
    quittingPrefixThenTailRoots prefix tail cutoff time = prefix time := by
  simp [quittingPrefixThenTailRoots, htime]

@[simp] theorem quittingPrefixThenTailRoots_cutoff
    (prefix tail : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingPrefixThenTailRoots prefix tail cutoff cutoff = tail 0 := by
  simp [quittingPrefixThenTailRoots]

@[simp] theorem quittingPrefixThenTailRoots_add_cutoff
    (prefix tail : ℕ → ι → PMF Bool) (cutoff time : ℕ) :
    quittingPrefixThenTailRoots prefix tail cutoff (cutoff + time) = tail time := by
  simp [quittingPrefixThenTailRoots, Nat.not_lt.mpr (Nat.le_add_right cutoff time)]

/-- At the splice time, the generated history-independent profile is exactly
the supplied tail profile. -/
theorem quittingRootSequenceProfile_prefixThenTail_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefix tail : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingRootSequenceProfile reward
        (quittingPrefixThenTailRoots prefix tail cutoff) cutoff =
      quittingRootSequenceProfile reward tail 0 := by
  funext player time history
  simp [quittingRootSequenceProfile]

/-- The prescribed terminal value at the splice is the tail's time-zero
terminal value. -/
theorem quittingRootSequenceTerminalValue_prefixThenTail_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefix tail : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequenceTerminalValue reward
        (quittingPrefixThenTailRoots prefix tail cutoff) who cutoff =
      quittingRootSequenceTerminalValue reward tail who 0 := by
  unfold quittingRootSequenceTerminalValue
  rw [quittingRootSequenceProfile_prefixThenTail_cutoff]

/-- A unilateral hazard at the splice becomes the correspondingly shifted
hazard on the tail. -/
theorem quittingRootSequenceHazardTerminalValue_prefixThenTail_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefix tail : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPrefixThenTailRoots prefix tail cutoff) who hazard cutoff =
      quittingRootSequenceHazardTerminalValue reward tail who
        (fun time => hazard (cutoff + time)) 0 := by
  unfold quittingRootSequenceHazardTerminalValue
  apply congrArg
    (fun sequence => quittingRootSequenceTerminalValue reward sequence who 0)
  funext time player
  unfold quittingRootSequenceUpdate
  by_cases hplayer : player = who
  · subst player
    simp
  · simp [Function.update_of_ne hplayer]

/-- Target closure transports from a time-zero tail to the selected splice. -/
theorem isQuittingTargetClosedAt_prefixThenTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefix tail : ℕ → ι → PMF Bool) (target : ι) (cutoff : ℕ)
    (hclosed : IsQuittingTargetClosedAt reward tail target 0) :
    IsQuittingTargetClosedAt reward
      (quittingPrefixThenTailRoots prefix tail cutoff) target cutoff := by
  intro hazard
  rw [quittingRootSequenceHazardTerminalValue_prefixThenTail_cutoff,
    quittingRootSequenceTerminalValue_prefixThenTail_cutoff]
  exact hclosed (fun time => hazard (cutoff + time))

end GameTheory
