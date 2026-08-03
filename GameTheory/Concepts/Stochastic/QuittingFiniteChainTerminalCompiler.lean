/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingInfinitePathCompiler
import GameTheory.Concepts.Stochastic.QuittingSimpleBranches
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformPayoffSelection

/-!
# Finite quitting-chain terminal compiler

An infinite recurrent path is not needed to consume a supplied finite
Bellman chain.  The positive sub-Bellman telescope already separates its
terminal deviation gap into three exact pieces:

* the playerwise opponent-survival weights along the finite chain;
* the weighted prescribed one-step residuals; and
* the surviving terminal Snell debt.

This file packages that estimate first for one time-dependent deviation and
then for a terminal behavior profile.  If the root path is extended by the
all-Continue root after the cutoff, the terminal debt is explicitly bounded
by `max 0 qᵢ`, the choice between quitting alone and Never.  Consequently an
accuracy-indexed family of finite chains can be used directly: no compact
limit, relative recurrence, or selected infinite path is assumed.

The compiler uses the actual terminal value of the prescribed root sequence.
A separate finite backward-induction bridge may identify a supplied chain's
declared values with this terminal value and turn exact local root Nash into
zero residual.  Those facts are not assumed here implicitly.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite positive sub-Bellman telescope with an externally supplied
terminal debt.  This is the exact scalar compiler interface: no convergence
or recurrence hypothesis occurs. -/
theorem quittingRootSequenceHazardTerminalGap_le_finiteBudget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) (debt : ℝ)
    (hdebt :
      max
          (quittingRootSequenceHazardTerminalValue reward roots who hazard
              (start + fuel) -
            quittingRootSequenceTerminalValue reward roots who
              (start + fuel))
          0 ≤ debt) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard start -
        quittingRootSequenceTerminalValue reward roots who start ≤
      (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingPrescribedOneStepResidual reward roots who
              (quittingRootSequenceTerminalValue reward roots who)
              (start + offset)) +
        quittingOpponentSurvivalWeight roots who start fuel * debt := by
  let prescribed := quittingRootSequenceTerminalValue reward roots who
  let deviation :=
    quittingRootSequenceHazardTerminalValue reward roots who hazard
  have hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed := by
    intro time
    exact quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
      reward roots who time
  have hresidual : ∀ time, 0 ≤ quittingPrescribedOneStepResidual
      reward roots who prescribed time := by
    intro time
    exact quittingPrescribedOneStepResidual_nonneg
      reward roots who prescribed hprescribed time
  have hdeviation : ∀ time, deviation time ≤
      quittingLiveBellmanValue reward roots who deviation time := by
    intro time
    exact quittingRootSequenceHazardTerminalValue_le_liveBellmanValue
      reward roots who hazard time
  have htelescope :=
    quittingPositiveSubBellmanGap_le_sum_residual_add_tail
      reward roots who prescribed deviation hdeviation hresidual start fuel
  have hscaled := mul_le_mul_of_nonneg_left hdebt
    (quittingOpponentSurvivalWeight_nonneg roots who start fuel)
  calc
    quittingRootSequenceHazardTerminalValue reward roots who hazard start -
          quittingRootSequenceTerminalValue reward roots who start ≤
        max
          (quittingRootSequenceHazardTerminalValue reward roots who hazard
              start -
            quittingRootSequenceTerminalValue reward roots who start)
          0 := le_max_left _ _
    _ ≤ (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingPrescribedOneStepResidual reward roots who prescribed
              (start + offset)) +
        quittingOpponentSurvivalWeight roots who start fuel *
          max (deviation (start + fuel) - prescribed (start + fuel)) 0 :=
      htelescope
    _ ≤ (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingPrescribedOneStepResidual reward roots who prescribed
              (start + offset)) +
        quittingOpponentSurvivalWeight roots who start fuel * debt :=
      add_le_add_right hscaled _

/-- From the cutoff onward, a root sequence which is identically
all-Continue has prescribed terminal value zero. -/
theorem quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingRootSequenceTerminalValue reward roots who cutoff = 0 := by
  have hprofile : quittingRootSequenceProfile reward roots cutoff =
      quittingAlwaysContinueProfile reward := by
    funext player time history
    unfold quittingRootSequenceProfile quittingAlwaysContinueProfile
      StochasticGame.stationaryBehaviorProfile
    rw [htail (cutoff + time) (Nat.le_add_right cutoff time)]
    rfl
  unfold quittingRootSequenceTerminalValue
  rw [hprofile]
  exact quittingTerminalPayoff_quittingAlwaysContinue reward who

/-- Against an all-Continue suffix, every unilateral tail hazard is bounded
by the terminal Snell choice `max 0 qᵢ`: quit alone or Never. -/
theorem quittingRootSequenceHazardTerminalValue_le_singletonSnell_of_allContinue_from
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard cutoff ≤
      max 0 (reward (quittingSingletonTerminal who) who) := by
  let shiftedDeviation : (quittingGame reward).BehaviorStrategy who :=
    fun time _history ↦ hazard (cutoff + time)
  have hprofile :
      quittingRootSequenceProfile reward
          (quittingRootSequenceUpdate roots who hazard) cutoff =
        Function.update (quittingAlwaysContinueProfile reward) who
          shiftedDeviation := by
    funext player time history
    unfold quittingRootSequenceProfile quittingRootSequenceUpdate
      quittingAlwaysContinueProfile StochasticGame.stationaryBehaviorProfile
    by_cases hplayer : player = who
    · subst player
      simp [shiftedDeviation]
    · rw [Function.update_of_ne hplayer,
        Function.update_of_ne hplayer]
      rw [htail (cutoff + time) (Nat.le_add_right cutoff time)]
      rfl
  unfold quittingRootSequenceHazardTerminalValue
    quittingRootSequenceTerminalValue
  rw [hprofile]
  exact quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
    reward who shiftedDeviation

/-- The positive tail gap at an all-Continue cutoff is bounded by the same
explicit Quit-versus-Never Snell debt. -/
theorem quittingFiniteChain_terminalDebt_le_singletonSnell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    max
        (quittingRootSequenceHazardTerminalValue reward roots who hazard
            cutoff -
          quittingRootSequenceTerminalValue reward roots who cutoff)
        0 ≤
      max 0 (reward (quittingSingletonTerminal who) who) := by
  rw [quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
    reward roots who cutoff htail, sub_zero]
  apply max_le
  · exact quittingRootSequenceHazardTerminalValue_le_singletonSnell_of_allContinue_from
      reward roots who hazard cutoff htail
  · exact le_max_left _ _

/-! ## Supplied boundary-zero chains -/

/-- A finite policy-evaluation chain with boundary value zero is selected
exactly by its all-Continue extension.  The proof is finite backward
induction, so no compactness or infinite-path selection is involved. -/
theorem eq_quittingRootSequenceTerminalValue_of_finite_zeroBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) :
    ∀ time, time ≤ cutoff →
      value time =
        fun who ↦ quittingRootSequenceTerminalValue reward roots who time := by
  intro time htime
  exact Nat.decreasingInduction (n := cutoff) (motive := fun time _ ↦
      value time =
        fun who ↦ quittingRootSequenceTerminalValue reward roots who time)
    (fun liveTime hlive ih ↦ by
      rw [hpolicy liveTime hlive]
      funext who
      rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
      unfold quittingRootSuccessorPayoff
      apply quittingRootExpectedPayoff_continuation_congr
      exact congrFun ih who)
    (by
      rw [hterminal]
      funext who
      rw [Pi.zero_apply,
        quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
          reward roots who cutoff htail])
    htime

/-- Local exact root Nash at one selected finite-chain node makes that
node's actual prescribed terminal residual zero. -/
theorem quittingFiniteChain_prescribedResidual_eq_zero_of_rootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (time : ℕ)
    (hselected : value (time + 1) =
      fun player ↦ quittingRootSequenceTerminalValue reward roots player
        (time + 1))
    (hnash : IsεQuittingRootNash reward (value (time + 1)) 0
      (roots time)) :
    quittingPrescribedOneStepResidual reward roots who
      (quittingRootSequenceTerminalValue reward roots who) time = 0 := by
  let prescribed := quittingRootSequenceTerminalValue reward roots who
  let actualTail : Payoff ι := fun _ ↦ prescribed (time + 1)
  have hcoordinate : value (time + 1) who = prescribed (time + 1) := by
    exact congrFun hselected who
  have hquitNash := hnash who (PMF.pure true)
  have hcontinueNash := hnash who (PMF.pure false)
  have hquitCongruence := quittingRootExpectedPayoff_continuation_congr
    reward (value (time + 1)) actualTail
      (Function.update (roots time) who (PMF.pure true)) who hcoordinate
  have hcontinueCongruence := quittingRootExpectedPayoff_continuation_congr
    reward (value (time + 1)) actualTail
      (Function.update (roots time) who (PMF.pure false)) who hcoordinate
  have hrootCongruence := quittingRootExpectedPayoff_continuation_congr
    reward (value (time + 1)) actualTail (roots time) who hcoordinate
  have hquit : quittingFixedOpponentsQuitValue reward roots who time ≤
      quittingRootSuccessorPayoff reward actualTail (roots time) who := by
    rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward roots who actualTail time]
    unfold quittingRootQuitPayoff quittingRootSuccessorPayoff
    rw [← hquitCongruence, ← hrootCongruence]
    simpa only [add_zero] using hquitNash
  have hcontinue :
      quittingFixedOpponentsContinueReward reward roots who time +
          quittingFixedOpponentsContinueMass roots who time *
            prescribed (time + 1) ≤
        quittingRootSuccessorPayoff reward actualTail (roots time) who := by
    rw [← quittingRootContinuePayoff_eq_fixedOpponents
      reward roots who actualTail time]
    unfold quittingRootContinuePayoff quittingRootSuccessorPayoff
    rw [← hcontinueCongruence, ← hrootCongruence]
    simpa only [add_zero] using hcontinueNash
  have hmax : quittingLiveBellmanValue reward roots who prescribed time ≤
      quittingRootSuccessorPayoff reward actualTail (roots time) who := by
    unfold quittingLiveBellmanValue
    exact max_le hquit hcontinue
  have hprescribed : prescribed time =
      quittingRootSuccessorPayoff reward actualTail (roots time) who :=
    quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
      reward roots who time
  have hnonneg := quittingPrescribedOneStepResidual_nonneg
    reward roots who prescribed
      (fun liveTime ↦
        quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
          reward roots who liveTime)
      time
  have hupper : quittingLiveBellmanValue reward roots who prescribed time ≤
      prescribed time := by
    rw [hprescribed]
    exact hmax
  unfold quittingPrescribedOneStepResidual at hnonneg ⊢
  exact le_antisymm (sub_nonpos.mpr hupper) hnonneg

/-- **Finite-chain unilateral compiler.**  Extend a supplied finite root
chain by all-Continue.  Every infinite time-dependent unilateral deviation
is then charged to the finite weighted prescribed residual plus the
surviving Quit-versus-Never debt. -/
theorem quittingRootSequenceHazardTerminalGap_le_finiteChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 -
        quittingRootSequenceTerminalValue reward roots who 0 ≤
      (∑ time ∈ Finset.range cutoff,
          quittingOpponentSurvivalWeight roots who 0 time *
            quittingPrescribedOneStepResidual reward roots who
              (quittingRootSequenceTerminalValue reward roots who) time) +
        quittingOpponentSurvivalWeight roots who 0 cutoff *
          max 0 (reward (quittingSingletonTerminal who) who) := by
  have hdebt := quittingFiniteChain_terminalDebt_le_singletonSnell
    reward roots who hazard cutoff htail
  have hbound := quittingRootSequenceHazardTerminalGap_le_finiteBudget
    reward roots who hazard 0 cutoff
      (max 0 (reward (quittingSingletonTerminal who) who))
      (by simpa only [Nat.zero_add] using hdebt)
  simpa only [Nat.zero_add] using hbound

/-- **Exact finite-chain compiler.**  If the supplied boundary-zero chain
is evaluated exactly and every pre-cutoff root is an exact local root Nash
equilibrium, all finite residual charges vanish.  The only remaining
unilateral debt is the surviving option to quit alone at the cutoff. -/
theorem quittingRootSequenceHazardTerminalGap_le_finiteExactChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 -
        value 0 who ≤
      quittingOpponentSurvivalWeight roots who 0 cutoff *
        max 0 (reward (quittingSingletonTerminal who) who) := by
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_finite_zeroBoundary
      reward roots value cutoff htail hterminal hpolicy
  have hvalueZero : value 0 who =
      quittingRootSequenceTerminalValue reward roots who 0 :=
    congrFun (hselected 0 (Nat.zero_le cutoff)) who
  have hsum :
      (∑ time ∈ Finset.range cutoff,
          quittingOpponentSurvivalWeight roots who 0 time *
            quittingPrescribedOneStepResidual reward roots who
              (quittingRootSequenceTerminalValue reward roots who) time) = 0 := by
    apply Finset.sum_eq_zero
    intro time htime
    have hlt : time < cutoff := Finset.mem_range.mp htime
    rw [quittingFiniteChain_prescribedResidual_eq_zero_of_rootNash
      reward roots value who time
        (hselected (time + 1) (Nat.succ_le_of_lt hlt))
        (hnash time hlt), mul_zero]
  have hgap := quittingRootSequenceHazardTerminalGap_le_finiteChain
    reward roots who hazard cutoff htail
  rw [hsum, zero_add, ← hvalueZero] at hgap
  exact hgap

/-- The all-Continue extension of an exact boundary-zero finite chain
delivers its declared initial value exactly. -/
theorem quittingTerminalPayoff_finiteExactChainProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) :
    quittingTerminalPayoff reward (quittingInfinitePathProfile reward roots) =
      value 0 := by
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_finite_zeroBoundary
      reward roots value cutoff htail hterminal hpolicy
  funext who
  rw [quittingTerminalPayoff_infinitePathProfile]
  exact (congrFun (hselected 0 (Nat.zero_le cutoff)) who).symm

/-- **Game-facing finite-chain compiler.**  A common bound on each player's
finite weighted residual and surviving terminal Snell debt makes the
finite-chain profile a terminal approximate Nash equilibrium. -/
theorem finiteChainProfile_isεAsymptoticNash_of_weightedBudgets
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (ε : ℝ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hbudget : ∀ who,
      (∑ time ∈ Finset.range cutoff,
          quittingOpponentSurvivalWeight roots who 0 time *
            quittingPrescribedOneStepResidual reward roots who
              (quittingRootSequenceTerminalValue reward roots who) time) +
        quittingOpponentSurvivalWeight roots who 0 cutoff *
          max 0 (reward (quittingSingletonTerminal who) who) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingInfinitePathProfile reward roots) := by
  intro who deviation
  have hgap := quittingRootSequenceHazardTerminalGap_le_finiteChain
    reward roots who (quittingBehaviorLiveHazard reward deviation)
      cutoff htail
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingInfinitePathProfile reward roots) who deviation
  rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
  rw [hdeviation, quittingTerminalPayoff_infinitePathProfile]
  have hbound := hgap.trans (hbudget who)
  linarith

/-- A uniform bound on the surviving singleton-quit debts of an exact
boundary-zero chain makes its all-Continue extension a terminal approximate
Nash equilibrium. -/
theorem finiteExactChainProfile_isεAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (ε : ℝ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hdebt : ∀ who,
      quittingOpponentSurvivalWeight roots who 0 cutoff *
        max 0 (reward (quittingSingletonTerminal who) who) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingInfinitePathProfile reward roots) := by
  intro who deviation
  have hgap := quittingRootSequenceHazardTerminalGap_le_finiteExactChain
    reward roots value who (quittingBehaviorLiveHazard reward deviation)
      cutoff htail hterminal hpolicy hnash
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingInfinitePathProfile reward roots) who deviation
  rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
  rw [hdeviation, quittingTerminalPayoff_infinitePathProfile]
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_finite_zeroBoundary
      reward roots value cutoff htail hterminal hpolicy
  change quittingRootSequenceHazardTerminalValue reward roots who
      (quittingBehaviorLiveHazard reward deviation) 0 ≤
    quittingRootSequenceTerminalValue reward roots who 0 + ε
  rw [← congrFun (hselected 0 (Nat.zero_le cutoff)) who]
  linarith [hgap.trans (hdebt who)]

/-- **All-accuracy finite-chain existence wrapper.**  If an exact
boundary-zero finite chain with arbitrarily small surviving singleton debt
exists at every positive accuracy, the quitting game has a uniform
equilibrium payoff.  The finite chains and their initial values may depend on
the requested accuracy; compact terminal-payoff selection supplies one fixed
uniform payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finiteExactChains
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hchains : ∀ ε : ℝ, 0 < ε →
      ∃ roots : ℕ → ι → PMF Bool, ∃ value : ℕ → Payoff ι, ∃ cutoff : ℕ,
        (∀ time, cutoff ≤ time →
          roots time = (quittingAllContinueRoot : ι → PMF Bool)) ∧
        value cutoff = 0 ∧
        (∀ time, time < cutoff →
          value time = quittingRootSuccessorPayoff reward
            (value (time + 1)) (roots time)) ∧
        (∀ time, time < cutoff →
          IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) ∧
        (∀ who,
          quittingOpponentSurvivalWeight roots who 0 cutoff *
            max 0 (reward (quittingSingletonTerminal who) who) ≤ ε)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward
  intro ε hε
  rcases hchains ε hε with
    ⟨roots, value, cutoff, htail, hterminal, hpolicy, hnash, hdebt⟩
  exact ⟨quittingInfinitePathProfile reward roots,
    finiteExactChainProfile_isεAsymptoticNash reward roots value cutoff ε
      htail hterminal hpolicy hnash hdebt⟩

end GameTheory
