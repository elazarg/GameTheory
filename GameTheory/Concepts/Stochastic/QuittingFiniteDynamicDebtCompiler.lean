/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtSemantics

/-!
# Finite-chain compiler using exact dynamic debt

The older finite-chain compiler charges the coarse surviving singleton debt
`opponentSurvival * max 0 singletonReward`.  Exact dynamic debt can be
strictly smaller because a player's own prescribed Quit action may discharge
the downstream option.

This file installs the corrected consumer.  An infinite deviation is unfolded
exactly to the finite cutoff.  The all-Continue suffix bounds its remaining
value by the singleton-or-Never option, and monotonicity in the terminal live
payoff lets the exact finite dynamic-debt semantics take over.  Therefore a
small exact debt at every player coordinate makes the all-Continue extension
a terminal approximate Nash profile.  The usual terminal-to-uniform selection
then closes an all-accuracy family.

No compactness or assertion that such small-debt chains exist is made here.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Finite unfolding and terminal monotonicity -/

/-- An infinite hazard value is exactly its finite terminal-boundary
recursion, with the actual infinite value of the surviving suffix installed
at the cutoff. -/
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
      rw [show start + (fuel + 1) = start + 1 + fuel by omega]
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
        quittingFiniteTerminalHazardValue, ← ih (start + 1)]

/-- Finite hazard payoff is monotone in its supplied terminal live value. -/
theorem quittingFiniteTerminalHazardValue_mono_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) {lower upper : ℝ} (hterminal : lower ≤ upper) :
    ∀ start fuel,
      quittingFiniteTerminalHazardValue reward roots who hazard lower
          start fuel ≤
        quittingFiniteTerminalHazardValue reward roots who hazard upper
          start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact hterminal
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalHazardValue]
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have htail := mul_le_mul_of_nonneg_left (ih (start + 1)) hmass
      have hcontinue :
          quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalHazardValue reward roots who hazard
                    lower (start + 1) fuel ≤
            quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalHazardValue reward roots who hazard
                    upper (start + 1) fuel := by
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hcontinue
        (show 0 ≤ (hazard start false).toReal from ENNReal.toReal_nonneg)
      linarith

/-! ## Exact-D finite-chain unilateral bound -/

/-- The gain of every infinite unilateral hazard against an all-Continue
extension is bounded by exact dynamic debt, initialized with the terminal
singleton-or-Never option. -/
theorem quittingRootSequenceHazardTerminalGap_le_finiteDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value cutoff = 0) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 -
        value 0 who ≤
      quittingFiniteDynamicDebt reward roots who (fun time => value time who)
        (max 0 (reward (quittingSingletonTerminal who) who)) 0 cutoff := by
  let terminalCap := max 0 (reward (quittingSingletonTerminal who) who)
  let tailValue :=
    quittingRootSequenceHazardTerminalValue reward roots who hazard cutoff
  have htailValue : tailValue ≤ terminalCap := by
    exact quittingRootSequenceHazardTerminalValue_le_singletonSnell_of_allContinue_from
      reward roots who hazard cutoff htail
  have hunfold :=
    quittingRootSequenceHazardTerminalValue_eq_finiteTerminalHazardValue
      reward roots who hazard 0 cutoff
  have hmono := quittingFiniteTerminalHazardValue_mono_terminal
    reward roots who hazard htailValue 0 cutoff
  have hterminalWho : value cutoff who = 0 := by
    rw [hterminal]
    rfl
  have hdebt := quittingFiniteTerminalHazardGain_le_dynamicDebt
    reward roots who (fun time => value time who) terminalCap hazard 0 cutoff
  dsimp only [tailValue] at hunfold hmono
  dsimp only [terminalCap] at hdebt ⊢
  simp only [Nat.zero_add] at hunfold
  simp only [hterminalWho, zero_add] at hdebt
  rw [hunfold]
  exact (sub_le_sub_right hmono (value 0 who)).trans hdebt

/-- **Corrected game-facing finite-chain compiler.**  Exact dynamic debt,
rather than its coarse multiplicative envelope, controls every unilateral
terminal deviation. -/
theorem finiteChainProfile_isεAsymptoticNash_of_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (ε : ℝ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hdebt : ∀ who,
      quittingFiniteDynamicDebt reward roots who (fun time => value time who)
        (max 0 (reward (quittingSingletonTerminal who) who)) 0 cutoff ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingInfinitePathProfile reward roots) := by
  have hdelivery := quittingTerminalPayoff_finiteExactChainProfile
    reward roots value cutoff htail hterminal hpolicy
  intro who deviation
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingInfinitePathProfile reward roots) who deviation
  rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
  rw [hdeviation, hdelivery]
  have hgap := (quittingRootSequenceHazardTerminalGap_le_finiteDynamicDebt
    reward roots value who (quittingBehaviorLiveHazard reward deviation)
      cutoff htail hterminal).trans (hdebt who)
  linarith

/-- All-accuracy existence wrapper for the corrected exact-D finite-chain
waist.  Compact terminal-payoff selection supplies one fixed uniform payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finiteDynamicDebtChains
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hchains : ∀ ε : ℝ, 0 < ε →
      ∃ roots : ℕ → ι → PMF Bool, ∃ value : ℕ → Payoff ι, ∃ cutoff : ℕ,
        (∀ time, cutoff ≤ time →
          roots time = (quittingAllContinueRoot : ι → PMF Bool)) ∧
        value cutoff = 0 ∧
        (∀ time, time < cutoff →
          value time = quittingRootSuccessorPayoff reward
            (value (time + 1)) (roots time)) ∧
        (∀ who,
          quittingFiniteDynamicDebt reward roots who
            (fun time => value time who)
            (max 0 (reward (quittingSingletonTerminal who) who))
            0 cutoff ≤ ε)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward
  intro ε hε
  rcases hchains ε hε with
    ⟨roots, value, cutoff, htail, hterminal, hpolicy, hdebt⟩
  exact ⟨quittingInfinitePathProfile reward roots,
    finiteChainProfile_isεAsymptoticNash_of_dynamicDebt
      reward roots value cutoff ε htail hterminal hpolicy hdebt⟩

end GameTheory
