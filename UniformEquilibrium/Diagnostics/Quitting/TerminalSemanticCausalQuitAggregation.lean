/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PureTimeExtremality

/-!
# Exact causal account for finite Quit-direction deviations

Moving a fraction of one player's Continue mass to Quit at chronologically
ordered rows produces a causal recursion. The current signed Quit advantage
is collected at the current modification rate, while every later term is
discounted by the probability of refusing the current modification.

This identity uses the literal signed row advantage. It makes no claim that
an eventwise positive-part account lower-bounds that advantage.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Recursive gain account for moving baseline Continue probability toward
Quit. The row gap uses the literal baseline continuation value. -/
def quittingFiniteCausalQuitGain
    (quitValue continueReward continueMass : ℕ → ℝ)
    (baseline : ℕ → PMF Bool) (lambda : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | start, fuel + 1 =>
      let baselineTail := quittingFiniteHazardValue
        quitValue continueReward continueMass baseline (start + 1) fuel
      lambda start * (baseline start false).toReal *
          (quitValue start -
            (continueReward start + continueMass start * baselineTail)) +
        (1 - lambda start) * (baseline start false).toReal *
          continueMass start *
            quittingFiniteCausalQuitGain quitValue continueReward continueMass
              baseline lambda (start + 1) fuel

/-- **Exact finite causal-convexification identity.** If `modified` is
obtained by moving the fraction `lambda t` of the baseline Continue mass to
Quit at every row, then its finite payoff gain is exactly the causal account
above. -/
theorem quittingFiniteHazardValue_sub_eq_causalQuitGain
    (quitValue continueReward continueMass : ℕ → ℝ)
    (baseline modified : ℕ → PMF Bool) (lambda : ℕ → ℝ)
    (hquit : ∀ time,
      (modified time true).toReal =
        (baseline time true).toReal +
          lambda time * (baseline time false).toReal)
    (hcontinue : ∀ time,
      (modified time false).toReal =
        (1 - lambda time) * (baseline time false).toReal) :
    ∀ start fuel,
      quittingFiniteHazardValue quitValue continueReward continueMass
          modified start fuel -
        quittingFiniteHazardValue quitValue continueReward continueMass
          baseline start fuel =
      quittingFiniteCausalQuitGain quitValue continueReward continueMass
        baseline lambda start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingFiniteHazardValue, quittingFiniteCausalQuitGain]
  | succ fuel ih =>
      rw [quittingFiniteHazardValue, quittingFiniteHazardValue,
        quittingFiniteCausalQuitGain, hquit, hcontinue]
      have htail := ih (start + 1)
      have htailEq :
          quittingFiniteHazardValue quitValue continueReward continueMass
              modified (start + 1) fuel =
            quittingFiniteHazardValue quitValue continueReward continueMass
                baseline (start + 1) fuel +
              quittingFiniteCausalQuitGain quitValue continueReward
                continueMass baseline lambda (start + 1) fuel := by
        linarith
      rw [htailEq]
      ring

/-- The exact finite causal identity for a player in a quitting game against
fixed opponent roots. -/
theorem quittingFiniteRootPayoff_sub_eq_causalQuitGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (baseline modified : ℕ → PMF Bool) (lambda : ℕ → ℝ)
    (hquit : ∀ time,
      (modified time true).toReal =
        (baseline time true).toReal +
          lambda time * (baseline time false).toReal)
    (hcontinue : ∀ time,
      (modified time false).toReal =
        (1 - lambda time) * (baseline time false).toReal)
    (start fuel : ℕ) :
    quittingFiniteRootPayoff reward roots who modified start fuel -
        quittingFiniteRootPayoff reward roots who baseline start fuel =
      quittingFiniteCausalQuitGain
        (quittingFixedOpponentsQuitValue reward roots who)
        (quittingFixedOpponentsContinueReward reward roots who)
        (quittingFixedOpponentsContinueMass roots who)
        baseline lambda start fuel := by
  rw [quittingFiniteRootPayoff_eq_hazardValue,
    quittingFiniteRootPayoff_eq_hazardValue]
  exact quittingFiniteHazardValue_sub_eq_causalQuitGain
    _ _ _ baseline modified lambda hquit hcontinue start fuel

end GameTheory
