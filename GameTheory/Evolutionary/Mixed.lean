/-
# Evolutionary stability against mixed mutants

This module instantiates the carrier-parametric ESS kernel with finite laws.
It is separate from `Basic` so the foundational static definitions retain no
probability dependency.
-/

import GameTheory.Evolutionary.Basic
import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Evolutionary

open GameTheory.Math.Probability

universe uS

variable {S : Type uS}

/-- Expected encounter payoff when both the resident and opponent population
strategies are finite laws over pure actions. -/
def mixedPayoff (payoff : S → S → ℝ) (resident opponent : FinDist S) : ℝ :=
  resident.expect fun own => opponent.expect fun other => payoff own other

/-- ESS with arbitrary finite-law mutants. This is the explicit mixed-mutation
specialization; `IsESS payoff resident` itself remains carrier-parametric. -/
abbrev IsMixedESS (payoff : S → S → ℝ) (resident : FinDist S) : Prop :=
  IsESS (mixedPayoff payoff) resident

/-- Neutral stability with arbitrary finite-law mutants. -/
abbrev IsMixedNSS (payoff : S → S → ℝ) (resident : FinDist S) : Prop :=
  IsNSS (mixedPayoff payoff) resident

end GameTheory.Evolutionary
