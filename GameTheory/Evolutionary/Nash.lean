/-
# Evolutionary stability and canonical Nash equilibrium

This module is the one-way bridge from the static evolutionary payoff kernel
to the shared utility-free form and equilibrium predicate.
-/

import GameTheory.Core.Utility
import GameTheory.Evolutionary.Basic
import GameTheory.Evolutionary.Mixed

noncomputable section

namespace GameTheory.Evolutionary

open GameTheory.Math.Probability

universe uS

variable {S : Type uS}

/-- The other player in a two-player symmetric encounter. -/
def opponent : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

/-- The deterministic two-player form used to present a symmetric encounter. -/
@[reducible]
def symmetricForm (S : Type uS) : GameForm (Fin 2) :=
  GameForm.deterministic
    { Strategy := fun _ => S
      Outcome := Fin 2 → S }
    fun profile => profile

/-- The orientation-sensitive utility induced by a population payoff kernel. -/
def symmetricUtility (payoff : S → S → ℝ) :
    Utility (symmetricForm S).sig :=
  fun profile who => payoff (profile who) (profile (opponent who))

/-- The profile in which both players use the resident strategy. -/
def residentProfile (resident : S) : Profile (symmetricForm S).sig :=
  fun _ => resident

/-- An ESS induces an ordinary Nash equilibrium of the canonical symmetric
two-player presentation. No evolutionary-specific equilibrium predicate is
introduced. -/
theorem IsESS.isNash_symmetric {payoff : S → S → ℝ} {resident : S}
    (h : IsESS payoff resident) :
    IsNash (symmetricForm S) (euPreference (symmetricUtility payoff))
      (residentProfile resident) := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  fin_cases who <;>
    simpa [symmetricForm, symmetricUtility, residentProfile, opponent] using
      h.1 replacement

/-- A mixed-mutation ESS is Nash in the symmetric encounter game whose pure
strategies are finite population laws. -/
theorem IsMixedESS.isNash_symmetric
    {payoff : S → S → ℝ} {resident : FinDist S}
    (h : IsMixedESS payoff resident) :
    IsNash (symmetricForm (FinDist S))
      (euPreference (symmetricUtility (mixedPayoff payoff)))
      (residentProfile resident) :=
  IsESS.isNash_symmetric h

end GameTheory.Evolutionary
