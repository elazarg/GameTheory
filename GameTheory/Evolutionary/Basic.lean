/-
# Static evolutionary stability

ESS and NSS are properties of a homogeneous two-argument payoff kernel. No
population state, dynamics, finite carrier, topology, or game form is part of
their definition.
-/

import Mathlib.Data.Real.Basic

namespace GameTheory.Evolutionary

universe uS

variable {S : Type uS}

/-- A resident strategy is evolutionarily stable when no mutant does better
against it, and every tying distinct mutant loses the second-order test. -/
def IsESS (payoff : S → S → ℝ) (resident : S) : Prop :=
  (∀ mutant, payoff resident resident ≥ payoff mutant resident) ∧
  (∀ mutant,
    payoff resident resident = payoff mutant resident →
      resident ≠ mutant →
        payoff resident mutant > payoff mutant mutant)

/-- Neutral stability weakens the second-order ESS comparison. -/
def IsNSS (payoff : S → S → ℝ) (resident : S) : Prop :=
  (∀ mutant, payoff resident resident ≥ payoff mutant resident) ∧
  (∀ mutant,
    payoff resident resident = payoff mutant resident →
      payoff resident mutant ≥ payoff mutant mutant)

/-- Every ESS is neutrally stable. -/
theorem IsESS.isNSS {payoff : S → S → ℝ} {resident : S}
    (h : IsESS payoff resident) : IsNSS payoff resident := by
  refine ⟨h.1, fun mutant heq => ?_⟩
  by_cases hsame : resident = mutant
  · subst mutant
    exact le_refl _
  · exact le_of_lt (h.2 mutant heq hsame)

/-- The first ESS clause is the symmetric Nash condition. -/
theorem IsESS.nash_condition {payoff : S → S → ℝ} {resident : S}
    (h : IsESS payoff resident) :
    ∀ mutant, payoff resident resident ≥ payoff mutant resident :=
  h.1

/-- A distinct mutant tying against the resident loses the stability test. -/
theorem IsESS.stability {payoff : S → S → ℝ} {resident mutant : S}
    (h : IsESS payoff resident)
    (heq : payoff resident resident = payoff mutant resident)
    (hne : resident ≠ mutant) :
    payoff resident mutant > payoff mutant mutant :=
  h.2 mutant heq hne

/-- A strict symmetric Nash strategy is automatically an ESS. -/
theorem isESS_of_strict_nash {payoff : S → S → ℝ} {resident : S}
    (hstrict :
      ∀ mutant, mutant ≠ resident →
        payoff resident resident > payoff mutant resident) :
    IsESS payoff resident := by
  refine ⟨fun mutant => ?_, fun mutant heq hne => ?_⟩
  · by_cases hsame : mutant = resident
    · subst mutant
      exact le_refl _
    · exact le_of_lt (hstrict mutant hsame)
  · exact absurd heq (ne_of_gt (hstrict mutant hne.symm))

/-- Distinct ESS are strictly separated against the first resident. -/
theorem IsESS.strict_against_other_ess
    {payoff : S → S → ℝ} {first second : S}
    (hfirst : IsESS payoff first) (hsecond : IsESS payoff second)
    (hne : first ≠ second) :
    payoff first first > payoff second first := by
  rcases lt_or_eq_of_le (hfirst.1 second) with hstrict | hequal
  · exact hstrict
  · have hstability := hfirst.2 second hequal.symm hne
    exact (not_lt_of_ge (hsecond.1 first) hstability).elim

end GameTheory.Evolutionary
