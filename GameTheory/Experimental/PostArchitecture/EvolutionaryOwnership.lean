/-
# EXP-044: evolutionary static/dynamic ownership

The generic half recovers the complete pinned static ESS family against the
canonical Core Nash predicate. The Boolean witness makes the second ESS clause
nonvacuous: the mutant ties against the resident but loses the tie-break test.
-/

import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.EvolutionaryOwnership

open GameTheory GameTheory.Math.Probability

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
  have hge := hfirst.1 second
  by_contra hnot
  push Not at hnot
  have heq : payoff first first = payoff second first :=
    le_antisymm hnot hge
  have hstability := hfirst.2 second heq hne
  have hreverse := hsecond.1 first
  linarith

/-! ## One-way bridge to the canonical static form -/

/-- The other player in a two-player symmetric encounter. -/
def opponent : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

/-- The deterministic two-player form used to present a symmetric encounter. -/
@[reducible]
def symmetricForm (S : Type uS) : GameForm (Fin 2) where
  sig :=
    { Strategy := fun _ => S
      Outcome := Fin 2 → S }
  play profile := FinDist.pure profile

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

/-! ## Nonvacuous hostile witness -/

/-- A mutant ties the resident against the resident, but the resident wins
when each is tested against the mutant. Argument order is own strategy first. -/
def tieBreakPayoff : Bool → Bool → ℝ
  | true, true => 1
  | false, true => 1
  | true, false => 2
  | false, false => 0

theorem mutant_ties_against_resident :
    tieBreakPayoff true true = tieBreakPayoff false true :=
  rfl

theorem resident_wins_tie_break :
    tieBreakPayoff true false > tieBreakPayoff false false := by
  norm_num [tieBreakPayoff]

/-- The resident is ESS, and the proof must use the nonvacuous second clause
for the false mutant. -/
theorem true_isESS : IsESS tieBreakPayoff true := by
  constructor
  · intro mutant
    cases mutant <;> norm_num [tieBreakPayoff]
  · intro mutant heq hne
    cases mutant
    · norm_num [tieBreakPayoff]
    · exact False.elim (hne rfl)

/-- The hostile ESS reaches the shared static Nash surface. -/
theorem true_isNash_symmetric :
    IsNash (symmetricForm Bool) (euPreference (symmetricUtility tieBreakPayoff))
      (residentProfile true) :=
  true_isESS.isNash_symmetric

end GameTheory.Experimental.PostArchitecture.EvolutionaryOwnership
