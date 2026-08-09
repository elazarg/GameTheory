/-
# Individual-rationality hostile fixture

The low profile produces outcome `false`.  The improved profile produces a
fair non-point-mass law.  Player `false` moves from utility one to expected
utility two, while player `true` remains at one.  This exercises weak Pareto
improvement, nonzero unequal reservations, pointwise suprema, and rejection of
an excessive outside option without introducing another payoff semantics.
-/

import GameTheory.Core.Response

noncomputable section

namespace GameTheory.Tests.Welfare

open GameTheory Probability

/-- A genuinely stochastic outcome law. -/
def fair : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

@[reducible]
def fixtureForm : GameForm Bool where
  sig :=
    { Strategy := fun _ => Bool
      Outcome := Bool }
  play profile := if profile false then fair else FinDist.pure false

/-- Player `false` values the high outcome; player `true` is indifferent. -/
def fixtureUtility (outcome player : Bool) : ℝ :=
  if player then 1 else if outcome then 3 else 1

def low : Profile fixtureForm.sig := fun _ => false

def improved : Profile fixtureForm.sig := fun player => !player

def reservation : Bool → ℝ
  | false => 1
  | true => 1

def lowerReservation : Bool → ℝ
  | false => 1 / 2
  | true => 3 / 4

def firstReservation : Bool → ℝ
  | false => 2
  | true => 1 / 2

def secondReservation : Bool → ℝ
  | false => 3 / 2
  | true => 1

def excessiveReservation : Bool → ℝ
  | false => 5 / 2
  | true => 1

theorem expectedUtility_low (player : Bool) :
    expectedUtility fixtureUtility player (fixtureForm.play low) = 1 := by
  cases player <;> simp [fixtureUtility, low]

theorem expectedUtility_improved (player : Bool) :
    expectedUtility fixtureUtility player (fixtureForm.play improved) =
      if player then 1 else 2 := by
  cases player
  · show expectedUtility fixtureUtility false fair = 2
    unfold expectedUtility
    rw [fair, FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure]
    norm_num [fixtureUtility]
  · show expectedUtility fixtureUtility true fair = 1
    unfold expectedUtility
    rw [fair, FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure]
    norm_num [fixtureUtility]

theorem low_isIndividuallyRational :
    IsIndividuallyRational fixtureForm fixtureUtility reservation low := by
  intro player
  rw [expectedUtility_low]
  cases player <;> norm_num [reservation]

theorem improved_paretoDominates_low :
    ParetoDominates fixtureForm (euPreference fixtureUtility) improved low := by
  constructor
  · intro player
    show expectedUtility fixtureUtility player (fixtureForm.play low) ≤
      expectedUtility fixtureUtility player (fixtureForm.play improved)
    rw [expectedUtility_low, expectedUtility_improved]
    cases player <;> norm_num
  · refine ⟨false, ?_⟩
    rw [euPreference_strict_iff, expectedUtility_low, expectedUtility_improved]
    norm_num

theorem improved_isIndividuallyRational :
    IsIndividuallyRational fixtureForm fixtureUtility reservation improved :=
  low_isIndividuallyRational.of_paretoDominates improved_paretoDominates_low

theorem lowerReservation_le :
    ∀ player, lowerReservation player ≤ reservation player := by
  intro player
  cases player <;> norm_num [lowerReservation, reservation]

theorem improved_isIndividuallyRational_lower :
    IsIndividuallyRational fixtureForm fixtureUtility lowerReservation improved :=
  improved_isIndividuallyRational.mono lowerReservation_le

theorem improved_isIndividuallyRational_first :
    IsIndividuallyRational fixtureForm fixtureUtility firstReservation improved := by
  intro player
  rw [expectedUtility_improved]
  cases player <;> norm_num [firstReservation]

theorem improved_isIndividuallyRational_second :
    IsIndividuallyRational fixtureForm fixtureUtility secondReservation improved := by
  intro player
  rw [expectedUtility_improved]
  cases player <;> norm_num [secondReservation]

theorem improved_isIndividuallyRational_sup :
    IsIndividuallyRational fixtureForm fixtureUtility
      (fun player => max (firstReservation player) (secondReservation player))
      improved :=
  improved_isIndividuallyRational_first.sup
    improved_isIndividuallyRational_second

theorem improved_not_isIndividuallyRational_excessive :
    ¬ IsIndividuallyRational fixtureForm fixtureUtility
      excessiveReservation improved := by
  intro hir
  have hfalse := hir false
  rw [expectedUtility_improved] at hfalse
  norm_num [excessiveReservation] at hfalse

end GameTheory.Tests.Welfare
