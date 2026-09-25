/-
# Guarded expected-utility welfare fixture

This binary example retains a genuinely stochastic profile outcome and tests
individual rationality and Pareto transfer with explicit PMF expectations.
-/

import GameTheory.Core.Welfare

noncomputable section

namespace GameTheory.Tests.Welfare

open GameTheory GameTheory.Math.Probability

/-- A genuinely stochastic outcome law. -/
def fair : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

@[reducible]
def fixtureForm : GameForm Bool where
  sig := { Strategy := fun _ => Bool, Outcome := Bool }
  play profile := if profile false then fair else PMF.pure false

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

theorem fixtureIntegrable (player : Bool) (law : PMF Bool) :
    UtilityIntegrable fixtureUtility player law :=
  payoffIntegrable_of_bounded law (fun outcome => fixtureUtility outcome player)
    (C := 3) (by intro outcome; cases player <;> cases outcome <;> norm_num
      [fixtureUtility])

theorem expectedUtility_low (player : Bool) :
    expectedUtility fixtureUtility player (fixtureForm.play low)
      (fixtureIntegrable player (fixtureForm.play low)) = 1 := by
  cases player <;> simp [low, fixtureUtility, expectedUtility_pure]

theorem expectedUtility_improved (player : Bool) :
    expectedUtility fixtureUtility player (fixtureForm.play improved)
      (fixtureIntegrable player (fixtureForm.play improved)) =
        if player then 1 else 2 := by
  cases player
  · have hfalse : PayoffIntegrable (PMF.pure false)
      (fun outcome => fixtureUtility outcome false) :=
        payoffIntegrable_pure false _
    have htrue : PayoffIntegrable (PMF.pure true)
      (fun outcome => fixtureUtility outcome false) :=
        payoffIntegrable_pure true _
    have hm := expect_mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure false) (PMF.pure true)
      (fun outcome => fixtureUtility outcome false) hfalse htrue
    have hproof : fixtureIntegrable false fair =
        payoffIntegrable_mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure false) (PMF.pure true)
          (fun outcome => fixtureUtility outcome false) hfalse htrue := by
      apply Subsingleton.elim
    have hv : expectedUtility fixtureUtility false fair (fixtureIntegrable false fair) = 2 := by
      unfold expectedUtility
      calc
        expect fair (fun outcome => fixtureUtility outcome false)
            (fixtureIntegrable false fair) =
            expect fair (fun outcome => fixtureUtility outcome false)
              (payoffIntegrable_mix (1 / 2) (by norm_num) (by norm_num)
                (PMF.pure false) (PMF.pure true)
                (fun outcome => fixtureUtility outcome false) hfalse htrue) :=
          expect_proof_irrel fair _ _ _
        _ = 2 := by
          have hm' := hm
          norm_num [fair, fixtureUtility, expect_pure] at hm'
          exact hm'
    simpa [improved] using hv
  · have hconst : PayoffIntegrable fair (fun _ : Bool => (1 : ℝ)) :=
      payoffIntegrable_of_bounded fair _ (C := 1) (by intro _; norm_num)
    have hvalue := expect_constant fair 1 hconst
    unfold expectedUtility
    have hproof := expect_proof_irrel fair (fun _ : Bool => (1 : ℝ))
      (fixtureIntegrable true fair) hconst
    simpa [fixtureUtility, improved] using hproof.trans hvalue

theorem low_isIndividuallyRational :
    IsIndividuallyRational fixtureForm fixtureUtility reservation low := by
  intro player
  refine ⟨fixtureIntegrable player (fixtureForm.play low), ?_⟩
  rw [expectedUtility_low]
  cases player <;> norm_num [reservation]

theorem improved_paretoDominates_low :
    ParetoDominates fixtureForm (euPreference fixtureUtility) improved low := by
  constructor
  · intro player
    apply (euPreference_iff fixtureUtility player
      (fixtureForm.play improved) (fixtureForm.play low)
      (fixtureIntegrable player (fixtureForm.play improved))
      (fixtureIntegrable player (fixtureForm.play low))).2
    rw [expectedUtility_low, expectedUtility_improved]
    cases player <;> norm_num
  · refine ⟨false, ?_⟩
    apply (euPreference_strict_iff fixtureUtility false
      (fixtureForm.play improved) (fixtureForm.play low)
      (fixtureIntegrable false (fixtureForm.play improved))
      (fixtureIntegrable false (fixtureForm.play low))).2
    rw [expectedUtility_low, expectedUtility_improved]
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
  refine ⟨fixtureIntegrable player (fixtureForm.play improved), ?_⟩
  rw [expectedUtility_improved]
  cases player <;> norm_num [firstReservation]

theorem improved_isIndividuallyRational_second :
    IsIndividuallyRational fixtureForm fixtureUtility secondReservation improved := by
  intro player
  refine ⟨fixtureIntegrable player (fixtureForm.play improved), ?_⟩
  rw [expectedUtility_improved]
  cases player <;> norm_num [secondReservation]

theorem improved_isIndividuallyRational_sup :
    IsIndividuallyRational fixtureForm fixtureUtility
      (fun player => max (firstReservation player) (secondReservation player))
      improved :=
  improved_isIndividuallyRational_first.sup improved_isIndividuallyRational_second

theorem improved_not_isIndividuallyRational_excessive :
    ¬ IsIndividuallyRational fixtureForm fixtureUtility
      excessiveReservation improved := by
  intro hir
  obtain ⟨hint, hvalue⟩ := hir false
  rw [expectedUtility_improved] at hvalue
  norm_num [excessiveReservation] at hvalue

end GameTheory.Tests.Welfare
