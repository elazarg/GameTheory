/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.MovingKernelEpochPotentialAccount
import Math.Probability.MovingEndpointOccupationEvidence
import Math.Probability.AnalyticMarkovChargeAlternative

/-!
# Universal-calendar analytic Markov charge alternatives

This file composes analytic finite-state Markov charge alternatives with
the generic moving-kernel epoch telescope.

For one analytic signed state charge, either a stationary circulation has
positive aggregate charge or a punctured potential supplies a sublinear
one-sided calendar account.  Applying the construction to both orientations
gives a common-burn-in two-sided account unless one orientation has a
positive circulation.

All account branches are uniform over the initial law and over the entire
sequence of marginals satisfying the Markov recurrence.  Witness-state
occupation remains available as a specialization.
-/

noncomputable section

namespace Math
namespace Probability

open Filter Math.OnlineLearning

variable {S : Type*}

/-- Kernel frozen during epoch `epoch` after the analytic burn-in. -/
def shiftedUniversalCalendarKernel
    (kernel : ℝ → S → PMF S) (startEpoch epoch : ℕ) :
    S → PMF S :=
  kernel (universalEpochScale (startEpoch + epoch))

/-- An analytic state charge frozen during one shifted universal-calendar
epoch. -/
def shiftedUniversalCalendarCharge
    (charge : ℝ → S → ℝ) (startEpoch epoch : ℕ) :
    S → ℝ :=
  charge (universalEpochScale (startEpoch + epoch))

/-- The fixed witness-state occupation cost. -/
def witnessIndicatorCost
    [DecidableEq S] (witness : S) :
    ℕ → S → ℝ :=
  fun _ state => if state = witness then 1 else 0

/-- The generic scheduled indicator cost is exactly cumulative state
occupation in the endpoint-transport decomposition. -/
theorem cumulativeExpectedScheduledCost_witnessIndicatorCost
    [Finite S] [DecidableEq S]
    (law : ℕ → PMF S) (witness : S) (horizon : ℕ) :
    cumulativeExpectedScheduledCost law
        (witnessIndicatorCost witness) horizon =
      MovingEndpointOccupationEvidence.cumulativeOccupation
        law witness horizon := by
  letI := Fintype.ofFinite S
  unfold cumulativeExpectedScheduledCost witnessIndicatorCost
    MovingEndpointOccupationEvidence.cumulativeOccupation
  apply Finset.sum_congr rfl
  intro stage _
  rw [expect_eq_sum]
  simp

/-- Punctured potential frozen during one shifted universal-calendar
epoch. -/
def AnalyticScaledChargedOccupationPotential.shiftedWitnessPotential
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {witness : S}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel)
      (witnessOccupationCharge witness))
    (startEpoch epoch : ℕ) : S → ℝ :=
  P.puncturedPotentialAt
    (universalEpochScale (startEpoch + epoch))

/-- The punctured potential for an arbitrary analytic state charge, frozen
during one shifted universal-calendar epoch. -/
def AnalyticScaledChargedOccupationPotential.shiftedMarkovChargePotential
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel) charge)
    (startEpoch epoch : ℕ) : S → ℝ :=
  P.puncturedPotentialAt
    (universalEpochScale (startEpoch + epoch))

/-- The account property at one fixed analytic burn-in. -/
def IsShiftedUniversalCalendarChargeAccountAt
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (charge : ℝ → S → ℝ)
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel) charge)
    (startEpoch : ℕ) : Prop :=
  ∀ law : ℕ → PMF S,
    (∀ stage,
      law (stage + 1) =
        (law stage).bind
          (shiftedUniversalCalendarKernel kernel startEpoch
            (anytimeEpochIndex stage))) →
      (∀ horizon,
        cumulativeExpectedScheduledCost law
            (shiftedUniversalCalendarCharge charge startEpoch)
            horizon ≤
          completedAndCurrentEpochBudget
            (epochPotentialBill
              (P.shiftedMarkovChargePotential startEpoch))
            horizon) ∧
        IsAsymptoticallySublinear
          (completedAndCurrentEpochBudget
            (epochPotentialBill
              (P.shiftedMarkovChargePotential startEpoch)))

/-- A one-sided sublinear account for an analytic state charge along the
piecewise-frozen moving kernel. -/
def HasShiftedUniversalCalendarChargeAccount
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (charge : ℝ → S → ℝ) : Prop :=
  ∃ (P : AnalyticScaledChargedOccupationPotential
        (analyticMarkovOccupationColumn kernel) charge)
      (startEpoch : ℕ),
    IsShiftedUniversalCalendarChargeAccountAt
      kernel charge P startEpoch

/-- A common-burn-in pair of accounts for an analytic charge and its
negative. -/
def HasShiftedUniversalCalendarTwoSidedChargeAccount
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (charge : ℝ → S → ℝ) : Prop :=
  ∃ (positive :
        AnalyticScaledChargedOccupationPotential
          (analyticMarkovOccupationColumn kernel) charge)
      (negative :
        AnalyticScaledChargedOccupationPotential
          (analyticMarkovOccupationColumn kernel)
          (fun t state => -charge t state))
      (startEpoch : ℕ),
    IsShiftedUniversalCalendarChargeAccountAt
        kernel charge positive startEpoch ∧
      IsShiftedUniversalCalendarChargeAccountAt
        kernel (fun t state => -charge t state)
          negative startEpoch

/-- The potential branch supplies a single sublinear account which controls
every state law following the shifted piecewise-frozen kernel. -/
def HasShiftedUniversalCalendarWitnessOccupationAccount
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (witness : S) : Prop :=
  ∃ (P : AnalyticScaledChargedOccupationPotential
        (analyticMarkovOccupationColumn kernel)
        (witnessOccupationCharge witness))
      (startEpoch : ℕ),
    ∀ law : ℕ → PMF S,
      (∀ stage,
        law (stage + 1) =
          (law stage).bind
            (shiftedUniversalCalendarKernel kernel startEpoch
              (anytimeEpochIndex stage))) →
        (∀ horizon,
          cumulativeExpectedScheduledCost law
              (witnessIndicatorCost witness) horizon ≤
            completedAndCurrentEpochBudget
              (epochPotentialBill
                (P.shiftedWitnessPotential startEpoch))
              horizon) ∧
          IsAsymptoticallySublinear
            (completedAndCurrentEpochBudget
              (epochPotentialBill
                (P.shiftedWitnessPotential startEpoch)))

namespace AnalyticScaledChargedOccupationPotential

/-- Pointwise charge-to-drift domination at a fixed burn-in compiles to the
moving-kernel account at that burn-in. -/
theorem isShiftedUniversalCalendarChargeAccountAt_of_le_drift
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel) charge)
    (startEpoch : ℕ)
    (hcost :
      ∀ epoch state,
        charge (universalEpochScale (startEpoch + epoch)) state ≤
          expect
              (kernel
                (universalEpochScale (startEpoch + epoch)) state)
              (P.puncturedPotentialAt
                (universalEpochScale (startEpoch + epoch))) -
            P.puncturedPotentialAt
              (universalEpochScale (startEpoch + epoch)) state) :
    IsShiftedUniversalCalendarChargeAccountAt
      kernel charge P startEpoch := by
  intro law law_step
  apply exists_sublinearMovingKernelCostAccount
    law
    (shiftedUniversalCalendarKernel kernel startEpoch)
    (shiftedUniversalCalendarCharge charge startEpoch)
    (P.shiftedMarkovChargePotential startEpoch)
    law_step
  · intro epoch state
    exact hcost epoch state
  · simpa [epochPotentialBill, shiftedMarkovChargePotential,
      shiftedPuncturedPotentialEpochBudget] using
        P.tendsto_shiftedPuncturedPotentialEpochBudget_div_length
          startEpoch

/-- A scaled analytic state-charge potential yields the generic shifted
calendar account. -/
theorem exists_shiftedUniversalCalendarChargeAccount
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel) charge) :
    ∃ startEpoch : ℕ,
      ∀ law : ℕ → PMF S,
        (∀ stage,
          law (stage + 1) =
            (law stage).bind
              (shiftedUniversalCalendarKernel kernel startEpoch
                (anytimeEpochIndex stage))) →
          (∀ horizon,
            cumulativeExpectedScheduledCost law
                (shiftedUniversalCalendarCharge charge startEpoch)
                horizon ≤
              completedAndCurrentEpochBudget
                (epochPotentialBill
                  (P.shiftedMarkovChargePotential startEpoch))
                horizon) ∧
            IsAsymptoticallySublinear
              (completedAndCurrentEpochBudget
                (epochPotentialBill
                  (P.shiftedMarkovChargePotential startEpoch))) := by
  obtain ⟨startEpoch, hcost⟩ :=
    P.exists_startEpoch_markovCharge_le_punctured_drift
  exact
    ⟨startEpoch,
      P.isShiftedUniversalCalendarChargeAccountAt_of_le_drift
        startEpoch hcost⟩

/-- Two scaled potentials share one common burn-in for the charge and its
negative. -/
theorem exists_commonStartEpoch_twoSidedChargeAccount
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {charge : ℝ → S → ℝ}
    (positive : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel) charge)
    (negative : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel)
      (fun t state => -charge t state)) :
    ∃ startEpoch : ℕ,
      IsShiftedUniversalCalendarChargeAccountAt
          kernel charge positive startEpoch ∧
        IsShiftedUniversalCalendarChargeAccountAt
          kernel (fun t state => -charge t state)
            negative startEpoch := by
  obtain ⟨positiveStart, positiveCost⟩ :=
    positive.exists_startEpoch_markovCharge_le_punctured_drift
  obtain ⟨negativeStart, negativeCost⟩ :=
    negative.exists_startEpoch_markovCharge_le_punctured_drift
  let startEpoch := max positiveStart negativeStart
  have positiveStart_le : positiveStart ≤ startEpoch := by
    exact le_max_left _ _
  have negativeStart_le : negativeStart ≤ startEpoch := by
    exact le_max_right _ _
  have positiveCost' :
      ∀ epoch state,
        charge (universalEpochScale (startEpoch + epoch)) state ≤
          expect
              (kernel
                (universalEpochScale (startEpoch + epoch)) state)
              (positive.puncturedPotentialAt
                (universalEpochScale (startEpoch + epoch))) -
            positive.puncturedPotentialAt
              (universalEpochScale (startEpoch + epoch)) state := by
    intro epoch state
    have h :=
      positiveCost (startEpoch - positiveStart + epoch) state
    have heq :
        positiveStart +
            (startEpoch - positiveStart + epoch) =
          startEpoch + epoch := by
      omega
    simpa only [heq] using h
  have negativeCost' :
      ∀ epoch state,
        -charge (universalEpochScale (startEpoch + epoch)) state ≤
          expect
              (kernel
                (universalEpochScale (startEpoch + epoch)) state)
              (negative.puncturedPotentialAt
                (universalEpochScale (startEpoch + epoch))) -
            negative.puncturedPotentialAt
              (universalEpochScale (startEpoch + epoch)) state := by
    intro epoch state
    have h :=
      negativeCost (startEpoch - negativeStart + epoch) state
    have heq :
        negativeStart +
            (startEpoch - negativeStart + epoch) =
          startEpoch + epoch := by
      omega
    simpa only [heq] using h
  exact
    ⟨startEpoch,
      positive.isShiftedUniversalCalendarChargeAccountAt_of_le_drift
        startEpoch positiveCost',
      negative.isShiftedUniversalCalendarChargeAccountAt_of_le_drift
        startEpoch negativeCost'⟩

/-- A scaled witness potential yields the generic shifted-calendar
occupation account. -/
theorem exists_shiftedUniversalCalendarWitnessOccupationAccount
    [Fintype S] [DecidableEq S]
    {kernel : ℝ → S → PMF S} {witness : S}
    (P : AnalyticScaledChargedOccupationPotential
      (analyticMarkovOccupationColumn kernel)
      (witnessOccupationCharge witness)) :
    ∃ startEpoch : ℕ,
      ∀ law : ℕ → PMF S,
        (∀ stage,
          law (stage + 1) =
            (law stage).bind
              (shiftedUniversalCalendarKernel kernel startEpoch
                (anytimeEpochIndex stage))) →
          (∀ horizon,
            cumulativeExpectedScheduledCost law
                (witnessIndicatorCost witness) horizon ≤
              completedAndCurrentEpochBudget
                (epochPotentialBill
                  (P.shiftedWitnessPotential startEpoch))
                horizon) ∧
            IsAsymptoticallySublinear
              (completedAndCurrentEpochBudget
                (epochPotentialBill
                  (P.shiftedWitnessPotential startEpoch))) := by
  obtain ⟨startEpoch, hcost⟩ :=
    P.exists_startEpoch_witnessIndicator_le_punctured_drift
  refine ⟨startEpoch, fun law law_step => ?_⟩
  apply exists_sublinearMovingKernelCostAccount
    law
    (shiftedUniversalCalendarKernel kernel startEpoch)
    (witnessIndicatorCost witness)
    (P.shiftedWitnessPotential startEpoch)
    law_step
  · intro epoch state
    exact hcost epoch state
  · simpa [epochPotentialBill, shiftedWitnessPotential,
      shiftedPuncturedPotentialEpochBudget] using
        P.tendsto_shiftedPuncturedPotentialEpochBudget_div_length
          startEpoch

end AnalyticScaledChargedOccupationPotential

/-- **Analytic state-charge calendar alternative.**

Either one pole-cleared analytic stationary flow has positive total charge,
or every law following the shifted piecewise-frozen kernel has a sublinear
one-sided account for the analytic state charge. -/
theorem analyticPositiveChargedMarkovCirculation_xor_calendarChargeAccount
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (charge : ℝ → S → ℝ)
    (hkernel :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => (kernel t source destination).toReal) 0)
    (hcharge :
      ∀ source, AnalyticAt ℝ (fun t => charge t source) 0) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation
          (analyticMarkovOccupationColumn kernel) charge))
      (HasShiftedUniversalCalendarChargeAccount kernel charge) := by
  have halternative :=
    analyticPositiveChargedCirculation_xor_scaledPotential
      (analyticMarkovOccupationColumn kernel) charge
      (analytic_analyticMarkovOccupationColumn kernel hkernel)
      hcharge
  rw [xor_def] at halternative ⊢
  rcases halternative with
      ⟨hcirculation, hnotPotential⟩ |
      ⟨hpotential, hnotCirculation⟩
  · refine Or.inl ⟨hcirculation, ?_⟩
    rintro ⟨P, -, -⟩
    exact hnotPotential ⟨P⟩
  · refine Or.inr ⟨?_, hnotCirculation⟩
    obtain ⟨P⟩ := hpotential
    obtain ⟨startEpoch, haccount⟩ :=
      P.exists_shiftedUniversalCalendarChargeAccount
    exact ⟨P, startEpoch, haccount⟩

/-- Applying the analytic alternative to a charge and its negative gives
either an oriented positive charged circulation or a common-burn-in pair of
sublinear one-sided accounts.  The two account branches therefore control
the absolute signed cumulative charge along one and the same calendar. -/
theorem
    analyticPositiveChargedMarkovCirculation_or_neg_or_twoSidedAccount
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (charge : ℝ → S → ℝ)
    (hkernel :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => (kernel t source destination).toReal) 0)
    (hcharge :
      ∀ source, AnalyticAt ℝ (fun t => charge t source) 0) :
    (Nonempty
      (AnalyticPositiveChargedCirculation
        (analyticMarkovOccupationColumn kernel) charge)) ∨
      (Nonempty
        (AnalyticPositiveChargedCirculation
          (analyticMarkovOccupationColumn kernel)
          (fun t state => -charge t state))) ∨
        HasShiftedUniversalCalendarTwoSidedChargeAccount
          kernel charge := by
  have positiveAlternative :=
    analyticPositiveChargedCirculation_xor_scaledPotential
      (analyticMarkovOccupationColumn kernel) charge
      (analytic_analyticMarkovOccupationColumn kernel hkernel)
      hcharge
  rw [xor_def] at positiveAlternative
  rcases positiveAlternative with
      ⟨positiveCirculation, -⟩ |
      ⟨positivePotential, -⟩
  · exact Or.inl positiveCirculation
  · have negativeAlternative :=
      analyticPositiveChargedCirculation_xor_scaledPotential
        (analyticMarkovOccupationColumn kernel)
        (fun t state => -charge t state)
        (analytic_analyticMarkovOccupationColumn kernel hkernel)
        (fun source => (hcharge source).neg)
    rw [xor_def] at negativeAlternative
    rcases negativeAlternative with
        ⟨negativeCirculation, -⟩ |
        ⟨negativePotential, -⟩
    · exact Or.inr (Or.inl negativeCirculation)
    · obtain ⟨positive⟩ := positivePotential
      obtain ⟨negative⟩ := negativePotential
      obtain ⟨startEpoch, positiveAccount, negativeAccount⟩ :=
        positive.exists_commonStartEpoch_twoSidedChargeAccount
          negative
      exact Or.inr (Or.inr
        ⟨positive, negative, startEpoch,
          positiveAccount, negativeAccount⟩)

/-- **Analytic witness-state recurrence alternative.**

Either a pole-cleared analytic stationary flow carries positive mass at the
witness state, or every law following the shifted universal-calendar kernel
has a sublinear expected witness-occupation account. -/
theorem analyticPositiveWitnessCirculation_xor_calendarOccupationAccount
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (witness : S)
    (hkernel :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => (kernel t source destination).toReal) 0) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation
          (analyticMarkovOccupationColumn kernel)
          (witnessOccupationCharge witness)))
      (HasShiftedUniversalCalendarWitnessOccupationAccount
        kernel witness) := by
  have halternative :=
    analyticPositiveWitnessCirculation_xor_scaledOccupationPotential
      kernel witness hkernel
  rw [xor_def] at halternative ⊢
  rcases halternative with
      ⟨hcirculation, hnotPotential⟩ |
      ⟨hpotential, hnotCirculation⟩
  · refine Or.inl ⟨hcirculation, ?_⟩
    rintro ⟨P, -, -⟩
    exact hnotPotential ⟨P⟩
  · refine Or.inr ⟨?_, hnotCirculation⟩
    obtain ⟨P⟩ := hpotential
    obtain ⟨startEpoch, haccount⟩ :=
      P.exists_shiftedUniversalCalendarWitnessOccupationAccount
    exact ⟨P, startEpoch, haccount⟩

end Probability
end Math
