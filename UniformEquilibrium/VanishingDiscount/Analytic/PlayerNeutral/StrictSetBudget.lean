/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.LeadingDriftAlternative
import Math.Probability.AdaptiveOccupationSetBudget

/-!
# Setwise budget for strictly separated player-neutral transitions

A strict leading-drift certificate separates more than its distinguished
column.  Every column on which the same bounded potential has positive drift
belongs to a finite strict set.  The minimum drift on that set is positive,
and the complete strict set has one horizon-uniform adaptive occupation
budget.

This is the finite deflation datum needed to discard every strictly
separated response at once.  It does not claim that the remaining zero-drift
family has already been compiled into a recurrent child or punishment.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace PlayerNeutralStrictLeadingDrift

local instance playerNeutralOccupationIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}

/-- Endpoint drift of one operational column under the bounded normalized
leading potential. -/
def normalizedDrift
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (index : germ.PlayerNeutralOccupationIndex who) : ℝ :=
  expect (germ.playerNeutralOccupationKernel who index) C.potential -
    C.potential (germ.playerNeutralOccupationSource who index)

/-- All player-neutral columns strictly separated by the same leading
potential. -/
def strictIndexSet
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    Finset (germ.PlayerNeutralOccupationIndex who) := by
  classical
  exact Finset.univ.filter fun index => 0 < C.normalizedDrift index

theorem mem_strictIndexSet_iff
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (index : germ.PlayerNeutralOccupationIndex who) :
    index ∈ C.strictIndexSet ↔ 0 < C.normalizedDrift index := by
  classical
  simp [strictIndexSet]

/-- The originally selected strict column belongs to the complete strict
set. -/
theorem index_mem_strictIndexSet
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.index ∈ C.strictIndexSet := by
  rw [C.mem_strictIndexSet_iff]
  rw [normalizedDrift, C.selected_drift]
  exact C.margin_pos

theorem strictIndexSet_nonempty
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.strictIndexSet.Nonempty :=
  ⟨C.index, C.index_mem_strictIndexSet⟩

/-- The finite collection of positive drift values on the complete strict
set. -/
def strictDriftValues
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    Finset ℝ := by
  classical
  exact C.strictIndexSet.image C.normalizedDrift

theorem strictDriftValues_nonempty
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.strictDriftValues.Nonempty := by
  classical
  exact C.strictIndexSet_nonempty.image C.normalizedDrift

/-- The common positive margin of all strictly separated columns. -/
def strictMargin
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) : ℝ :=
  C.strictDriftValues.min' C.strictDriftValues_nonempty

theorem strictMargin_pos
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    0 < C.strictMargin := by
  classical
  have hmem :
      C.strictMargin ∈ C.strictDriftValues :=
    Finset.min'_mem _ C.strictDriftValues_nonempty
  obtain ⟨index, index_mem, hvalue⟩ :=
    Finset.mem_image.mp hmem
  rw [← hvalue]
  exact (C.mem_strictIndexSet_iff index).mp index_mem

theorem strictMargin_le_normalizedDrift
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    {index : germ.PlayerNeutralOccupationIndex who}
    (index_mem : index ∈ C.strictIndexSet) :
    C.strictMargin ≤ C.normalizedDrift index := by
  classical
  exact Finset.min'_le C.strictDriftValues _
    (Finset.mem_image.mpr ⟨index, index_mem, rfl⟩)

/-- Every column left after removing the complete strict set has exactly zero
drift under the leading potential. -/
theorem normalizedDrift_eq_zero_of_not_mem_strictIndexSet
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    {index : germ.PlayerNeutralOccupationIndex who}
    (index_not_mem : index ∉ C.strictIndexSet) :
    C.normalizedDrift index = 0 := by
  apply le_antisymm
  · exact le_of_not_gt fun positive =>
      index_not_mem ((C.mem_strictIndexSet_iff index).mpr positive)
  · simpa only [normalizedDrift] using C.drift_nonneg index

/-- Each operational column is either in the uniformly budgeted strict set
or is complementary to the leading potential. -/
theorem mem_strictIndexSet_or_normalizedDrift_eq_zero
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (index : germ.PlayerNeutralOccupationIndex who) :
    index ∈ C.strictIndexSet ∨ C.normalizedDrift index = 0 := by
  classical
  by_cases index_mem : index ∈ C.strictIndexSet
  · exact Or.inl index_mem
  · exact Or.inr
      (C.normalizedDrift_eq_zero_of_not_mem_strictIndexSet index_mem)

/-- Under pure history-dependent switching, the sum of expected use counts
over every strictly separated column is uniformly bounded in the horizon. -/
theorem strictSetUseBudget
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex who)
    (source_compatible :
      ∀ n history,
        germ.playerNeutralOccupationSource who (choice n history) =
          history (Fin.last n))
    (T : ℕ) :
    C.strictMargin *
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison
                (germ.playerNeutralOccupationKernel who) choice))
            (T + 1))
          (fun history =>
            ∑ index : {index // index ∈ C.strictIndexSet},
              selectedTransitionUseCount choice index.1 T history) ≤
      C.strictIndexSet.card := by
  classical
  exact margin_mul_expect_transitionSetUseCount_le_card
    initial
    (germ.playerNeutralOccupationKernel who)
    (germ.playerNeutralOccupationSource who)
    choice C.strictIndexSet C.potential C.bounded source_compatible
    (by
      intro index
      simpa only [normalizedDrift] using C.drift_nonneg index)
    (by
      intro index index_mem
      exact C.strictMargin_le_normalizedDrift index_mem)
    T

/-- Under behavioral switching, the total expected predictable mass placed
on every strictly separated column is uniformly bounded in the horizon. -/
theorem strictSetMassBudget
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex who))
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index =
            history (Fin.last n))
    (T : ℕ) :
    C.strictMargin *
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison
                (germ.playerNeutralOccupationKernel who) selection))
            (T + 1))
          (fun history =>
            ∑ index : {index // index ∈ C.strictIndexSet},
              selectedTransitionMassSum selection index.1 T history) ≤
      C.strictIndexSet.card := by
  classical
  exact margin_mul_expect_transitionSetMassSum_le_card
    initial
    (germ.playerNeutralOccupationKernel who)
    (germ.playerNeutralOccupationSource who)
    selection C.strictIndexSet C.potential C.bounded source_compatible
    (by
      intro index
      simpa only [normalizedDrift] using C.drift_nonneg index)
    (by
      intro index index_mem
      exact C.strictMargin_le_normalizedDrift index_mem)
    T

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
