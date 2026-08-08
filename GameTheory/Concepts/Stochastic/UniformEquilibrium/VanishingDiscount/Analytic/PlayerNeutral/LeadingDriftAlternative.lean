/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.PotentialJet
import Math.Probability.AdaptiveOccupationFlow

/-!
# Strict endpoint drift from a player-neutral potential jet

The leading coefficient of a gauge-fixed player-neutral potential jet pairs
nonnegatively with every endpoint operational column. Since the index family
is finite, either every pairing vanishes or one fixed column has strictly
positive pairing.

In the strict branch, an affine normalization makes the leading coefficient
`[0,1]`-valued. Constant shifts cancel from transition drift and positive
rescaling preserves all signs, so the selected column retains a positive
margin. The resulting certificate supports standard adaptive use and mixed
mass budgets. It does not construct a punishment or show that the selected
column is reached.
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

local instance playerNeutralOccupationIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

/-- A fixed player-neutral endpoint column with strictly positive drift
under a bounded normalization of the leading gauge-fixed coefficient. -/
structure PlayerNeutralStrictLeadingDrift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor) where
  index : germ.PlayerNeutralOccupationIndex who
  potential : G.State → ℝ
  pairingScale : ℝ
  margin : ℝ
  pairingScale_pos : 0 < pairingScale
  margin_pos : 0 < margin
  bounded : ∀ state, 0 ≤ potential state ∧ potential state ≤ 1
  drift_nonneg :
    ∀ candidate,
      0 ≤
        expect (germ.playerNeutralOccupationKernel who candidate)
            potential -
          potential
            (germ.playerNeutralOccupationSource who candidate)
  selected_drift :
    expect (germ.playerNeutralOccupationKernel who index) potential -
        potential (germ.playerNeutralOccupationSource who index) =
      margin
  drift_eq_pairing_div :
    ∀ candidate,
      expect (germ.playerNeutralOccupationKernel who candidate) potential -
          potential
            (germ.playerNeutralOccupationSource who candidate) =
        (∑ state,
          jet.factor 0 state *
            actualOccupationColumn
              (germ.playerNeutralOccupationKernel who)
              (germ.playerNeutralOccupationSource who)
              candidate state) /
          pairingScale

/-- The endpoint leading pairings are all zero, or one fixed
player-neutral column has a bounded normalized potential with a strict
positive drift margin. -/
theorem
    playerNeutralLeadingPairings_zero_or_strictDrift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    (∀ index,
      (∑ state,
        jet.factor 0 state *
          actualOccupationColumn
            (germ.playerNeutralOccupationKernel who)
            (germ.playerNeutralOccupationSource who)
            index state) = 0) ∨
    Nonempty
      (germ.PlayerNeutralStrictLeadingDrift B who jet) := by
  classical
  let pairing :
      germ.PlayerNeutralOccupationIndex who → ℝ :=
    fun index =>
      ∑ state,
        jet.factor 0 state *
          actualOccupationColumn
            (germ.playerNeutralOccupationKernel who)
            (germ.playerNeutralOccupationSource who)
            index state
  have pairing_nonneg :
      ∀ index, 0 ≤ pairing index := by
    intro index
    exact germ.playerNeutralGaugeFixedPotentialJet_pair_nonneg
      B who jet circulation index
  by_cases all_zero : ∀ index, pairing index = 0
  · exact Or.inl all_zero
  · right
    push Not at all_zero
    obtain ⟨selected, selected_ne⟩ := all_zero
    have selected_pos : 0 < pairing selected :=
      lt_of_le_of_ne (pairing_nonneg selected) (Ne.symm selected_ne)
    let raw : G.State → ℝ := jet.factor 0
    let bound : ℝ := ∑ state, |raw state| + 1
    have bound_pos : 0 < bound := by
      dsimp only [bound]
      positivity
    let scale : ℝ := 2 * bound
    have scale_pos : 0 < scale :=
      mul_pos (by norm_num) bound_pos
    let potential : G.State → ℝ :=
      fun state => raw state / scale + 1 / 2
    have potential_bounded :
        ∀ state, 0 ≤ potential state ∧ potential state ≤ 1 := by
      intro state
      have abs_le_sum :
          |raw state| ≤ ∑ other, |raw other| :=
        Finset.single_le_sum
          (fun other _ => abs_nonneg (raw other))
          (Finset.mem_univ state)
      have lower : -bound ≤ raw state := by
        dsimp only [bound]
        linarith [neg_abs_le (raw state)]
      have upper : raw state ≤ bound := by
        dsimp only [bound]
        linarith [le_abs_self (raw state)]
      have divided_lower :
          -(1 / 2 : ℝ) ≤ raw state / scale := by
        apply (le_div_iff₀ scale_pos).2
        dsimp only [scale]
        linarith
      have divided_upper :
          raw state / scale ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ scale_pos).2
        dsimp only [scale]
        linarith
      dsimp only [potential]
      constructor <;> linarith
    have normalized_drift :
        ∀ index,
          expect (germ.playerNeutralOccupationKernel who index)
                potential -
              potential
                (germ.playerNeutralOccupationSource who index) =
            pairing index / scale := by
      intro index
      have raw_drift :
          expect (germ.playerNeutralOccupationKernel who index) raw -
              raw (germ.playerNeutralOccupationSource who index) =
            pairing index := by
        rw [← potential_pair_actualOccupationColumn]
      rw [show potential =
          fun state => (1 / scale) * raw state + 1 / 2 by
        funext state
        dsimp only [potential]
        ring]
      rw [expect_add, expect_const_mul, expect_const]
      rw [show
        (fun state => 1 / scale * raw state + 1 / 2)
            (germ.playerNeutralOccupationSource who index) =
          1 / scale *
              raw (germ.playerNeutralOccupationSource who index) +
            1 / 2 by rfl]
      rw [← raw_drift]
      ring
    let margin : ℝ := pairing selected / scale
    have margin_pos : 0 < margin :=
      div_pos selected_pos scale_pos
    refine ⟨{
      index := selected
      potential := potential
      pairingScale := scale
      margin := margin
      pairingScale_pos := scale_pos
      margin_pos := margin_pos
      bounded := potential_bounded
      drift_nonneg := ?_
      selected_drift := ?_
      drift_eq_pairing_div := ?_
    }⟩
    · intro index
      rw [normalized_drift index]
      exact div_nonneg (pairing_nonneg index) scale_pos.le
    · rw [normalized_drift selected]
    · intro index
      exact normalized_drift index

namespace PlayerNeutralStrictLeadingDrift

/-- Pure history-dependent switching among source-compatible
player-neutral kernels pays the strict endpoint margin for every use of the
selected column. -/
theorem selectedUseBudget
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}
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
    C.margin *
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison
                (germ.playerNeutralOccupationKernel who) choice))
            (T + 1))
          (selectedTransitionUseCount choice C.index T) ≤
      1 := by
  classical
  exact margin_mul_expect_selectedTransitionUseCount_le_one
    initial
    (germ.playerNeutralOccupationKernel who)
    (germ.playerNeutralOccupationSource who)
    choice C.index C.potential C.bounded source_compatible
    C.drift_nonneg C.selected_drift.ge T

/-- Behavioral switching among source-compatible player-neutral kernels
pays the strict endpoint margin for cumulative conditional probability mass
placed on the selected column. -/
theorem selectedMassBudget
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}
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
    C.margin *
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison
                (germ.playerNeutralOccupationKernel who) selection))
            (T + 1))
          (selectedTransitionMassSum selection C.index T) ≤
      1 := by
  classical
  exact margin_mul_expect_selectedTransitionMassSum_le_one
    initial
    (germ.playerNeutralOccupationKernel who)
    (germ.playerNeutralOccupationSource who)
    selection C.index C.potential C.bounded source_compatible
    C.drift_nonneg C.selected_drift.ge T

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
