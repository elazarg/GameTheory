/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTightness
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloSpineOccupation

/-!
# Quantitative terminal atoms on a semantic plateau

A limiting pure-time best-response law represents semantic debt as the sum of
its mass-weighted terminal gains.  Since the outcome space is finite, one atom
carries at least the uniform average of those signed contributions.  Reward
boundedness then separates this product bound into explicit mass and gain
floors.  These are finite, search-facing necessary conditions; they do not
time-disintegrate the selected atom or compile it into a prefix event.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A positive semantic debt forces one terminal atom to carry at least its
uniform share of the signed mass--gain moment. -/
theorem exists_terminalOutcome_mass_mul_gain_ge_debt_div_card
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who) :
    ∃ outcome : QuittingTerminalOutcome ι,
      quittingTerminalSemanticDebt pair who /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        mass outcome *
          (quittingTerminalOutcomeReward reward outcome who - pair.1 who) := by
  let contribution : QuittingTerminalOutcome ι → ℝ := fun outcome =>
    mass outcome *
      (quittingTerminalOutcomeReward reward outcome who - pair.1 who)
  have hsum : (∑ outcome, contribution outcome) =
      quittingTerminalSemanticDebt pair who := by
    dsimp only [contribution]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hmass.2, one_mul]
    unfold quittingTerminalRewardMoment at hmoment
    unfold quittingTerminalSemanticDebt
    linarith
  have hcardPos : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  by_contra hnone
  push Not at hnone
  have hsumLt : (∑ outcome, contribution outcome) <
      ∑ _outcome : QuittingTerminalOutcome ι,
        quittingTerminalSemanticDebt pair who /
          Fintype.card (QuittingTerminalOutcome ι) := by
    apply Finset.sum_lt_sum
    · intro outcome _houtcome
      exact (hnone outcome).le
    · exact ⟨none, Finset.mem_univ none, hnone none⟩
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumLt
  have haverage :
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          (quittingTerminalSemanticDebt pair who /
            Fintype.card (QuittingTerminalOutcome ι)) =
        quittingTerminalSemanticDebt pair who := by
    field_simp
  linarith

omit [DecidableEq ι] in
/-- Quantitative profitable-atom passport.  If rewards and the prescribed
coordinate lie in `[-M,M]`, one atom carries the average debt contribution,
has gain at least the same average, and has mass at least that average divided
by the maximal gain `2*M`. -/
theorem exists_terminalOutcome_quantitative_profitableAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprescribed : |pair.1 who| ≤ M)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who)
    (hdebt : 0 < quittingTerminalSemanticDebt pair who) :
    ∃ outcome : QuittingTerminalOutcome ι,
      quittingTerminalSemanticDebt pair who /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        mass outcome *
          (quittingTerminalOutcomeReward reward outcome who - pair.1 who) ∧
      quittingTerminalSemanticDebt pair who /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        quittingTerminalOutcomeReward reward outcome who - pair.1 who ∧
      quittingTerminalSemanticDebt pair who /
          (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤
        mass outcome := by
  obtain ⟨outcome, hproduct⟩ :=
    exists_terminalOutcome_mass_mul_gain_ge_debt_div_card
      reward pair who mass hmass hmoment
  let gain := quittingTerminalOutcomeReward reward outcome who - pair.1 who
  have hcardPos : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have haveragePos : 0 < quittingTerminalSemanticDebt pair who /
      Fintype.card (QuittingTerminalOutcome ι) := div_pos hdebt hcardPos
  have hmassNonneg : 0 ≤ mass outcome := hmass.1 outcome
  have hproductPos : 0 < mass outcome * gain :=
    haveragePos.trans_le hproduct
  have hmassPos : 0 < mass outcome := by
    by_contra hnot
    have hzero : mass outcome = 0 :=
      le_antisymm (le_of_not_gt hnot) hmassNonneg
    simp [hzero] at hproductPos
  have hgainPos : 0 < gain := by nlinarith
  have hmassLeOne : mass outcome ≤ 1 := by
    calc
      mass outcome ≤ ∑ candidate, mass candidate := by
        exact Finset.single_le_sum (fun candidate _ => hmass.1 candidate)
          (Finset.mem_univ outcome)
      _ = 1 := hmass.2
  have houtcomeBound :
      |quittingTerminalOutcomeReward reward outcome who| ≤ M := by
    cases outcome with
    | none => simpa [quittingTerminalOutcomeReward] using hM.le
    | some terminal =>
        simpa [quittingTerminalOutcomeReward] using hreward terminal who
  have hgainUpper : gain ≤ 2 * M := by
    have houtcomeUpper := (abs_le.mp houtcomeBound).2
    have hprescribedLower := (abs_le.mp hprescribed).1
    dsimp only [gain]
    linarith
  have hgainFloor : quittingTerminalSemanticDebt pair who /
      Fintype.card (QuittingTerminalOutcome ι) ≤ gain := by
    nlinarith
  have hmassFloor : quittingTerminalSemanticDebt pair who /
      (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤ mass outcome := by
    have hdenomPos : 0 <
        2 * M * (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
      positivity
    apply (div_le_iff₀ hdenomPos).2
    have hscaled := (div_le_iff₀ hcardPos).1 hproduct
    nlinarith
  exact ⟨outcome, hproduct, hgainFloor, hmassFloor⟩

/-- Carrier membership supplies the prescribed-coordinate bound required by
the quantitative profitable-atom passport. -/
theorem exists_terminalOutcome_quantitative_profitableAtom_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who)
    (hdebt : 0 < quittingTerminalSemanticDebt pair who) :
    ∃ outcome : QuittingTerminalOutcome ι,
      quittingTerminalSemanticDebt pair who /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        mass outcome *
          (quittingTerminalOutcomeReward reward outcome who - pair.1 who) ∧
      quittingTerminalSemanticDebt pair who /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        quittingTerminalOutcomeReward reward outcome who - pair.1 who ∧
      quittingTerminalSemanticDebt pair who /
          (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤
        mass outcome := by
  have hbox := quittingTerminalSemanticCarrier_mem_box
    (reward := reward) pair hM.le hreward hpair
  exact exists_terminalOutcome_quantitative_profitableAtom
    reward pair who mass hM hreward
      (abs_le.mpr ⟨hbox.1.1 who, hbox.1.2 who⟩)
      hmass hmoment hdebt

/-- On an all-Continue semantic plateau, the quantitative atom is never the
debtor's own singleton.  It is quantitatively profitable and belongs to the
same Never / collision / opponent-before-stop trichotomy as the qualitative
tightness theorem. -/
theorem exists_terminalOutcome_quantitative_trichotomy_of_allContinuePlateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who)
    (hdebt : 0 < quittingTerminalSemanticDebt pair who) :
    ∃ outcome : QuittingTerminalOutcome ι,
      quittingTerminalSemanticDebt pair who /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        mass outcome *
          (quittingTerminalOutcomeReward reward outcome who - pair.1 who) ∧
      quittingTerminalSemanticDebt pair who /
          Fintype.card (QuittingTerminalOutcome ι) ≤
        quittingTerminalOutcomeReward reward outcome who - pair.1 who ∧
      quittingTerminalSemanticDebt pair who /
          (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤
        mass outcome ∧
      ((outcome = none ∧ pair.1 who < 0) ∨
        (∃ terminal : {S : Finset ι // S.Nonempty},
          outcome = some terminal ∧ who ∈ terminal.val ∧
            terminal.val ≠ {who} ∧ pair.1 who < reward terminal who) ∨
        (∃ terminal : {S : Finset ι // S.Nonempty},
          outcome = some terminal ∧ who ∉ terminal.val ∧
            pair.1 who < reward terminal who)) := by
  obtain ⟨outcome, hproduct, hgain, hmassFloor⟩ :=
    exists_terminalOutcome_quantitative_profitableAtom_of_mem_carrier
      reward pair hpair who mass hM hreward hmass hmoment hdebt
  have hcardPos : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hgainPositive : pair.1 who <
      quittingTerminalOutcomeReward reward outcome who := by
    have haveragePositive : 0 < quittingTerminalSemanticDebt pair who /
        Fintype.card (QuittingTerminalOutcome ι) := div_pos hdebt hcardPos
    linarith
  refine ⟨outcome, hproduct, hgain, hmassFloor, ?_⟩
  cases outcome with
  | none =>
      left
      exact ⟨rfl, by
        simpa [quittingTerminalOutcomeReward] using hgainPositive⟩
  | some terminal =>
      by_cases hmem : who ∈ terminal.val
      · right
        left
        refine ⟨terminal, rfl, hmem, ?_, by
          simpa [quittingTerminalOutcomeReward] using hgainPositive⟩
        intro heq
        have hterminal : terminal = quittingSingletonTerminal who :=
          Subtype.ext heq
        have hsingleton :=
          (isZeroQuittingRootNash_allContinue_iff_singleton_le
            reward pair.1).mp hnash who
        apply (not_lt_of_ge hsingleton)
        simpa [hterminal, quittingTerminalOutcomeReward] using hgainPositive
      · right
        right
        exact ⟨terminal, rfl, hmem, by
          simpa [quittingTerminalOutcomeReward] using hgainPositive⟩

end GameTheory
