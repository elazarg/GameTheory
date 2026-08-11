/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget

/-!
# Debt-simplex geometry of a minimum terminal-semantic plateau

At a positive minimum of total best-response debt, normalize the coordinate
debts by their sum.  They form a probability simplex.  The singleton margin
has an exact complementary-debt plus nonnegative-slack decomposition.  Thus a
player can be singleton-tight only at its debt vertex and at zero matching
slack.

The auxiliary Nash moat is rigid along the open segment from the envelope to
the prescribed payoff.  At the prescribed endpoint, every exact Nash root is
either all-Continue or a solo root through one of the vertex/zero-slack gates.
The solo conclusion below is read from the product law; it is not asserted
from collision-freeness alone.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The share of total best-response debt carried by one player. -/
def quittingTerminalSemanticDebtShare
    (pair : QuittingTerminalSemanticPair ι) (who : ι) : ℝ :=
  quittingTerminalSemanticDebt pair who /
    quittingTerminalSemanticDebtSum pair

/-- Excess of the envelope/singleton margin over total minimum debt. -/
def quittingTerminalSemanticSingletonSlack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι) : ℝ :=
  pair.2 who - reward (quittingSingletonTerminal who) who -
    quittingTerminalSemanticDebtSum pair

/-- Singleton slack normalized by positive total debt. -/
def quittingTerminalSemanticNormalizedSingletonSlack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι) : ℝ :=
  quittingTerminalSemanticSingletonSlack reward pair who /
    quittingTerminalSemanticDebtSum pair

/-- The unique possible nontrivial exact-root gate: one player carries all
debt and its singleton slack vanishes. -/
def IsMinimumTerminalSemanticDebtGate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι) : Prop :=
  quittingTerminalSemanticDebt pair who =
      quittingTerminalSemanticDebtSum pair ∧
    quittingTerminalSemanticSingletonSlack reward pair who = 0

omit [DecidableEq ι] in
/-- The debt shares of a positive semantic pair sum to one. -/
theorem sum_quittingTerminalSemanticDebtShare_eq_one
    (pair : QuittingTerminalSemanticPair ι)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    ∑ who, quittingTerminalSemanticDebtShare pair who = 1 := by
  unfold quittingTerminalSemanticDebtShare
  rw [← Finset.sum_div, show (∑ who, quittingTerminalSemanticDebt pair who) =
      quittingTerminalSemanticDebtSum pair by rfl]
  exact div_self (ne_of_gt hpositive)

/-- Every debt share is nonnegative at a semantic carrier point. -/
theorem quittingTerminalSemanticDebtShare_nonneg_of_mem_carrier
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) (who : ι) :
    0 ≤ quittingTerminalSemanticDebtShare pair who := by
  exact div_nonneg
    (quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair who) hpositive.le

/-- The singleton slack is nonnegative at every positive minimum pair. -/
theorem minimumTerminalSemantic_singletonSlack_nonneg
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) (who : ι) :
    0 ≤ quittingTerminalSemanticSingletonSlack reward pair who := by
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) pair hM hreward hpair hminimum hpositive who
  unfold quittingTerminalSemanticSingletonSlack
  linarith

omit [DecidableEq ι] in
/-- Exact complementary-debt plus slack accounting for the prescribed
singleton gap. -/
theorem minimumTerminalSemantic_singletonGap_eq_complementaryDebt_add_slack
    (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    pair.1 who - reward (quittingSingletonTerminal who) who =
      (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who) +
        quittingTerminalSemanticSingletonSlack reward pair who := by
  unfold quittingTerminalSemanticDebt
    quittingTerminalSemanticSingletonSlack
  ring

omit [DecidableEq ι] in
/-- Normalized debt-simplex form of the singleton gap. -/
theorem minimumTerminalSemantic_normalizedSingletonGap
    (pair : QuittingTerminalSemanticPair ι)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) (who : ι) :
    (pair.1 who - reward (quittingSingletonTerminal who) who) /
        quittingTerminalSemanticDebtSum pair =
      1 - quittingTerminalSemanticDebtShare pair who +
        quittingTerminalSemanticNormalizedSingletonSlack reward pair who := by
  have hne : quittingTerminalSemanticDebtSum pair ≠ 0 := ne_of_gt hpositive
  unfold quittingTerminalSemanticDebtShare
    quittingTerminalSemanticNormalizedSingletonSlack
  rw [minimumTerminalSemantic_singletonGap_eq_complementaryDebt_add_slack]
  field_simp

/-- Singleton tightness is exactly the debt-vertex/zero-slack gate. -/
theorem minimumTerminalSemantic_singletonTight_iff_debtGate
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) (who : ι) :
    pair.1 who = reward (quittingSingletonTerminal who) who ↔
      IsMinimumTerminalSemanticDebtGate reward pair who := by
  have hdebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt pair player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hdebtLe : quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  have hslack := minimumTerminalSemantic_singletonSlack_nonneg
    (reward := reward) pair hM hreward hpair hminimum hpositive who
  have hidentity :=
    minimumTerminalSemantic_singletonGap_eq_complementaryDebt_add_slack
      (reward := reward) pair who
  constructor
  · intro htight
    unfold IsMinimumTerminalSemanticDebtGate
    constructor <;> linarith
  · rintro ⟨hdebt, hslackZero⟩
    linarith

/-- A positive semantic pair has at most one debt gate. -/
theorem minimumTerminalSemantic_debtGate_unique
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    {first second : ι}
    (hfirst : IsMinimumTerminalSemanticDebtGate reward pair first)
    (hsecond : IsMinimumTerminalSemanticDebtGate reward pair second) :
    first = second := by
  by_contra hne
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hsumLe :
      ∑ who ∈ ({first, second} : Finset ι),
          quittingTerminalSemanticDebt pair who ≤
        ∑ who, quittingTerminalSemanticDebt pair who :=
    Finset.sum_le_univ_sum_of_nonneg hdebtNonneg
  have hsumPair :
      ∑ who ∈ ({first, second} : Finset ι),
          quittingTerminalSemanticDebt pair who =
        quittingTerminalSemanticDebt pair first +
          quittingTerminalSemanticDebt pair second := by
    simp [hne]
  rw [hsumPair, show (∑ who, quittingTerminalSemanticDebt pair who) =
      quittingTerminalSemanticDebtSum pair by rfl,
    hfirst.1, hsecond.1] at hsumLe
  linarith

/-- Along the open envelope-to-prescribed homotopy, the exact Nash root is
uniquely all-Continue. -/
theorem minimumTerminalSemantic_debtHomotopy_eq_allContinue
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M t : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun who => t * quittingTerminalSemanticDebt pair who)
      0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  let shift : Payoff ι :=
    fun who => t * quittingTerminalSemanticDebt pair who
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hdebtLe : ∀ who, quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebtSum pair := by
    intro who
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  apply minimumTerminalSemantic_auxiliaryNash_eq_allContinue
    (reward := reward) pair shift root hM hreward hpair hminimum hpositive
  · intro who
    exact mul_nonneg ht0 (hdebtNonneg who)
  · intro who
    dsimp [shift]
    nlinarith [hdebtLe who]
  · simpa [shift] using hnash

/-- Positive singleton mass at an exact root exposes a genuine debt gate. -/
theorem minimumTerminalSemantic_debtGate_of_singletonMass_pos
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (who : ι) (hmass : 0 < quittingRootCoalitionMass root {who}) :
    IsMinimumTerminalSemanticDebtGate reward pair who := by
  have hcritical := minimumTerminalSemantic_exactNash_criticalFace
    (reward := reward) pair root hM hreward hpair hminimum hpositive hnash
  have hdebt : quittingTerminalSemanticDebt pair who =
      quittingTerminalSemanticDebtSum pair := hcritical.2 who hmass
  have hquit : 0 < (root who true).toReal :=
    QuittingFiniteRootWindow.quitProbability_pos_of_singletonCoalitionMass_pos
      root who hmass
  have hsingleton :=
    quittingTerminalSemantic_minimum_positiveDebt_singleton_eq_of_quit_pos
      reward pair root hM hreward hpair hminimum hnash who
        (hdebt.symm ▸ hpositive) hquit
  refine ⟨hdebt, ?_⟩
  unfold quittingTerminalSemanticSingletonSlack
  unfold quittingTerminalSemanticDebt at hdebt
  linarith

/-- Exact roots at the prescribed minimum plateau are all-Continue or are
solo at one debt-vertex/zero-slack gate. -/
theorem minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) ∨
      ∃ owner,
        IsMinimumTerminalSemanticDebtGate reward pair owner ∧
        0 < (root owner true).toReal ∧
        ∀ other, other ≠ owner → root other = PMF.pure false := by
  by_cases hroot : root = (quittingAllContinueRoot : ι → PMF Bool)
  · exact Or.inl hroot
  · have hcritical := minimumTerminalSemantic_exactNash_criticalFace
      (reward := reward) pair root hM hreward hpair hminimum hpositive hnash
    have habsorptionPos : 0 < quittingRootAbsorptionMass root := by
      have habsorptionNonneg := quittingRootAbsorptionMass_nonneg root
      apply lt_of_le_of_ne habsorptionNonneg
      intro habsorptionZero
      have hcontinue : quittingStationaryContinueMass root = 1 := by
        unfold quittingRootAbsorptionMass at habsorptionZero
        linarith
      apply hroot
      funext who
      have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
        hcontinue who
      simpa [quittingAllContinueRoot] using hpure
    have hsingletonSum : 0 <
        ∑ who, quittingRootCoalitionMass root {who} := by
      have habsorption :=
        QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
          root
      rw [hcritical.1, add_zero] at habsorption
      linarith
    obtain ⟨owner, _, hownerMass⟩ :=
      (Finset.sum_pos_iff_of_nonneg fun who _ =>
        MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
          root {who}).mp hsingletonSum
    have hgate := minimumTerminalSemantic_debtGate_of_singletonMass_pos
      (reward := reward) pair root hM hreward hpair hminimum hpositive
        hnash owner hownerMass
    have hquit : 0 < (root owner true).toReal :=
      QuittingFiniteRootWindow.quitProbability_pos_of_singletonCoalitionMass_pos
        root owner hownerMass
    refine Or.inr ⟨owner, hgate, hquit, ?_⟩
    intro other hne
    exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero
      (root other)
      (quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
        reward pair root hM hreward hpair hminimum hnash
          (hgate.1.symm ▸ hpositive) hne)

/-- Away from every vertex/zero-slack gate, exact minimum dynamics is frozen
at the all-Continue identity root. -/
theorem minimumTerminalSemantic_exactNash_eq_allContinue_of_no_debtGate
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hnoGate : ∀ who, ¬ IsMinimumTerminalSemanticDebtGate reward pair who) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  rcases minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo
      (reward := reward) pair root hM hreward hpair hminimum hpositive hnash with
    hroot | ⟨owner, hgate, _⟩
  · exact hroot
  · exact (hnoGate owner hgate).elim

end GameTheory
