/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashDebtSupport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashRenewalObstruction
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllContinuePlateau

/-!
# Debt-homotopy selection at the minimum semantic stratum

For a semantic pair with cap `B`, prescribed payoff `U`, and debt
`d = B - U`, consider exact one-stage Nash roots against

`B - t d`, for `0 <= t <= 1`.

The auxiliary-Nash budget gives a quantitative selection moat: absorption at
parameter `t` is charged at scale `(1 - t) D`, where `D` is total debt.  At an
attained positive minimum, every root on the open homotopy is therefore
all-Continue.  The only possible first support entry is at `t = 1`, where the
minimum debt-simplex theorem restricts it to a unique solo debt gate.  In a
counterexample that gate supplies either a strict joining label or a positive
punishment moat.

The final section records a sharp limitation.  The honest period-one
local/global profile admits the constant all-Continue exact-Nash selection on
the entire closed homotopy, while its debt remains at least one above a zero
global infimum.  Thus continuity and finite mixed-Nash existence alone do not
select descent or conditioned cancellation.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Quantitative homotopy moat above an attained minimum -/

/-- Along the debt homotopy, every unit of absorption is charged at least
`(1 - t) * D`, where `D` is the current total semantic debt. -/
theorem terminalSemantic_debtHomotopy_absorption_budget
    (base pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (t : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun who => t * quittingTerminalSemanticDebt pair who)
      0 root) :
    (1 - t) * quittingTerminalSemanticDebtSum pair *
        quittingRootAbsorptionMass root ≤
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum base := by
  let debt : Payoff ι := fun who => quittingTerminalSemanticDebt pair who
  let shift : Payoff ι := fun who => t * debt who
  have hdebtNonneg : ∀ who, 0 ≤ debt who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have htotalNonneg : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ => hdebtNonneg who
  have hdebtLe : ∀ who,
      debt who ≤ quittingTerminalSemanticDebtSum pair := by
    intro who
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  have hshiftNonneg : ∀ who, 0 ≤ shift who := fun who =>
    mul_nonneg ht0 (hdebtNonneg who)
  have hbudget := terminalSemantic_auxiliaryNash_excess_budget
    (reward := reward) base pair shift root hM hreward hminimum hpair
      hshiftNonneg (by simpa [shift, debt] using hnash)
  have hscaleNonneg : 0 ≤ (1 - t) *
      quittingTerminalSemanticDebtSum pair :=
    mul_nonneg (sub_nonneg.mpr ht1) htotalNonneg
  have hcollision :
      (1 - t) * quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root ≤
        quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root := by
    apply mul_le_mul_of_nonneg_right _
      (quittingRootCollisionMass_nonneg root)
    nlinarith
  have hsingleton :
      ∑ who, quittingRootCoalitionMass root {who} *
          ((1 - t) * quittingTerminalSemanticDebtSum pair) ≤
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - shift who) := by
    apply Finset.sum_le_sum
    intro who _
    apply mul_le_mul_of_nonneg_left _
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
    dsimp [shift, debt]
    nlinarith [mul_nonneg ht0
      (sub_nonneg.mpr (hdebtLe who))]
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  calc
    (1 - t) * quittingTerminalSemanticDebtSum pair *
          quittingRootAbsorptionMass root =
        (1 - t) * quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
          ∑ who, quittingRootCoalitionMass root {who} *
            ((1 - t) * quittingTerminalSemanticDebtSum pair) := by
      rw [habsorption, mul_add, Finset.mul_sum]
      ring_nf
    _ ≤ quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - shift who) :=
      add_le_add hcollision hsingleton
    _ ≤ quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base := hbudget

/-- Before the endpoint, a non-all-Continue exact root certifies strict debt
excess above the attained minimum.  The theorem is deliberately qualitative:
a first support entry may have arbitrarily small absorption mass. -/
theorem terminalSemantic_debtHomotopy_nontrivial_forces_strict_excess
    (base pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (t : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun who => t * quittingTerminalSemanticDebt pair who)
      0 root)
    (hroot : root ≠ (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingTerminalSemanticDebtSum base <
      quittingTerminalSemanticDebtSum pair := by
  have hbudget := terminalSemantic_debtHomotopy_absorption_budget
    (reward := reward) base pair root t hM hreward hminimum hpair ht0 ht1.le
      hnash
  have habsorptionNonneg := quittingRootAbsorptionMass_nonneg root
  have habsorptionPos : 0 < quittingRootAbsorptionMass root := by
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
  have hleft : 0 < (1 - t) *
      quittingTerminalSemanticDebtSum pair *
        quittingRootAbsorptionMass root :=
    mul_pos (mul_pos (sub_pos.mpr ht1) hpositive) habsorptionPos
  linarith

/-! ## Endpoint selection at a counterexample minimum -/

/-- A nontrivial endpoint of the debt homotopy is a unique solo debt gate.
In a counterexample, that gate immediately has either a strict outsider
joiner or a positive punishment moat. -/
theorem QuittingCounterexampleRegime.minimumDebtHomotopy_endpoint_selection
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun who => quittingTerminalSemanticDebt pair who)
      0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) ∨
      ∃ owner,
        IsMinimumTerminalSemanticDebtGate reward pair owner ∧
        0 < (root owner true).toReal ∧
        (∀ other, other ≠ owner → root other = PMF.pure false) ∧
        ((∃ other, other ≠ owner ∧
            quittingSoloReward reward owner other <
              quittingSingletonCollisionReward reward owner other) ∨
          quittingSoloReward reward owner owner <
            quittingPunishmentValue reward owner) := by
  have htail : pair.2 -
      (fun who => quittingTerminalSemanticDebt pair who) = pair.1 := by
    funext who
    change pair.2 who - quittingTerminalSemanticDebt pair who = pair.1 who
    unfold quittingTerminalSemanticDebt
    ring
  have hnashPrescribed : IsεQuittingRootNash reward pair.1 0 root := by
    rw [← htail]
    exact hnash
  rcases minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo
      (reward := reward) pair root hM hreward hpair hminimum hpositive
        hnashPrescribed with hcontinue | ⟨owner, hgate, hquit, hsolo⟩
  · exact Or.inl hcontinue
  · exact Or.inr ⟨owner, hgate, hquit, hsolo,
      regime.strictJoiner_or_soloReward_lt_punishmentValue owner⟩

/-! ## Honest closed-homotopy stalling regression -/

/-- Every terminal atom of the local/global table is nonpositive. -/
theorem localGlobalCounterexample_terminalOutcomeReward_le_zero
    (outcome : QuittingTerminalOutcome Bool) (who : Bool) :
    quittingTerminalOutcomeReward localGlobalCounterexampleReward outcome who ≤
      0 := by
  rcases outcome with _ | terminal
  · simp [quittingTerminalOutcomeReward]
  · cases who with
    | false =>
        by_cases hmem : false ∈ terminal.1 <;>
          simp [quittingTerminalOutcomeReward,
            localGlobalCounterexampleReward, hmem]
    | true =>
        simp [quittingTerminalOutcomeReward,
          localGlobalCounterexampleReward]

/-- The unilateral best-response cap of the honest period-one profile is the
zero vector. -/
theorem quittingContinuationBestResponseValue_localGlobalCounterexample_eq_zero
    (who : Bool) :
    quittingContinuationBestResponseValue localGlobalCounterexampleReward
        localGlobalCounterexampleProfile who = 0 := by
  apply le_antisymm
  · exact quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
      localGlobalCounterexampleProfile who 0
        (fun outcome =>
          localGlobalCounterexample_terminalOutcomeReward_le_zero outcome who)
  · have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        localGlobalCounterexampleReward localGlobalCounterexampleProfile who
        (quittingAlwaysContinueStrategy localGlobalCounterexampleReward who)
        (M := 1) (by norm_num) abs_localGlobalCounterexampleReward_le_one
    cases who with
    | false =>
        rw [update_localGlobalCounterexampleProfile_false_continue,
          quittingTerminalPayoff_quittingAlwaysContinue] at hdeviation
        exact hdeviation
    | true =>
        have hzero : quittingTerminalPayoff localGlobalCounterexampleReward
            (Function.update localGlobalCounterexampleProfile true
              (quittingAlwaysContinueStrategy
                localGlobalCounterexampleReward true)) true = 0 := by
          simp [quittingTerminalPayoff, localGlobalCounterexampleReward]
        rw [hzero] at hdeviation
        exact hdeviation

/-- The semantic pair of the honest period-one regression is exactly
`((-1,0),(0,0))`. -/
theorem quittingTerminalSemanticPair_localGlobalCounterexample_eq :
    quittingTerminalSemanticPair localGlobalCounterexampleReward
        localGlobalCounterexampleProfile =
      (localGlobalCounterexampleContinuation, fun _ => 0) := by
  apply Prod.ext
  · exact quittingTerminalPayoff_localGlobalCounterexampleProfile_eq
  · funext who
    exact quittingContinuationBestResponseValue_localGlobalCounterexample_eq_zero
      who

/-- The all-Continue root is exact Nash at every point of the closed debt
homotopy of the honest period-one regression. -/
theorem isZeroQuittingRootNash_allContinue_localGlobal_debtHomotopy
    (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsεQuittingRootNash localGlobalCounterexampleReward
      ((quittingTerminalSemanticPair localGlobalCounterexampleReward
          localGlobalCounterexampleProfile).2 -
        fun who => t * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair localGlobalCounterexampleReward
            localGlobalCounterexampleProfile) who)
      0 (quittingAllContinueRoot : Bool → PMF Bool) := by
  apply (isZeroQuittingRootNash_allContinue_iff_singleton_le
    localGlobalCounterexampleReward _).2
  intro who
  rw [quittingTerminalSemanticPair_localGlobalCounterexample_eq]
  cases who with
  | false =>
      simp [quittingTerminalSemanticDebt,
        localGlobalCounterexampleContinuation]
      linarith
  | true =>
      simp [quittingTerminalSemanticDebt,
        localGlobalCounterexampleContinuation]

/-- **Closed-homotopy stalling regression.**  An honest period-one renewal
profile has debt at least one above a zero infimum, yet the constant
all-Continue selection is exact Nash on the full cap-to-prescribed homotopy
and its semantic prefix action is the identity. -/
theorem localGlobal_periodOne_debtHomotopy_stalls :
    quittingTerminalDebtSumInf localGlobalCounterexampleReward = 0 ∧
    1 ≤ quittingTerminalDebtSum localGlobalCounterexampleReward
      localGlobalCounterexampleProfile ∧
    quittingCyclicBehaviorProfile localGlobalCounterexampleReward
        (quittingTailWindowCycle localGlobalRenewalRoots 0 0) 0 =
      localGlobalCounterexampleProfile ∧
    (∀ t, 0 ≤ t → t ≤ 1 →
      IsεQuittingRootNash localGlobalCounterexampleReward
        ((quittingTerminalSemanticPair localGlobalCounterexampleReward
            localGlobalCounterexampleProfile).2 -
          fun who => t * quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair localGlobalCounterexampleReward
              localGlobalCounterexampleProfile) who)
        0 (quittingAllContinueRoot : Bool → PMF Bool)) ∧
    quittingTerminalSemanticPrefix localGlobalCounterexampleReward
        quittingAllContinueRoot
        (quittingTerminalSemanticPair localGlobalCounterexampleReward
          localGlobalCounterexampleProfile) =
      quittingTerminalSemanticPair localGlobalCounterexampleReward
        localGlobalCounterexampleProfile := by
  refine ⟨quittingTerminalDebtSumInf_localGlobalCounterexample_eq_zero,
    one_le_terminalDebtSum_localGlobalCounterexample,
    cyclicBehaviorProfile_tailWindow_localGlobal_eq, ?_, ?_⟩
  · exact fun t ht0 ht1 =>
      isZeroQuittingRootNash_allContinue_localGlobal_debtHomotopy t ht0 ht1
  · have hsemantic := semanticPair_allContinue_capNashPrefix_localGlobal
    rw [quittingTerminalSemanticPair_rootThenContinuation
      localGlobalCounterexampleReward quittingAllContinueRoot
        localGlobalCounterexampleProfile (M := 1) (by norm_num)
        abs_localGlobalCounterexampleReward_le_one] at hsemantic
    exact hsemantic

end GameTheory
