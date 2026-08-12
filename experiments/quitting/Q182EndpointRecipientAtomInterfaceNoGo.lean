/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterfactualAtomExternalityRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCausalCollisionRecipientAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawExploitabilityFloor
import UniformEquilibrium.Quitting.Classification.PlayerReindex

/-!
# Q182: the endpoint-recipient atom interface does not source-match

Passport:

* Frontier seam attacked: Q182, from a positive endpoint debt recipient and
  its literal atom/rectangle to one legal source-matched gain.
* Existing theorem consumed: `hasQuittingEndpointDebtRecipientAtom_of_pos`
  and the exact-prefix counterfactual-atom regression.
* Stronger theorem delivered: the exact exported recipient-atom interface is
  inhabited while every recipient deviation from the source is nonprofitable,
  even with arbitrarily deep exact all-Continue prefix stacks.
* Named downstream consumer: Q182 must add global-minimum state return or an
  independently signed source edge; the recipient-atom decoder itself cannot
  be iterated into strategic closure.

The point is an interface separation, not a new dispatch.  In the concrete
two-player quitting game below, resetting `mover` transfers one unit of debt
to `observer`.  The current causal-collision consumer therefore produces
`HasQuittingEndpointDebtRecipientAtom` on that exact edge.  Nonetheless the
observer has no profitable unilateral deviation from the source.  Empty-prefix
source matching already fails, while replicated exact Nash roots show that
arbitrarily deep literal prefix access does not repair it.

This experiment does not satisfy positive global-minimum provenance: the
reward table has zero-debt profiles.  Consequently it rules out closure from
the exported local interface, but it does not rule out a theorem which uses
global minimality to return the reset endpoint to the same state-matched
chronology.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Why a globally minimal finite regression would settle the conjecture.**

If the total semantic debt has a positive global minimum on the attainable
carrier, every literal profile has full behavioral exploitability at least
`minimumDebt / card`.  Approximating the selected best-response supremum by
half that amount produces one fixed positive terminal exploitability gap.
Hence a concrete finite model satisfying this provenance cannot be a harmless
interface regression: it is already a counterexample to uniform-equilibrium
existence. -/
theorem no_uniformPayoff_of_positive_globalSemanticDebtMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
    reward).2
  let gap :=
    (quittingTerminalSemanticDebtSum minimum / (Fintype.card ι : ℝ)) / 2
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hgap : 0 < gap := by
    exact div_pos (div_pos hpositive hcard) (by norm_num)
  refine ⟨gap, hgap, ?_⟩
  intro profile
  let debt : ι → ℝ := fun who =>
    quittingTerminalDeviationDebt reward profile who
  have hlower :=
    minimumTerminalSemanticDebt_div_card_le_terminalExploitability
      reward minimum profile (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hminimum
  obtain ⟨who, _hwhoMem, hwho⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun player : ι => max 0 (debt player))
  have hexploit : quittingTerminalExploitability reward profile =
      max 0 (debt who) := by
    unfold quittingTerminalExploitability
    exact hwho
  have hdebtNonneg : 0 ≤ debt who := by
    exact quittingTerminalDeviationDebt_nonneg reward profile who
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  have hlarge : 2 * gap ≤ debt who := by
    rw [hexploit, max_eq_right hdebtNonneg] at hlower
    dsimp only [gap]
    linarith
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward profile who hgap
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  refine ⟨who, deviation, ?_⟩
  dsimp only [debt] at hlarge
  unfold quittingTerminalDeviationDebt at hlarge
  linarith

omit [Nonempty ι] in
/-- The all-Continue prefix is also the identity on the complete terminal-law
coordinate.  Thus the cap plateau fixes the entire joint semantic/law state,
not only its payoff/envelope projection. -/
theorem quittingTerminalOutcomeLawPrefix_allContinue_eq
    (mass : QuittingTerminalOutcome ι → ℝ) :
    quittingTerminalOutcomeLawPrefix
        (quittingAllContinueRoot : ι → PMF Bool) mass = mass := by
  funext outcome
  cases outcome with
  | none =>
      simp [quittingTerminalOutcomeLawPrefix,
        quittingStationaryContinueMass, quittingAllContinueRoot,
        quittingAllContinueAction, pmfPi_apply]
  | some terminal =>
      simp [quittingTerminalOutcomeLawPrefix,
        quittingStationaryContinueMass, quittingRootCoalitionMass,
        quittingRootQuitRates, quittingAllContinueRoot,
        quittingAllContinueAction, pmfPi_apply, coalitionMass,
        terminal.property.ne_empty]

omit [Nonempty ι] in
/-- **Joint semantic/law gauge at the strongest reset-face selector.**

Positive global minimum provenance, a co-realized zero-debt reset face, and
positive retained incidence yield a canonical point at which the only exact
cap--Nash transformation is all-Continue.  That transformation fixes both
the semantic pair and the complete terminal law.  Therefore repeated exact
cap prefixing cannot spend debt, change incidence, or generate a new source
edge at this selector. -/
theorem exists_resetFace_positiveIncidence_jointCapFixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : (target, mass) ∈
      quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner mass) :
    ∃ returned : QuittingTerminalSemanticLawPoint ι,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalTotalOpponentIncidenceMass owner returned.2 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned.1 ∧
      IsεQuittingRootNash reward returned.1.2 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot
        returned.1 = returned.1 ∧
      quittingTerminalOutcomeLawPrefix quittingAllContinueRoot returned.2 =
        returned.2 ∧
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.1.2 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool) := by
  obtain ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
      hsourceLe, hnash, hsemanticFixed, hallRoots⟩ :=
    exists_resetFace_positiveTotalIncidence_allContinueCapPlateau
      source target mass owner hM hreward hminimum hsourcePositive
        htarget hreset hincidence
  exact ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
    hsourceLe, hnash, hsemanticFixed,
    quittingTerminalOutcomeLawPrefix_allContinue_eq returned.2, hallRoots⟩

namespace CounterfactualAtomExternalityRegression

/-- The local two-player regression cannot be upgraded with a positive global
semantic-debt minimum.  This is not a failure of its atom calculations: such
an upgrade would contradict unconditional two-player uniform-equilibrium
existence. -/
theorem not_exists_positive_globalSemanticDebtMinimum :
    ¬∃ minimum : QuittingTerminalSemanticPair Player,
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum minimum := by
  rintro ⟨minimum, hminimum, hpositive⟩
  have hno := no_uniformPayoff_of_positive_globalSemanticDebtMinimum
    reward minimum hminimum hpositive
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two
      (by decide) reward)

/-- The counterfactual debt transfer satisfies the exact endpoint-recipient
atom interface exported by the causal collision pipeline. -/
theorem has_endpointDebtRecipientAtom :
    HasQuittingEndpointDebtRecipientAtom reward source mover observer
      replacement := by
  apply hasQuittingEndpointDebtRecipientAtom_of_pos reward source mover
    observer replacement (M := 1) (by norm_num) reward_bound
  change 0 < quittingTerminalDeviationDebt reward target observer -
    quittingTerminalDeviationDebt reward source observer
  rw [target_debt_observer, source_debt_observer]
  norm_num

/-- **Exact local interface no-go.**  A positive endpoint recipient together
with its prescribed/rectangle atom does not imply any profitable unilateral
deviation by that recipient from the source. -/
theorem endpointRecipientAtom_but_no_sourceMatchedObserverGain :
    HasQuittingEndpointDebtRecipientAtom reward source mover observer
        replacement ∧
      ¬∃ deviation : (quittingGame reward).BehaviorStrategy observer,
        0 < quittingTerminalPayoff reward
            (Function.update source observer deviation) observer -
          quittingTerminalPayoff reward source observer := by
  refine ⟨has_endpointDebtRecipientAtom, ?_⟩
  rintro ⟨deviation, hpositive⟩
  have hnonpositive := source_observer_deviation_payoff_le_zero deviation
  rw [source_payoff_observer] at hpositive
  linarith

/-- The same interface failure coexists with exact Nash-root stacks of every
finite depth, unit mover-deleted survival, and exact preservation of the
source semantic pair by the prefix.  Thus prefix length and literal access
are not the missing information. -/
theorem endpointRecipientAtom_exactPrefixes_but_no_sourceMatchedObserverGain
    (depth : ℕ) :
    HasQuittingEndpointDebtRecipientAtom reward source mover observer
        replacement ∧
      IsQuittingLiteralExactRootStack reward (roots depth) source ∧
      quittingLiteralRootStackOpponentSurvival (roots depth) mover = 1 ∧
      quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward (roots depth) source) =
        quittingTerminalSemanticPair reward source ∧
      ¬∃ deviation : (quittingGame reward).BehaviorStrategy observer,
        0 < quittingTerminalPayoff reward
            (Function.update
              (quittingLiteralRootStackProfile reward (roots depth) source)
              observer deviation) observer -
          quittingTerminalPayoff reward
            (quittingLiteralRootStackProfile reward (roots depth) source)
              observer := by
  refine ⟨has_endpointDebtRecipientAtom, roots_exactStack depth,
    moverDeletedSurvival_eq_one depth, prefixed_semanticPair_eq_source depth,
    ?_⟩
  rintro ⟨deviation, hpositive⟩
  have hpacket := exactPrefix_positiveAtom_but_no_observerGain depth
  have hnonpositive := hpacket.2.2.2.2.1 deviation
  exact (not_lt_of_ge hnonpositive) hpositive

end CounterfactualAtomExternalityRegression

end GameTheory
