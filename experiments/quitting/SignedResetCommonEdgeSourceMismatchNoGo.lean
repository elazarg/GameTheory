/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.Q182EndpointRecipientAtomInterfaceNoGo

/-!
# The signed reset edge is not source-matched

The local data common to the prescribed-atom and positive-collision routes do
not sign a legal deviation at the original source.  The two-player regression
below has, on one literal mover reset:

* the exact endpoint-recipient atom;
* a positive-mass joint collision paying the mover positively;
* a literal best-response edge which removes all of the recipient's endpoint
  debt;
* reset-square commutation;
* arbitrary exact all-Continue prefix depth, preserving the complete source
  terminal law; and
* exact conservation of total semantic debt across the mover reset.

Nevertheless every recipient deviation from the displayed source is
nonprofitable.  The signed edge exists only at the reset endpoint, not at its
source.  This is a local architectural regression, not a quitting-game
counterexample: the table has no positive global terminal-semantic debt
minimum.  Global-minimum return provenance is exactly the hypothesis missing
from this example.
-/

noncomputable section

namespace GameTheory

open Math.Probability

namespace CounterfactualAtomExternalityRegression

/-- All-Continue exact-prefix stacks preserve the complete terminal law of
the regression source, not only its semantic pair. -/
theorem prefixed_terminalOutcomeMass_eq_source (depth : ℕ) :
    quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward (roots depth) source) =
      quittingTerminalOutcomeMass reward source := by
  unfold roots
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [List.replicate_succ, quittingLiteralRootStackProfile_cons]
      calc
        quittingTerminalOutcomeMass reward
            (quittingRootThenContinuationProfile reward
              quittingAllContinueRoot
              (quittingLiteralRootStackProfile reward
                (List.replicate depth quittingAllContinueRoot) source)) =
            quittingTerminalOutcomeLawPrefix quittingAllContinueRoot
              (quittingTerminalOutcomeMass reward
                (quittingLiteralRootStackProfile reward
                  (List.replicate depth quittingAllContinueRoot) source)) :=
          (quittingTerminalOutcomeLawPrefix_outcomeMass reward
            quittingAllContinueRoot _).symm
        _ = quittingTerminalOutcomeMass reward
              (quittingLiteralRootStackProfile reward
                (List.replicate depth quittingAllContinueRoot) source) :=
          quittingTerminalOutcomeLawPrefix_allContinue_eq _
        _ = quittingTerminalOutcomeMass reward source := ih

/-- The observer's pure-Continue response is a unit-gain legal edge at the
reset endpoint.  Thus this regression does contain the desired strategic
sign, but at the wrong displayed source. -/
theorem target_observer_continue_gain_eq_one :
    quittingTerminalPayoff reward
          (Function.update target observer
            (quittingPureTimeBehaviorStrategy reward observer none)) observer -
        quittingTerminalPayoff reward target observer = 1 := by
  rw [target_observer_continue_payoff, target_payoff_observer]
  norm_num

/-- **Combined local-interface no-go.**  Atom, collision, a signed response,
commuting reset square, exact-prefix access, and complete-law retention still
do not move the signed response edge back to the original source.

The final conjunct records the precise missing provenance: this finite table
cannot satisfy a positive global terminal-semantic minimum. -/
theorem combined_atom_collision_signedReset_but_sourceMismatch (depth : ℕ) :
    HasQuittingEndpointDebtRecipientAtom reward source mover observer
        replacement ∧
      IsQuittingLiteralExactRootStack reward (roots depth) source ∧
      quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward (roots depth) source) =
        quittingTerminalSemanticPair reward source ∧
      quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward (roots depth) source) =
        quittingTerminalOutcomeMass reward source ∧
      quittingTerminalOutcomeMass reward target (some jointTerminal) = 1 ∧
      reward jointTerminal mover = 1 ∧
      quittingTerminalDeviationDebt reward target observer = 1 ∧
      quittingTerminalPayoff reward
            (Function.update target observer
              (quittingPureTimeBehaviorStrategy reward observer none)) observer -
          quittingTerminalPayoff reward target observer = 1 ∧
      Function.update target observer
          (quittingPureTimeBehaviorStrategy reward observer none) =
        Function.update
          (Function.update source observer
            (quittingPureTimeBehaviorStrategy reward observer none))
          mover replacement ∧
      quittingTerminalDebtSum reward target =
        quittingTerminalDebtSum reward source ∧
      (¬∃ deviation : (quittingGame reward).BehaviorStrategy observer,
        0 < quittingTerminalPayoff reward
              (Function.update source observer deviation) observer -
            quittingTerminalPayoff reward source observer) ∧
      ¬∃ minimum : QuittingTerminalSemanticPair Player,
        (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum minimum ≤
            quittingTerminalSemanticDebtSum candidate) ∧
        0 < quittingTerminalSemanticDebtSum minimum := by
  refine ⟨has_endpointDebtRecipientAtom, roots_exactStack depth,
    prefixed_semanticPair_eq_source depth,
    prefixed_terminalOutcomeMass_eq_source depth, target_joint_mass_eq_one,
    ?_, target_debt_observer, target_observer_continue_gain_eq_one, ?_,
    target_totalDebt.trans source_totalDebt.symm, ?_,
    not_exists_positive_globalSemanticDebtMinimum⟩
  · simp [reward, jointTerminal, mover, observer]
  · unfold target
    exact Function.update_comm (by decide : mover ≠ observer) _ _ source
  · rintro ⟨deviation, hgain⟩
    rw [source_payoff_observer, sub_zero] at hgain
    exact (not_lt_of_ge (source_observer_deviation_payoff_le_zero deviation))
      hgain

end CounterfactualAtomExternalityRegression

end GameTheory
