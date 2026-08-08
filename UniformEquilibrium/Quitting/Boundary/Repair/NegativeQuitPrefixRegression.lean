/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate
import GameTheory.Concepts.Stochastic.Models.Quitting.SimpleBranches

/-!
# A negative one-player quit prefix is not a global equilibrium certificate

This regression isolates the fence used by the prefix-consumption argument.
In the one-player game whose only singleton quitting reward is `-1`, the
all-Continue (`Never`) profile is an exact terminal equilibrium: quitting is
not profitable.  The same game nevertheless has a one-stage sure-quit prefix
whose prescribed payoff is `-1`; when its physical continuation is `Never`,
continuing instead yields `0`, so the prefix has unit one-stage exploitability.

Thus a positive floor attached to one stored prefix cannot by itself be read as
a global terminal-equilibrium gap.  The prefix must be consumed by a charged
replacement argument, or accompanied by a separate global-gap conclusion.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

/-- The one-player quitting reward used by the negative-prefix regression. -/
def negativeQuitPrefixReward :
    {S : Finset Unit // S.Nonempty} → Payoff Unit :=
  fun _ _ => -1

/-- The physical `Never` continuation payoff for this regression. -/
def negativeQuitPrefixNeverTail : Payoff Unit :=
  fun _ => 0

/-- A stored endpoint that agrees with the sure-quit prefix's local payoff. -/
def negativeQuitPrefixStoredEndpoint : Payoff Unit :=
  fun _ => -1

/-- The one-stage sure-quit root. -/
def negativeQuitPrefixSureRoot : Unit → PMF Bool :=
  fun _ => PMF.pure true

@[simp] theorem negativeQuitPrefixReward_singleton :
    negativeQuitPrefixReward (quittingSingletonTerminal ()) () = -1 := by
  rfl

@[simp] theorem negativeQuitPrefixNeverTail_apply :
    negativeQuitPrefixNeverTail () = 0 := by
  rfl

@[simp] theorem negativeQuitPrefixStoredEndpoint_apply :
    negativeQuitPrefixStoredEndpoint () = -1 := by
  rfl

@[simp] theorem negativeQuitPrefixSureRoot_apply :
    negativeQuitPrefixSureRoot () = PMF.pure true := by
  rfl

@[simp] theorem negativeQuitPrefix_sureQuitPayoff :
    quittingRootQuitPayoff negativeQuitPrefixReward
        negativeQuitPrefixNeverTail negativeQuitPrefixSureRoot () = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  have hroot :
      Function.update negativeQuitPrefixSureRoot () (PMF.pure true) =
        negativeQuitPrefixSureRoot := by
    funext player
    cases player
    simp
  rw [hroot]
  change expect (pmfPi (fun _ : Unit => PMF.pure true)) _ = _
  rw [pmfPi_pure, expect_pure]
  simp [negativeQuitPrefixReward, quittingRootPayoff]

@[simp] theorem negativeQuitPrefix_continuePayoff :
    quittingRootContinuePayoff negativeQuitPrefixReward
        negativeQuitPrefixNeverTail negativeQuitPrefixSureRoot () = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  have hroot :
      Function.update negativeQuitPrefixSureRoot () (PMF.pure false) =
        (fun _ : Unit => PMF.pure false) := by
    funext player
    cases player
    simp
  rw [hroot]
  change expect (pmfPi (fun _ : Unit => PMF.pure false)) _ = _
  rw [pmfPi_pure, expect_pure]
  simp [quittingRootPayoff]

@[simp] theorem negativeQuitPrefix_prescribedPayoff :
    quittingRootSuccessorPayoff negativeQuitPrefixReward
        negativeQuitPrefixNeverTail negativeQuitPrefixSureRoot () = -1 := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  change expect (pmfPi (fun _ : Unit => PMF.pure true)) _ = _
  rw [pmfPi_pure, expect_pure]
  simp [negativeQuitPrefixReward, quittingRootPayoff]

/-- The sure-quit prefix has unit one-stage endpoint exploitability against
the physical `Never` continuation. -/
theorem negativeQuitPrefix_endpointExploitability_eq_one :
    max
        (quittingRootQuitPayoff negativeQuitPrefixReward
          negativeQuitPrefixNeverTail negativeQuitPrefixSureRoot () -
          quittingRootSuccessorPayoff negativeQuitPrefixReward
            negativeQuitPrefixNeverTail negativeQuitPrefixSureRoot ())
        (quittingRootContinuePayoff negativeQuitPrefixReward
          negativeQuitPrefixNeverTail negativeQuitPrefixSureRoot () -
          quittingRootSuccessorPayoff negativeQuitPrefixReward
            negativeQuitPrefixNeverTail negativeQuitPrefixSureRoot ()) = 1 := by
  norm_num

/-! ## The stored-endpoint fence -/

@[simp] theorem negativeQuitPrefix_storedQuitPayoff :
    quittingRootQuitPayoff negativeQuitPrefixReward
        negativeQuitPrefixStoredEndpoint negativeQuitPrefixSureRoot () = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  change expect (pmfPi (fun _ : Unit => PMF.pure true)) _ = _
  rw [pmfPi_pure, expect_pure]
  simp [negativeQuitPrefixReward, quittingRootPayoff]

@[simp] theorem negativeQuitPrefix_storedContinuePayoff :
    quittingRootContinuePayoff negativeQuitPrefixReward
        negativeQuitPrefixStoredEndpoint negativeQuitPrefixSureRoot () = -1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  have hroot :
      Function.update negativeQuitPrefixSureRoot () (PMF.pure false) =
        (fun _ : Unit => PMF.pure false) := by
    funext player
    cases player
    simp
  rw [hroot]
  change expect (pmfPi (fun _ : Unit => PMF.pure false)) _ = _
  rw [pmfPi_pure, expect_pure]
  simp [negativeQuitPrefixStoredEndpoint, quittingRootPayoff]

@[simp] theorem negativeQuitPrefix_storedPrescribedPayoff :
    quittingRootSuccessorPayoff negativeQuitPrefixReward
        negativeQuitPrefixStoredEndpoint negativeQuitPrefixSureRoot () = -1 := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  change expect (pmfPi (fun _ : Unit => PMF.pure true)) _ = _
  rw [pmfPi_pure, expect_pure]
  simp [negativeQuitPrefixReward, quittingRootPayoff]

/-- The sure-quit prefix is locally complementary even when its stored
endpoint is the negative singleton payoff: both pure endpoint values equal
the prescribed successor value `-1`. -/
theorem negativeQuitPrefix_storedEndpoint_localComplementarity :
    quittingRootQuitPayoff negativeQuitPrefixReward
        negativeQuitPrefixStoredEndpoint negativeQuitPrefixSureRoot () =
      quittingRootContinuePayoff negativeQuitPrefixReward
        negativeQuitPrefixStoredEndpoint negativeQuitPrefixSureRoot () ∧
    quittingRootContinuePayoff negativeQuitPrefixReward
        negativeQuitPrefixStoredEndpoint negativeQuitPrefixSureRoot () =
      quittingRootSuccessorPayoff negativeQuitPrefixReward
        negativeQuitPrefixStoredEndpoint negativeQuitPrefixSureRoot () := by
  simp

/-- The all-Continue profile is an exact terminal equilibrium in the same
one-player game. -/
theorem negativeQuitPrefix_never_isExactTerminalNash :
    (quittingGame negativeQuitPrefixReward).IsεAsymptoticNash
      (quittingTerminalPayoff negativeQuitPrefixReward) 0
      (quittingAlwaysContinueProfile negativeQuitPrefixReward) := by
  apply (isεAsymptoticNash_quittingAlwaysContinue_iff
    negativeQuitPrefixReward le_rfl).2
  intro who
  cases who
  norm_num

end GameTheory
