/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Projective.Boundary.PacketTargetSemantics
import UniformEquilibrium.Quitting.Projective.TargetMismatch

/-!
# Fixed-target semantic regression for a projective packet

The existing analytic target-mismatch example is the substantive projective
connection to the game-generic terminal semantics.  Its packet value `(1,1)`
has an explicit quantitative terminal rejection witness at error `1 / 10`.
The already proved sure-exit payoff `(1,2)` is packaged as an accepted
alternative.

This regression does not derive rejection or retargeting from generic packet,
chart, or Farkas data.  It records one concrete projective mismatch using the
terminal-layer witness types.
-/

noncomputable section

namespace GameTheory
namespace QuittingProjectiveTargetMismatch

open StochasticGame

/-- Explicit quantitative terminal rejection of the analytic packet target. -/
def packetTargetRejectionWitness :
    QuittingTerminalTargetRejectionWitness reward packet.value where
  error := 1 / 10
  error_pos := by norm_num
  separates := by
    classical
    intro profile hnash
    by_contra hseparated
    push_neg at hseparated
    have hclose : ∀ who,
        |quittingTerminalPayoff reward profile who - 1| ≤ (1 / 10 : ℝ) := by
      intro who
      simpa using (hseparated who).le
    have hgap := one_ninth_le_of_terminalNash_close
      (profile := profile) hnash hclose
    norm_num at hgap

@[simp]
theorem packetTargetRejectionWitness_error :
    packetTargetRejectionWitness.error = 1 / 10 :=
  rfl

/-- The rejected analytic target is conditionally packaged with the exact
sure-exit payoff `(1,2)` as an accepted alternative.  The target itself comes
from the independently proved sure-exit theorem, not from a generic
projective retarget producer. -/
noncomputable def packetFirstExitRetargetingWitness :
    QuittingTerminalTargetRetargetingWitness reward packet.value where
  target := firstExitValue
  target_ne := by
    intro heq
    have hcoord := congrFun heq true
    norm_num [firstExitValue] at hcoord
  acceptance := Classical.choice
    (exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff
      reward firstExitValue firstExitValue_isUniformEquilibriumPayoff)
  rejection := packetTargetRejectionWitness

/-- The concrete replacement target is strategically accepted at the exact
declared payoff. -/
theorem packetFirstExitRetargetingWitness_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      packetFirstExitRetargetingWitness.target :=
  packetFirstExitRetargetingWitness.acceptance.isUniformEquilibriumPayoff

end QuittingProjectiveTargetMismatch
end GameTheory
