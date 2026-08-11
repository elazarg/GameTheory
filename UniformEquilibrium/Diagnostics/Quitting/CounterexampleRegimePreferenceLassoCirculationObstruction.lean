/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSupport

/-!
# The strict packet lasso excludes the packet-mass circulation phase

The complementary singleton-mixture compiler turns a normalized packet into
a period-one face circulation only when every positive-mass coordinate is
pinned by the *mixture* itself.  A counterexample's strict supported-
preference lasso witnesses the opposite at its entrance: the packet target,
which is the owner's singleton payoff, is strictly below the singleton
mixture.

Consequently no phase of any `FaceCirculationCertificate` can use the full
packet mass vector as its phase mixture.  A circulation decoder must provide
genuinely new phase-varying weights and the corresponding full-vector affine
step and vertex-pinning data.  Pair-collision signs do not repair this
singleton target-pinning failure.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingStrictSupportedPreferenceLasso

/-- The strict entrance is a literal failure of the active-mixture pinning
hypothesis used by the one-face singleton circulation compiler. -/
theorem not_activePinned_singletonMixture
    {packet : QuittingNormalizedSingletonSourcePacket reward}
    (lasso : QuittingStrictSupportedPreferenceLasso packet) :
    ¬ ∀ owner, 0 < packet.mass owner →
      quittingSingletonMixture reward packet.mass owner =
        reward (quittingSingletonTerminal owner) owner := by
  intro hpinned
  have hmass : 0 < packet.mass lasso.entrance :=
    (packet.mem_support_iff lasso.entrance).mp lasso.entrance_mem
  have htarget :=
    packet.positive_mass_pins_target lasso.entrance hmass
  have hmixture := hpinned lasso.entrance hmass
  linarith [lasso.target_lt_mixture]

/-- **Packet-mass phase obstruction.**  No phase of a face circulation can
use the lasso packet's whole singleton mass vector.  The certificate's phase
target pin would force mixture equality at the strict entrance. -/
theorem faceCirculation_mixWeight_ne_packetMass
    {packet : QuittingNormalizedSingletonSourcePacket reward}
    (lasso : QuittingStrictSupportedPreferenceLasso packet)
    {floor : Payoff ι} {L : ℕ} [NeZero L]
    (certificate :
      FaceCirculationCertificate (weightOfReward reward) floor L)
    (phase : ZMod L) :
    certificate.mixWeight phase ≠ packet.mass := by
  intro hweight
  have hmass : 0 < packet.mass lasso.entrance :=
    (packet.mem_support_iff lasso.entrance).mp lasso.entrance_mem
  have hphaseMass : 0 < certificate.mixWeight phase lasso.entrance := by
    rw [hweight]
    exact hmass
  have hpin := certificate.target_pinned phase lasso.entrance hphaseMass
  rw [hweight, mixTarget_weightOfReward_eq_quittingSingletonMixture,
    weightOfReward_singleton] at hpin
  have htarget :=
    packet.positive_mass_pins_target lasso.entrance hmass
  linarith [lasso.target_lt_mixture]

end QuittingStrictSupportedPreferenceLasso

end GameTheory
