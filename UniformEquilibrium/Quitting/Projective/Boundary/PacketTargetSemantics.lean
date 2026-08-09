/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics
import UniformEquilibrium.Quitting.Projective.SingletonLCP

/-!
# Thin projective specialization of fixed-target terminal semantics

The game-generic acceptance, rejection, and conditional-retargeting notions
live in the terminal target-selection layer.  This file only specializes those
notions to the payoff vector stored in a normalized singleton projective
packet.

The wrappers consume no packet field other than `packet.value`.  In
particular, they do not select a semantic branch from projective equations,
construct an executable cemetery continuation, decode a chart/Farkas
obstruction, or produce a replacement target.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The generic fixed-target semantic alternative specialized to the value
carried by a normalized singleton projective packet. -/
theorem QuittingProjectiveSingletonPacket.terminalTargetSemanticAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingProjectiveSingletonPacket reward) :
    Nonempty
        (QuittingTerminalTargetAcceptanceCertificate reward packet.value) ∨
      Nonempty
        (QuittingTerminalTargetRejectionWitness reward packet.value) :=
  quittingTerminalTarget_semanticAlternative reward packet.value

/-- At the uniform-payoff waist, a packet value is either the exact fixed
target or carries a quantitative terminal separation witness.  This is a
semantic classification, not a projective production arrow. -/
theorem QuittingProjectiveSingletonPacket.value_uniform_or_terminalRejected
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingProjectiveSingletonPacket reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none packet.value ∨
      Nonempty
        (QuittingTerminalTargetRejectionWitness reward packet.value) := by
  rcases packet.terminalTargetSemanticAlternative with haccept | hrejection
  · exact Or.inl
      ((nonempty_quittingTerminalTargetAcceptanceCertificate_iff
        reward packet.value).1 haccept)
  · exact Or.inr hrejection

/-- Conditional packet-facing retarget adapter.  Its premise is separately
produced target-free uniform-payoff existence; it does not construct a
retarget from packet or rejection data. -/
theorem QuittingProjectiveSingletonPacket.terminalTargetAcceptance_or_retarget_of_exists_uniformPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingProjectiveSingletonPacket reward)
    (hexists : ∃ target : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    Nonempty
        (QuittingTerminalTargetAcceptanceCertificate reward packet.value) ∨
      Nonempty
        (QuittingTerminalTargetRetargetingWitness reward packet.value) :=
  quittingTerminalTarget_acceptance_or_retarget_of_exists_uniformPayoff
    reward packet.value hexists

end GameTheory
