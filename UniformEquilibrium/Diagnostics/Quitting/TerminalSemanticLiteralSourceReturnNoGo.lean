/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMacroscopicAtomNashProvenance
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine

/-!
# Literal source return and root--tail complementarity

A positive best-endpoint deviation at a reached row cannot be inserted,
unchanged, as an exact Nash--Bellman edge.  Its gain is live mass times the
root--tail coordinate Nash defect, while exact endpoint complementarity on
the same root--tail fiber forces that defect to vanish.

This is an architectural no-go, not a closure theorem.  A viable compiler
must change the root, change the continuation payoff, tolerate Nash error at
least the retained gain, or explicitly charge the non-Nash row in a larger
account.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The shifted semantic tail used by the actual row at `stage`. -/
def quittingLiteralActualRowTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))

/-- The literal product root played on the actual live history at `stage`. -/
def quittingLiteralActualRowRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    ι → PMF Bool :=
  quittingProfileLiveRoot reward profile stage

/-- The canonical legal gain obtained by replacing the actual marginal at one
reached row by its better pure endpoint and leaving the source and tail
unchanged. -/
def quittingLiteralActualRowBestEndpointGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) : ℝ :=
  let tail := quittingLiteralActualRowTail reward profile stage
  let root := quittingLiteralActualRowRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let deviation := quittingStagePureEndpointBehaviorDeviation
    reward profile who stage action
  quittingTerminalPayoff reward (Function.update profile who deviation) who -
    quittingTerminalPayoff reward profile who

/-- A packet carrying the literal behavioral row, a named terminal event, and
the positive gain at that same row. -/
structure QuittingLiteralPositiveActualRowPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  profile : (quittingGame reward).BehaviorProfile
  stage : ℕ
  who : ι
  terminal : {S : Finset ι // S.Nonempty}
  mass : ℝ
  mass_eq : mass = quittingStageCoalitionMass reward profile stage terminal
  mass_pos : 0 < mass
  gain_pos : 0 <
    quittingLiteralActualRowBestEndpointGain reward profile who stage

namespace QuittingLiteralPositiveActualRowPacket

/-- The current literal semantic payoff at the marked row. -/
def source
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward packet.profile packet.stage)

/-- The packet's root--tail Nash defect. -/
def complementarityResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward) : ℝ :=
  quittingRootCoordinateNashDefect reward
    (quittingLiteralActualRowTail reward packet.profile packet.stage).1
    (quittingLiteralActualRowRoot reward packet.profile packet.stage)
    packet.who

/-- The actual legal gain is exactly live mass times the invariant root--tail
complementarity residual. -/
theorem gain_eq_liveMass_mul_complementarityResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward) :
    quittingLiteralActualRowBestEndpointGain reward packet.profile
        packet.who packet.stage =
      quittingLiveMass reward packet.profile packet.stage *
        packet.complementarityResidual := by
  exact quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
    reward packet.profile packet.who packet.stage

/-- Positive actual gain makes the fixed-fiber complementarity residual
strictly positive. -/
theorem complementarityResidual_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward) :
    0 < packet.complementarityResidual := by
  have hlive := quittingLiveMass_nonneg reward packet.profile packet.stage
  have hgain := packet.gain_pos
  rw [packet.gain_eq_liveMass_mul_complementarityResidual] at hgain
  by_contra hnot
  have hresidualNonpos : packet.complementarityResidual ≤ 0 :=
    le_of_not_gt hnot
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hlive hresidualNonpos))
    hgain

/-- A one-edge embedding which preserves the source payoff, actual root, and
actual shifted-tail payoff.  Preserving the whole behavioral tail is a
strictly stronger condition. -/
def IsLiteralNashBellmanEmbedding
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward)
    (current tail : QuittingNashBellmanPoint ι) : Prop :=
  current.1 = packet.source.1 ∧
    quittingRootOfSimplex current.2 =
      quittingLiteralActualRowRoot reward packet.profile packet.stage ∧
    tail.1 =
      (quittingLiteralActualRowTail reward packet.profile packet.stage).1 ∧
    IsQuittingNashBellmanEdge reward current tail

/-- Exact endpoint complementarity kills the packet residual on a literal
root--tail fiber. -/
theorem complementarityResidual_eq_zero_of_literalNashBellmanEmbedding
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward)
    {current tail : QuittingNashBellmanPoint ι}
    (hembed : packet.IsLiteralNashBellmanEmbedding current tail) :
    packet.complementarityResidual = 0 := by
  have hnashEndpoint := hembed.2.2.2.2
  rw [hembed.2.1, hembed.2.2.1] at hnashEndpoint
  have hnash :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward
      (quittingLiteralActualRowTail reward packet.profile packet.stage).1
      (quittingLiteralActualRowRoot reward packet.profile packet.stage)).1
      hnashEndpoint
  exact (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
    reward
    (quittingLiteralActualRowTail reward packet.profile packet.stage).1
    (quittingLiteralActualRowRoot reward packet.profile packet.stage)).1
    hnash packet.who

/-- On the exact Nash--Bellman graph, the packet's literal behavioral gain is
zero. -/
theorem gain_eq_zero_of_literalNashBellmanEmbedding
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward)
    {current tail : QuittingNashBellmanPoint ι}
    (hembed : packet.IsLiteralNashBellmanEmbedding current tail) :
    quittingLiteralActualRowBestEndpointGain reward packet.profile
        packet.who packet.stage = 0 := by
  rw [packet.gain_eq_liveMass_mul_complementarityResidual,
    packet.complementarityResidual_eq_zero_of_literalNashBellmanEmbedding
      hembed, mul_zero]

/-- No positive actual-row packet can be an exact Nash--Bellman edge while
retaining its literal source root and literal tail. -/
theorem not_exists_literalNashBellmanEmbedding
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward) :
    ¬ ∃ current tail : QuittingNashBellmanPoint ι,
      packet.IsLiteralNashBellmanEmbedding current tail := by
  rintro ⟨current, tail, hembed⟩
  have hzero := packet.gain_eq_zero_of_literalNashBellmanEmbedding hembed
  exact (ne_of_gt packet.gain_pos) hzero

/-- A positive packet cannot occur at any date of an exact Nash--Bellman
chronology if occurrence preserves its root and next continuation payoff. -/
theorem not_occurs_in_exactNashBellmanChronology
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward)
    (point : ℕ → QuittingNashBellmanPoint ι)
    (hexact : ∀ date,
      IsQuittingNashBellmanEdge reward (point date) (point (date + 1))) :
    ¬ ∃ date,
      (point date).1 = packet.source.1 ∧
        quittingRootOfSimplex (point date).2 =
          quittingLiteralActualRowRoot reward packet.profile packet.stage ∧
        (point (date + 1)).1 =
          (quittingLiteralActualRowTail reward packet.profile
            packet.stage).1 := by
  rintro ⟨date, hsource, hroot, htail⟩
  apply packet.not_exists_literalNashBellmanEmbedding
  exact ⟨point date, point (date + 1), hsource, hroot, htail, hexact date⟩

/-- An approximate root-Nash repair which preserves the literal root--tail
fiber must pay at least the actual behavioral gain as Nash error. -/
theorem gain_le_nashError_of_literal_root_tail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward)
    {error : ℝ} (herror : 0 ≤ error)
    (hnash : IsεQuittingRootNash reward
      (quittingLiteralActualRowTail reward packet.profile packet.stage).1
      error
      (quittingLiteralActualRowRoot reward packet.profile packet.stage)) :
    quittingLiteralActualRowBestEndpointGain reward packet.profile
        packet.who packet.stage ≤ error := by
  have hdefect := quittingRootCoordinateNashDefect_le_of_isεQuittingRootNash
    reward
    (quittingLiteralActualRowTail reward packet.profile packet.stage).1
    (quittingLiteralActualRowRoot reward packet.profile packet.stage)
    packet.who error hnash
  rw [packet.gain_eq_liveMass_mul_complementarityResidual]
  calc
    quittingLiveMass reward packet.profile packet.stage *
          packet.complementarityResidual ≤
        quittingLiveMass reward packet.profile packet.stage * error :=
      mul_le_mul_of_nonneg_left hdefect
        (quittingLiveMass_nonneg reward packet.profile packet.stage)
    _ ≤ 1 * error :=
      mul_le_mul_of_nonneg_right
        (quittingLiveMass_le_one reward packet.profile packet.stage) herror
    _ = error := one_mul error

/-- Attaching a suffix after the non-Nash packet row cannot make the unchanged
source a terminal approximate equilibrium below the retained gain. -/
theorem not_terminalApproximateEquilibrium_below_gain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingLiteralPositiveActualRowPacket reward)
    {error : ℝ}
    (herror : error < quittingLiteralActualRowBestEndpointGain reward
      packet.profile packet.who packet.stage) :
    ¬ (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error packet.profile := by
  intro hnash
  let tail := quittingLiteralActualRowTail reward packet.profile packet.stage
  let root := quittingLiteralActualRowRoot reward packet.profile packet.stage
  let action := quittingRootBestEndpointAction reward tail.1 root packet.who
  let deviation := quittingStagePureEndpointBehaviorDeviation
    reward packet.profile packet.who packet.stage action
  have hdeviation := hnash packet.who deviation
  dsimp only [quittingLiteralActualRowBestEndpointGain, tail, root, action,
    deviation] at herror
  linarith

end QuittingLiteralPositiveActualRowPacket

end GameTheory
