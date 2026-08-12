/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonStrategicDispatch
import UniformEquilibrium.Quitting.Punishment.InstantPunishment

/-!
# Strategic compression of the concentrated singleton handoff

The positive-punishment arm of the static singleton dispatcher is not a live
residual.  Positive punishment makes the singleton reward individually
rational.  If no outsider gains by joining the sure singleton exit, the
instant-punishment compiler produces a uniform-equilibrium payoff; in a
counterexample regime some outsider must therefore gain strictly, which
supplies the existing atomic-toggle handoff.

The same conclusion consumes the complete relabeled concentrated-singleton
dispatch.  Its tail-escape and fixed-owner-join-loss arms share a positive
collision gap: the reset owner strictly gains by joining the named singleton
exit.  Thus every nondeletion arm compresses to one static atomic handoff.

No new residual predicate is introduced here.
-/

noncomputable section

namespace GameTheory

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- **Static singleton compression.**  The three-way static singleton
dispatcher reduces exactly to atomic instability or player deletion.

Full behavioral best-response semantics enter through
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment`. -/
theorem QuittingCounterexampleRegime.singletonStaticStrategicDispatch_compress
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (regime : QuittingCounterexampleRegime reward) (owner : iota)
    (hdispatch : HasQuittingSingletonStaticStrategicDispatch reward owner
      regime.terminalGap) :
    HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward owner regime.terminalGap := by
  classical
  rcases hdispatch with hatomic | hpunishment | hdeletion
  · exact Or.inl hatomic
  · have hupper := quittingPunishmentValue_le_max_solo reward owner
    rw [quittingSetReward_singleton_eq_soloReward] at hupper
    have hsoloPos : 0 < quittingSoloReward reward owner owner := by
      by_contra hnot
      have hsoloNonpos : quittingSoloReward reward owner owner ≤ 0 :=
        le_of_not_gt hnot
      rw [max_eq_right hsoloNonpos] at hupper
      linarith
    have hIR : IsQuittingInstantPunishmentIR reward owner := by
      unfold IsQuittingInstantPunishmentIR
      rwa [max_eq_left hsoloPos.le] at hupper
    have hnotNoJoin : ¬ IsQuittingInstantNoJoin reward owner := by
      intro hnoJoin
      have hUE := isUniformEquilibriumPayoff_soloReward_of_instantPunishment
        reward owner hIR hnoJoin
      exact regime.not_exists_uniformEquilibriumPayoff
        ⟨quittingSoloReward reward owner, hUE⟩
    unfold IsQuittingInstantNoJoin at hnotNoJoin
    push Not at hnotNoJoin
    obtain ⟨joiner, hjoinerNe, hstrict⟩ := hnotNoJoin
    exact Or.inl
      (regime.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
        owner joiner hjoinerNe hstrict)
  · exact Or.inr hdeletion

/-- **Exhaustive singleton-leaf consumer.**  The exact top-level stopping-law
singleton orientation carries the ambient static dispatcher, so it too
reduces to atomic instability or exact deletion.  The terminal membership
and singleton-cardinality fields are provenance for the stopping-law leaf;
the static compression itself does not need them. -/
theorem QuittingCounterexampleRegime.stoppingLawSingletonStrategicOrientation_compress
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (regime : QuittingCounterexampleRegime reward)
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (horientation :
      HasQuittingStoppingLawSingletonStrategicOrientation packet) :
    HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward packet.observer
        regime.terminalGap := by
  obtain ⟨_observerMem, _singleton, hstatic⟩ := horientation
  exact regime.singletonStaticStrategicDispatch_compress
    packet.observer hstatic

/-- **Full concentrated-singleton compression.**  Every arm of the relabeled
concentrated singleton handoff is already either an exact player deletion or
the same static atomic-toggle handoff.  In the tail-escape and
fixed-owner-join-loss arms, the reset owner is the strict joiner of the
singleton exit of `other`. -/
theorem QuittingCounterexampleRegime.concentratedSingletonStrategicDispatch_compress
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (regime : QuittingCounterexampleRegime reward)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : iota)
    (hdispatch : HasQuittingConcentratedSingletonStrategicDispatch
      regime packet other) :
    HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward other
        regime.terminalGap := by
  classical
  obtain ⟨_terminal, _endpoint, _static, hstrategic⟩ := hdispatch
  rcases hstrategic with hatomic | hpunishment | hdeletion | htail | hloss
  · exact Or.inl hatomic
  · exact regime.singletonStaticStrategicDispatch_compress other
      (Or.inr (Or.inl hpunishment))
  · exact Or.inr hdeletion
  · dsimp [HasQuittingConcentratedSingletonOwnerTailEscape] at htail
    have hstrict : quittingSoloReward reward other owner <
        quittingSingletonCollisionReward reward other owner :=
      sub_pos.mp htail.1
    have hownerNe : owner ≠ other := by
      intro heq
      subst owner
      simp [quittingSingletonCollisionReward, quittingSoloReward] at hstrict
    exact Or.inl
      (regime.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
        other owner hownerNe hstrict)
  · dsimp [HasQuittingConcentratedSingletonFixedOwnerJoinLoss] at hloss
    have hstrict : quittingSoloReward reward other owner <
        quittingSingletonCollisionReward reward other owner :=
      sub_pos.mp hloss.1
    have hownerNe : owner ≠ other := by
      intro heq
      subst owner
      simp [quittingSingletonCollisionReward, quittingSoloReward] at hstrict
    exact Or.inl
      (regime.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
        other owner hownerNe hstrict)

end GameTheory
