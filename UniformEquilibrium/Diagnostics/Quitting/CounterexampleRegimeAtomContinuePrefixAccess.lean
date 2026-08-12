/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAtomExactPrefixChronology
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# Accessing a terminal atom through an exact prefix by continuing

The prescribed path through a long exact prefix may be preempted by the
atom mover's own hazards.  This is not a strategic access obstruction: the
mover may use one legal behavioral deviation which Continues through the
prefix and then plays either its original terminal strategy or the selected
atom strategy.

After that update, the probability of reaching the literal terminal suffix
is exactly the mover-deleted survival product.  Along an atom exact-prefix
chronology this product tends to one.  Consequently every terminal atom in
the stopping-law alternative lifts, with only an eventually harmless factor,
to an atom between literal profiles at the front of the exact chronology.

The rectangle branch also remains a genuine pure-time rectangle: forcing the
observer to Continue through a prefix of length `L` simply shifts its terminal
quit date by `L`.  Thus owner preemption is not a residual singleton-active
branch.  What remains after this adapter is the atom's sign/orientation and
the marked-row strategic consumer, not access to its terminal date.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Force one player to Continue at every root of a finite prefix word. -/
def quittingLiteralRootStackForceContinue
    (roots : List (ι → PMF Bool)) (who : ι) : List (ι → PMF Bool) :=
  roots.map fun root => Function.update root who (PMF.pure false)

/-- Continue through a finite root word and then use a supplied continuation
strategy.  This is one ordinary behavioral strategy of the same player. -/
def quittingLiteralRootStackContinueDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} : List (ι → PMF Bool) →
      (quittingGame reward).BehaviorStrategy who →
      (quittingGame reward).BehaviorStrategy who
  | [], continuation => continuation
  | _root :: roots, continuation =>
      quittingRootAndContinuationDeviation reward (PMF.pure false)
        (quittingLiteralRootStackContinueDeviation reward roots continuation)

/-- Updating a literal prefix profile by the Continue-through deviation
literally forces the player's prefix marginals to Continue and performs the
requested update at the terminal suffix. -/
theorem update_quittingLiteralRootStackProfile_continueDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : ι) (continuation : (quittingGame reward).BehaviorStrategy who) :
    Function.update
        (quittingLiteralRootStackProfile reward roots terminal) who
        (quittingLiteralRootStackContinueDeviation reward roots continuation) =
      quittingLiteralRootStackProfile reward
        (quittingLiteralRootStackForceContinue roots who)
        (Function.update terminal who continuation) := by
  induction roots with
  | nil => simp [quittingLiteralRootStackContinueDeviation,
      quittingLiteralRootStackForceContinue]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons,
        quittingLiteralRootStackContinueDeviation,
        quittingLiteralRootStackForceContinue, List.map_cons]
      rw [update_quittingRootThenContinuationProfile_eq, ih]
      rfl

/-- A common finite prefix scales every signed terminal-law atom by its full
joint survival.  All fresh prefix absorption cancels in the difference. -/
theorem quittingTerminalPayoffDifferenceAtom_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalPayoffDifferenceAtom reward
        (quittingLiteralRootStackProfile reward roots first)
        (quittingLiteralRootStackProfile reward roots second)
        observer outcome =
      quittingLiteralRootStackJointSurvival roots *
        quittingTerminalPayoffDifferenceAtom reward first second observer
          outcome := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      cases outcome with
      | none =>
          calc
            quittingTerminalPayoffDifferenceAtom reward
                (quittingLiteralRootStackProfile reward (root :: roots) first)
                (quittingLiteralRootStackProfile reward (root :: roots) second)
                observer none =
              quittingStationaryContinueMass root *
                quittingTerminalPayoffDifferenceAtom reward
                  (quittingLiteralRootStackProfile reward roots first)
                  (quittingLiteralRootStackProfile reward roots second)
                  observer none := by
                    simp [quittingTerminalPayoffDifferenceAtom,
                      quittingTerminalOutcomeMass_rootThenContinuation]
                    ring
            _ = quittingLiteralRootStackJointSurvival (root :: roots) *
                quittingTerminalPayoffDifferenceAtom reward first second
                  observer none := by
                    rw [ih]
                    simp [quittingLiteralRootStackJointSurvival]
                    ring
      | some terminal =>
          calc
            quittingTerminalPayoffDifferenceAtom reward
                (quittingLiteralRootStackProfile reward (root :: roots) first)
                (quittingLiteralRootStackProfile reward (root :: roots) second)
                observer (some terminal) =
              quittingStationaryContinueMass root *
                quittingTerminalPayoffDifferenceAtom reward
                  (quittingLiteralRootStackProfile reward roots first)
                  (quittingLiteralRootStackProfile reward roots second)
                  observer (some terminal) := by
                    simp [quittingTerminalPayoffDifferenceAtom,
                      quittingTerminalOutcomeMass_rootThenContinuation]
                    ring
            _ = quittingLiteralRootStackJointSurvival (root :: roots) *
                quittingTerminalPayoffDifferenceAtom reward first second
                  observer (some terminal) := by
                    rw [ih]
                    simp [quittingLiteralRootStackJointSurvival]
                    ring

/-- The survival of the prefix after forcing `who` to Continue is exactly
the player-deleted survival used by terminal-debt transport. -/
theorem quittingLiteralRootStackJointSurvival_forceContinue
    (roots : List (ι → PMF Bool)) (who : ι) :
    quittingLiteralRootStackJointSurvival
        (quittingLiteralRootStackForceContinue roots who) =
      quittingLiteralRootStackOpponentSurvival roots who := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival,
      quittingLiteralRootStackForceContinue,
      quittingLiteralRootStackOpponentSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackJointSurvival,
        quittingLiteralRootStackForceContinue,
        quittingLiteralRootStackOpponentSurvival, List.map_cons,
        List.prod_cons]
      change quittingRootOpponentContinueMass root who *
          quittingLiteralRootStackJointSurvival
            (quittingLiteralRootStackForceContinue roots who) =
        quittingRootOpponentContinueMass root who *
          quittingLiteralRootStackOpponentSurvival roots who
      rw [ih]

/-- Forcing one further player to Continue can only increase the survival of
an already modified finite prefix. -/
theorem quittingLiteralRootStackJointSurvival_le_forceContinue
    (roots : List (ι → PMF Bool)) (who : ι) :
    quittingLiteralRootStackJointSurvival roots ≤
      quittingLiteralRootStackJointSurvival
        (quittingLiteralRootStackForceContinue roots who) := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival,
      quittingLiteralRootStackForceContinue]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackJointSurvival,
        quittingLiteralRootStackForceContinue, List.map_cons, List.prod_cons]
      exact mul_le_mul
        (quittingStationaryContinueMass_le_update_pure_false root who) ih
        (quittingLiteralRootStackJointSurvival_nonneg roots)
        (quittingStationaryContinueMass_nonneg
          (Function.update root who (PMF.pure false)))

/-- The terminal atom alternative lifted to the front of a finite root word.
The source mover Continues throughout the prefix; the target mover Continues
throughout and then uses the displayed terminal strategy.  In rectangle
branches the observer's global pure quit date is shifted past the prefix. -/
def HasQuittingContinuePrefixDebtSlopeAtomAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge : ℝ) : Prop :=
  let source := quittingLiteralRootStackProfile reward
    (quittingLiteralRootStackForceContinue roots mover) terminal
  let moverRoots := quittingLiteralRootStackForceContinue roots mover
  let rectangleRoots := quittingLiteralRootStackForceContinue moverRoots observer
  (∃ outcome : {S : Finset ι // S.Nonempty},
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward source
          (quittingLiteralRootStackProfile reward moverRoots
            (Function.update terminal mover target)) observer (some outcome)) ∨
  ((∃ outcome : {S : Finset ι // S.Nonempty},
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (quittingLiteralRootStackProfile reward rectangleRoots
              (Function.update (Function.update terminal mover target) observer
                (quittingPureTimeBehaviorStrategy reward observer none)))
            (quittingLiteralRootStackProfile reward rectangleRoots
              (Function.update terminal observer
                (quittingPureTimeBehaviorStrategy reward observer none)))
            observer (some outcome)) ∨
    ∃ stop : ℕ, ∃ outcome : {S : Finset ι // S.Nonempty},
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (quittingLiteralRootStackProfile reward rectangleRoots
              (Function.update (Function.update terminal mover target) observer
                (quittingPureTimeBehaviorStrategy reward observer (some stop))))
            (quittingLiteralRootStackProfile reward rectangleRoots
              (Function.update terminal observer
                (quittingPureTimeBehaviorStrategy reward observer (some stop))))
            observer (some outcome))

/-- Once mover-deleted survival is at least one half, every terminal atom
lifts through the exact prefix with half its original charge. -/
theorem hasQuittingContinuePrefixDebtSlopeAtomAlternative_of_halfSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    {charge : ℝ} (hcharge : 0 < charge)
    (hsurvival : 1 / 2 ≤
      quittingLiteralRootStackOpponentSurvival roots mover)
    (hatom : HasQuittingStoppingLawDebtSlopeAtomAlternative reward terminal
      mover observer target charge) :
    HasQuittingContinuePrefixDebtSlopeAtomAlternative reward roots terminal
      mover observer target (charge / 2) := by
  let moverRoots := quittingLiteralRootStackForceContinue roots mover
  let source := quittingLiteralRootStackProfile reward moverRoots terminal
  have hmoverSurvival : quittingLiteralRootStackJointSurvival moverRoots =
      quittingLiteralRootStackOpponentSurvival roots mover :=
    quittingLiteralRootStackJointSurvival_forceContinue roots mover
  rcases hatom with hprescribed | hrectangle
  · left
    obtain ⟨outcome, houtcome⟩ := hprescribed
    refine ⟨outcome, ?_⟩
    rw [quittingTerminalPayoffDifferenceAtom_literalRootStack,
      hmoverSurvival]
    have hatomNonneg : 0 ≤
        quittingTerminalPayoffDifferenceAtom reward terminal
          (Function.update terminal mover target) observer (some outcome) := by
      have hcard : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
        positivity
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsurvival hatomNonneg]
  · right
    let rectangleRoots := quittingLiteralRootStackForceContinue moverRoots observer
    have hrectangleSurvival : 1 / 2 ≤
        quittingLiteralRootStackJointSurvival rectangleRoots := by
      exact hsurvival.trans <| by
        rw [← hmoverSurvival]
        exact quittingLiteralRootStackJointSurvival_le_forceContinue
          moverRoots observer
    rcases hrectangle with hnever | ⟨stop, outcome, houtcome⟩
    · left
      obtain ⟨outcome, houtcome⟩ := hnever
      refine ⟨outcome, ?_⟩
      rw [quittingTerminalPayoffDifferenceAtom_literalRootStack]
      have hatomNonneg : 0 ≤
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update (Function.update terminal mover target) observer
              (quittingPureTimeBehaviorStrategy reward observer none))
            (Function.update terminal observer
              (quittingPureTimeBehaviorStrategy reward observer none))
            observer (some outcome) := by
        have hcard : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
          positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hrectangleSurvival hatomNonneg]
    · right
      refine ⟨stop, outcome, ?_⟩
      rw [quittingTerminalPayoffDifferenceAtom_literalRootStack]
      have hatomNonneg : 0 ≤
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update (Function.update terminal mover target) observer
              (quittingPureTimeBehaviorStrategy reward observer (some stop)))
            (Function.update terminal observer
              (quittingPureTimeBehaviorStrategy reward observer (some stop)))
            observer (some outcome) := by
        have hcard : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
          positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hrectangleSurvival hatomNonneg]

/-- Both mover-side profiles used by the lifted atom are ordinary unilateral
updates of the original exact-prefix profile.  The first Continues through
the prefix and resumes the original terminal strategy; the second Continues
through the same prefix and then uses the selected atom strategy. -/
theorem quittingContinuePrefix_atomEndpoints_are_unilateralUpdates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : (quittingGame reward).BehaviorStrategy mover) :
    Function.update
        (quittingLiteralRootStackProfile reward roots terminal) mover
        (quittingLiteralRootStackContinueDeviation reward roots
          (terminal mover)) =
      quittingLiteralRootStackProfile reward
        (quittingLiteralRootStackForceContinue roots mover) terminal ∧
    Function.update
        (quittingLiteralRootStackProfile reward roots terminal) mover
        (quittingLiteralRootStackContinueDeviation reward roots target) =
      quittingLiteralRootStackProfile reward
        (quittingLiteralRootStackForceContinue roots mover)
        (Function.update terminal mover target) := by
  constructor
  · rw [update_quittingLiteralRootStackProfile_continueDeviation,
      Function.update_eq_self]
  · exact update_quittingLiteralRootStackProfile_continueDeviation
      reward roots terminal mover target

namespace QuittingStoppingLawAtomExactPrefixChronology

/-- **Preemption-free atom access.**  Every atom exact-prefix chronology has
eventually positive atoms at its front after one legal Continue-through
deviation by the mover.  This conclusion does not require joint prescribed
survival and therefore also consumes the singleton-active preemption branch.
-/
theorem continuePrefix_atomAlternative_eventually
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier) :
    ∀ᶠ rank in atTop,
      HasQuittingContinuePrefixDebtSlopeAtomAlternative reward
        (chronology.roots rank)
        (frontier.profiles (frontier.subseq rank)) chronology.mover.1
        chronology.observer
        (frontier.bestResponse chronology.mover (frontier.subseq rank))
        (chronology.charge / 2) := by
  have hsurvival := chronology.opponentSurvival_tendsto_one
    chronology.mover.2
  have hhalf : ∀ᶠ rank in atTop, 1 / 2 ≤
      quittingLiteralRootStackOpponentSurvival
        (chronology.roots rank) chronology.mover.1 :=
    hsurvival.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)) |>.mono
      fun _ h => h.le
  filter_upwards [chronology.atom_eventually, hhalf] with rank hatom hsurvivalRank
  exact hasQuittingContinuePrefixDebtSlopeAtomAlternative_of_halfSurvival
    reward (chronology.roots rank)
      (frontier.profiles (frontier.subseq rank)) chronology.mover.1
      chronology.observer
      (frontier.bestResponse chronology.mover (frontier.subseq rank))
      chronology.charge_pos hsurvivalRank hatom

/-- Explicit singleton-active specialization: the unique active owner is the
mover of the accessed atom, so all possible owner preemption is removed by
the same legal Continue-through deviation. -/
theorem singletonActive_continuePrefix_atomAlternative_eventually
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier)
    (owner : ι) (hactive : frontier.active = {owner}) :
    chronology.mover.1 = owner ∧
      ∀ᶠ rank in atTop,
        HasQuittingContinuePrefixDebtSlopeAtomAlternative reward
          (chronology.roots rank)
          (frontier.profiles (frontier.subseq rank)) owner
          chronology.observer
          (frontier.bestResponse chronology.mover (frontier.subseq rank))
          (chronology.charge / 2) := by
  have hmover : chronology.mover.1 = owner := by
    simpa [hactive] using chronology.mover.2
  subst owner
  exact ⟨rfl, chronology.continuePrefix_atomAlternative_eventually⟩

end QuittingStoppingLawAtomExactPrefixChronology

end GameTheory
