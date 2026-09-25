/-
# EXP-141: infinite canonical play without countable histories

The legal action carrier is the real line. The path measure and each finite
chronological marginal use the canonical PMF runner without a countability
assumption on the full history carrier.
-/

import GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.PMFInfinitePlayGate

open GameTheory.Math.Probability
open GameTheory.Stochastic
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure.Game
open MeasureTheory

@[reducible]
def realActionGame : Stochastic.Game Unit where
  State := Unit
  Action := fun _ => ℝ
  transition _ _ := PMF.pure ()
  stageUtility _ _ _ := 0

local instance realActionNonempty :
    ∀ i, Nonempty (realActionGame.Action i) :=
  fun _ => ⟨0⟩

def zeroPolicy : Game.PublicPolicy realActionGame () :=
  fun _ => PMF.pure 0

def zeroProfile : Game.PublicProfile realActionGame () :=
  fun _ => zeroPolicy

def zeroBehavior : realActionGame.BehaviorProfile () :=
  Game.toBehaviorProfile realActionGame () zeroProfile

/-- A legal one-step history can retain any real action, independently of the
particular policy used to sample the path law. -/
def realActionHistory (action : ℝ) : CanonicalHistory realActionGame () :=
  (realActionGame.toExecution ()).initHistory.extend
    (Game.canonicalJoint realActionGame () () (fun _ => action)).2
    (Game.canonicalRealized realActionGame ()
      (state := ()) (target := ()) (actions := fun _ => action)
      (by simp [realActionGame]))

private def lastAction (history : CanonicalHistory realActionGame ()) : Option ℝ :=
  match history.trace with
  | .start => none
  | .extend _ joint _ _ => joint ()

theorem realActionHistory_injective : Function.Injective realActionHistory := by
  intro first second heq
  have hread := congrArg lastAction heq
  simpa [lastAction, realActionHistory, ExecutionProtocol.History.extend,
    Game.canonicalJoint] using hread

/-- The ambient canonical history carrier is not countable, even though this
particular policy chooses the pure action zero. -/
theorem realActionHistory_not_countable :
    ¬ Countable (CanonicalHistory realActionGame ()) := by
  intro hcount
  exact not_countable (α := ℝ)
    (@Function.Injective.countable ℝ (CanonicalHistory realActionGame ())
      hcount realActionHistory realActionHistory_injective)

/-- Ionescu--Tulcea yields a probability law for real-valued legal actions. -/
theorem realAction_infinitePlay_probability :
    IsProbabilityMeasure
      (infinitePlayMeasure realActionGame () zeroBehavior) :=
  inferInstance

/-- Its two-stage chronological marginal is exactly the canonical PMF law. -/
theorem realAction_chronological_marginal_two :
    (infinitePlayMeasure realActionGame () zeroBehavior).map
        (chronologicalProjection realActionGame () 2) =
      (realActionGame.chronologicalHistoryLaw () zeroBehavior 2).toMeasure :=
  map_chronologicalProjection_infinitePlayMeasure
    realActionGame () zeroBehavior 2

end GameTheory.Experimental.PostArchitecture.PMFInfinitePlayGate
