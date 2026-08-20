/-
# EXP-116: bounded stochastic Kuhn on an infinite history carrier

The baseline always chooses `false`.  The one-step history produced by action
`true` is therefore off its support, but the fully supported finite-site cover
still contains that public-history information state.  The public unilateral
and Nash-transfer theorems then apply without a `Fintype PublicHistory`
instance.
-/

import GameTheory.Stochastic.Kuhn

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.StochasticKuhn

open GameTheory.Math.Probability GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Stochastic
open GameTheory.Stochastic.Game

/-- One player can move the public state to either Boolean value. -/
@[reducible]
def offPathGame : Game Unit where
  State := Bool
  Action := fun _ => Bool
  transition _ action := FinDist.pure (action ())
  stageUtility _ _ _ := 0

local instance actionNonempty :
    ∀ i, Nonempty (offPathGame.Action i) :=
  fun _ => ⟨false⟩

local instance actionFintype :
    ∀ i, Fintype (offPathGame.Action i) :=
  fun _ => inferInstance

/-- The hostile carrier really is infinite; no hidden finite-history instance
can discharge the bounded Kuhn theorems. -/
theorem publicHistory_infinite : Infinite offPathGame.PublicHistory := by
  let record : offPathGame.StageRecord :=
    ⟨false, fun _ => false, false⟩
  exact Infinite.of_injective (fun n => List.replicate n record)
    (List.replicate_left_injective record)

/-- A baseline that assigns zero probability to action `true` everywhere. -/
def baseline (initial : Bool) : offPathGame.PublicProfile initial :=
  fun _ _ => FinDist.pure false

theorem true_not_mem_baseline_initial (initial : Bool) :
    true ∉ (baseline initial () []).support := by
  rw [baseline, FinDist.mem_support_pure]
  decide

def trueActions : ∀ _ : Unit, Bool := fun _ => true

def trueJoint : ∀ _ : Unit, Option Bool := fun _ => some true

theorem trueJoint_legal :
    (offPathGame.toExecution false).Legal false trueJoint := by
  constructor
  · simp
  · intro i
    simp [trueJoint]

theorem true_realized :
    true ∈
      ((offPathGame.toExecution false).step false
        ⟨trueJoint, trueJoint_legal⟩).support := by
  show true ∈ (FinDist.pure true).support
  exact FinDist.mem_support_pure.mpr rfl

/-- The history reached only by the excluded baseline action. -/
def offPathHistory : (offPathGame.toExecution false).History :=
  (offPathGame.toExecution false).initHistory.extend
    trueJoint_legal true_realized

theorem offPathHistory_reachesWithin :
    (offPathGame.toExecution false).ReachesWithin 1
      (offPathGame.toExecution false).initHistory offPathHistory := by
  simpa [offPathHistory] using
    (ExecutionProtocol.ReachesWithin.step trueJoint trueJoint_legal
      true_realized
      (ExecutionProtocol.ReachesWithin.refl 0 offPathHistory))

/-- Counterfactual coverage includes the off-baseline public history. -/
theorem offPath_info_mem_boundedInformationSites :
    (offPathGame.perfectMonitoring false).infoOf () offPathHistory.trace ∈
      offPathGame.boundedInformationSites false 1 () := by
  exact offPathGame.boundedInformationSites_cover false 1
    offPathHistory offPathHistory_reachesWithin (by simp) ()

/-- The hostile game consumes the public unilateral theorem with its infinite
public-history carrier. -/
theorem unilateral_consumer (who : Unit)
    (replacement : offPathGame.MixedPublicPolicy who) :
    ((offPathGame.pureHorizonForm false 1).mixed).play
        (Profile.update
          (fun i => PublicPolicy.toMixed offPathGame false 1
            (baseline false i)) who replacement) =
      (offPathGame.publicHorizonForm false 1).play
        (Profile.update (baseline false) who
          (MixedPublicPolicy.toBehavioral offPathGame false replacement)) :=
  offPathGame.kuhn_behavioral_update_toMixed
    false (baseline false) who replacement 1

/-- The same infinite-carrier witness reaches exact Nash transfer. -/
theorem nash_consumer
    (utility : (offPathGame.toExecution false).History → Unit → ℝ)
    (hnash : IsNash (offPathGame.publicHorizonForm false 1)
      (euPreference utility) (baseline false)) :
    IsNash (offPathGame.pureHorizonForm false 1).mixed
      (euPreference utility)
      (fun i => PublicPolicy.toMixed offPathGame false 1
        (baseline false i)) :=
  offPathGame.isNash_toMixed_of_isNash_behavioral
    false utility (baseline false) 1 hnash

end GameTheory.Experimental.PostArchitecture.StochasticKuhn
