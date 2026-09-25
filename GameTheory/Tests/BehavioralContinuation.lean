import GameTheory.Protocol.BehavioralContinuation
import GameTheory.Tests.FOSGStrategic
import GameTheory.Tests.SingleMover
import GameTheory.Tests.SubgameRoots

/-! # Behavioral continuation admission controls

The simultaneous two-player fixture defeats arbitrary randomized deviations,
rejects a profitable unilateral deviation, and has the same equilibrium for
two certified evaluation bounds. The infinite-player fixture checks that
single-mover continuation Nash does not introduce ambient player finiteness.
-/

noncomputable section

namespace GameTheory.Tests.BehavioralContinuation

open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol
open GameTheory.Languages.NFG.OneShotFOSG
open GameTheory.Tests.FOSGStrategic

private theorem terminal_of_step {state target : source.execution.State}
    (joint : {joint // source.execution.Legal state joint})
    (realized : target ∈ (source.execution.step state joint).support) :
    source.execution.terminal target := by
  cases state with
  | initial =>
      rw [PMF.mem_support_pure_iff] at realized
      subst target
      trivial
  | finished actions => exact (joint.2.1 trivial).elim

private theorem initial_or_terminal (history : source.History) :
    history = source.execution.initHistory ∨ source.execution.terminal history.state := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start => exact Or.inl rfl
  | extend prior joint legal realized =>
      exact Or.inr (terminal_of_step ⟨joint, legal⟩ realized)

theorem simultaneous_bounded : source.execution.BoundedHorizon 1 := by
  intro state trace enough
  cases trace with
  | start => simp [Trace.length] at enough
  | extend prior joint legal realized => exact terminal_of_step ⟨joint, legal⟩ realized

theorem simultaneous_bounded_three : source.execution.BoundedHorizon 3 := by
  intro state trace enough
  exact simultaneous_bounded state trace (by omega)

/-- Both simultaneous players choose their strictly dominant action. Their
continuation optimum covers every behavioral replacement, including mixtures. -/
theorem simultaneous_behavioral_perfect :
    source.information.IsBehavioralSubgamePerfect simultaneous_bounded
      (behavioralProfile allTrueActions) sourceUtility := by
  intro history _
  rcases initial_or_terminal history with rfl | terminal
  · exact allTrue_isNash
  · rw [isNash_iff]
    intro who replacement
    have hpreferred := sourceUtility_integrable
      (source.information.runBehavioralFrom (behavioralProfile allTrueActions)
        1 history) who
    have halternative := sourceUtility_integrable
      (source.information.runBehavioralFrom
        (Profile.update (behavioralProfile allTrueActions) who replacement)
        1 history) who
    refine ⟨hpreferred, halternative, ?_⟩
    have hpreferredLaw := source.information.runBehavioralFrom_of_terminal
      (behavioralProfile allTrueActions) 1 terminal
    have halternativeLaw := source.information.runBehavioralFrom_of_terminal
      (Profile.update (behavioralProfile allTrueActions) who replacement) 1 terminal
    have hpure : UtilityIntegrable sourceUtility who (PMF.pure history) :=
      payoffIntegrable_pure history (fun outcome => sourceUtility outcome who)
    have hpreferredValue := expectedUtility_congr_law sourceUtility who
      hpreferredLaw hpreferred hpure
    have halternativeValue := expectedUtility_congr_law sourceUtility who
      halternativeLaw halternative hpure
    rw [expectedUtility_pure] at hpreferredValue halternativeValue
    rw [hpreferredValue, halternativeValue]

/-- The all-false profile has a profitable unilateral replacement at the
initial proper root, so the behavioral SPE predicate rejects it. -/
theorem simultaneous_not_behavioral_perfect :
    ¬ source.information.IsBehavioralSubgamePerfect simultaneous_bounded
      (behavioralProfile allFalseActions) sourceUtility := by
  intro perfect
  exact allFalse_not_isNash
    (perfect source.execution.initHistory source.information.initHistory_isSubgameRoot)

/-- Three units of certified fuel describe the same completed subgames. -/
theorem simultaneous_larger_bound :
    source.information.IsBehavioralSubgamePerfect simultaneous_bounded_three
      (behavioralProfile allTrueActions) sourceUtility :=
  (source.information.isBehavioralSubgamePerfect_bound_iff simultaneous_bounded
    simultaneous_bounded_three _ _).mp simultaneous_behavioral_perfect

private theorem simultaneous_terminates : source.execution.WellFoundedPlay := by
  apply source.execution.wellFoundedPlay_of_rank
    (fun state => match state with | .initial => 1 | .finished _ => 0)
  intro state target successor
  obtain ⟨joint, legal, realized⟩ := successor
  cases state with
  | initial =>
      rw [PMF.mem_support_pure_iff] at realized
      subst target
      exact Nat.zero_lt_one
  | finished actions => exact (legal.1 trivial).elim

/-- The finite-player pure implication consumes the behavioral result without
changing whole-policy deviations into one-shot deviations. -/
theorem simultaneous_pure_embedding :
    source.information.IsSubgamePerfect simultaneous_terminates
      (policyProfile GameTheory.Examples.FOSG.twoBitSource allTrueActions) sourceUtility :=
  source.information.isSubgamePerfect_of_behavioral simultaneous_bounded
    simultaneous_terminates _ sourceUtility simultaneous_behavioral_perfect

/-- Behavioral continuations inherit the same shared mixture-transfer theorem
as pure continuations. The identity compiler has point-mass deviation coverage. -/
theorem simultaneous_shared_transfer :
    source.information.IsBehavioralSubgamePerfect simultaneous_bounded
      (behavioralProfile allTrueActions) sourceUtility := by
  apply source.information.isContinuationNash_of_laws source.information
    (sourceSig := source.information.behavioralSignature)
    (targetSig := source.information.behavioralSignature)
    (sourcePlay := fun history profiles =>
      source.information.runBehavioralFrom profiles 1 history)
    (targetPlay := fun history profiles =>
      source.information.runBehavioralFrom profiles 1 history)
    (fun _ policy => policy) id id (behavioralProfile allTrueActions)
    (utility := sourceUtility)
  · intro history proper
    refine ⟨history, proper, rfl, ?_⟩
    intro who replacement
    refine ⟨PMF.pure replacement, ?_⟩
    simp only [PMF.pure_bind]
    rfl
  · intro history proper who replacement
    have hprofile :
        Profile.map (sig := source.information.behavioralSignature)
          (target := source.information.behavioralSignature)
          (fun _ strategy => strategy) (behavioralProfile allTrueActions) =
            behavioralProfile allTrueActions := by
      funext player
      rfl
    have hguard := sourceUtility_integrable
      (source.information.runBehavioralFrom
        (Profile.update (behavioralProfile allTrueActions) who replacement)
        1 history) who
    simpa only [hprofile, Function.id_def] using hguard
  · exact simultaneous_behavioral_perfect

/-- Honest compiled laws also use the shared reflection theorem at every
proper behavioral root. -/
theorem simultaneous_shared_reflection :
    source.information.IsBehavioralSubgamePerfect simultaneous_bounded
      (behavioralProfile allTrueActions) sourceUtility := by
  apply source.information.isContinuationNash_of_compiled_laws source.information
    (sourceSig := source.information.behavioralSignature)
    (targetSig := source.information.behavioralSignature)
    (sourcePlay := fun history profiles =>
      source.information.runBehavioralFrom profiles 1 history)
    (targetPlay := fun history profiles =>
      source.information.runBehavioralFrom profiles 1 history)
    (fun _ policy => policy) id id
    (profile := behavioralProfile allTrueActions) (utility := sourceUtility)
  · intro history proper
    exact ⟨history, proper, fun _ => rfl⟩
  · exact simultaneous_behavioral_perfect

/-- Existing imperfect-information root rejection remains the proper-root
criterion used by behavioral continuation Nash. -/
example : ¬ GameTheory.Tests.dealModel.IsSubgameRoot SubgameRoots.highDealHistory :=
  SubgameRoots.highDeal_not_isSubgameRoot

namespace InfinitePlayers

open GameTheory.Tests.SingleMover

/-- The genuinely random profile among natural-number players is a valid
single-mover continuation equilibrium for indifferent preferences. -/
theorem random_profile_perfect :
    model.IsSingleMoverBehavioralSubgamePerfect single bounded profile (fun _ _ => 0) := by
  rw [model.isSingleMoverBehavioralSubgamePerfect_iff single bounded]
  intro history _ who replacement
  refine ⟨payoffIntegrable_zero _, payoffIntegrable_zero _, ?_⟩
  simp [expectedUtility, expect_constant]

theorem bounded_four : protocol.BoundedHorizon 4 := by
  intro state trace enough
  exact bounded state trace (by omega)

/-- Horizon independence requires no finite-player instance. -/
theorem random_profile_larger_bound :
    model.IsSingleMoverBehavioralSubgamePerfect single bounded_four profile
      (fun _ _ => 0) :=
  (model.isSingleMoverBehavioralSubgamePerfect_bound_iff single bounded bounded_four
    profile (fun _ _ => 0)).mp random_profile_perfect

/-- The single-mover pure implication also type-checks for infinitely many
potential players; only a terminating protocol is required. -/
example (certificate : protocol.WellFoundedPlay)
    (policies : Profile model.strategicSignature) (utility : protocol.History → ℕ → ℝ)
    (perfect : model.IsSingleMoverBehavioralSubgamePerfect single bounded
      (Profile.map (target := model.behavioralSignature)
        (fun who (policy : model.Policy who) => policy.toBehavioral) policies) utility) :
    model.IsSubgamePerfect certificate policies utility :=
  model.isSubgamePerfect_of_singleMoverBehavioral single bounded certificate
    policies utility perfect

end InfinitePlayers

section FiniteSingleMover

variable {E : ExecutionProtocol Unit} (M : InformationModel E)

private theorem single (state : E.State) {first second : Unit}
    (_first : E.active state first) (_second : E.active state second) : first = second :=
  Subsingleton.elim _ _

/-- On a finite single-player protocol, both continuation forms literally
agree for arbitrary retained histories. -/
example (fuel : ℕ) (history : E.History) :
    M.toSingleMoverBehavioralContinuationGameForm single fuel history =
      M.toBehavioralContinuationGameForm fuel history :=
  M.toSingleMoverBehavioralContinuationGameForm_eq single fuel history

/-- The single-mover and simultaneous specializations share one SPE meaning. -/
example {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.behavioralSignature) (utility : E.History → Unit → ℝ) :
    M.IsSingleMoverBehavioralSubgamePerfect single bounded profile utility ↔
      M.IsBehavioralSubgamePerfect bounded profile utility :=
  M.isSingleMoverBehavioralSubgamePerfect_iff_behavioral single bounded profile utility

end FiniteSingleMover

end GameTheory.Tests.BehavioralContinuation
