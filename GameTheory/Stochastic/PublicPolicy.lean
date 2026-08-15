/-
# Proof-facing public stochastic policies

Callers can reason with ordinary actions and proof-free public histories while
the perfect-monitoring Protocol model remains the sole execution semantics.
The translation is lossless and respects unilateral profile replacement.
-/

import GameTheory.Stochastic.FiniteHorizon

noncomputable section

namespace GameTheory.Stochastic

open GameTheory.Math.Probability Stochastic Protocol

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Stochastic.Game.{uι, us, ua} ι)

/-- A stochastic-facing behavioral policy: after a proof-free public history,
draw one ordinary action. -/
abbrev PublicPolicy (i : ι) : Type _ :=
  G.PublicHistory → FinDist (G.Action i)

/-- The direct public-policy signature uses the canonical Protocol history as
its outcome, but its strategies contain no legal-choice subtype or `Option`. -/
abbrev publicSignature (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    GameSignature ι where
  Strategy := PublicPolicy G
  Outcome := (G.toExecution initial).History

/-- Profiles of ordinary public-history policies. -/
abbrev PublicProfile (initial : G.State) [∀ i, Nonempty (G.Action i)] :=
  Profile (publicSignature G initial)

namespace PublicPolicy

/-- Shift one ordinary public policy past an already observed
reverse-chronological prefix. -/
def after {G : Stochastic.Game ι} {i : ι}
    (policy : PublicPolicy G i) (observed : G.PublicHistory) :
    PublicPolicy G i :=
  fun continuation => policy (continuation ++ observed)

end PublicPolicy

namespace PublicProfile

/-- Shift every ordinary public policy past an already observed prefix. -/
def after {G : Stochastic.Game ι} {initial restart : G.State}
    [∀ i, Nonempty (G.Action i)]
    (profile : PublicProfile G initial) (observed : G.PublicHistory) :
    PublicProfile G restart :=
  fun i => PublicPolicy.after (profile i) observed

@[simp]
theorem after_apply {G : Stochastic.Game ι} {initial restart : G.State}
    [∀ i, Nonempty (G.Action i)]
    (profile : PublicProfile G initial) (observed continuation : G.PublicHistory)
    (i : ι) :
    (after (restart := restart) profile observed) i continuation =
      profile i (continuation ++ observed) :=
  rfl

end PublicProfile

/-- The all-active perfect-monitoring menu is equivalent to the underlying
action carrier.  In particular, the translation does not choose a fallback. -/
def actionChoiceEquiv (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (i : ι) (history : G.PublicHistory) :
    G.Action i ≃ (G.perfectMonitoring initial).Choice i history where
  toFun action := ⟨some action, ⟨action, rfl⟩⟩
  invFun choice := choice.1.get <| by
    rcases choice.2 with ⟨action, haction⟩
    simp [haction]
  left_inv action := Option.get_some action _
  right_inv choice :=
    Subtype.ext (Option.some_get (x := choice.1) _)

/-- Compile an ordinary public-history policy into the canonical behavioral
Protocol policy. -/
def toBehavioralPolicy (initial : G.State) [∀ i, Nonempty (G.Action i)]
    {i : ι} (policy : PublicPolicy G i) :
    (G.perfectMonitoring initial).BehavioralPolicy i :=
  fun history => FinDist.map (actionChoiceEquiv G initial i history) (policy history)

/-- Decode a canonical all-active behavioral policy back to ordinary actions. -/
def ofBehavioralPolicy (initial : G.State) [∀ i, Nonempty (G.Action i)]
    {i : ι} (policy : (G.perfectMonitoring initial).BehavioralPolicy i) :
    PublicPolicy G i :=
  fun history =>
    FinDist.map (actionChoiceEquiv G initial i history).symm (policy history)

@[simp]
theorem ofBehavioralPolicy_toBehavioralPolicy
    (initial : G.State) [∀ i, Nonempty (G.Action i)] {i : ι}
    (policy : PublicPolicy G i) :
    ofBehavioralPolicy G initial (toBehavioralPolicy G initial policy) = policy := by
  funext history
  let equivalence := actionChoiceEquiv G initial i history
  have hround : equivalence.symm ∘ equivalence = id := by
    funext action
    exact equivalence.symm_apply_apply action
  show FinDist.map equivalence.symm (FinDist.map equivalence (policy history)) =
    policy history
  rw [FinDist.map_comp, hround, FinDist.map_id]

@[simp]
theorem toBehavioralPolicy_ofBehavioralPolicy
    (initial : G.State) [∀ i, Nonempty (G.Action i)] {i : ι}
    (policy : (G.perfectMonitoring initial).BehavioralPolicy i) :
    toBehavioralPolicy G initial (ofBehavioralPolicy G initial policy) = policy := by
  funext history
  let equivalence := actionChoiceEquiv G initial i history
  have hround : equivalence ∘ equivalence.symm = id := by
    funext choice
    exact equivalence.apply_symm_apply choice
  show FinDist.map equivalence (FinDist.map equivalence.symm (policy history)) =
    policy history
  rw [FinDist.map_comp, hround, FinDist.map_id]

/-- Public stochastic policies and canonical perfect-monitoring behavioral
policies are the same data, up to the proved legal-choice presentation. -/
def policyEquiv (initial : G.State) [∀ i, Nonempty (G.Action i)] (i : ι) :
    PublicPolicy G i ≃ (G.perfectMonitoring initial).BehavioralPolicy i where
  toFun := toBehavioralPolicy G initial
  invFun := ofBehavioralPolicy G initial
  left_inv := ofBehavioralPolicy_toBehavioralPolicy G initial
  right_inv := toBehavioralPolicy_ofBehavioralPolicy G initial

/-- Compile a whole public-policy profile to the canonical Protocol profile. -/
def toBehaviorProfile (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : PublicProfile G initial) : G.BehaviorProfile initial :=
  fun i => toBehavioralPolicy G initial (profile i)

/-- Decode a canonical Protocol profile to ordinary public policies. -/
def ofBehaviorProfile (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) : PublicProfile G initial :=
  fun i => ofBehavioralPolicy G initial (profile i)

@[simp]
theorem ofBehaviorProfile_toBehaviorProfile
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : PublicProfile G initial) :
    ofBehaviorProfile G initial (toBehaviorProfile G initial profile) = profile := by
  funext i
  exact ofBehavioralPolicy_toBehavioralPolicy G initial (profile i)

@[simp]
theorem toBehaviorProfile_ofBehaviorProfile
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) :
    toBehaviorProfile G initial (ofBehaviorProfile G initial profile) = profile := by
  funext i
  exact toBehavioralPolicy_ofBehavioralPolicy G initial (profile i)

/-- The lossless translation of whole profiles. -/
def profileEquiv (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    PublicProfile G initial ≃ G.BehaviorProfile initial where
  toFun := toBehaviorProfile G initial
  invFun := ofBehaviorProfile G initial
  left_inv := ofBehaviorProfile_toBehaviorProfile G initial
  right_inv := toBehaviorProfile_ofBehaviorProfile G initial

/-- Embed an ordinary simultaneous action as the unique all-active legal joint
choice expected by the canonical execution. -/
def canonicalJoint (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (state : G.State) (actions : ∀ i, G.Action i) :
    {joint : ∀ i, Option ((G.toExecution initial).Action i) //
      (G.toExecution initial).Legal state joint} :=
  ⟨fun i => some (actions i), by
    constructor
    · show ¬False
      simp
    · intro i
      show True ∧ actions i ∈ Set.univ
      simp⟩

@[simp]
theorem toExecution_step_canonicalJoint
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (state : G.State) (actions : ∀ i, G.Action i) :
    (G.toExecution initial).step state (canonicalJoint G initial state actions) =
      G.transition state actions := by
  simpa only [canonicalJoint] using
    G.toExecution_step_some initial state actions

/-- Transport a native stochastic transition witness across the named
canonical-step equality. -/
theorem canonicalRealized (initial : G.State) [∀ i, Nonempty (G.Action i)]
    {state target : G.State} {actions : ∀ i, G.Action i}
    (realized : target ∈ (G.transition state actions).support) :
    target ∈ ((G.toExecution initial).step state
      (canonicalJoint G initial state actions)).support := by
  rw [toExecution_step_canonicalJoint G initial]
  exact realized

/-- One native stochastic transition, viewed as a canonical Protocol event. -/
def canonicalEvent (initial : G.State) [∀ i, Nonempty (G.Action i)]
    {state target : G.State} (actions : ∀ i, G.Action i)
    (realized : target ∈ (G.transition state actions).support) :
    (G.toExecution initial).StepEvent where
  source := state
  joint := canonicalJoint G initial state actions
  isLegal := (canonicalJoint G initial state actions).2
  target := target
  realized := canonicalRealized G initial realized

@[simp]
theorem stageRecordOfCanonicalEvent_joint
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    {state target : G.State} (actions : ∀ i, G.Action i)
    (realized : target ∈ (G.transition state actions).support) :
    (G.stageRecordOfEvent initial
      (canonicalEvent G initial actions realized)).joint = actions := by
  funext i
  have hjoint := G.stageRecordOfEvent_joint initial
    (canonicalEvent G initial actions realized) i
  have hjoint' : some (actions i) = some
      ((G.stageRecordOfEvent initial
        (canonicalEvent G initial actions realized)).joint i) := by
    simpa only [canonicalEvent, canonicalJoint] using hjoint
  exact (Option.some.inj hjoint').symm

@[simp]
theorem eventUtility_canonicalEvent
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    {state target : G.State} (actions : ∀ i, G.Action i)
    (realized : target ∈ (G.transition state actions).support) (who : ι) :
    G.eventUtility initial (canonicalEvent G initial actions realized) who =
      G.stageUtility state actions who := by
  show G.stageUtility state
    (G.stageRecordOfEvent initial
      (canonicalEvent G initial actions realized)).joint who =
    G.stageUtility state actions who
  rw [stageRecordOfCanonicalEvent_joint G initial]

section FinitePlayers

variable [Fintype ι]

/-- At one public history, canonical behavioral play is exactly the independent
product of the ordinary action laws, followed by the legal joint embedding. -/
theorem behavioralJoint_toBehaviorProfile
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : PublicProfile G initial) {state : G.State}
    (trace : (G.toExecution initial).Trace state)
    (hterm : ¬ (G.toExecution initial).terminal state) :
    (G.perfectMonitoring initial).behavioralJoint
        (toBehaviorProfile G initial profile) trace hterm =
      FinDist.map (canonicalJoint G initial state)
        (FinDist.pi fun i =>
          profile i ((G.perfectMonitoring initial).infoOf i trace)) := by
  unfold InformationModel.behavioralJoint toBehaviorProfile toBehavioralPolicy
  rw [FinDist.pi_map, FinDist.map_comp]
  apply congrArg (fun f => FinDist.map f _)
  funext actions
  apply Subtype.ext
  funext i
  rfl

/-- One canonical execution step, exposed in ordinary stochastic actions and
transitions. The right side still continues with the sole Protocol runner. -/
theorem runBehavioralFrom_succ_toBehaviorProfile
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : PublicProfile G initial) (fuel : ℕ)
    (history : (G.toExecution initial).History) :
    (G.perfectMonitoring initial).runBehavioralFrom
        (toBehaviorProfile G initial profile) (fuel + 1) history =
      (FinDist.pi fun i =>
          profile i ((G.perfectMonitoring initial).infoOf i history.trace)).bind
        fun actions =>
          (G.transition history.state actions).bindOnSupport fun _ realized =>
            (G.perfectMonitoring initial).runBehavioralFrom
              (toBehaviorProfile G initial profile) fuel
              (history.extend (canonicalJoint G initial history.state actions).2
                (canonicalRealized G initial realized)) := by
  have hterm : ¬ (G.toExecution initial).terminal history.state := by
    show ¬False
    simp
  rw [(G.perfectMonitoring initial).runBehavioralFrom_succ_of_not_terminal
      (toBehaviorProfile G initial profile) fuel hterm,
    behavioralJoint_toBehaviorProfile G initial profile history.trace hterm]
  simp only [FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind]
  apply FinDist.bind_congr
  intro actions _
  have hstep := toExecution_step_canonicalJoint G initial history.state actions
  cases hstep
  apply FinDist.bindOnSupport_congr
  intro target realized
  rfl

end FinitePlayers

/-- Compiling a unilateral replacement changes exactly that player's
canonical behavioral policy. -/
theorem toBehaviorProfile_update [DecidableEq ι]
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : PublicProfile G initial) (who : ι)
    (replacement : PublicPolicy G who) :
    toBehaviorProfile G initial (Profile.update profile who replacement) =
      Profile.update (toBehaviorProfile G initial profile) who
        (toBehavioralPolicy G initial replacement) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [toBehaviorProfile]
  · simp [toBehaviorProfile, Profile.update_of_ne, hi]

end Game

end GameTheory.Stochastic
