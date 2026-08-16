/-
# General MAID strategic and equilibrium transfer

The native strategy coordinate for one player is its whole family of
decision-site-local behavioral rules. Decision sites are not relabelled as
players. The native frontier evaluator and the compiled EFG are presented as
ordinary `GameForm`s over those source-player coordinates.
-/

import GameTheory.Languages.MAID.FrontierEquivalence
import GameTheory.Protocol.Strategic
import GameTheory.Core.Approximate
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Languages.MAID.Strategic

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Protocol
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.FrontierEquivalence

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- The native strategic carrier assigns each source player its complete
family of site-local behavioral rules. -/
abbrev nativeBehavioralSignature
    (diagram : Structure Player Node) : GameSignature Player where
  Strategy := OwnerPolicy diagram
  Outcome := Assignment diagram

/-- Native order-free frontier evaluation as an ordinary strategic form. -/
@[reducible]
def nativeBehavioralGameForm
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) : GameForm Player where
  sig := nativeBehavioralSignature diagram
  play policy :=
    FinDist.map (fun reached => reached.values)
      (run diagram semantics policy (Fintype.card Node)
        (FrontierState.initial semantics))

@[simp]
theorem nativeBehavioralGameForm_play
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram)) :
    (nativeBehavioralGameForm semantics).play policy =
      FinDist.map (fun reached => reached.values)
        (run diagram semantics policy (Fintype.card Node)
          (FrontierState.initial semantics)) :=
  rfl

/-- The compiled behavioral EFG form, with complete histories forgotten to
their typed assignments. -/
@[reducible]
def compiledBehavioralGameForm
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [DecidableEq Node]
    (semantics : Semantics diagram) : GameForm Player :=
  ((information topological semantics).toBehavioralGameForm
      topological.order.length).mapOutcome
    (fun history =>
      Stage.assignment topological semantics history.state)

/-- The native and compiled forms agree on every embedded source policy
profile. -/
theorem native_play_eq_compiled_play
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram)) :
    (nativeBehavioralGameForm semantics).play policy =
      (compiledBehavioralGameForm topological semantics).play
        (behavioralProfile topological semantics policy) :=
  nativeRun_eq_compiledBehavioralRun topological semantics policy

/-- Recover the typed source value carried by one legal choice at an acting
information state. -/
def actingChoiceValue
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram)
    {owner : Player} (site : DecisionSite diagram owner)
    (observed : Config diagram (diagram.observedParents site.1))
    (choice :
      (information topological semantics).Choice owner
        (.acting site observed)) :
    diagram.Value site.1 :=
  choice.2.choose

theorem actingChoiceValue_spec
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram)
    {owner : Player} (site : DecisionSite diagram owner)
    (observed : Config diagram (diagram.observedParents site.1))
    (choice :
      (information topological semantics).Choice owner
        (.acting site observed)) :
    choice.1 =
      some ⟨site,
        actingChoiceValue topological semantics site observed choice⟩ :=
  choice.2.choose_spec

/-- Forget the compiled menu wrapper from one owner's behavioral policy. -/
def sourceOwnerPolicy
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram)
    (owner : Player)
    (behavioral :
      (information topological semantics).BehavioralPolicy owner) :
    OwnerPolicy diagram owner :=
  fun site observed =>
    FinDist.map
      (actingChoiceValue topological semantics site observed)
      (behavioral (.acting site observed))

/-- Encoding and then forgetting one source owner's local rules is the
identity. -/
theorem sourceOwnerPolicy_ownerBehavioralPolicy
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram)
    (owner : Player) (policy : OwnerPolicy diagram owner) :
    sourceOwnerPolicy topological semantics owner
        (ownerBehavioralPolicy topological semantics owner policy) =
      policy := by
  funext site observed
  unfold sourceOwnerPolicy ownerBehavioralPolicy
  rw [FinDist.map_comp]
  calc
    _ = FinDist.map id (policy site observed) := by
      apply congrArg (fun f => FinDist.map f (policy site observed))
      funext value
      have haction :=
        Option.some.inj
          (actingChoiceValue_spec topological semantics site observed
            ⟨some ⟨site, value⟩, ⟨value, rfl⟩⟩)
      exact eq_of_heq (Sigma.mk.inj_iff.mp haction).2.symm
    _ = _ := FinDist.map_id _

/-- Forgetting and then re-encoding an arbitrary compiled behavioral policy is
the identity, including its necessarily unique inactive choice. -/
theorem ownerBehavioralPolicy_sourceOwnerPolicy
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram)
    (owner : Player)
    (behavioral :
      (information topological semantics).BehavioralPolicy owner) :
    ownerBehavioralPolicy topological semantics owner
        (sourceOwnerPolicy topological semantics owner behavioral) =
      behavioral := by
  funext view
  cases view with
  | inactive =>
      let idle :
          (information topological semantics).Choice owner
            (.inactive : View diagram owner) :=
        ⟨none, rfl⟩
      have hsubsingleton :
          Subsingleton
            ((information topological semantics).Choice owner
              (.inactive : View diagram owner)) := by
        constructor
        intro first second
        apply Subtype.ext
        have hfirst : first.1 = none := by
          have hmem :
              first.1 ∈
                ({none} : Set (Option (Action diagram owner))) :=
            first.2
          exact hmem
        have hsecond : second.1 = none := by
          have hmem :
              second.1 ∈
                ({none} : Set (Option (Action diagram owner))) :=
            second.2
          exact hmem
        exact hfirst.trans hsecond.symm
      unfold ownerBehavioralPolicy
      rw [FinDist.eq_pure_of_subsingleton
        (behavioral (.inactive : View diagram owner)) idle]
  | acting site observed =>
      show
        FinDist.map
            (fun value =>
              (⟨some ⟨site, value⟩, ⟨value, rfl⟩⟩ :
                (information topological semantics).Choice owner
                  (.acting site observed)))
            (FinDist.map
              (actingChoiceValue topological semantics site observed)
              (behavioral (.acting site observed))) =
          behavioral (.acting site observed)
      rw [FinDist.map_comp]
      calc
        _ =
            FinDist.map id
              (behavioral (.acting site observed)) := by
          apply congrArg (fun f =>
            FinDist.map f (behavioral (.acting site observed)))
          funext choice
          apply Subtype.ext
          exact
            (actingChoiceValue_spec topological semantics
              site observed choice).symm
        _ = _ := FinDist.map_id _

/-- Source-owner local rules and compiled EFG behavioral policies are
equivalent coordinate by coordinate. -/
def ownerPolicyEquiv
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (owner : Player) :
    OwnerPolicy diagram owner ≃
      (information topological semantics).BehavioralPolicy owner where
  toFun := ownerBehavioralPolicy topological semantics owner
  invFun := sourceOwnerPolicy topological semantics owner
  left_inv :=
    sourceOwnerPolicy_ownerBehavioralPolicy
      topological semantics owner
  right_inv :=
    ownerBehavioralPolicy_sourceOwnerPolicy
      topological semantics owner

/-- The coordinate equivalences assemble into an equivalence between native
source-owner policy profiles and compiled EFG behavioral profiles. -/
def behavioralProfileEquiv
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) :
    Profile (nativeBehavioralSignature diagram) ≃
      Profile (information topological semantics).behavioralSignature where
  toFun := behavioralProfile topological semantics
  invFun := fun behavioral owner =>
    sourceOwnerPolicy topological semantics owner (behavioral owner)
  left_inv := fun policy => by
    funext owner
    exact sourceOwnerPolicy_ownerBehavioralPolicy
      topological semantics owner (policy owner)
  right_inv := fun behavioral => by
    funext owner
    exact ownerBehavioralPolicy_sourceOwnerPolicy
      topological semantics owner (behavioral owner)

@[simp]
theorem behavioralProfileEquiv_apply
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram)) :
    behavioralProfileEquiv topological semantics policy =
      behavioralProfile topological semantics policy :=
  rfl

/-- The profile equivalence sends one source-owner deviation to an update of
that same source owner in the compiled EFG. Decision sites never become
deviator coordinates. -/
theorem behavioralProfileEquiv_update
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram))
    (owner : Player) (replacement : OwnerPolicy diagram owner) :
    behavioralProfileEquiv topological semantics
        (Profile.update policy owner replacement) =
      Profile.update
        (behavioralProfileEquiv topological semantics policy)
        owner
        (ownerPolicyEquiv topological semantics owner replacement) := by
  funext other
  by_cases howner : other = owner
  · subst other
    simp [behavioralProfileEquiv, ownerPolicyEquiv,
      behavioralProfile, behavioralPolicy]
  · simp [behavioralProfileEquiv, ownerPolicyEquiv,
      behavioralProfile, behavioralPolicy, howner]

/-- The native/compiled play equality stated through the profile
equivalence. -/
theorem native_play_eq_compiled_play_equiv
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram)) :
    (nativeBehavioralGameForm semantics).play policy =
      (compiledBehavioralGameForm topological semantics).play
      (behavioralProfileEquiv topological semantics policy) :=
  native_play_eq_compiled_play topological semantics policy

/-- Native and compiled play commute with replacement of one source owner's
whole site-local policy family. -/
theorem native_play_update_eq_compiled_play_update
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram))
    (owner : Player) (replacement : OwnerPolicy diagram owner) :
    (nativeBehavioralGameForm semantics).play
        (Profile.update policy owner replacement) =
      (compiledBehavioralGameForm topological semantics).play
        (Profile.update
          (behavioralProfileEquiv topological semantics policy)
          owner
          (ownerPolicyEquiv topological semantics owner replacement)) := by
  calc
    _ =
        (compiledBehavioralGameForm topological semantics).play
          (behavioralProfileEquiv topological semantics
            (Profile.update policy owner replacement)) :=
      native_play_eq_compiled_play_equiv topological semantics _
    _ = _ :=
      congrArg (compiledBehavioralGameForm topological semantics).play
        (behavioralProfileEquiv_update topological semantics
          policy owner replacement)

/-- The same update law oriented around an arbitrary compiled behavioral
deviation. -/
theorem native_play_update_symm_eq_compiled_play_update
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram))
    (owner : Player)
    (replacement :
      (information topological semantics).BehavioralPolicy owner) :
    (nativeBehavioralGameForm semantics).play
        (Profile.update policy owner
          ((ownerPolicyEquiv topological semantics owner).symm
            replacement)) =
      (compiledBehavioralGameForm topological semantics).play
        (Profile.update
          (behavioralProfileEquiv topological semantics policy)
          owner replacement) := by
  simpa using
    native_play_update_eq_compiled_play_update topological semantics
      policy owner
        ((ownerPolicyEquiv topological semantics owner).symm replacement)

/-- Every compiled behavioral profile is the image of a source-owner policy
profile, and its assignment law is the native law of that inverse image. -/
theorem native_play_symm_eq_compiled_play
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram)
    (behavioral :
      Profile (information topological semantics).behavioralSignature) :
    (nativeBehavioralGameForm semantics).play
        ((behavioralProfileEquiv topological semantics).symm behavioral) =
      (compiledBehavioralGameForm topological semantics).play behavioral := by
  rw [native_play_eq_compiled_play]
  exact congrArg
    (compiledBehavioralGameForm topological semantics).play
    ((behavioralProfileEquiv topological semantics).apply_symm_apply
      behavioral)

/-- Native and compiled MAID forms preserve approximate Nash equilibrium at
the same slack. A unilateral deviation remains replacement of one source
owner's complete family of site-local rules. -/
theorem isεNash_native_iff_compiled
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (ε : ℝ)
    (policy : Profile (nativeBehavioralSignature diagram)) :
    IsεNash (nativeBehavioralGameForm semantics)
        (fun assignment owner => semantics.utility owner assignment)
        ε policy ↔
      IsεNash (compiledBehavioralGameForm topological semantics)
        (fun assignment owner => semantics.utility owner assignment)
        ε (behavioralProfileEquiv topological semantics policy) := by
  apply
    (isεNash_iff_of_profileEquiv_of_expectedUtility_eq
      (nativeBehavioralGameForm semantics)
      (compiledBehavioralGameForm topological semantics)
      (fun assignment owner => semantics.utility owner assignment)
      (fun assignment owner => semantics.utility owner assignment)
      (behavioralProfileEquiv topological semantics)
      (fun sourceProfile owner replacement =>
        ⟨ownerPolicyEquiv topological semantics owner replacement,
          behavioralProfileEquiv_update topological semantics
            sourceProfile owner replacement⟩)
      (fun sourceProfile owner targetReplacement =>
        ⟨(ownerPolicyEquiv topological semantics owner).symm
            targetReplacement,
          by
            funext other
            have hupdate := congrFun
              (behavioralProfileEquiv_update topological semantics
                sourceProfile owner
                ((ownerPolicyEquiv topological semantics owner).symm
                  targetReplacement))
              other
            calc
              _ = Profile.update
                  (behavioralProfileEquiv topological semantics sourceProfile)
                  owner
                  (ownerPolicyEquiv topological semantics owner
                    ((ownerPolicyEquiv topological semantics owner).symm
                      targetReplacement)) other := hupdate
              _ = _ := by
                rw [(ownerPolicyEquiv topological semantics owner).apply_symm_apply]
                rfl⟩)
      (fun targetProfile owner =>
        congrArg
          (expectedUtility
            (fun assignment owner => semantics.utility owner assignment)
            owner)
          (native_play_symm_eq_compiled_play topological semantics
            targetProfile).symm)
      ε policy).symm

/-- Native behavioral Nash equilibrium is exactly
behavioral Nash equilibrium of the compiled EFG after histories are forgotten
to typed assignments. Deviations range over source players; one deviation
replaces all and only that owner's site-local rules. -/
theorem isNash_native_iff_compiled
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram)) :
    IsNash (nativeBehavioralGameForm semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment)
        policy ↔
      IsNash (compiledBehavioralGameForm topological semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment)
        (behavioralProfileEquiv topological semantics policy) := by
  rw [isNash_iff_isεNash_zero, isNash_iff_isεNash_zero]
  exact isεNash_native_iff_compiled topological semantics 0 policy

end GameTheory.Languages.MAID.Strategic
