/-
# Local semantic discharge for one-site MAID observation reduction

This experiment isolates the graph-free bridge needed by a future graphical
requisite-information theorem.  A single target owner has one decision site;
only that site's observation domain may be pruned.  Every other owner's policy
space is therefore represented exactly.

`LocalUtilityFactorsAt` is deliberately stronger and more structured than
deviation coverage.  It says that, uniformly over every full target-owner
replacement, canonical native expected utility factors through one law of
full observation contexts and a continuation value that sees only the kept
context and chosen action.  It contains neither a reduced replacement nor a
preference inequality.

Kernel marginalization then constructs a signal-blind rule with exactly the
same kept-context/action law.  The result discharges the existing
`ObservationPruning.CoversFullDeviationsAt` certificate.  No graphical
soundness claim is made here.
-/

import GameTheory.Languages.MAID.ObservationPruning
import GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDLocalReduction

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- If pruning changes none of one owner's observation domains, every full
owner policy has an exact reduced preimage. -/
theorem expandOwnerPolicy_surjective_of_kept_eq_observed
    (pruning : Pruning diagram) (owner : Player)
    (hkept : ∀ site : DecisionSite diagram owner,
      pruning.kept site.1 = diagram.observedParents site.1) :
    Function.Surjective (pruning.expandOwnerPolicy owner) := by
  intro full
  have hobservedKept : ∀ site : DecisionSite diagram owner,
      diagram.observedParents site.1 ⊆ pruning.kept site.1 := by
    intro site
    rw [hkept site]
  let reduced : pruning.ReducedOwnerPolicy owner := fun site observed =>
    full site (Config.restrict (hobservedKept site) observed)
  refine ⟨reduced, ?_⟩
  funext site observed
  unfold Pruning.expandOwnerPolicy
  dsimp only [reduced]
  apply congrArg (full site)
  funext node
  rfl

/-- The honest scope of the first local-reduction theorem.  The target owner
has exactly one decision site, and pruning leaves every other owner's
observation domains unchanged. -/
structure IsSingleSitePruningAt (pruning : Pruning diagram)
    (owner : Player) (target : DecisionSite diagram owner) : Prop where
  target_unique : ∀ site : DecisionSite diagram owner, site = target
  kept_eq_observed_of_ne : ∀ {other : Player}, other ≠ owner →
    ∀ site : DecisionSite diagram other,
      pruning.kept site.1 = diagram.observedParents site.1

/-- A graph-free local semantic factorization.  One context law works
uniformly for every full target-owner replacement, and continuation utility
sees only the kept observation and the action at the unique target site.

This proposition does not mention a reduced replacement, deviation coverage,
or a preference comparison. -/
def LocalUtilityFactorsAt
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner) : Prop :=
  ∃ contextLaw :
      PMF (Config diagram (diagram.observedParents target.1)),
    ∃ continuation :
        Config diagram (pruning.kept target.1) →
          diagram.Value target.1 → ℝ,
      (∀ replacement : OwnerPolicy diagram owner,
        ∃ hplay : UtilityIntegrable
            (fun assignment who => semantics.utility who assignment)
            owner
            ((nativeBehavioralGameForm semantics).play
              (Profile.update (pruning.expandPolicy policy)
                owner replacement)),
          ∃ hjoint : PayoffIntegrable
            (fullJoint contextLaw
              (Config.restrict (pruning.kept_sub_observed target.1))
              (replacement target))
            (fun result => continuation result.1 result.2),
            expectedUtility
                (fun assignment who => semantics.utility who assignment)
                owner
                ((nativeBehavioralGameForm semantics).play
                  (Profile.update (pruning.expandPolicy policy)
                    owner replacement)) hplay =
              expect (fullJoint contextLaw
                (Config.restrict (pruning.kept_sub_observed target.1))
                (replacement target))
                (fun result => continuation result.1 result.2) hjoint) ∧
      (∀ (other : Player), other ≠ owner →
        ∀ replacement : OwnerPolicy diagram other,
          UtilityIntegrable
            (fun assignment who => semantics.utility who assignment)
            other
            ((nativeBehavioralGameForm semantics).play
              (Profile.update (pruning.expandPolicy policy)
                other replacement)))

/-- Turn one reduced rule into the target owner's complete reduced policy when
that owner has no other decision site. -/
def reducedOwnerPolicyOfUniqueSite (pruning : Pruning diagram)
    (owner : Player) (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (kernel : Config diagram (pruning.kept target.1) →
      PMF (diagram.Value target.1)) :
    pruning.ReducedOwnerPolicy owner :=
  fun site observed => by
    have hsite := hunique site
    subst site
    exact kernel observed

@[simp]
theorem reducedOwnerPolicyOfUniqueSite_target
    (pruning : Pruning diagram) (owner : Player)
    (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (kernel : Config diagram (pruning.kept target.1) →
      PMF (diagram.Value target.1))
    (observed : Config diagram (pruning.kept target.1)) :
    reducedOwnerPolicyOfUniqueSite pruning owner target hunique kernel
        target observed =
      kernel observed := by
  simp [reducedOwnerPolicyOfUniqueSite]

theorem reducedNativeGameForm_play
    (pruning : Pruning diagram) [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy) :
    (pruning.reducedNativeGameForm semantics).play policy =
      (nativeBehavioralGameForm semantics).play
        (pruning.expandPolicy policy) :=
  rfl

/-- A uniform local utility factorization constructs the exact semantic
coverage certificate for one-site pruning.  The target deviation is
marginalized over removed observations; every other owner's deviation is
represented literally. -/
theorem coversFullDeviationsAt_of_localUtilityFactorsAt
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (shape : IsSingleSitePruningAt pruning owner target)
    (hfactor : LocalUtilityFactorsAt pruning semantics policy owner target) :
    pruning.CoversFullDeviationsAt semantics policy := by
  obtain ⟨contextLaw, continuation, hutility, hother⟩ := hfactor
  intro deviator fullReplacement
  by_cases hdeviator : deviator = owner
  · subst deviator
    let keep :
        Config diagram (diagram.observedParents target.1) →
          Config diagram (pruning.kept target.1) :=
      Config.restrict (pruning.kept_sub_observed target.1)
    let averaged : Config diagram (pruning.kept target.1) →
        PMF (diagram.Value target.1) :=
      averagedKernel contextLaw keep (fullReplacement target)
    let reducedReplacement : pruning.ReducedOwnerPolicy owner :=
      reducedOwnerPolicyOfUniqueSite pruning owner target
        shape.target_unique averaged
    refine ⟨reducedReplacement, ?_⟩
    rw [euPreference_apply, reducedNativeGameForm_play,
      pruning.expandPolicy_update]
    have hexpandedTarget :
        pruning.expandOwnerPolicy owner reducedReplacement target =
          fun observed => averaged (keep observed) := by
      funext observed
      unfold Pruning.expandOwnerPolicy
      dsimp only [reducedReplacement]
      rw [reducedOwnerPolicyOfUniqueSite_target]
    obtain ⟨hfullPlay, hfullJoint, hfullEq⟩ := hutility fullReplacement
    obtain ⟨hredPlay, hredJoint, hredEq⟩ := hutility
      (pruning.expandOwnerPolicy owner reducedReplacement)
    have hjoint := fullJoint_eq_fullJoint_averagedKernel
      contextLaw keep (fullReplacement target)
    have hredLaw :
        fullJoint contextLaw keep
            (pruning.expandOwnerPolicy owner reducedReplacement target) =
          fullJoint contextLaw keep
            (fun context => averaged (keep context)) :=
      congrArg (fullJoint contextLaw keep) hexpandedTarget
    have hredJoint' : PayoffIntegrable
        (fullJoint contextLaw keep
          (fun context => averaged (keep context)))
        (fun result => continuation result.1 result.2) :=
      payoffIntegrable_congr_law hredLaw hredJoint
    refine ⟨hredPlay, hfullPlay, le_of_eq ?_⟩
    calc
      expectedUtility
          (fun assignment who => semantics.utility who assignment)
          owner
          ((nativeBehavioralGameForm semantics).play
            (Profile.update (pruning.expandPolicy policy)
              owner fullReplacement)) hfullPlay =
          expect (fullJoint contextLaw keep (fullReplacement target))
            (fun result => continuation result.1 result.2) hfullJoint := hfullEq
      _ = expect (fullJoint contextLaw keep
            (fun context => averaged (keep context)))
            (fun result => continuation result.1 result.2) hredJoint' :=
        expect_congr_law hjoint _ hfullJoint hredJoint'
      _ = expectedUtility
            (fun assignment who => semantics.utility who assignment)
            owner
            ((nativeBehavioralGameForm semantics).play
              (Profile.update (pruning.expandPolicy policy) owner
                (pruning.expandOwnerPolicy owner reducedReplacement)))
            hredPlay := by
        calc
          _ = expect (fullJoint contextLaw keep
                (pruning.expandOwnerPolicy owner reducedReplacement target))
                (fun result => continuation result.1 result.2)
                hredJoint :=
            (expect_congr_law hredLaw _ hredJoint hredJoint').symm
          _ = _ := hredEq.symm
  · have hkept : ∀ site : DecisionSite diagram deviator,
        pruning.kept site.1 = diagram.observedParents site.1 :=
      shape.kept_eq_observed_of_ne hdeviator
    obtain ⟨reducedReplacement, hexpand⟩ :=
      expandOwnerPolicy_surjective_of_kept_eq_observed
        pruning deviator hkept fullReplacement
    refine ⟨reducedReplacement, ?_⟩
    rw [euPreference_apply, reducedNativeGameForm_play,
      pruning.expandPolicy_update, hexpand]
    have hguard := hother deviator hdeviator fullReplacement
    exact ⟨hguard, hguard, le_refl _⟩

end GameTheory.Experimental.PostArchitecture.MAIDLocalReduction
