/-
# Observation pruning for typed MAIDs

A pruning chooses a smaller observed-parent set at every decision site.  The
reduced policy domain remains grouped by source owner and expands canonically
to the accepted site-local MAID policy by restricting each full observation.

This is the semantic target for later graphical requisite tests.  It does not
call a parent irrelevant merely because a graph predicate says so.  Exact law
transfer uses literal policy representation; safe equilibrium reduction uses
the stronger certificate that every omitted full deviation is weakly covered
by a reduced deviation.  Both directions are proved against the canonical
native and compiled forms.
-/

import GameTheory.Languages.MAID.Strategic

noncomputable section

namespace GameTheory.Languages.MAID.ObservationPruning

open GameTheory
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.ToEFG

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- A proposed smaller information domain for every decision site. -/
structure Pruning (diagram : Structure Player Node) where
  kept : Node → Finset Node
  kept_sub_observed : ∀ node,
    kept node ⊆ diagram.observedParents node

namespace Config

/-- Restrict an observed-parent configuration to a smaller node set. -/
def restrict {small large : Finset Node} (subset : small ⊆ large)
    (configuration : Config diagram large) : Config diagram small :=
  fun node => configuration ⟨node.1, subset node.2⟩

end Config

namespace Pruning

/-- One owner's policy family after observation pruning. Decision sites remain
grouped by their source owner. -/
abbrev ReducedOwnerPolicy (pruning : Pruning diagram) (owner : Player) :=
  (site : DecisionSite diagram owner) →
    Config diagram (pruning.kept site.1) →
      GameTheory.Math.Probability.FinDist (diagram.Value site.1)

/-- A complete profile over the pruned observation domains. -/
abbrev ReducedPolicy (pruning : Pruning diagram) :=
  (owner : Player) → ReducedOwnerPolicy pruning owner

/-- Expand a pruned owner policy by forgetting the removed observations. -/
def expandOwnerPolicy (pruning : Pruning diagram) (owner : Player)
    (policy : ReducedOwnerPolicy pruning owner) : OwnerPolicy diagram owner :=
  fun site observed =>
    policy site
      (Config.restrict (pruning.kept_sub_observed site.1) observed)

/-- Expand every source owner's pruned policy. -/
def expandPolicy (pruning : Pruning diagram)
    (policy : ReducedPolicy pruning) : Policy diagram :=
  fun owner => pruning.expandOwnerPolicy owner (policy owner)

/-- A full policy is represented by the proposed pruning when it is literally
the expansion of some reduced policy. -/
def Represents (pruning : Pruning diagram) (full : Policy diagram) : Prop :=
  ∃ reduced : ReducedPolicy pruning, pruning.expandPolicy reduced = full

/-- The pruned strategic carrier has one coordinate per source owner and
complete assignments as outcomes. -/
abbrev reducedBehavioralSignature (pruning : Pruning diagram) :
    GameSignature Player where
  Strategy := ReducedOwnerPolicy pruning
  Outcome := Assignment diagram

/-- Native frontier evaluation restricted to policies that use only the kept
observations. -/
@[reducible]
def reducedNativeGameForm (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) : GameForm Player where
  sig := reducedBehavioralSignature pruning
  play policy :=
    (nativeBehavioralGameForm semantics).play
      (pruning.expandPolicy policy)

/-- Compiled EFG evaluation on the same reduced source-owner policy domain. -/
@[reducible]
def reducedCompiledGameForm (pruning : Pruning diagram)
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [DecidableEq Node] (semantics : Semantics diagram) : GameForm Player where
  sig := reducedBehavioralSignature pruning
  play policy :=
    (compiledBehavioralGameForm topological semantics).play
      (behavioralProfile topological semantics
        (pruning.expandPolicy policy))

/-- Expanding a unilateral reduced-policy update changes only the same source
owner in the full native profile. -/
theorem expandPolicy_update (pruning : Pruning diagram)
    [DecidableEq Player] (policy : ReducedPolicy pruning)
    (owner : Player) (replacement : ReducedOwnerPolicy pruning owner) :
    pruning.expandPolicy
        (Profile.update (sig := pruning.reducedBehavioralSignature)
          policy owner replacement) =
      Profile.update (sig := nativeBehavioralSignature diagram)
        (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner replacement) := by
  funext other
  by_cases howner : other = owner
  · subst other
    simp [expandPolicy]
  · simp [expandPolicy, howner]

/-- Native and compiled assignment laws remain exact after restricting the
policy domain. -/
theorem reducedNative_play_eq_reducedCompiled_play
    (pruning : Pruning diagram)
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning) :
    (pruning.reducedNativeGameForm semantics).play policy =
      (pruning.reducedCompiledGameForm topological semantics).play policy :=
  native_play_eq_compiled_play topological semantics
    (pruning.expandPolicy policy)

/-- A represented full policy has exactly the reduced native assignment law. -/
theorem native_play_eq_reducedNative_play_of_expands
    (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (full : Policy diagram)
    (reduced : ReducedPolicy pruning)
    (hexpands : pruning.expandPolicy reduced = full) :
    (nativeBehavioralGameForm semantics).play full =
      (pruning.reducedNativeGameForm semantics).play reduced := by
  rw [← hexpands]

/-- A represented full policy has exactly the reduced compiled assignment
law, for every accepted topological serialization. -/
theorem compiled_play_eq_reducedCompiled_play_of_expands
    (pruning : Pruning diagram)
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [DecidableEq Node] (semantics : Semantics diagram)
    (full : Policy diagram) (reduced : ReducedPolicy pruning)
    (hexpands : pruning.expandPolicy reduced = full) :
    (compiledBehavioralGameForm topological semantics).play
        (behavioralProfile topological semantics full) =
      (pruning.reducedCompiledGameForm topological semantics).play reduced := by
  rw [← hexpands]

/-! ## Safe reduction -/

/-- A reduced profile covers the original full deviation space when every full
owner-policy replacement is weakly dominated, for that owner, by some reduced
replacement.  This is the semantic certificate needed for safe information
removal: unlike `Represents`, it constrains deviations that are not themselves
in the image of `expandPolicy`.

The certificate is profile-local because a removed observation may be
irrelevant against one fixed collection of opposing policies and strategically
live against another.  A graphical requisite-information theorem can discharge
this condition uniformly when its stronger structural hypotheses hold. -/
def CoversFullDeviationsAt (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning) : Prop :=
  ∀ owner (fullReplacement : OwnerPolicy diagram owner),
    ∃ reducedReplacement : ReducedOwnerPolicy pruning owner,
      euPreference (fun assignment who => semantics.utility who assignment)
        owner
        ((pruning.reducedNativeGameForm semantics).play
          (Profile.update policy owner reducedReplacement))
        ((nativeBehavioralGameForm semantics).play
          (Profile.update (pruning.expandPolicy policy) owner fullReplacement))

/-- Deviation coverage gives the load-bearing safe-reduction direction: Nash
in the smaller policy space remains Nash against every original full-policy
deviation after expansion. -/
theorem isNash_expanded_of_isNash_reduced
    (pruning : Pruning diagram)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning)
    (hcover : pruning.CoversFullDeviationsAt semantics policy)
    (hnash : IsNash (pruning.reducedNativeGameForm semantics)
      (euPreference fun assignment owner => semantics.utility owner assignment)
      policy) :
    IsNash (nativeBehavioralGameForm semantics)
      (euPreference fun assignment owner => semantics.utility owner assignment)
      (pruning.expandPolicy policy) := by
  rw [isNash_iff] at hnash ⊢
  intro owner fullReplacement
  obtain ⟨reducedReplacement, hcovered⟩ :=
    hcover owner fullReplacement
  have hreduced := hnash owner reducedReplacement
  rw [euPreference_apply] at hcovered hreduced ⊢
  exact hcovered.trans hreduced

/-- Every expanded full-space Nash profile covers all full deviations: choose
the owner's current reduced policy as the covering replacement.  Thus coverage
is not merely a convenient sufficient certificate; together with reduced Nash
it is the exact missing obligation at one reduced profile. -/
theorem coversFullDeviationsAt_of_isNash_expanded
    (pruning : Pruning diagram)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning)
    (hnash : IsNash (nativeBehavioralGameForm semantics)
      (euPreference fun assignment owner =>
        semantics.utility owner assignment)
      (pruning.expandPolicy policy)) :
    pruning.CoversFullDeviationsAt semantics policy := by
  rw [isNash_iff] at hnash
  intro owner fullReplacement
  refine ⟨policy owner, ?_⟩
  simpa only [Profile.update_eq_self] using
    hnash owner fullReplacement

/-- Nash against the full site-local policy space implies Nash after pruning
without any coverage premise.  The converse above needs deviation coverage: a
removed observation may otherwise enable a profitable full-space deviation. -/
theorem isNash_reducedNative_of_isNash_expanded
    (pruning : Pruning diagram)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning)
    (hnash : IsNash (nativeBehavioralGameForm semantics)
      (euPreference fun assignment owner =>
        semantics.utility owner assignment)
      (pruning.expandPolicy policy)) :
    IsNash (pruning.reducedNativeGameForm semantics)
      (euPreference fun assignment owner => semantics.utility owner assignment)
      policy := by
  rw [isNash_iff] at hnash ⊢
  intro owner replacement
  have hdeviation := hnash owner
    (pruning.expandOwnerPolicy owner replacement)
  rw [← pruning.expandPolicy_update policy owner replacement]
    at hdeviation
  exact hdeviation

/-- At a profile whose reduced deviations cover the full deviation space,
expansion identifies the full and reduced native Nash questions exactly. -/
theorem isNash_expanded_iff_reducedNative_of_covers
    (pruning : Pruning diagram)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning)
    (hcover : pruning.CoversFullDeviationsAt semantics policy) :
    IsNash (nativeBehavioralGameForm semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment)
        (pruning.expandPolicy policy) ↔
      IsNash (pruning.reducedNativeGameForm semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment)
        policy := by
  constructor
  · exact pruning.isNash_reducedNative_of_isNash_expanded semantics policy
  · exact pruning.isNash_expanded_of_isNash_reduced semantics policy hcover

/-- Full native Nash is exactly reduced native Nash plus coverage of the
deviations removed from the policy domain. -/
theorem isNash_expanded_iff_reducedNative_and_covers
    (pruning : Pruning diagram)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning) :
    IsNash (nativeBehavioralGameForm semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment)
        (pruning.expandPolicy policy) ↔
      IsNash (pruning.reducedNativeGameForm semantics)
          (euPreference fun assignment owner =>
            semantics.utility owner assignment)
          policy ∧
        pruning.CoversFullDeviationsAt semantics policy := by
  constructor
  · intro hnash
    exact ⟨
      pruning.isNash_reducedNative_of_isNash_expanded
        semantics policy hnash,
      pruning.coversFullDeviationsAt_of_isNash_expanded
        semantics policy hnash⟩
  · rintro ⟨hnash, hcover⟩
    exact pruning.isNash_expanded_of_isNash_reduced
      semantics policy hcover hnash

/-- The reduced native and compiled forms have exactly the same canonical Nash
predicate. -/
theorem isNash_reducedNative_iff_reducedCompiled
    (pruning : Pruning diagram)
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning) :
    IsNash (pruning.reducedNativeGameForm semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment) policy ↔
      IsNash (pruning.reducedCompiledGameForm topological semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment) policy := by
  rw [isNash_iff, isNash_iff]
  constructor
  · intro hnash owner replacement
    have hdeviation := hnash owner replacement
    rw [native_play_eq_compiled_play topological semantics
        (pruning.expandPolicy policy),
      native_play_eq_compiled_play topological semantics
        (pruning.expandPolicy
          (Profile.update policy owner replacement))]
      at hdeviation
    exact hdeviation
  · intro hnash owner replacement
    have hdeviation := hnash owner replacement
    rw [← native_play_eq_compiled_play topological semantics
        (pruning.expandPolicy policy),
      ← native_play_eq_compiled_play topological semantics
        (pruning.expandPolicy
          (Profile.update policy owner replacement))]
      at hdeviation
    exact hdeviation

/-- Deviation coverage also identifies full native Nash with reduced compiled
Nash; no second equilibrium or utility semantics is introduced at the compiler
boundary. -/
theorem isNash_expanded_iff_reducedCompiled_of_covers
    (pruning : Pruning diagram)
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : ReducedPolicy pruning)
    (hcover : pruning.CoversFullDeviationsAt semantics policy) :
    IsNash (nativeBehavioralGameForm semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment)
        (pruning.expandPolicy policy) ↔
      IsNash (pruning.reducedCompiledGameForm topological semantics)
        (euPreference fun assignment owner =>
          semantics.utility owner assignment)
        policy :=
  (pruning.isNash_expanded_iff_reducedNative_of_covers
      semantics policy hcover).trans
    (pruning.isNash_reducedNative_iff_reducedCompiled
      topological semantics policy)

end Pruning

end GameTheory.Languages.MAID.ObservationPruning
