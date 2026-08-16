/-
# EXP-107: finite same-owner source-rule transport

This module iterates the one-source strategic nonreachability theorem over a
dependent list of source rules.  It deliberately stops at transport for one
fixed target: no acyclicity, coverage, or equilibrium statement is introduced
here.
-/

import GameTheory.Experimental.PostArchitecture.MAIDStrategicNonreachability

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDStrategicNonreachabilityList

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDStrategicNonreachability

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
variable {semantics : Semantics diagram}

/-! ## Typed source changes and the finite fold -/

/-- One same-owner source rule to be changed while considering a fixed target.

The source rule uses the source's complete declared context.  The two graph
and site certificates are stored with the rule so that a list cannot silently
forget which one-source transport theorem justifies its use.
-/
structure SourceChange (view : UtilityView semantics) [DecidableEq Node]
    {owner : Player} (target : DecisionSite diagram owner) where
  source : DecisionSite diagram owner
  source_ne_target : source ≠ target
  sourceRule : FullContext source → FinDist (diagram.Value source.1)
  not_sReachable : ¬ UtilityView.SReachable view source target

/-- The policy obtained by changing the one source carried by a package. -/
def applySourceChange [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    {view : UtilityView semantics} {target : DecisionSite diagram owner}
    (change : SourceChange view target) : OwnerPolicy diagram owner :=
  replaceSiteRule policy change.source change.sourceRule

/-- Apply source changes from left to right. -/
def applySourceChanges [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    {view : UtilityView semantics} {target : DecisionSite diagram owner} :
    List (SourceChange view target) → OwnerPolicy diagram owner
  | [] => policy
  | change :: changes =>
      applySourceChanges (applySourceChange policy change) changes

/-- The source sites in a change list, used for the distinctness certificate. -/
def sourceSites [DecidableEq Node] {view : UtilityView semantics} {owner : Player}
    {target : DecisionSite diagram owner} :
    List (SourceChange view target) → List (DecisionSite diagram owner) :=
  List.map SourceChange.source

/-- No source is changed twice in the finite fold. -/
def DistinctSources [DecidableEq Node] {view : UtilityView semantics} {owner : Player}
    {target : DecisionSite diagram owner}
    (changes : List (SourceChange view target)) : Prop :=
  (sourceSites changes).Nodup

/-- Every source in a list is fully mixed in the supplied policy. -/
def FullyMixedOn [DecidableEq Node] {view : UtilityView semantics} {owner : Player}
    {target : DecisionSite diagram owner}
    (policy : OwnerPolicy diagram owner)
    (changes : List (SourceChange view target)) : Prop :=
  ∀ change, change ∈ changes → FullyMixedAt policy change.source

/-! ## Lookup and fully-mixed preservation -/

theorem applySourceChange_at_of_ne [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    {view : UtilityView semantics} {target : DecisionSite diagram owner}
    (change : SourceChange view target)
    (site : DecisionSite diagram owner) (hne : site ≠ change.source) :
    applySourceChange policy change site = policy site := by
  exact replaceSiteRule_of_ne policy change.source site change.sourceRule hne

theorem fullyMixedAt_applySourceChange_of_ne [DecidableEq Node]
    {owner : Player} (policy : OwnerPolicy diagram owner)
    {view : UtilityView semantics} {target : DecisionSite diagram owner}
    (change : SourceChange view target) (site : DecisionSite diagram owner)
    (hmixed : FullyMixedAt policy site) (hne : site ≠ change.source) :
    FullyMixedAt (applySourceChange policy change) site := by
  apply FullyMixedAt.congr site hmixed
  intro context
  exact congrFun (applySourceChange_at_of_ne policy change site hne).symm
    context

theorem applySourceChanges_at_of_not_mem [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    {view : UtilityView semantics} {target : DecisionSite diagram owner}
    (changes : List (SourceChange view target))
    (site : DecisionSite diagram owner)
    (hsite : ∀ change, change ∈ changes → site ≠ change.source) :
    applySourceChanges policy changes site = policy site := by
  induction changes generalizing policy with
  | nil => rfl
  | cons change changes ih =>
      rw [applySourceChanges]
      rw [ih]
      · exact applySourceChange_at_of_ne policy change site (hsite change (by simp))
      · intro other hother
        exact hsite other (by simp [hother])

theorem fullyMixedOn_applySourceChange_of_ne
    [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    {view : UtilityView semantics} {target : DecisionSite diagram owner}
    (change : SourceChange view target)
    (changes : List (SourceChange view target))
    (hmixed : FullyMixedOn policy changes)
    (hsource : ∀ other, other ∈ changes → other.source ≠ change.source) :
    FullyMixedOn (applySourceChange policy change) changes := by
  intro other hother
  exact fullyMixedAt_applySourceChange_of_ne policy change other.source
    (hmixed other hother) (hsource other hother)

/-! ## Repeated optimality transport -/

theorem IsOptimalSiteRule.transport_applySourceChanges_of_distinct
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    [Fintype (Assignment diagram)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (view : UtilityView semantics)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    {changes : List (SourceChange view target)}
    (hdistinct : DistinctSources changes)
    (hmixed : FullyMixedOn replacement changes)
    [Fintype (FullContext target)]
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (targetRule : FullContext target → FinDist (diagram.Value target.1))
    (hoptimal : IsOptimalSiteRule semantics base owner replacement target
      targetRule) :
    IsOptimalSiteRule semantics base owner
      (applySourceChanges replacement changes) target targetRule := by
  induction changes generalizing replacement with
  | nil =>
      simpa [applySourceChanges] using hoptimal
  | cons change changes ih =>
      rw [applySourceChanges]
      have hhead : FullyMixedAt replacement change.source :=
        hmixed change (by simp)
      have htransport :=
        IsOptimalSiteRule.transport_replaceSiteRule_of_not_sReachable
          topological semantics view base owner replacement change.source target
          change.source_ne_target change.sourceRule change.not_sReachable hhead
          targetRule hoptimal
      apply ih (replacement := applySourceChange replacement change)
        (hdistinct := by
          simpa [DistinctSources, sourceSites] using hdistinct.tail)
        (hmixed := by
          exact fullyMixedOn_applySourceChange_of_ne replacement change changes
            (by
              intro other hother
              exact hmixed other (by simp [hother]))
            (by
              intro other hother heq
              have hsource : change.source ∉ sourceSites changes := by
                intro hmem
                exact (List.pairwise_cons.mp hdistinct).1 _ hmem rfl
              apply hsource
              exact List.mem_map.mpr ⟨other, hother, heq⟩))
        htransport

end GameTheory.Experimental.PostArchitecture.MAIDStrategicNonreachabilityList
