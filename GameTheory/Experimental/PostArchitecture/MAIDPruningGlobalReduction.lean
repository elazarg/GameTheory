/-
# EXP-107: global deviation coverage from sufficient recall

This module closes the semantic pruning argument.  It processes each owner's
decision sites in source-first strategic-relevance order, chooses a reduced
site-optimal rule, and telescopes against an arbitrary full owner deviation.
The induction invariant compares policies that already agree outside the
unprocessed suffix; it does not infer whole-owner optimality from unrelated
sitewise inequalities.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningRecallOrder
import GameTheory.Experimental.PostArchitecture.MAIDPruningSiteReduction
import GameTheory.Experimental.PostArchitecture.MAIDStrategicNonreachabilityList

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningGlobalReduction

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDPruningRecallOrder
open GameTheory.Experimental.PostArchitecture.MAIDPruningSiteReduction
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDSiteLocalReduction
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDStrategicNonreachabilityList

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
variable {semantics : Semantics diagram}

/-! ## Later-source change lists -/

/-- Package arbitrary rules at later sites as justified nonreachability
changes for one fixed earlier target. -/
private def laterSourceChanges [DecidableEq Node] {owner : Player}
    (view : UtilityView semantics) (target : DecisionSite diagram owner)
    (replacement : OwnerPolicy diagram owner) :
    (sites : List (DecisionSite diagram owner)) →
      (∀ source, source ∈ sites → source ≠ target) →
      (∀ source, source ∈ sites →
        ¬ UtilityView.SReachable view source target) →
      List (SourceChange view target)
  | [], _, _ => []
  | source :: sites, hne, hnot =>
      { source := source
        source_ne_target := hne source (by simp)
        sourceRule := replacement source
        not_sReachable := hnot source (by simp) } ::
        laterSourceChanges view target replacement sites
          (fun other hother => hne other (by simp [hother]))
          (fun other hother => hnot other (by simp [hother]))

private theorem sourceSites_laterSourceChanges [DecidableEq Node]
    {owner : Player} (view : UtilityView semantics)
    (target : DecisionSite diagram owner)
    (replacement : OwnerPolicy diagram owner)
    (sites : List (DecisionSite diagram owner))
    (hne : ∀ source, source ∈ sites → source ≠ target)
    (hnot : ∀ source, source ∈ sites →
      ¬ UtilityView.SReachable view source target) :
    sourceSites (laterSourceChanges view target replacement sites hne hnot) =
      sites := by
  induction sites with
  | nil => rfl
  | cons source sites ih =>
      simp only [laterSourceChanges, sourceSites, List.map_cons,
        List.cons.injEq, true_and]
      exact ih _ _

private theorem apply_laterSourceChanges_at_of_mem [DecidableEq Node]
    {owner : Player} (view : UtilityView semantics)
    (target : DecisionSite diagram owner)
    (initial replacement : OwnerPolicy diagram owner)
    (sites : List (DecisionSite diagram owner))
    (hne : ∀ source, source ∈ sites → source ≠ target)
    (hnot : ∀ source, source ∈ sites →
      ¬ UtilityView.SReachable view source target)
    (hnodup : sites.Nodup) (site : DecisionSite diagram owner)
    (hsite : site ∈ sites) :
    applySourceChanges initial
        (laterSourceChanges view target replacement sites hne hnot) site =
      replacement site := by
  induction sites generalizing initial with
  | nil => simp at hsite
  | cons source sites ih =>
      rw [laterSourceChanges, applySourceChanges]
      by_cases heq : site = source
      · subst site
        rw [applySourceChanges_at_of_not_mem]
        · simp [applySourceChange]
        · intro entry hentry hsame
          have hsource : entry.source ∈ sites := by
            rw [← sourceSites_laterSourceChanges view target replacement sites
              (fun other hother =>
                hne other (List.mem_cons_of_mem source hother))
              (fun other hother =>
                hnot other (List.mem_cons_of_mem source hother))]
            exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
          apply (List.nodup_cons.mp hnodup).1
          rw [hsame]
          exact hsource
      · apply ih (initial := _)
          (hne := fun other hother =>
            hne other (List.mem_cons_of_mem source hother))
          (hnot := fun other hother =>
            hnot other (List.mem_cons_of_mem source hother))
          (List.nodup_cons.mp hnodup).2
        exact (List.mem_cons.mp hsite).resolve_left heq

/-! ## The telescoping owner induction -/

/-- A source-first list orders every later site after each earlier target. -/
private def SourceFirst [DecidableEq Node] {owner : Player}
    (view : UtilityView semantics)
    (sites : List (DecisionSite diagram owner)) : Prop :=
  sites.Pairwise fun target source =>
    ¬ UtilityView.SReachable view source target

/-- Process a source-first suffix.  The arbitrary full replacement and the
current reduced replacement must agree outside that suffix.  The result is a
reduced whole-owner replacement whose payoff weakly dominates the arbitrary
one. -/
private theorem exists_reducedOwnerPolicy_dominates_on_sourceFirst
    (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (view : UtilityView semantics)
    (hfixpoint : UtilityView.IsEdgeAdditionFixpoint view pruning)
    (owner : Player) (sites : List (DecisionSite diagram owner))
    (hnodup : sites.Nodup) (hsourceFirst : SourceFirst view sites)
    (initial : pruning.ReducedOwnerPolicy owner)
    (hmixed : ∀ site, site ∈ sites →
      FullyMixedAt (pruning.expandOwnerPolicy owner initial) site)
    (fullReplacement : OwnerPolicy diagram owner)
    (hagrees : ∀ site, site ∉ sites →
      pruning.expandOwnerPolicy owner initial site = fullReplacement site) :
    ∃ reducedReplacement : pruning.ReducedOwnerPolicy owner,
      expectedUtility
          (fun assignment who => semantics.utility who assignment) owner
          ((nativeBehavioralGameForm semantics).play
            (Profile.update (pruning.expandPolicy policy) owner
              fullReplacement)) ≤
        expectedUtility
          (fun assignment who => semantics.utility who assignment) owner
          ((nativeBehavioralGameForm semantics).play
            (Profile.update (pruning.expandPolicy policy) owner
              (pruning.expandOwnerPolicy owner reducedReplacement))) := by
  letI : Fintype (Assignment diagram) := by
    unfold Assignment
    infer_instance
  induction sites generalizing initial fullReplacement with
  | nil =>
      refine ⟨initial, ?_⟩
      have heq : pruning.expandOwnerPolicy owner initial = fullReplacement := by
        funext site
        exact hagrees site (by simp)
      rw [heq]
  | cons target sites ih =>
      have hnodupTail := (List.nodup_cons.mp hnodup).2
      have htargetNotMem := (List.nodup_cons.mp hnodup).1
      have hsourceFirstHead := (List.pairwise_cons.mp hsourceFirst).1
      have hsourceFirstTail := (List.pairwise_cons.mp hsourceFirst).2
      obtain ⟨reducedRule, hoptimal⟩ :=
        exists_reduced_isOptimalSiteRule_of_edgeAdditionStableAt pruning
          topological semantics policy owner initial target view
          (hfixpoint owner target)
      let fullRule := expandKeptSiteRule pruning target reducedRule
      let updated := replaceReducedSiteRule pruning initial target reducedRule
      have hexpand : pruning.expandOwnerPolicy owner updated =
          replaceSiteRule (pruning.expandOwnerPolicy owner initial) target
            fullRule := by
        exact expandOwnerPolicy_replaceReducedSiteRule pruning initial target
          reducedRule
      have hne : ∀ source, source ∈ sites → source ≠ target := by
        intro source hsource heq
        subst source
        exact htargetNotMem hsource
      let changes := laterSourceChanges view target fullReplacement sites hne
        hsourceFirstHead
      have hchangesDistinct : DistinctSources changes := by
        unfold DistinctSources changes
        rw [sourceSites_laterSourceChanges view target fullReplacement sites hne
          hsourceFirstHead]
        exact hnodupTail
      have hchangesMixed : FullyMixedOn
          (pruning.expandOwnerPolicy owner initial) changes := by
        intro entry hentry
        apply hmixed entry.source
        simp only [List.mem_cons]
        right
        rw [← sourceSites_laterSourceChanges view target fullReplacement sites
          hne hsourceFirstHead]
        exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
      let changed := applySourceChanges
        (pruning.expandOwnerPolicy owner initial) changes
      letI : Fintype (FullContext target) := by
        unfold FullContext Config
        infer_instance
      letI : ∀ term : view.UtilitySite owner,
          Fintype (TermConfig view term) := fun _ => by
        unfold TermConfig Config
        infer_instance
      have htransported : IsOptimalSiteRule semantics
          (pruning.expandPolicy policy) owner changed target fullRule := by
        exact
          IsOptimalSiteRule.transport_applySourceChanges_of_distinct
            topological semantics view (pruning.expandPolicy policy) owner
            (pruning.expandOwnerPolicy owner initial) target hchangesDistinct
            hchangesMixed fullRule hoptimal
      let nextFull := replaceSiteRule changed target fullRule
      have hleft : replaceSiteRule changed target
          (fullReplacement target) = fullReplacement := by
        funext site
        by_cases heq : site = target
        · subst site
          simp
        · rw [replaceSiteRule_of_ne _ target site _ heq]
          by_cases hmem : site ∈ sites
          · exact apply_laterSourceChanges_at_of_mem view target
              (pruning.expandOwnerPolicy owner initial) fullReplacement sites
              hne hsourceFirstHead hnodupTail site hmem
          · dsimp [changed, changes]
            rw [applySourceChanges_at_of_not_mem]
            · exact hagrees site (by simp [heq, hmem])
            · intro entry hentry
              have hsource : entry.source ∈ sites := by
                rw [← sourceSites_laterSourceChanges view target
                  fullReplacement sites hne hsourceFirstHead]
                exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
              intro hsame
              subst site
              exact hmem hsource
      have hstep :
          expectedUtility
              (fun assignment who => semantics.utility who assignment) owner
              ((nativeBehavioralGameForm semantics).play
                (Profile.update (pruning.expandPolicy policy) owner
                  fullReplacement)) ≤
            expectedUtility
              (fun assignment who => semantics.utility who assignment) owner
              ((nativeBehavioralGameForm semantics).play
                (Profile.update (pruning.expandPolicy policy) owner
                  nextFull)) := by
        simpa only [siteRuleExpectedUtility, siteReplacementLaw, hleft,
          nextFull] using htransported.upperBound (fullReplacement target)
      have hmixedUpdated : ∀ site, site ∈ sites →
          FullyMixedAt (pruning.expandOwnerPolicy owner updated) site := by
        intro site hsite
        apply FullyMixedAt.congr site (hmixed site (by simp [hsite]))
        intro context
        rw [hexpand, replaceSiteRule_of_ne]
        intro heq
        subst site
        exact htargetNotMem hsite
      have hagreesNext : ∀ site, site ∉ sites →
          pruning.expandOwnerPolicy owner updated site = nextFull site := by
        intro site hsite
        by_cases heq : site = target
        · subst site
          simp [nextFull, hexpand, fullRule]
        · rw [hexpand, replaceSiteRule_of_ne _ target site _ heq]
          dsimp [nextFull]
          rw [replaceSiteRule_of_ne _ target site _ heq]
          symm
          dsimp [changed, changes]
          apply applySourceChanges_at_of_not_mem
          intro entry hentry
          have hsource : entry.source ∈ sites := by
            rw [← sourceSites_laterSourceChanges view target fullReplacement
              sites hne hsourceFirstHead]
            exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
          intro hsame
          subst site
          exact hsite hsource
      obtain ⟨reducedReplacement, htail⟩ := ih hnodupTail
        hsourceFirstTail updated hmixedUpdated nextFull hagreesNext
      exact ⟨reducedReplacement, hstep.trans htail⟩

/-! ## Topological construction and coverage -/

/-- The source-first topological order has the pairwise nonreachability needed
by the telescoping owner induction. -/
private theorem orientedTopologicalOrder_sourceFirst
    (view : UtilityView semantics) [Fintype Node] [DecidableEq Node]
    (owner : Player) (hacyclic : UtilityView.SReachAcyclic view) :
    SourceFirst view
      (orientedTopologicalOrder view owner hacyclic).order := by
  unfold SourceFirst
  rw [List.pairwise_iff_get]
  intro earlier later hindex
  exact later_not_oriented_source view owner
    (orientedTopologicalOrder view owner hacyclic) hindex

/-- Under sufficient recall and an edge-addition fixpoint, every arbitrary
full owner deviation is weakly payoff-dominated by a reduced owner policy. -/
theorem exists_reducedOwnerPolicy_dominates
    (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (view : UtilityView semantics)
    (hacyclic : UtilityView.SReachAcyclic view)
    (hfixpoint : UtilityView.IsEdgeAdditionFixpoint view pruning)
    (owner : Player) (fullReplacement : OwnerPolicy diagram owner) :
    ∃ reducedReplacement : pruning.ReducedOwnerPolicy owner,
      expectedUtility
          (fun assignment who => semantics.utility who assignment) owner
          ((nativeBehavioralGameForm semantics).play
            (Profile.update (pruning.expandPolicy policy) owner
              fullReplacement)) ≤
        expectedUtility
          (fun assignment who => semantics.utility who assignment) owner
          ((nativeBehavioralGameForm semantics).play
            (Profile.update (pruning.expandPolicy policy) owner
              (pruning.expandOwnerPolicy owner reducedReplacement))) := by
  let ownerOrder := orientedTopologicalOrder view owner hacyclic
  let initial := uniformReducedOwnerPolicyOfSemantics pruning semantics owner
  apply exists_reducedOwnerPolicy_dominates_on_sourceFirst pruning topological
    semantics policy view hfixpoint owner ownerOrder.order ownerOrder.nodup
    (orientedTopologicalOrder_sourceFirst view owner hacyclic) initial
  · intro site _
    exact expand_uniformReducedOwnerPolicyOfSemantics_fullyMixedAt_all
      pruning semantics owner site
  · intro site hsite
    exact False.elim (hsite (ownerOrder.complete site))

/-- Sufficient recall turns an edge-addition fixpoint into the exact semantic
certificate required for safe observation pruning. -/
theorem coversFullDeviationsAt_of_edgeAdditionFixpoint
    (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (view : UtilityView semantics)
    (hacyclic : UtilityView.SReachAcyclic view)
    (hfixpoint : UtilityView.IsEdgeAdditionFixpoint view pruning) :
    pruning.CoversFullDeviationsAt semantics policy := by
  intro owner fullReplacement
  obtain ⟨reducedReplacement, hdominates⟩ :=
    exists_reducedOwnerPolicy_dominates pruning topological semantics policy
      view hacyclic hfixpoint owner fullReplacement
  refine ⟨reducedReplacement, ?_⟩
  rw [euPreference_apply]
  rw [show (pruning.reducedNativeGameForm semantics).play
      (Profile.update policy owner reducedReplacement) =
        (nativeBehavioralGameForm semantics).play
          (Profile.update (pruning.expandPolicy policy) owner
            (pruning.expandOwnerPolicy owner reducedReplacement)) by
    exact congrArg (nativeBehavioralGameForm semantics).play
      (pruning.expandPolicy_update policy owner reducedReplacement)]
  exact hdominates

end GameTheory.Experimental.PostArchitecture.MAIDPruningGlobalReduction
