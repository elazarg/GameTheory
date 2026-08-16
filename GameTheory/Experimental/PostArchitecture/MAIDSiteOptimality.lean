/-
# Site-local optimality for typed MAIDs

These transparent predicates vary one decision rule while fixing every other
rule in the owner's replacement.  Expected utility is always computed by the
canonical native MAID form.
-/

import GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- A whole-owner policy is fully mixed at one decision site when every action
is supported at every declared observation context. -/
def FullyMixedAt {owner : Player} (policy : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) : Prop :=
  ∀ context action, action ∈ (policy target context).support

theorem fullyMixedAt_iff_prob_pos {owner : Player}
    (policy : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) :
    FullyMixedAt policy target ↔
      ∀ context action, 0 < (policy target context).prob action := by
  constructor
  · intro hmixed context action
    exact FinDist.prob_pos_iff.mpr (hmixed context action)
  · intro hpositive context action
    exact FinDist.prob_pos_iff.mp (hpositive context action)

theorem FullyMixedAt.congr {owner : Player}
    {first second : OwnerPolicy diagram owner}
    (target : DecisionSite diagram owner) (hmixed : FullyMixedAt first target)
    (heq : ∀ context, first target context = second target context) :
    FullyMixedAt second target := by
  intro context action
  rw [← heq context]
  exact hmixed context action

theorem fullyMixedAt_replaceSiteRule_iff [DecidableEq Node]
    {owner : Player} (policy : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    FullyMixedAt (replaceSiteRule policy target rule) target ↔
      ∀ context action, action ∈ (rule context).support := by
  simp only [FullyMixedAt, replaceSiteRule_same]

/-- Expected utility when only the target rule varies and all other rules in
the owner's replacement remain fixed. -/
def siteRuleExpectedUtility [DecidableEq Player] [Fintype Node]
    [DecidableEq Node] (semantics : Semantics diagram)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) : ℝ :=
  expectedUtility (fun assignment who => semantics.utility who assignment)
    owner (siteReplacementLaw semantics base owner replacement target rule)

/-- A target rule is optimal against arbitrary behavioral alternatives at that
site, holding the rest of the whole-owner replacement fixed. -/
def IsOptimalSiteRule [DecidableEq Player] [Fintype Node]
    [DecidableEq Node] (semantics : Semantics diagram)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) : Prop :=
  ∀ alternative,
    siteRuleExpectedUtility semantics base owner replacement target
        alternative ≤
      siteRuleExpectedUtility semantics base owner replacement target rule

theorem siteReplacementLaw_congr [DecidableEq Player] [Fintype Node]
    [DecidableEq Node] (semantics : Semantics diagram)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (first second : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1))
    (heq : ∀ context, first context = second context) :
    siteReplacementLaw semantics base owner replacement target first =
      siteReplacementLaw semantics base owner replacement target second := by
  have hrules : first = second := funext heq
  subst second
  rfl

theorem siteReplacementLaw_self [DecidableEq Player] [Fintype Node]
    [DecidableEq Node] (semantics : Semantics diagram)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) :
    siteReplacementLaw semantics base owner replacement target
        (replacement target) =
      (nativeBehavioralGameForm semantics).play
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner replacement) := by
  unfold siteReplacementLaw
  rw [replaceSiteRule_self]

theorem isOptimalSiteRule_congr [DecidableEq Player] [Fintype Node]
    [DecidableEq Node] (semantics : Semantics diagram)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (first second : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1))
    (heq : ∀ context, first context = second context) :
    IsOptimalSiteRule semantics base owner replacement target first ↔
      IsOptimalSiteRule semantics base owner replacement target second := by
  have hrules : first = second := funext heq
  subst second
  rfl

theorem IsOptimalSiteRule.upperBound [DecidableEq Player] [Fintype Node]
    [DecidableEq Node] {semantics : Semantics diagram}
    {base : Policy diagram} {owner : Player}
    {replacement : OwnerPolicy diagram owner}
    {target : DecisionSite diagram owner}
    {rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)}
    (hoptimal : IsOptimalSiteRule semantics base owner replacement target rule)
    (alternative : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    siteRuleExpectedUtility semantics base owner replacement target
        alternative ≤
      siteRuleExpectedUtility semantics base owner replacement target rule :=
  hoptimal alternative

theorem IsOptimalSiteRule.currentRule_le [DecidableEq Player]
    [Fintype Node] [DecidableEq Node] {semantics : Semantics diagram}
    {base : Policy diagram} {owner : Player}
    {replacement : OwnerPolicy diagram owner}
    {target : DecisionSite diagram owner}
    {rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)}
    (hoptimal : IsOptimalSiteRule semantics base owner replacement target rule) :
    siteRuleExpectedUtility semantics base owner replacement target
        (replacement target) ≤
      siteRuleExpectedUtility semantics base owner replacement target rule :=
  hoptimal.upperBound (replacement target)

/-- A deterministic action choice at every target context. -/
abbrev PureSiteRule {owner : Player}
    (target : DecisionSite diagram owner) :=
  Config diagram (diagram.observedParents target.1) →
    diagram.Value target.1

/-- Read a deterministic target rule as a canonical behavioral kernel. -/
def behavioralRuleOfPure {owner : Player}
    (target : DecisionSite diagram owner) (rule : PureSiteRule target) :
    Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1) :=
  fun context => FinDist.pure (rule context)

/-- Independently sample one deterministic action for every target context.
This is the canonical `FinDist.pi` law, with dependent context finiteness kept
local to the construction. -/
def independentPureSiteRuleLaw [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)] {owner : Player}
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) : FinDist (PureSiteRule target) := by
  letI : Fintype
      (Config diagram (diagram.observedParents target.1)) := by
    unfold Config
    infer_instance
  exact FinDist.pi rule

/-- A behavioral target rule is exactly an independent mixture over
deterministic context-indexed rules.  The target executes once, while the
prefix, every other owner site, and the suffix remain fixed. -/
theorem siteReplacementLaw_eq_bind_pureSiteRules
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    siteReplacementLaw semantics base owner replacement target rule =
      (independentPureSiteRuleLaw target rule).bind fun pureRule =>
        siteReplacementLaw semantics base owner replacement target
          (behavioralRuleOfPure target pureRule) := by
  let targetIndex := topological.order.idxOf target.1
  have htargetIndex : targetIndex < topological.order.length :=
    List.idxOf_lt_length_of_mem (topological.complete target.1)
  let before := topological.order.take targetIndex
  let after := topological.order.drop (targetIndex + 1)
  have htargetGet : topological.order[targetIndex] = target.1 :=
    List.getElem_idxOf htargetIndex
  have horder : before ++ target.1 :: after = topological.order := by
    unfold before after
    calc
      topological.order.take targetIndex ++
          target.1 :: topological.order.drop (targetIndex + 1) =
          (topological.order.take targetIndex ++ [target.1]) ++
            topological.order.drop (targetIndex + 1) := by simp
      _ = topological.order.take (targetIndex + 1) ++
            topological.order.drop (targetIndex + 1) := by
        rw [← htargetGet]
        rw [List.take_append_getElem htargetIndex]
      _ = topological.order := List.take_append_drop _ _
  have hnodup : (before ++ target.1 :: after).Nodup := by
    rw [horder]
    exact topological.nodup
  have htargetBefore : target.1 ∉ before := by
    intro htarget
    exact (List.nodup_append.mp hnodup).2.2 target.1 htarget
      target.1 (by simp) rfl
  have htargetAfter : target.1 ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1
  let fixedPolicy : Policy diagram :=
    Profile.update (sig := nativeBehavioralSignature diagram)
      base owner replacement
  let prefixLaw :=
    assignmentRun semantics fixedPolicy before semantics.defaultValue
  have hplay : ∀ siteRule,
      siteReplacementLaw semantics base owner replacement target siteRule =
        prefixLaw.bind fun state =>
          (siteRule (Assignment.restrict diagram state
            (diagram.observedParents target.1))).bind fun action =>
            assignmentRun semantics fixedPolicy after
              (Stage.Assignment.setOne state ⟨target.1, action⟩) := by
    intro siteRule
    let surgeryPolicy : Policy diagram :=
      Profile.update (sig := nativeBehavioralSignature diagram)
        base owner (replaceSiteRule replacement target siteRule)
    unfold siteReplacementLaw
    rw [nativeBehavioralGameForm_play,
      map_values_nativeRun_eq_assignmentRun topological semantics
        surgeryPolicy,
      ← horder]
    simpa [surgeryPolicy, fixedPolicy, prefixLaw] using
      assignmentRun_site_surgery_eq semantics base owner replacement target
        siteRule before after htargetBefore htargetAfter
          semantics.defaultValue
  rw [hplay rule]
  calc
    prefixLaw.bind (fun state =>
        (rule (Assignment.restrict diagram state
          (diagram.observedParents target.1))).bind fun action =>
            assignmentRun semantics fixedPolicy after
              (Stage.Assignment.setOne state ⟨target.1, action⟩)) =
      prefixLaw.bind (fun state =>
        (independentPureSiteRuleLaw target rule).bind fun pureRule =>
          assignmentRun semantics fixedPolicy after
            (Stage.Assignment.setOne state
              ⟨target.1, pureRule (Assignment.restrict diagram state
                (diagram.observedParents target.1))⟩)) := by
      apply FinDist.bind_congr
      intro state _
      let context := Assignment.restrict diagram state
        (diagram.observedParents target.1)
      let continuation := fun action =>
        assignmentRun semantics fixedPolicy after
          (Stage.Assignment.setOne state ⟨target.1, action⟩)
      have hmarginal :
          (independentPureSiteRuleLaw target rule).map
              (fun pureRule => pureRule context) =
            rule context := by
        letI : Fintype
            (Config diagram (diagram.observedParents target.1)) := by
          unfold Config
          infer_instance
        letI : DecidableEq
            (Config diagram (diagram.observedParents target.1)) := by
          unfold Config
          infer_instance
        unfold independentPureSiteRuleLaw
        exact FinDist.map_apply_pi context rule
      calc
        (rule context).bind continuation =
            ((independentPureSiteRuleLaw target rule).map
              (fun pureRule => pureRule context)).bind continuation := by
                rw [hmarginal]
        _ = (independentPureSiteRuleLaw target rule).bind
              (fun pureRule => continuation (pureRule context)) :=
          FinDist.bind_map _ _ _
    _ = (independentPureSiteRuleLaw target rule).bind fun pureRule =>
        prefixLaw.bind fun state =>
          assignmentRun semantics fixedPolicy after
            (Stage.Assignment.setOne state
              ⟨target.1, pureRule (Assignment.restrict diagram state
                (diagram.observedParents target.1))⟩) :=
      FinDist.bind_comm prefixLaw (independentPureSiteRuleLaw target rule)
        (fun state pureRule =>
          assignmentRun semantics fixedPolicy after
            (Stage.Assignment.setOne state
              ⟨target.1, pureRule (Assignment.restrict diagram state
                (diagram.observedParents target.1))⟩))
    _ = (independentPureSiteRuleLaw target rule).bind fun pureRule =>
        siteReplacementLaw semantics base owner replacement target
          (behavioralRuleOfPure target pureRule) := by
      apply FinDist.bind_congr
      intro pureRule _
      rw [hplay (behavioralRuleOfPure target pureRule)]
      apply FinDist.bind_congr
      intro state _
      simp [behavioralRuleOfPure]

/-- Finite deterministic target rules contain an expected-utility maximizer.
The behavioral-mixture theorem above upgrades this pure comparison to full
site-rule optimality below. -/
theorem exists_pureSiteRule_dominates_pure
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) :
    ∃ best : PureSiteRule target,
      ∀ alternative : PureSiteRule target,
        siteRuleExpectedUtility semantics base owner replacement target
            (behavioralRuleOfPure target alternative) ≤
          siteRuleExpectedUtility semantics base owner replacement target
            (behavioralRuleOfPure target best) := by
  letI : Fintype
      (Config diagram (diagram.observedParents target.1)) := by
    unfold Config
    infer_instance
  letI : Finite (PureSiteRule target) := by
    unfold PureSiteRule
    infer_instance
  letI : Nonempty (PureSiteRule target) :=
    ⟨fun _ => semantics.defaultValue target.1⟩
  exact Finite.exists_max fun rule : PureSiteRule target =>
    siteRuleExpectedUtility semantics base owner replacement target
      (behavioralRuleOfPure target rule)

/-- A fully optimal behavioral rule exists at every finite target site.  The
witness is deterministic: exact site-law multilinearity reduces every
behavioral alternative to an expectation over deterministic rules. -/
theorem exists_isOptimalSiteRule
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) :
    ∃ rule : Config diagram (diagram.observedParents target.1) →
        FinDist (diagram.Value target.1),
      IsOptimalSiteRule semantics base owner replacement target rule := by
  obtain ⟨best, hbest⟩ := exists_pureSiteRule_dominates_pure semantics
    base owner replacement target
  refine ⟨behavioralRuleOfPure target best, ?_⟩
  intro alternative
  unfold siteRuleExpectedUtility
  rw [siteReplacementLaw_eq_bind_pureSiteRules topological semantics base
    owner replacement target alternative]
  rw [expectedUtility_bind]
  refine FinDist.expect_le_of_forall _ _ _ fun pureRule _ => ?_
  simpa only [siteRuleExpectedUtility] using hbest pureRule

end GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
