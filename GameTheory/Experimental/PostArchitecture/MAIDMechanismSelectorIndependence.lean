/-
# EXP-107: mechanism-selector independence

The exact mechanism graph turns non-s-reachability into division-free
conditional independence between the fair selector and each relevant utility
configuration, conditional on the target's full context and action.  The law
remains the canonical two-component mixture constructed by the factorization
slice.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
import GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
import GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorFactorization
import GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorIndependence

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
open GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence
open GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorFactorization
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph.UtilityView
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization

universe uPlayer uNode uValue
universe uOmega uFirst uSecond uEvidence
universe uFirst' uSecond' uEvidence'

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

private theorem conditionallyIndependent_map_equiv
    {Omega : Type uOmega} {First : Type uFirst}
    {Second : Type uSecond} {Evidence : Type uEvidence}
    {First' : Type uFirst'} {Second' : Type uSecond'}
    {Evidence' : Type uEvidence'} {law : FinDist Omega}
    {first : Omega → First} {second : Omega → Second}
    {evidence : Omega → Evidence}
    (hindependent :
      IsConditionallyIndependent law first second evidence)
    (firstEquiv : First ≃ First') (secondEquiv : Second ≃ Second')
    (evidenceEquiv : Evidence ≃ Evidence') :
    IsConditionallyIndependent law (firstEquiv ∘ first)
      (secondEquiv ∘ second) (evidenceEquiv ∘ evidence) := by
  intro firstValue secondValue evidenceValue
  simpa [tripleAtom, pairAtom, atom, Function.comp_apply,
    Equiv.apply_eq_iff_eq_symm_apply] using
    hindependent (firstEquiv.symm firstValue)
      (secondEquiv.symm secondValue) (evidenceEquiv.symm evidenceValue)

/-- Proof-only all-chance presentation of the exact mechanism graph. -/
@[reducible]
def mechanismGraphStructure [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (source : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (mechanismGraphParents view source)) :
    Structure.{0, uNode, max uNode uValue} Unit
      (MechanismGraphNode view owner) where
  kind _ := .chance
  parents := mechanismGraphParents view source
  observedParents := mechanismGraphParents view source
  Value := mechanismGraphValue view
  observed_sub _ := Finset.Subset.rfl
  observed_eq_of_chance _ _ := rfl
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder topological

/-- Non-s-reachability excludes the exact singleton mechanism-to-term query
for every utility term relevant to the target. -/
theorem separates_mechanism_utility_of_not_sReachable
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (source target : DecisionSite diagram owner)
    (hnot : ¬ SReachable view source target)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term) :
    Separates (mechanismGraphParents view source)
      {.mechanism} {.object (.utility term)}
      (sReachConditioning view target) := by
  intro left hleft right hright hconnected
  have hleftEq : left = .mechanism := by simpa using hleft
  have hrightEq : right = .object (.utility term) := by simpa using hright
  subst left
  subst right
  exact hnot ⟨term, hrelevant, hconnected⟩

/-- The singleton mechanism, singleton utility, and target conditioning sets
are pairwise disjoint. -/
theorem mechanism_query_disjointness
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner) :
    Disjoint ({.mechanism} : Finset (MechanismGraphNode view owner))
        {.object (.utility term)} ∧
      Disjoint ({.mechanism} : Finset (MechanismGraphNode view owner))
        (sReachConditioning view target) ∧
      Disjoint ({.object (.utility term)} :
        Finset (MechanismGraphNode view owner))
        (sReachConditioning view target) := by
  constructor
  · simp
  constructor
  · simp [sReachConditioning]
  · simp [sReachConditioning]

/-- The fixed fair selector law satisfies coordinate conditional independence
for every target-relevant term excluded by s-reachability. -/
theorem mechanism_coordinates_conditionallyIndependent
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (hnot : ¬ SReachable view source target)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term) :
    CoordinatesConditionallyIndependent
      (diagram := mechanismGraphStructure view owner source
        (mechanismAugmentedTopologicalOrder view owner source topological))
      (mechanismSelectorLaw view owner base replacement source sourceRule)
      {.mechanism} {.object (.utility term)}
      (sReachConditioning view target) := by
  obtain ⟨hfirstSecond, hfirstEvidence, hsecondEvidence⟩ :=
    mechanism_query_disjointness view target term
  exact coordinatesConditionallyIndependent_of_factorizes_of_separates
    (diagram := mechanismGraphStructure view owner source
      (mechanismAugmentedTopologicalOrder view owner source topological))
    (mechanismSelectorLaw view owner base replacement source sourceRule)
    (mechanismGraphParents view source)
    (mechanismAugmentedTopologicalOrder view owner source topological)
    (mechanismSelectorKernels view owner base replacement source sourceRule)
    (mechanismSelectorLaw_factorizes topological view owner base replacement
      source sourceRule)
    {.mechanism} {.object (.utility term)}
    (sReachConditioning view target) hfirstSecond hfirstEvidence
    hsecondEvidence
    (separates_mechanism_utility_of_not_sReachable view source target hnot
      term hrelevant)

private theorem target_not_observed [DecidableEq Node]
    {owner : Player} (target : DecisionSite diagram owner) :
    target.1 ∉ diagram.observedParents target.1 := by
  intro htarget
  apply diagram.acyclic target.1
  apply Relation.TransGen.single
  exact diagram.observed_sub target.1 htarget

/-- A configuration on the singleton mechanism coordinate is its finite
selector value. -/
def selectorConfigurationEquiv [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (source : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (mechanismGraphParents view source)) :
    Config (mechanismGraphStructure view owner source topological)
        ({.mechanism} : Finset (MechanismGraphNode view owner)) ≃ Fin 2 where
  toFun configuration :=
    (configuration ⟨.mechanism, Finset.mem_singleton_self _⟩).down
  invFun selector node := by
    rcases node with ⟨node, hnode⟩
    have hequal : node = .mechanism := by simpa using hnode
    subst node
    exact ULift.up selector
  left_inv configuration := by
    funext node
    rcases node with ⟨node, hnode⟩
    have hequal : node = .mechanism := by simpa using hnode
    subst node
    apply ULift.ext
    rfl
  right_inv _ := rfl

/-- A singleton utility-object configuration is the existing exact term
configuration. -/
def termConfigurationEquiv [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (source : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (mechanismGraphParents view source))
    (term : view.UtilitySite owner) :
    Config (mechanismGraphStructure view owner source topological)
        ({.object (.utility term)} :
          Finset (MechanismGraphNode view owner)) ≃
      TermConfig view term where
  toFun configuration :=
    configuration ⟨.object (.utility term), Finset.mem_singleton_self _⟩
  invFun termValue node := by
    rcases node with ⟨node, hnode⟩
    have hequal : node = .object (.utility term) := by simpa using hnode
    subst node
    exact termValue
  left_inv configuration := by
    funext node
    rcases node with ⟨node, hnode⟩
    have hequal : node = .object (.utility term) := by simpa using hnode
    subst node
    rfl
  right_inv _ := rfl

/-- The s-reachability conditioning coordinates are exactly the target's full
observed context together with its action. -/
def conditioningConfigurationEquiv [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (source target : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (mechanismGraphParents view source)) :
    Config (mechanismGraphStructure view owner source topological)
        (sReachConditioning view target) ≃ FullAction target where
  toFun configuration :=
    (fun parent => configuration
      ⟨.object (.base parent.1), by
        simp [sReachConditioning, parent.2]⟩,
      configuration ⟨.object (.base target.1), by
        simp [sReachConditioning]⟩)
  invFun full node := by
    rcases node with ⟨node, hnode⟩
    cases node with
    | mechanism => simp [sReachConditioning] at hnode
    | object graphNode =>
        cases graphNode with
        | utility term => simp [sReachConditioning] at hnode
        | base node =>
            by_cases htarget : node = target.1
            · subst node
              exact full.2
            · exact full.1 ⟨node, by
                simpa [sReachConditioning, htarget] using hnode⟩
  left_inv configuration := by
    funext node
    rcases node with ⟨node, hnode⟩
    cases node with
    | mechanism => simp [sReachConditioning] at hnode
    | object graphNode =>
        cases graphNode with
        | utility term => simp [sReachConditioning] at hnode
        | base node =>
            by_cases htarget : node = target.1
            · subst node
              simp
            · simp [htarget]
  right_inv full := by
    apply Prod.ext
    · funext parent
      have hne : parent.1 ≠ target.1 := by
        intro hequal
        apply target_not_observed target
        simpa only [hequal] using parent.2
      simp [hne]
    · simp

private theorem selectorConfigurationEquiv_restrict
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (source : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (mechanismGraphParents view source))
    (assignment : MechanismAssignment view owner) :
    selectorConfigurationEquiv view owner source topological
        (Assignment.restrict
          (mechanismGraphStructure view owner source topological) assignment
          {.mechanism}) =
      (assignment .mechanism).down :=
  rfl

private theorem termConfigurationEquiv_restrict
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (source : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (mechanismGraphParents view source))
    (term : view.UtilitySite owner)
    (assignment : MechanismAssignment view owner) :
    termConfigurationEquiv view owner source topological term
        (Assignment.restrict
          (mechanismGraphStructure view owner source topological) assignment
          {.object (.utility term)}) =
      termConfig view term (projectObjects view assignment) :=
  rfl

private theorem conditioningConfigurationEquiv_restrict
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (source target : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (mechanismGraphParents view source))
    (assignment : MechanismAssignment view owner) :
    conditioningConfigurationEquiv view owner source target topological
        (Assignment.restrict
          (mechanismGraphStructure view owner source topological) assignment
          (sReachConditioning view target)) =
      fullAction view target (projectObjects view assignment) := by
  apply Prod.ext <;> rfl

/-- Non-s-reachability recoded to the concrete observables used by the
two component laws: selector, exact utility configuration, and full target
context/action. -/
theorem selector_term_conditionallyIndependent
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (hnot : ¬ SReachable view source target)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term) :
    IsConditionallyIndependent
      (mechanismSelectorLaw view owner base replacement source sourceRule)
      (fun assignment => (assignment .mechanism).down)
      (fun assignment => termConfig view term (projectObjects view assignment))
      (fun assignment => fullAction view target
        (projectObjects view assignment)) := by
  let mechanismTopological :=
    mechanismAugmentedTopologicalOrder view owner source topological
  have hcoordinates := mechanism_coordinates_conditionallyIndependent
    topological view owner base replacement source target sourceRule hnot term
    hrelevant
  have hrecoded := conditionallyIndependent_map_equiv hcoordinates
    (selectorConfigurationEquiv view owner source mechanismTopological)
    (termConfigurationEquiv view owner source mechanismTopological term)
    (conditioningConfigurationEquiv view owner source target
      mechanismTopological)
  have hselector :
      (selectorConfigurationEquiv view owner source mechanismTopological :
          Config
              (mechanismGraphStructure view owner source mechanismTopological)
              {.mechanism} → Fin 2) ∘
          (fun assignment =>
            Assignment.restrict
              (mechanismGraphStructure view owner source mechanismTopological)
              assignment {.mechanism}) =
        fun assignment => (assignment .mechanism).down := by
    funext assignment
    exact selectorConfigurationEquiv_restrict view owner source
      mechanismTopological assignment
  have hterm :
      (termConfigurationEquiv view owner source mechanismTopological term :
          Config
              (mechanismGraphStructure view owner source mechanismTopological)
              {.object (.utility term)} → TermConfig view term) ∘
          (fun assignment =>
            Assignment.restrict
              (mechanismGraphStructure view owner source mechanismTopological)
              assignment {.object (.utility term)}) =
        fun assignment =>
          termConfig view term (projectObjects view assignment) := by
    funext assignment
    exact termConfigurationEquiv_restrict view owner source
      mechanismTopological term assignment
  have hevidence :
      (conditioningConfigurationEquiv view owner source target
          mechanismTopological :
          Config
              (mechanismGraphStructure view owner source mechanismTopological)
              (sReachConditioning view target) → FullAction target) ∘
          (fun assignment =>
            Assignment.restrict
              (mechanismGraphStructure view owner source mechanismTopological)
              assignment (sReachConditioning view target)) =
        fun assignment => fullAction view target
          (projectObjects view assignment) := by
    funext assignment
    exact conditioningConfigurationEquiv_restrict view owner source target
      mechanismTopological assignment
  rw [hselector, hterm, hevidence] at hrecoded
  exact hrecoded

/-- The selected component before adding the mechanism coordinate. -/
def componentAugmentedLaw
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1)) (selector : Fin 2) :
    FinDist (AugmentedAssignment view owner) :=
  augmentedLaw view owner
    (componentPolicy base owner replacement source sourceRule selector)

/-- Mapping the mechanism law to its selector and any object observable is
the fair bind of the corresponding component observable. -/
theorem mechanismSelectorLaw_map_selector
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    {Result : Type*} (observable : AugmentedAssignment view owner → Result) :
    (mechanismSelectorLaw view owner base replacement source sourceRule).map
        (fun assignment =>
          ((assignment .mechanism).down,
            observable (projectObjects view assignment))) =
      (FinDist.uniformFin 2).bind fun selector =>
        (componentAugmentedLaw view owner base replacement source sourceRule
          selector).map fun assignment => (selector, observable assignment) := by
  unfold mechanismSelectorLaw componentAugmentedLaw
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro selector _
  rw [FinDist.map_comp]
  rfl

private theorem bind_tagged_prob
    {First Second : Type*} (outer : FinDist First)
    (kernel : First → FinDist Second) (first : First) (second : Second) :
    (outer.bind fun candidate =>
      (kernel candidate).map fun value => (candidate, value)).prob
        (first, second) =
      outer.prob first * (kernel first).prob second := by
  exact FinDist.prob_bind_map_prod outer kernel first second

/-- Point masses of selector-tagged observables expose exactly one component
and its fair selector weight. -/
theorem mechanismSelectorLaw_map_selector_prob
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    {Result : Type*} (observable : AugmentedAssignment view owner → Result)
    (selector : Fin 2) (result : Result) :
    ((mechanismSelectorLaw view owner base replacement source sourceRule).map
      (fun assignment =>
        ((assignment .mechanism).down,
          observable (projectObjects view assignment)))).prob
        (selector, result) =
      (FinDist.uniformFin 2).prob selector *
        ((componentAugmentedLaw view owner base replacement source sourceRule
          selector).map observable).prob result := by
  rw [mechanismSelectorLaw_map_selector]
  rw [show (fun selected =>
      (componentAugmentedLaw view owner base replacement source sourceRule
        selected).map fun assignment => (selected, observable assignment)) =
      (fun selected =>
        ((componentAugmentedLaw view owner base replacement source sourceRule
          selected).map observable).map fun value => (selected, value)) by
    funext selected
    rw [FinDist.map_comp]
    rfl]
  exact bind_tagged_prob (FinDist.uniformFin 2)
    (fun selected =>
      (componentAugmentedLaw view owner base replacement source sourceRule
        selected).map observable) selector result

/-- Forgetting the selector gives the fair mixture of the two component
object observables. -/
theorem mechanismSelectorLaw_map_objects
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    {Result : Type*} (observable : AugmentedAssignment view owner → Result) :
    (mechanismSelectorLaw view owner base replacement source sourceRule).map
        (fun assignment => observable (projectObjects view assignment)) =
      (FinDist.uniformFin 2).bind fun selector =>
        (componentAugmentedLaw view owner base replacement source sourceRule
          selector).map observable := by
  unfold mechanismSelectorLaw componentAugmentedLaw
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro selector _
  rw [FinDist.map_comp]
  rfl

/-- An untagged object-observable mass is the arithmetic mean of its two
component masses. -/
theorem mechanismSelectorLaw_map_objects_prob
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    {Result : Type*} (observable : AugmentedAssignment view owner → Result)
    (result : Result) :
    ((mechanismSelectorLaw view owner base replacement source sourceRule).map
      (fun assignment => observable (projectObjects view assignment))).prob
        result =
      (FinDist.uniformFin 2).prob 0 *
          ((componentAugmentedLaw view owner base replacement source sourceRule
            0).map observable).prob result +
        (FinDist.uniformFin 2).prob 1 *
          ((componentAugmentedLaw view owner base replacement source sourceRule
            1).map observable).prob result := by
  rw [mechanismSelectorLaw_map_objects, FinDist.prob_bind,
    FinDist.expect_uniformFin]
  norm_num [FinDist.prob_uniformFin, Fin.sum_univ_two]
  ring

private theorem map_selector_fullTerm_prob_eq_triple
    {Omega Selector Full Term : Type*} (law : FinDist Omega)
    (selector : Omega → Selector) (full : Omega → Full)
    (term : Omega → Term) (selectorValue : Selector)
    (fullValue : Full) (termValue : Term) :
    (law.map fun state => (selector state, (full state, term state))).prob
        (selectorValue, (fullValue, termValue)) =
      law.probOf
        (tripleAtom selector term full selectorValue termValue fullValue) := by
  rw [← FinDist.probOf_singleton, FinDist.probOf_map]
  congr 1
  ext state
  simp only [tripleAtom, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_singleton_iff, Prod.mk.injEq]
  tauto

private theorem map_fullTerm_prob_eq_pair
    {Omega Full Term : Type*} (law : FinDist Omega)
    (full : Omega → Full) (term : Omega → Term)
    (fullValue : Full) (termValue : Term) :
    (law.map fun state => (full state, term state)).prob
        (fullValue, termValue) =
      law.probOf (pairAtom term full termValue fullValue) := by
  rw [← FinDist.probOf_singleton, FinDist.probOf_map]
  congr 1
  ext state
  simp only [pairAtom, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_singleton_iff, Prod.mk.injEq]
  tauto

/-- Division-free component comparison.  At any full target context/action and
term configuration, the baseline and source-changed canonical laws satisfy
the same cross-product identity. -/
theorem componentTerm_cross_product
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (hnot : ¬ SReachable view source target)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term)
    (fullValue : FullAction target) (termValue : TermConfig view term) :
    ((componentAugmentedLaw view owner base replacement source sourceRule 0).map
        (fun assignment =>
          (fullAction view target assignment,
            termConfig view term assignment))).prob (fullValue, termValue) *
      ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
        (fullAction view target)).prob fullValue =
    ((componentAugmentedLaw view owner base replacement source sourceRule 0).map
        (fullAction view target)).prob fullValue *
      ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
        (fun assignment =>
          (fullAction view target assignment,
            termConfig view term assignment))).prob (fullValue, termValue) := by
  let law :=
    mechanismSelectorLaw view owner base replacement source sourceRule
  let selectorObservable := fun assignment : MechanismAssignment view owner =>
    (assignment .mechanism).down
  let fullObservable := fun assignment : MechanismAssignment view owner =>
    fullAction view target (projectObjects view assignment)
  let termObservable := fun assignment : MechanismAssignment view owner =>
    termConfig view term (projectObjects view assignment)
  have hindependent := selector_term_conditionallyIndependent topological view
    owner base replacement source target sourceRule hnot term hrelevant
  have hcross := hindependent (0 : Fin 2) termValue fullValue
  rw [← map_selector_fullTerm_prob_eq_triple law selectorObservable
      fullObservable termObservable 0 fullValue termValue,
    ← map_prob_eq_probOf_atom law fullObservable fullValue,
    ← map_pair_prob_eq_probOf_pairAtom law selectorObservable
      fullObservable 0 fullValue,
    ← map_fullTerm_prob_eq_pair law fullObservable termObservable
      fullValue termValue] at hcross
  dsimp only [law, selectorObservable, fullObservable, termObservable] at hcross
  rw [mechanismSelectorLaw_map_selector_prob view owner base replacement
      source sourceRule
      (fun assignment =>
        (fullAction view target assignment, termConfig view term assignment))
      0 (fullValue, termValue),
    mechanismSelectorLaw_map_objects_prob view owner base replacement source
      sourceRule (fullAction view target) fullValue,
    mechanismSelectorLaw_map_selector_prob view owner base replacement
      source sourceRule (fullAction view target) 0 fullValue,
    mechanismSelectorLaw_map_objects_prob view owner base replacement source
      sourceRule
      (fun assignment =>
        (fullAction view target assignment, termConfig view term assignment))
      (fullValue, termValue)] at hcross
  norm_num [FinDist.prob_uniformFin] at hcross
  nlinarith

end GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorIndependence
