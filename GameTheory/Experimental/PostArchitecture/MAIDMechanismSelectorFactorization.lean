/-
# EXP-107: mechanism-selector factorization

A fair proof-side selector chooses between two canonical owner policies that
differ only at one source decision.  The selector is the genuine mechanism
root used by `SReachable`; object coordinates are the existing deterministic
utility augmentation of canonical native play.

This file constructs no alternate evaluator and states no conditional
independence, optimality, coverage, or equilibrium theorem.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
import GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
import GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorFactorization

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph.UtilityView
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
open GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

/-- The mechanism root stores the selected component.  Object nodes retain
the existing base or exact utility-configuration value. -/
def mechanismGraphValue (view : UtilityView semantics) {owner : Player} :
    MechanismGraphNode view owner → Type (max uNode uValue)
  | .mechanism => ULift.{max uNode uValue} (Fin 2)
  | .object node => graphValue view node

/-- A dependent assignment on the mechanism-augmented utility graph. -/
abbrev MechanismAssignment (view : UtilityView semantics) (owner : Player) :=
  (node : MechanismGraphNode view owner) → mechanismGraphValue view node

/-- The mechanism graph is one root plus the existing utility graph. -/
def mechanismGraphNodeEquiv (view : UtilityView semantics) (owner : Player) :
    MechanismGraphNode view owner ≃ Unit ⊕ view.GraphNode owner where
  toFun
    | .mechanism => Sum.inl ()
    | .object node => Sum.inr node
  invFun
    | Sum.inl _ => .mechanism
    | Sum.inr node => .object node
  left_inv node := by cases node <;> rfl
  right_inv node := by cases node <;> rfl

instance mechanismGraphNodeFintype [Fintype Node]
    (view : UtilityView semantics) (owner : Player) :
    Fintype (MechanismGraphNode view owner) :=
  Fintype.ofEquiv (Unit ⊕ view.GraphNode owner)
    (mechanismGraphNodeEquiv view owner).symm

instance mechanismGraphValueFintype
    [DecidableEq Node] [∀ node, Fintype (diagram.Value node)]
    (view : UtilityView semantics) {owner : Player}
    (node : MechanismGraphNode view owner) :
    Fintype (mechanismGraphValue view node) := by
  cases node with
  | mechanism =>
      unfold mechanismGraphValue
      infer_instance
  | object node => exact graphValueFintype view node

instance mechanismGraphValueDecidableEq
    [DecidableEq Node] [∀ node, DecidableEq (diagram.Value node)]
    (view : UtilityView semantics) {owner : Player}
    (node : MechanismGraphNode view owner) :
    DecidableEq (mechanismGraphValue view node) := by
  cases node with
  | mechanism =>
      unfold mechanismGraphValue
      infer_instance
  | object node => exact graphValueDecidableEq view node

/-- Add the selected mechanism value to an existing augmented assignment. -/
def mechanismAugment (view : UtilityView semantics) {owner : Player}
    (selector : Fin 2) (assignment : AugmentedAssignment view owner) :
    MechanismAssignment view owner
  | .mechanism => ULift.up selector
  | .object node => assignment node

/-- Forget the mechanism root. -/
def projectObjects (view : UtilityView semantics) {owner : Player}
    (assignment : MechanismAssignment view owner) :
    AugmentedAssignment view owner :=
  fun node => assignment (.object node)

@[simp]
theorem mechanismAugment_mechanism (view : UtilityView semantics)
    {owner : Player} (selector : Fin 2)
    (assignment : AugmentedAssignment view owner) :
    (mechanismAugment view selector assignment .mechanism).down = selector :=
  rfl

@[simp]
theorem mechanismAugment_object (view : UtilityView semantics)
    {owner : Player} (selector : Fin 2)
    (assignment : AugmentedAssignment view owner)
    (node : view.GraphNode owner) :
    mechanismAugment view selector assignment (.object node) =
      assignment node :=
  rfl

@[simp]
theorem projectObjects_mechanismAugment (view : UtilityView semantics)
    {owner : Player} (selector : Fin 2)
    (assignment : AugmentedAssignment view owner) :
    projectObjects view (mechanismAugment view selector assignment) =
      assignment :=
  rfl

theorem mechanismAugment_injective (view : UtilityView semantics)
    {owner : Player} (selector : Fin 2) :
    Function.Injective (mechanismAugment view (owner := owner) selector) := by
  intro first second hequal
  funext node
  exact congrFun hequal (.object node)

/-- Mechanism first, followed by the existing augmented object order. -/
def mechanismAugmentedOrder (view : UtilityView semantics) (owner : Player)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    List (MechanismGraphNode view owner) :=
  .mechanism ::
    (augmentedOrder view owner topological).map
      MechanismGraphNode.object

@[simp]
theorem mechanismAugmentedOrder_length
    (view : UtilityView semantics) (owner : Player)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    (mechanismAugmentedOrder view owner topological).length =
      (augmentedOrder view owner topological).length + 1 := by
  simp [mechanismAugmentedOrder]

private theorem objectParent_mem_mechanismGraphParents
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (source : DecisionSite diagram owner) (node parent : view.GraphNode owner)
    (hparent : parent ∈ view.graphParents node) :
    (.object parent : MechanismGraphNode view owner) ∈
      mechanismGraphParents view source (.object node) := by
  cases node with
  | utility term =>
      simpa [mechanismGraphParents,
        UtilityView.graphParents] using hparent
  | base node =>
      by_cases hsource : node = source.1
      · simp [mechanismGraphParents, hsource,
          UtilityView.graphParents] at hparent ⊢
        exact hparent
      · simp [mechanismGraphParents, hsource,
          UtilityView.graphParents] at hparent ⊢
        exact hparent

private theorem objectParent_of_mem_mechanismGraphParents
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (source : DecisionSite diagram owner) (node parent : view.GraphNode owner)
    (hparent : (.object parent : MechanismGraphNode view owner) ∈
      mechanismGraphParents view source (.object node)) :
    parent ∈ view.graphParents node := by
  cases node with
  | utility term =>
      simpa [mechanismGraphParents,
        UtilityView.graphParents] using hparent
  | base node =>
      by_cases hsource : node = source.1
      · simp [mechanismGraphParents, hsource,
          UtilityView.graphParents] at hparent ⊢
        exact hparent
      · simp [mechanismGraphParents, hsource,
          UtilityView.graphParents] at hparent ⊢
        exact hparent

/-- Prefixing the mechanism root preserves the augmented topological order. -/
def mechanismAugmentedTopologicalOrder [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (source : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    GameTheory.Math.DAG.TopologicalOrder
      (mechanismGraphParents view source) where
  order := mechanismAugmentedOrder view owner topological
  nodup := by
    rw [mechanismAugmentedOrder, List.nodup_cons]
    constructor
    · simp
    · exact (augmentedTopologicalOrder view owner topological).nodup.map
        fun _ _ hequal => MechanismGraphNode.object.inj hequal
  complete node := by
    cases node with
    | mechanism => simp [mechanismAugmentedOrder]
    | object node =>
        simp only [mechanismAugmentedOrder, List.mem_cons,
          List.mem_map]
        exact Or.inr ⟨node,
          (augmentedTopologicalOrder view owner topological).complete node,
          rfl⟩
  respects := by
    intro index parent hparent
    rcases index with ⟨index, hindex⟩
    cases index with
    | zero =>
        simp [mechanismAugmentedOrder,
          mechanismGraphParents] at hparent
    | succ objectIndex =>
        have hobjectBound :
            objectIndex < (augmentedOrder view owner topological).length := by
          simpa [mechanismAugmentedOrder] using hindex
        let objectFin : Fin (augmentedOrder view owner topological).length :=
          ⟨objectIndex, hobjectBound⟩
        let mechanismFin :
            Fin (mechanismAugmentedOrder view owner topological).length :=
          ⟨objectIndex + 1, hindex⟩
        have hchild :
            (mechanismAugmentedOrder view owner
              topological)[mechanismFin] =
              MechanismGraphNode.object
                ((augmentedOrder view owner topological)[objectFin]) := by
          simp [mechanismAugmentedOrder, mechanismFin, objectFin]
        cases parent with
        | mechanism =>
            exact ⟨⟨0, by simp [mechanismAugmentedOrder]⟩,
              Nat.zero_lt_succ objectIndex, by
                simp [mechanismAugmentedOrder]⟩
        | object parent =>
            have hparentObject : parent ∈ view.graphParents
                ((augmentedOrder view owner topological)[objectFin]) := by
              apply objectParent_of_mem_mechanismGraphParents view source
              have hparent' :
                  MechanismGraphNode.object parent ∈
                    mechanismGraphParents view source
                      ((mechanismAugmentedOrder view owner
                        topological)[mechanismFin]) := by
                exact hparent
              rw [hchild] at hparent'
              exact hparent'
            obtain ⟨earlier, hearlier, heq⟩ :=
              (augmentedTopologicalOrder view owner topological).respects
                objectFin parent hparentObject
            have hearlierBound :
                earlier.val + 1 <
                  (mechanismAugmentedOrder view owner topological).length := by
              rw [mechanismAugmentedOrder, List.length_cons,
                List.length_map]
              exact Nat.succ_lt_succ earlier.isLt
            let earlierMechanism :
                Fin (mechanismAugmentedOrder view owner topological).length :=
              ⟨earlier.val + 1, hearlierBound⟩
            refine ⟨earlierMechanism, Nat.succ_lt_succ hearlier, ?_⟩
            have hobjectValue :
                (augmentedOrder view owner topological)[earlier] = parent :=
              heq
            rw [Fin.getElem_fin]
            unfold mechanismAugmentedOrder
            rw [List.getElem_cons_succ, List.getElem_map]
            rw [Fin.getElem_fin] at hobjectValue
            exact congrArg MechanismGraphNode.object hobjectValue

/-- The unchanged owner replacement embedded in the original profile. -/
def baselinePolicy [DecidableEq Player] (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner) :
    Policy diagram :=
  Profile.update (sig := nativeBehavioralSignature diagram)
    base owner replacement

/-- Component zero is the baseline replacement.  Component one changes only
the source rule inside that replacement. -/
def componentPolicy [DecidableEq Player] [DecidableEq Node]
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1)) (selector : Fin 2) :
    Policy diagram :=
  if selector = 0 then baselinePolicy base owner replacement
  else
    Profile.update (sig := nativeBehavioralSignature diagram) base owner
      (replaceSiteRule replacement source sourceRule)

/-- A fair selector followed by the corresponding canonical augmented native
play, injected into the mechanism graph. -/
def mechanismSelectorLaw
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1)) :
    FinDist (MechanismAssignment view owner) :=
  (FinDist.uniformFin 2).bind fun selector =>
    (augmentedLaw view owner
      (componentPolicy base owner replacement source sourceRule selector)).map
        (mechanismAugment view selector)

/-- Recode the object-parent portion of a mechanism configuration as the
corresponding parent configuration in the existing utility graph. -/
def objectParentConfiguration [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (source : DecisionSite diagram owner) (node : view.GraphNode owner)
    (configuration : ParentConfiguration
      (mechanismGraphValue view (owner := owner))
      (mechanismGraphParents view source) (.object node)) :
    ParentConfiguration (graphValue view (owner := owner))
      (view.graphParents (owner := owner)) node :=
  fun parent => configuration
    ⟨.object parent.1,
      objectParent_mem_mechanismGraphParents view source node parent.1
        parent.2⟩

private theorem mechanism_mem_sourceParents [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (source : DecisionSite diagram owner) :
    (.mechanism : MechanismGraphNode view owner) ∈
      mechanismGraphParents view source (.object (.base source.1)) := by
  simp [mechanismGraphParents]

/-- Read the selected finite component from the mechanism parent of the
source decision. -/
def sourceSelector [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (source : DecisionSite diagram owner)
    (configuration : ParentConfiguration
      (mechanismGraphValue view (owner := owner))
      (mechanismGraphParents view source) (.object (.base source.1))) : Fin 2 :=
  (configuration
    ⟨.mechanism, mechanism_mem_sourceParents view source⟩).down

/-- Local kernels on the exact mechanism graph.  Only the source decision can
inspect the selector; every other object uses the baseline component kernel.
-/
def mechanismSelectorKernels
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1)) :
    LocalKernels (mechanismGraphValue view (owner := owner))
      (mechanismGraphParents view source) :=
  fun node configuration => by
    cases node with
    | mechanism =>
        exact (FinDist.uniformFin 2).map ULift.up
    | object graphNode =>
        cases graphNode with
        | utility site =>
            exact augmentedKernels view
              (baselinePolicy base owner replacement) (.utility site)
              (objectParentConfiguration view source (.utility site)
                configuration)
        | base node =>
            by_cases hsource : node = source.1
            · subst node
              let selector := sourceSelector view source configuration
              exact augmentedKernels view
                (componentPolicy base owner replacement source sourceRule
                  selector) (.base source.1)
                (objectParentConfiguration view source (.base source.1)
                  configuration)
            · exact augmentedKernels view
                (baselinePolicy base owner replacement) (.base node)
                (objectParentConfiguration view source (.base node)
                  configuration)

/-- Every mechanism assignment is recovered from its selector coordinate and
object projection. -/
theorem mechanismAugment_projectObjects (view : UtilityView semantics)
    {owner : Player} (assignment : MechanismAssignment view owner) :
    mechanismAugment view (assignment .mechanism).down
        (projectObjects view assignment) = assignment := by
  funext node
  cases node with
  | mechanism =>
      apply ULift.ext
      rfl
  | object _ => rfl

private theorem prob_bind_eq_chosen_mul
    {Alpha Beta : Type*} (law : FinDist Alpha)
    (continuation : Alpha → FinDist Beta) (chosen : Alpha) (target : Beta)
    (hoffTarget : ∀ value ∈ law.support, value ≠ chosen →
      (continuation value).prob target = 0) :
    (law.bind continuation).prob target =
      law.prob chosen * (continuation chosen).prob target := by
  classical
  rw [FinDist.prob_bind, FinDist.expect_eq_sum_support]
  by_cases hchosen : chosen ∈ law.support
  · rw [Finset.sum_eq_single chosen]
    · intro value hvalue hne
      rw [hoffTarget value (FinDist.mem_supportFinset.mp hvalue) hne,
        mul_zero]
    · intro hnot
      exact absurd (FinDist.mem_supportFinset.mpr hchosen) hnot
  · rw [FinDist.prob_eq_zero_iff.mpr hchosen, zero_mul]
    apply Finset.sum_eq_zero
    intro value hvalue
    have hsupport := FinDist.mem_supportFinset.mp hvalue
    have hne : value ≠ chosen := by
      intro hequal
      subst value
      exact hchosen hsupport
    rw [hoffTarget value hsupport hne, mul_zero]

/-- Point masses of the selector law split into the fair selector mass and
the selected canonical augmented-law mass. -/
theorem mechanismSelectorLaw_prob
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, DecidableEq (diagram.Value node)]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (assignment : MechanismAssignment view owner) :
    (mechanismSelectorLaw view owner base replacement source sourceRule).prob
        assignment =
      (FinDist.uniformFin 2).prob (assignment .mechanism).down *
        (augmentedLaw view owner
          (componentPolicy base owner replacement source sourceRule
            (assignment .mechanism).down)).prob
          (projectObjects view assignment) := by
  let chosen := (assignment .mechanism).down
  unfold mechanismSelectorLaw
  rw [prob_bind_eq_chosen_mul (FinDist.uniformFin 2)
    (fun selector =>
      (augmentedLaw view owner
        (componentPolicy base owner replacement source sourceRule
          selector)).map (mechanismAugment view selector)) chosen assignment]
  · apply congrArg ((FinDist.uniformFin 2).prob chosen * ·)
    rw [← mechanismAugment_projectObjects view assignment]
    exact FinDist.prob_map_of_injective
      (mechanismAugment view chosen) (mechanismAugment_injective view chosen)
      _ _
  · intro selector _ hselector
    apply FinDist.prob_eq_zero_iff.mpr
    rw [FinDist.support_map]
    rintro ⟨objects, _, hequal⟩
    apply hselector
    calc
      selector =
          (mechanismAugment view selector objects .mechanism).down := rfl
      _ = (assignment .mechanism).down :=
        congrArg ULift.down (congrFun hequal .mechanism)

private theorem componentPolicy_apply_of_ne_source
    [DecidableEq Player] [DecidableEq Node]
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1)) (selector : Fin 2)
    (otherOwner : Player) (site : DecisionSite diagram otherOwner)
    (hne : site.1 ≠ source.1) :
    componentPolicy base owner replacement source sourceRule selector
        otherOwner site =
      baselinePolicy base owner replacement otherOwner site := by
  unfold componentPolicy
  by_cases hselector : selector = 0
  · simp [hselector]
  · simp only [hselector, if_false, baselinePolicy]
    by_cases howner : otherOwner = owner
    · subst otherOwner
      rw [Profile.update_same, Profile.update_same]
      apply replaceSiteRule_of_ne
      intro hsite
      exact hne (congrArg Subtype.val hsite)
    · rw [Profile.update_of_ne
        (sig := nativeBehavioralSignature diagram) base _ howner,
        Profile.update_of_ne
          (sig := nativeBehavioralSignature diagram) base replacement howner]

private theorem augmentedKernels_component_eq_baseline_of_ne
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1)) (selector : Fin 2)
    (node : view.GraphNode owner)
    (hne : node ≠ (.base source.1 : view.GraphNode owner)) :
    augmentedKernels view
        (componentPolicy base owner replacement source sourceRule selector)
        node =
      augmentedKernels view (baselinePolicy base owner replacement) node := by
  cases node with
  | utility _ => rfl
  | base node =>
      have hnode : node ≠ source.1 := by
        intro hequal
        subst node
        exact hne rfl
      funext configuration
      rw [augmentedKernels_base, augmentedKernels_base]
      unfold effectiveKernels
      split
      · rfl
      · rename_i siteOwner hkind
        rw [componentPolicy_apply_of_ne_source base owner replacement source
          sourceRule selector siteOwner ⟨node, hkind⟩ hnode]

@[simp]
theorem objectParentConfiguration_parentConfiguration
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (source : DecisionSite diagram owner)
    (assignment : MechanismAssignment view owner)
    (node : view.GraphNode owner) :
    objectParentConfiguration view source node
        (parentConfiguration
          (mechanismGraphValue view (owner := owner))
          (mechanismGraphParents view source) assignment (.object node)) =
      parentConfiguration (graphValue view (owner := owner))
        (view.graphParents (owner := owner))
        (projectObjects view assignment) node := by
  funext parent
  rfl

@[simp]
theorem sourceSelector_parentConfiguration
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (source : DecisionSite diagram owner)
    (assignment : MechanismAssignment view owner) :
    sourceSelector view source
        (parentConfiguration
          (mechanismGraphValue view (owner := owner))
          (mechanismGraphParents view source) assignment
          (.object (.base source.1))) =
      (assignment .mechanism).down :=
  rfl

/-- At every object, the mechanism kernel read from a full assignment is the
selected component's canonical augmented kernel. -/
theorem mechanismSelectorKernels_object_parentConfiguration
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (assignment : MechanismAssignment view owner)
    (node : view.GraphNode owner) :
    mechanismSelectorKernels view owner base replacement source sourceRule
        (.object node)
        (parentConfiguration
          (mechanismGraphValue view (owner := owner))
          (mechanismGraphParents view source) assignment (.object node)) =
      augmentedKernels view
        (componentPolicy base owner replacement source sourceRule
          (assignment .mechanism).down) node
        (parentConfiguration (graphValue view (owner := owner))
          (view.graphParents (owner := owner))
          (projectObjects view assignment) node) := by
  cases node with
  | utility site =>
      rw [augmentedKernels_component_eq_baseline_of_ne view owner base
        replacement source sourceRule (assignment .mechanism).down
        (.utility site) (by intro hequal; cases hequal)]
      simp [mechanismSelectorKernels]
  | base node =>
      by_cases hsource : node = source.1
      · subst node
        simp [mechanismSelectorKernels]
      · rw [augmentedKernels_component_eq_baseline_of_ne view owner base
          replacement source sourceRule (assignment .mechanism).down
          (.base node) (by
            intro hequal
            exact hsource (UtilityView.GraphNode.base.inj hequal))]
        simp [mechanismSelectorKernels, hsource]

/-- The root local factor is exactly the fair mass of the selector stored in
the assignment. -/
theorem mechanismSelector_localFactor_mechanism
    [DecidableEq Player] [DecidableEq Node]
    [∀ node, DecidableEq (diagram.Value node)]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (assignment : MechanismAssignment view owner) :
    localFactor (mechanismGraphValue view (owner := owner))
        (mechanismGraphParents view source)
        (mechanismSelectorKernels view owner base replacement source sourceRule)
        assignment .mechanism =
      (FinDist.uniformFin 2).prob (assignment .mechanism).down := by
  unfold localFactor mechanismSelectorKernels
  have hlift : assignment .mechanism =
      ULift.up (assignment .mechanism).down := by
    apply ULift.ext
    rfl
  rw [hlift]
  exact FinDist.prob_map_of_injective ULift.up
    (fun first second hequal => congrArg ULift.down hequal)
    (FinDist.uniformFin 2) _

/-- Every object local factor is the corresponding local factor of the
selected canonical augmented component. -/
theorem mechanismSelector_localFactor_object
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (assignment : MechanismAssignment view owner)
    (node : view.GraphNode owner) :
    localFactor (mechanismGraphValue view (owner := owner))
        (mechanismGraphParents view source)
        (mechanismSelectorKernels view owner base replacement source sourceRule)
        assignment (.object node) =
      localFactor (graphValue view (owner := owner))
        (view.graphParents (owner := owner))
        (augmentedKernels view
          (componentPolicy base owner replacement source sourceRule
            (assignment .mechanism).down))
        (projectObjects view assignment) node := by
  unfold localFactor
  rw [mechanismSelectorKernels_object_parentConfiguration]
  rfl

/-- The full mechanism factor product is the selector factor times the
selected component's existing augmented factor product. -/
theorem mechanismSelector_factorProduct
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, DecidableEq (diagram.Value node)]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (assignment : MechanismAssignment view owner) :
    factorProduct (mechanismGraphValue view (owner := owner))
        (mechanismGraphParents view source)
        (mechanismSelectorKernels view owner base replacement source sourceRule)
        Finset.univ assignment =
      (FinDist.uniformFin 2).prob (assignment .mechanism).down *
        factorProduct (graphValue view (owner := owner))
          (view.graphParents (owner := owner))
          (augmentedKernels view
            (componentPolicy base owner replacement source sourceRule
              (assignment .mechanism).down))
          Finset.univ (projectObjects view assignment) := by
  simp only [factorProduct]
  calc
    _ = ∏ node : Unit ⊕ view.GraphNode owner,
        Sum.elim
          (fun _ =>
            localFactor (mechanismGraphValue view (owner := owner))
              (mechanismGraphParents view source)
              (mechanismSelectorKernels view owner base replacement source
                sourceRule) assignment .mechanism)
          (fun object =>
            localFactor (mechanismGraphValue view (owner := owner))
              (mechanismGraphParents view source)
              (mechanismSelectorKernels view owner base replacement source
                sourceRule) assignment (.object object)) node := by
      apply Fintype.prod_equiv (mechanismGraphNodeEquiv view owner)
      intro node
      cases node <;> rfl
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp_rw [mechanismSelector_localFactor_mechanism,
        mechanismSelector_localFactor_object]
      simp

/-- The fair two-component image of canonical native play factorizes over the
exact mechanism graph used by `SReachable`. -/
theorem mechanismSelectorLaw_factorizes
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1)) :
    Factorizes (mechanismGraphValue view (owner := owner))
      (mechanismSelectorLaw view owner base replacement source sourceRule)
      (mechanismGraphParents view source)
      (mechanismSelectorKernels view owner base replacement source
        sourceRule) := by
  intro assignment
  calc
    (mechanismSelectorLaw view owner base replacement source sourceRule).prob
        assignment =
      (FinDist.uniformFin 2).prob (assignment .mechanism).down *
        (augmentedLaw view owner
          (componentPolicy base owner replacement source sourceRule
            (assignment .mechanism).down)).prob
          (projectObjects view assignment) :=
      mechanismSelectorLaw_prob view owner base replacement source sourceRule
        assignment
    _ = (FinDist.uniformFin 2).prob (assignment .mechanism).down *
        factorProduct (graphValue view (owner := owner))
          (view.graphParents (owner := owner))
          (augmentedKernels view
            (componentPolicy base owner replacement source sourceRule
              (assignment .mechanism).down)) Finset.univ
          (projectObjects view assignment) := by
      apply congrArg ((FinDist.uniformFin 2).prob
        (assignment .mechanism).down * ·)
      exact augmentedLaw_factorizes topological view owner
        (componentPolicy base owner replacement source sourceRule
          (assignment .mechanism).down) (projectObjects view assignment)
    _ = factorProduct (mechanismGraphValue view (owner := owner))
        (mechanismGraphParents view source)
        (mechanismSelectorKernels view owner base replacement source sourceRule)
        Finset.univ assignment :=
      (mechanismSelector_factorProduct view owner base replacement source
        sourceRule assignment).symm

end GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorFactorization
