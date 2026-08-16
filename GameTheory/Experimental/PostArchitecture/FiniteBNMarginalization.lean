/-
# EXP-104: finite Bayesian-network cylinder masses

This experiment connects the local factor algebra to events of a given joint
finite-support law.  Cylinder masses are stated without conditional
probabilities, so impossible evidence remains an ordinary zero-mass case.

The file deliberately assumes a point-mass factorization rather than defining
another Bayesian-network evaluator.  Reverse-topological marginalization is
the next theorem boundary: it must be proved from normalization of the local
kernels before graphical separation can be connected to conditional
independence.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
import GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence
import GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration
import GameTheory.Math.DAG

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization

open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration

universe uNode uValue

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- The probability mass of the cylinder fixed by `witness` on `nodes`. -/
def cylinderMass (law : FinDist (Assignment Value))
    (nodes : Finset Node) (witness : Assignment Value) : ℝ :=
  law.probOf {assignment | AgreeOn Value nodes assignment witness}

/-- A joint law has exactly the point masses prescribed by the local factors. -/
def Factorizes [Fintype Node] (law : FinDist (Assignment Value))
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents) : Prop :=
  ∀ assignment,
    law.prob assignment =
      factorProduct Value parents kernels Finset.univ assignment

/-- Expand a cylinder mass as a finite sum of point masses. -/
theorem cylinderMass_eq_sum [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value)) (nodes : Finset Node)
    (witness : Assignment Value) :
    cylinderMass Value law nodes witness =
      ∑ assignment : Assignment Value,
        if AgreeOn Value nodes assignment witness then law.prob assignment else 0 := by
  classical
  rw [cylinderMass, ← FinDist.expect_indicator_eq_probOf,
    FinDist.expect_eq_sum]
  apply Finset.sum_congr rfl
  intro assignment _
  simp only [Set.mem_setOf_eq]
  by_cases hagrees : AgreeOn Value nodes assignment witness
  · simp [hagrees, mul_one]
  · simp [hagrees]

/-- Under point-mass factorization, a cylinder is exactly the corresponding
finite sum of local factor products.  No normalization of an independently
constructed product law is assumed here. -/
theorem cylinderMass_eq_sum_factorProduct [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (hfactor : Factorizes Value law parents kernels)
    (nodes : Finset Node) (witness : Assignment Value) :
    cylinderMass Value law nodes witness =
      ∑ assignment : Assignment Value,
        if AgreeOn Value nodes assignment witness then
          factorProduct Value parents kernels Finset.univ assignment
        else 0 := by
  rw [cylinderMass_eq_sum Value law nodes witness]
  apply Finset.sum_congr rfl
  intro assignment _
  simp only [hfactor assignment]

theorem agreeOn_mono {smaller larger : Finset Node}
    (hsubset : smaller ⊆ larger) {first second : Assignment Value}
    (hagrees : AgreeOn Value larger first second) :
    AgreeOn Value smaller first second := by
  intro node hnode
  exact hagrees node (hsubset hnode)

/-- Fixing more coordinates produces a subevent of the original cylinder. -/
theorem cylinderEvent_mono {smaller larger : Finset Node}
    (hsubset : smaller ⊆ larger) (witness : Assignment Value) :
    {assignment | AgreeOn Value larger assignment witness} ⊆
      {assignment | AgreeOn Value smaller assignment witness} := by
  intro assignment hagrees
  exact agreeOn_mono Value hsubset hagrees

/-- A cylinder contained in a zero-mass cylinder also has zero mass. -/
theorem cylinderMass_eq_zero_mono
    (law : FinDist (Assignment Value)) {smaller larger : Finset Node}
    (hsubset : smaller ⊆ larger) (witness : Assignment Value)
    (hzero : cylinderMass Value law smaller witness = 0) :
    cylinderMass Value law larger witness = 0 := by
  exact FiniteConditionalIndependence.probOf_eq_zero_of_subset law
    (cylinderEvent_mono Value hsubset witness) hzero

/-! ## The local normalization step used by variable elimination -/

/-- Updating a coordinate outside a node's parent set does not change that
node's parent configuration. -/
theorem parentConfiguration_setOne_of_notMem
    [DecidableEq Node]
    (parents : Node → Finset Node)
    (assignment : Assignment Value) {changed node : Node}
    (value : Value changed) (hnotParent : changed ∉ parents node) :
    parentConfiguration Value parents
        (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) node =
      parentConfiguration Value parents assignment node := by
  funext parent
  have hparentNe : parent.1 ≠ changed := by
    intro heq
    apply hnotParent
    simpa only [heq] using parent.2
  unfold parentConfiguration
  unfold FinDist.DependentAssignment.setOne
  apply FinDist.DependentAssignment.resolve_of_notMem
  simpa only [Finset.mem_singleton] using hparentNe

/-- Updating a node does not change the configuration of its parents in an
acyclic network. -/
theorem parentConfiguration_setOne_self
    [DecidableEq Node]
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (assignment : Assignment Value) (node : Node) (value : Value node) :
    parentConfiguration Value parents
        (FinDist.DependentAssignment.setOne assignment ⟨node, value⟩) node =
      parentConfiguration Value parents assignment node := by
  have hnotSelf : node ∉ parents node := by
    intro hself
    exact (GameTheory.Math.DAG.acyclic_of_topologicalOrder topological node)
      (Relation.TransGen.single hself)
  exact parentConfiguration_setOne_of_notMem Value parents assignment value hnotSelf

/-- A local factor is unchanged when a different, non-parent coordinate is
updated. -/
theorem localFactor_setOne_of_ne_of_notParent
    [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (assignment : Assignment Value) {changed node : Node}
    (value : Value changed) (hne : node ≠ changed)
    (hnotParent : changed ∉ parents node) :
    localFactor Value parents kernels
        (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) node =
      localFactor Value parents kernels assignment node := by
  unfold localFactor
  rw [parentConfiguration_setOne_of_notMem Value parents assignment value hnotParent]
  have hnode :
      FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩ node =
        assignment node := by
    simp [FinDist.DependentAssignment.setOne,
      FinDist.DependentAssignment.resolve, hne]
  rw [hnode]

/-- A product of factors is invariant under changing a coordinate which none
of those factors reads. -/
theorem factorProduct_setOne_of_not_read
    [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (factors : Finset Node) (assignment : Assignment Value)
    {changed : Node} (value : Value changed)
    (hchanged : changed ∉ factors)
    (hnotParent : ∀ node ∈ factors, changed ∉ parents node) :
    factorProduct Value parents kernels factors
        (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) =
      factorProduct Value parents kernels factors assignment := by
  unfold factorProduct
  apply Finset.prod_congr rfl
  intro node hnode
  exact localFactor_setOne_of_ne_of_notParent Value parents kernels assignment value
    (fun heq => hchanged (heq ▸ hnode)) (hnotParent node hnode)

/-- The local factor at a node sums to one when that coordinate varies and all
other coordinates remain fixed.  This is the atomic reverse-elimination step;
the acyclicity premise is needed to keep the parent configuration fixed. -/
theorem sum_localFactor_setOne
    (node : Node) [DecidableEq Node] [Fintype (Value node)]
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (kernels : LocalKernels Value parents)
    (assignment : Assignment Value) :
    ∑ value : Value node,
      localFactor Value parents kernels
        (FinDist.DependentAssignment.setOne assignment ⟨node, value⟩) node = 1 := by
  have hparents (value : Value node) :=
    parentConfiguration_setOne_self Value parents topological assignment node value
  simp_rw [localFactor, hparents]
  have hself (value : Value node) :
      FinDist.DependentAssignment.setOne assignment ⟨node, value⟩ node = value := by
    simp [FinDist.DependentAssignment.setOne,
      FinDist.DependentAssignment.resolve]
  simp_rw [hself]
  exact FinDist.sum_prob _

/-- Eliminate one factor whose coordinate is not read by any remaining
factor.  This is the reusable algebraic step in reverse-topological
marginalization. -/
theorem sum_factorProduct_setOne
    (changed : Node) [DecidableEq Node] [Fintype (Value changed)]
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (kernels : LocalKernels Value parents)
    (factors : Finset Node) (assignment : Assignment Value)
    (hchanged : changed ∈ factors)
    (hnotRead : ∀ node ∈ factors.erase changed,
      changed ∉ parents node) :
    ∑ value : Value changed,
      factorProduct Value parents kernels factors
        (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) =
      factorProduct Value parents kernels (factors.erase changed) assignment := by
  have hdisjoint : Disjoint ({changed} : Finset Node) (factors.erase changed) := by
    simp
  have hcover : ({changed} : Finset Node) ∪ factors.erase changed = factors := by
    simpa only [Finset.singleton_union] using Finset.insert_erase hchanged
  have hsplit (value : Value changed) :
      factorProduct Value parents kernels factors
          (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) =
        factorProduct Value parents kernels {changed}
            (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) *
          factorProduct Value parents kernels (factors.erase changed)
            (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) := by
    calc
      factorProduct Value parents kernels factors
          (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) =
          factorProduct Value parents kernels
            ({changed} ∪ factors.erase changed)
            (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) := by
              rw [hcover]
      _ = _ := factorProduct_union Value parents kernels hdisjoint _
  simp_rw [hsplit]
  have hrest (value : Value changed) :
      factorProduct Value parents kernels (factors.erase changed)
          (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) =
        factorProduct Value parents kernels (factors.erase changed) assignment :=
    factorProduct_setOne_of_not_read Value parents kernels
      (factors.erase changed) assignment value (by simp)
        hnotRead
  simp_rw [hrest]
  rw [← Finset.sum_mul]
  have hsingleton (value : Value changed) :
      factorProduct Value parents kernels {changed}
          (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) =
        localFactor Value parents kernels
          (FinDist.DependentAssignment.setOne assignment ⟨changed, value⟩) changed := by
    simp [factorProduct]
  simp_rw [hsingleton]
  rw [sum_localFactor_setOne Value changed parents topological kernels assignment,
    one_mul]

private theorem cylinderMass_eq_factorProduct_of_pending
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (kernels : LocalKernels Value parents)
    (hfactor : Factorizes Value law parents kernels) :
    ∀ pending : List Node,
      pending.Nodup →
      pending.Pairwise (fun earlier later => later ∉ parents earlier) →
      ∀ (retained : Finset Node) (witness : Assignment Value),
        (∀ node ∈ pending, node ∉ retained) →
        retained ∪ pending.toFinset = Finset.univ →
        ParentClosed parents retained →
        cylinderMass Value law retained witness =
          factorProduct Value parents kernels retained witness := by
  intro pending
  induction pending with
  | nil =>
      intro _ _ retained witness _ hcover _
      have hretained : retained = Finset.univ := by
        simpa using hcover
      subst retained
      let emptyConfiguration : ComplementConfiguration Value Finset.univ :=
        fun node => False.elim (node.2 (Finset.mem_univ node.1))
      letI : Unique (ComplementConfiguration Value Finset.univ) :=
        { default := emptyConfiguration
          uniq := fun configuration => by
            funext node
            exact False.elim (node.2 (Finset.mem_univ node.1)) }
      rw [cylinderMass_eq_sum_factorProduct Value law parents kernels hfactor]
      rw [sum_ite_agrees_eq_sum_complement]
      rw [Fintype.sum_unique]
      apply congrArg (factorProduct Value parents kernels Finset.univ)
      funext node
      exact fillComplement_of_mem Value Finset.univ witness default
        (Finset.mem_univ node)
  | cons head tail ih =>
      intro hnodup hordered retained witness houtside hcover hclosed
      have hheadOutside : head ∉ retained :=
        houtside head (by simp)
      have htailNodup : tail.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hheadTail : head ∉ tail :=
        (List.nodup_cons.mp hnodup).1
      have hheadOrdered : ∀ later ∈ tail, later ∉ parents head :=
        (List.pairwise_cons.mp hordered).1
      have htailOrdered :
          tail.Pairwise (fun earlier later => later ∉ parents earlier) :=
        (List.pairwise_cons.mp hordered).2
      have htailOutside : ∀ node ∈ tail, node ∉ insert head retained := by
        intro node hnode
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun heq => hheadTail (heq ▸ hnode),
          houtside node (by simp [hnode])⟩
      have hcoverTail : insert head retained ∪ tail.toFinset = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro node
        have hcovered : node ∈ retained ∪ (head :: tail).toFinset := by
          rw [hcover]
          exact Finset.mem_univ node
        rcases Finset.mem_union.mp hcovered with hretained | hpending
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hretained)
        · have hcases : node = head ∨ node ∈ tail := by
            simpa using hpending
          rcases hcases with heq | htail
          · subst node
            exact Finset.mem_union_left _ (Finset.mem_insert_self head retained)
          · exact Finset.mem_union_right _ (by simpa using htail)
      have hclosedTail : ParentClosed parents (insert head retained) := by
        intro node hnode parent hparent
        rcases Finset.mem_insert.mp hnode with heq | hnode
        · subst node
          have hcovered : parent ∈ retained ∪ (head :: tail).toFinset := by
            rw [hcover]
            exact Finset.mem_univ parent
          rcases Finset.mem_union.mp hcovered with hretained | hpending
          · exact Finset.mem_insert_of_mem hretained
          · have hcases : parent = head ∨ parent ∈ tail := by
              simpa using hpending
            rcases hcases with heq | htail
            · subst parent
              exact False.elim
                ((GameTheory.Math.DAG.acyclic_of_topologicalOrder
                    topological head) (Relation.TransGen.single hparent))
            · exact False.elim (hheadOrdered parent htail hparent)
        · exact Finset.mem_insert_of_mem (hclosed node hnode hparent)
      have hinduction (value : Value head) :=
        ih htailNodup htailOrdered (insert head retained)
          (FinDist.DependentAssignment.setOne witness ⟨head, value⟩)
          htailOutside hcoverTail hclosedTail
      have hnotRead : ∀ node ∈ (insert head retained).erase head,
          head ∉ parents node := by
        intro node hnode hparent
        apply hheadOutside
        apply hclosed node
        · simpa [hheadOutside] using hnode
        · exact hparent
      calc
        cylinderMass Value law retained witness =
            ∑ assignment : Assignment Value,
              if AgreeOn Value retained assignment witness then
                factorProduct Value parents kernels Finset.univ assignment
              else 0 :=
          cylinderMass_eq_sum_factorProduct Value law parents kernels
            hfactor retained witness
        _ = ∑ value : Value head,
              ∑ assignment : Assignment Value,
                if AgreeOn Value (insert head retained) assignment
                    (FinDist.DependentAssignment.setOne witness ⟨head, value⟩)
                then factorProduct Value parents kernels Finset.univ assignment
                else 0 :=
          sum_ite_agrees_eq_sum_insert Value retained hheadOutside witness
            (factorProduct Value parents kernels Finset.univ)
        _ = ∑ value : Value head,
              cylinderMass Value law (insert head retained)
                (FinDist.DependentAssignment.setOne witness ⟨head, value⟩) := by
          apply Finset.sum_congr rfl
          intro value _
          symm
          exact cylinderMass_eq_sum_factorProduct Value law parents kernels
            hfactor (insert head retained)
              (FinDist.DependentAssignment.setOne witness ⟨head, value⟩)
        _ = ∑ value : Value head,
              factorProduct Value parents kernels (insert head retained)
                (FinDist.DependentAssignment.setOne witness ⟨head, value⟩) := by
          apply Finset.sum_congr rfl
          intro value _
          exact hinduction value
        _ = factorProduct Value parents kernels retained witness := by
          simpa [hheadOutside] using
            sum_factorProduct_setOne Value head parents topological kernels
              (insert head retained) witness (by simp) hnotRead

/-- Marginalizing every coordinate outside a parent-closed set leaves exactly
the product of the retained local factors.  No positivity hypothesis is
needed: the statement is about cylinder masses, including zero-mass ones. -/
theorem cylinderMass_eq_factorProduct_of_parentClosed
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (kernels : LocalKernels Value parents)
    (hfactor : Factorizes Value law parents kernels)
    (retained : Finset Node) (witness : Assignment Value)
    (hclosed : ParentClosed parents retained) :
    cylinderMass Value law retained witness =
      factorProduct Value parents kernels retained witness := by
  let pending := topological.order.filter (fun node => node ∉ retained)
  have horderedFull : topological.order.Pairwise
      (fun earlier later => later ∉ parents earlier) := by
    rw [List.pairwise_iff_getElem]
    intro firstIndex laterIndex hfirstBound hlaterBound hlt hedge
    obtain ⟨parentIndex, hparentLt, hparent⟩ :=
      topological.respects ⟨firstIndex, hfirstBound⟩
        topological.order[laterIndex] hedge
    have hindexEq : parentIndex = ⟨laterIndex, hlaterBound⟩ :=
      topological.nodup.get_inj_iff.mp hparent
    have hvalueEq : parentIndex.val = laterIndex := by
      simpa using congrArg Fin.val hindexEq
    rw [hvalueEq] at hparentLt
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hlt)) hparentLt
  have hnodup : pending.Nodup := by
    exact topological.nodup.filter _
  have hordered : pending.Pairwise
      (fun earlier later => later ∉ parents earlier) := by
    exact horderedFull.filter _
  have houtside : ∀ node ∈ pending, node ∉ retained := by
    intro node hnode
    exact of_decide_eq_true (List.mem_filter.mp hnode).2
  have hcover : retained ∪ pending.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro node
    by_cases hnode : node ∈ retained
    · exact Finset.mem_union_left _ hnode
    · apply Finset.mem_union_right
      simpa [pending, hnode] using topological.complete node
  exact cylinderMass_eq_factorProduct_of_pending Value law parents topological
    kernels hfactor pending hnodup hordered retained witness houtside hcover hclosed

/-! ## A finite normalization control -/

namespace BoolControl

abbrev BoolNode := Unit

abbrev BoolValue (_ : BoolNode) := Bool

def falseAssignment : Assignment BoolValue := fun _ => false

def falseLaw : FinDist (Assignment BoolValue) :=
  FinDist.pure falseAssignment

def parents (_ : BoolNode) : Finset BoolNode := ∅

def topological : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [()]
  nodup := by simp
  complete := by
    intro node
    simp only [Unit.ext node, List.mem_singleton]
  respects := by
    intro index parent hparent
    simp [parents] at hparent

def kernels : LocalKernels BoolValue parents :=
  fun _ _ => FinDist.pure false

/-- The one-node factor product normalizes by the same atomic elimination
lemma needed in the general reverse-topological proof. -/
theorem factorProduct_sum :
    ∑ value : Bool,
      factorProduct BoolValue parents kernels Finset.univ
        (FinDist.DependentAssignment.setOne falseAssignment ⟨(), value⟩) = 1 := by
  have heliminate := sum_factorProduct_setOne BoolValue () parents topological
    kernels Finset.univ falseAssignment (Finset.mem_univ ()) (by simp [parents])
  simpa [factorProduct] using heliminate

/-- The unconstrained cylinder is the whole sample space and has mass one. -/
theorem empty_cylinderMass :
    cylinderMass BoolValue falseLaw ∅ falseAssignment = 1 := by
  classical
  apply FinDist.probOf_pure_self
  simp [AgreeOn]

/-- An impossible value of the Boolean coordinate has zero cylinder mass. -/
theorem true_cylinderMass :
    cylinderMass BoolValue falseLaw Finset.univ (fun _ => true) = 0 := by
  rw [cylinderMass]
  have hset :
      {assignment | AgreeOn BoolValue Finset.univ assignment (fun _ => true)} =
        ({assignment | assignment () = true} : Set (Assignment BoolValue)) := by
    ext assignment
    constructor
    · intro hagrees
      exact hagrees () (Finset.mem_univ ())
    · intro hat node _
      change assignment () = true at hat
      simpa only [Unit.ext node] using hat
  rw [hset]
  classical
  unfold falseLaw
  rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure]
  simp [falseAssignment]

namespace TwoNode

inductive ChainNode
  | root
  | leaf
  deriving DecidableEq, Fintype

abbrev ChainValue (_ : ChainNode) := Bool

def parents : ChainNode → Finset ChainNode
  | .root => ∅
  | .leaf => {.root}

def topological : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.root, .leaf]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · have hroot : parent = .root := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩

def kernels : LocalKernels ChainValue parents :=
  fun _ _ => FinDist.pure false

def law : FinDist (Assignment ChainValue) :=
  FinDist.pi fun _ => FinDist.pure false

def allFalse : Assignment ChainValue := fun _ => false

def retained : Finset ChainNode := {.root}

theorem factorizes : Factorizes ChainValue law parents kernels := by
  intro assignment
  rw [law, FinDist.prob_pi]
  simp [factorProduct, localFactor, kernels]

theorem retained_parentClosed : ParentClosed parents retained := by
  intro node hnode
  cases node <;> simp [retained, parents] at hnode ⊢

/-- Eliminating the Boolean leaf leaves the normalized root factor. -/
theorem root_cylinderMass :
    cylinderMass ChainValue law retained allFalse = 1 := by
  rw [cylinderMass_eq_factorProduct_of_parentClosed ChainValue law parents
    topological kernels factorizes retained allFalse retained_parentClosed]
  simp [factorProduct, localFactor, kernels, retained, allFalse]

end TwoNode

end BoolControl

end GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
