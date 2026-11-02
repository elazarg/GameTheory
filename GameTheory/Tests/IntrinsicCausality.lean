module

/-
# Intrinsic causality regressions

The schedule itself must depend only on nature and predecessor decisions.
These fixtures reject anticipatory scheduling and the noncausal clapping-hands
information structure, while accepting an order that branches on a completed
decision.
-/

public import GameTheory.Languages.Intrinsic.Solution
public import Mathlib.Logic.Equiv.Bool

@[expose] public section

namespace GameTheory.Tests.IntrinsicCausality

open GameTheory.Languages.Intrinsic

/-- A two-agent feedback model whose first observation is the other decision
and whose second observation can reveal its own decision. -/
@[reducible]
def anticipatory : Model where
  Agent := Bool
  Nature := Unit
  Decision _ := Bool
  info
    | false =>
        { r := fun left right => left.decision true = right.decision true
          iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩ }
    | true =>
        { r := fun left right =>
            (left.decision false && !left.decision true) =
              (right.decision false && !right.decision true)
          iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩ }

/-- The proposed first agent is selected by agent `true`'s future decision. -/
def anticipatorySchedule : anticipatory.Schedule 2 where
  orderAt c := if c.decision true then finTwoEquiv.trans Equiv.boolNot else finTwoEquiv

/-- The first scheduled agent is precisely the future Boolean decision. -/
theorem anticipatorySchedule_zero (c : anticipatory.Configuration) :
    anticipatorySchedule.orderAt c 0 = c.decision true := by
  cases h : c.decision true <;> simp [anticipatorySchedule, h, finTwoEquiv]

/-- Equal nature states cannot choose different first agents in a causal
schedule, even if information would be local inside each schedule cell. -/
theorem anticipatorySchedule_not_causal :
    ¬ Model.IsCausalWith anticipatorySchedule := by
  intro hcausal
  let left : anticipatory.Configuration := ⟨(), fun _ => false⟩
  let right : anticipatory.Configuration := ⟨(), fun agent => agent⟩
  have hprefix := (hcausal left right (0 : Fin 2)
    ⟨rfl, fun earlier hearlier => by omega⟩).1
  have hfirst := hprefix 0 (by decide)
  rw [anticipatorySchedule_zero, anticipatorySchedule_zero] at hfirst
  exact Bool.false_ne_true hfirst

/-- Constant `true` for the first agent and copying the second observation
force the second agent to negate its own decision. -/
def anticipatoryProfile : anticipatory.PureProfile
  | false => ⟨fun _ => true, fun _ _ _ => rfl⟩
  | true => ⟨fun c => c.decision false && !c.decision true, fun _ _ h => h⟩

/-- The feedback model has an admissible pure profile without any solution. -/
theorem anticipatory_not_solvable : ¬ anticipatory.IsSolvable := by
  intro hsolvable
  obtain ⟨decision, hfixed, -⟩ := hsolvable anticipatoryProfile ()
  have hfalse : decision false = true := hfixed false
  have htrue : decision true = (decision false && !decision true) := hfixed true
  rw [hfalse] at htrue
  cases h : decision true <;> simp [h] at htrue

/-- Three Boolean decisions with no nature uncertainty. -/
abbrev ThreeConfiguration := Config Unit (Fin 3) (fun _ => Bool)

/-- Each agent hears a clap exactly when its two neighbors choose opposite
hands in the indicated cyclic direction. -/
def clapObservation (agent : Fin 3) (configuration : ThreeConfiguration) : Bool :=
  if agent = 0 then configuration.decision 1 && !configuration.decision 2
  else if agent = 1 then configuration.decision 2 && !configuration.decision 0
  else configuration.decision 0 && !configuration.decision 1

/-- The clapping-hands information structure is given by equality of each
agent's Boolean observation. -/
@[reducible]
def clappingHands : Model where
  Agent := Fin 3
  Nature := Unit
  Decision _ := Bool
  info agent :=
    { r := fun left right => clapObservation agent left = clapObservation agent right
      iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩ }

/-- Every agent has nonconstant information, so no agent can act first.
The rejection holds for every exhaustive schedule and every slot count. -/
theorem clappingHands_not_causal {slots : Nat}
    (schedule : clappingHands.Schedule slots) :
    ¬ Model.IsCausalWith schedule := by
  intro hcausal
  let base : clappingHands.Configuration := ⟨(), fun _ => false⟩
  have hslots : 0 < slots :=
    Nat.zero_lt_of_lt ((schedule.orderAt base).symm 0).isLt
  let first : Fin slots := ⟨0, hslots⟩
  have hinfo (right : clappingHands.Configuration) :
      clapObservation (schedule.orderAt base first) base =
        clapObservation (schedule.orderAt base first) right :=
    (hcausal base right first ⟨rfl, fun earlier hearlier => by
      change earlier.val < 0 at hearlier
      omega⟩).2
  have hagent : (schedule.orderAt base first).val = 0 ∨
      (schedule.orderAt base first).val = 1 ∨ (schedule.orderAt base first).val = 2 := by
    have hbound := (schedule.orderAt base first).isLt
    omega
  rcases hagent with hzero | hone | htwo
  · have h := hinfo ⟨(), fun agent => decide (agent = 1)⟩
    rw [show schedule.orderAt base first = 0 from Fin.ext hzero] at h
    change false = true at h
    exact Bool.false_ne_true h
  · have h := hinfo ⟨(), fun agent => decide (agent = 2)⟩
    rw [show schedule.orderAt base first = 1 from Fin.ext hone] at h
    change false = true at h
    exact Bool.false_ne_true h
  · have h := hinfo ⟨(), fun agent => decide (agent = 0)⟩
    rw [show schedule.orderAt base first = 2 from Fin.ext htwo] at h
    change false = true at h
    exact Bool.false_ne_true h

/-- Agent zero has no information; the other agents observe only its decision. -/
def predecessorInfo (agent : Fin 3) : Setoid ThreeConfiguration :=
  if agent = 0 then
    { r := fun _ _ => True
      iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ }
  else
    { r := fun left right => left.decision 0 = right.decision 0
      iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩ }

/-- A first agent supplies the only information used by the later agents. -/
@[reducible]
def predecessorBranching : Model where
  Agent := Fin 3
  Nature := Unit
  Decision _ := Bool
  info := predecessorInfo

/-- The order of the later agents depends only on the completed first decision. -/
def predecessorBranchingSchedule : predecessorBranching.Schedule 3 where
  orderAt configuration :=
    if configuration.decision 0 then Equiv.swap (1 : Fin 3) 2 else Equiv.refl _

/-- Agent zero always acts first. -/
theorem predecessorBranchingSchedule_zero
    (configuration : predecessorBranching.Configuration) :
    predecessorBranchingSchedule.orderAt configuration 0 = 0 := by
  cases h : configuration.decision 0 <;>
    simp [predecessorBranchingSchedule, h, Equiv.swap_apply_of_ne_of_ne]

/-- The completed first decision determines both the later order and all
information used by the remaining agents. -/
theorem predecessorBranching_isCausal :
    Model.IsCausalWith predecessorBranchingSchedule := by
  intro left right slot hagree
  by_cases hslot : slot = 0
  · subst slot
    constructor
    · intro earlier hearlier
      have heq : earlier = (0 : Fin 3) := Fin.ext (by omega)
      subst earlier
      rw [predecessorBranchingSchedule_zero, predecessorBranchingSchedule_zero]
    · rw [predecessorBranchingSchedule_zero]
      trivial
  · have hpos : 0 < slot.val := by
      by_contra h
      exact hslot (Fin.ext (by omega))
    have hzero := hagree.2 (0 : Fin 3) hpos
    rw [predecessorBranchingSchedule_zero] at hzero
    have horder : predecessorBranchingSchedule.orderAt left =
        predecessorBranchingSchedule.orderAt right := by
      simp only [predecessorBranchingSchedule, hzero]
    constructor
    · intro earlier _
      rw [horder]
    · have hne : predecessorBranchingSchedule.orderAt left slot ≠ 0 := by
        intro heq
        apply hslot
        apply (predecessorBranchingSchedule.orderAt left).injective
        rw [heq, predecessorBranchingSchedule_zero]
      change (predecessorInfo (predecessorBranchingSchedule.orderAt left slot)).r left right
      rw [predecessorInfo, ite_eq_right hne]
      exact hzero

/-- Both later orders actually occur. -/
theorem predecessorBranchingSchedule_nonconstant :
    predecessorBranchingSchedule.orderAt ⟨(), fun _ => false⟩ 1 ≠
      predecessorBranchingSchedule.orderAt ⟨(), fun _ => true⟩ 1 := by
  decide

/-- Causality supplies unique closed-loop solutions for every information-local
profile on the genuinely branching schedule. -/
theorem predecessorBranching_isSolvable : predecessorBranching.IsSolvable :=
  Model.isSolvable_of_isCausalWith predecessorBranching_isCausal
    (fun _ => ⟨false⟩)

/-- An empty decision carrier makes the complete configuration space empty. -/
@[reducible]
def emptyDecision : Model where
  Agent := Unit
  Nature := Unit
  Decision _ := Empty
  info _ :=
    { r := fun _ _ => True
      iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ }

/-- Empty configuration space makes even an exhaustive schedule vacuous. -/
def emptyDecisionSchedule : emptyDecision.Schedule 1 where
  orderAt configuration := (configuration.decision ()).elim

/-- The empty configuration space satisfies causality vacuously. -/
theorem emptyDecision_isCausal : Model.IsCausalWith emptyDecisionSchedule := by
  intro left _ _ _
  exact (left.decision ()).elim

/-- Information-local rules still exist on the empty configuration space. -/
def emptyDecisionProfile : emptyDecision.PureProfile := fun _ =>
  { act := fun configuration => configuration.decision ()
    respects := fun left _ _ => (left.decision ()).elim }

/-- Nonempty decisions are necessary when deriving solvability from causality:
there cannot be a solution with an empty decision coordinate. -/
theorem emptyDecision_not_solvable : ¬ emptyDecision.IsSolvable := by
  intro hsolvable
  obtain ⟨decision, _, _⟩ := hsolvable emptyDecisionProfile ()
  exact (decision ()).elim

end GameTheory.Tests.IntrinsicCausality
