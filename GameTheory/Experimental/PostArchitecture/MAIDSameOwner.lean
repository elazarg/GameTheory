/-
# EXP-038: same-owner incomparable MAID decisions

This is the strategy-space falsifier missing from EXP-037. One source player
owns two incomparable Boolean decisions. The left decision observes only the
left Boolean parent and the right decision observes only the right parent.

A native policy is site-local by type. A naive per-player frontier compiler
instead gives one policy the combined view and asks for both actions at once.
The cross-reading compiled policy below is legal for that interface but cannot
come from any native policy.
-/

import Mathlib.Data.Bool.Basic

namespace GameTheory.Experimental.MAIDSameOwner

inductive Site
  | left
  | right
  deriving DecidableEq

structure Parents where
  leftSignal : Bool
  rightSignal : Bool
  deriving DecidableEq

structure Decisions where
  leftAction : Bool
  rightAction : Bool
  deriving DecidableEq

/-- A native rule receives exactly the observed parents of its decision site. -/
def NativePolicy := (site : Site) → Bool → Bool

/-- Native simultaneous evaluation preserves site-local observation. -/
def nativeDecisions (policy : NativePolicy) (parents : Parents) : Decisions where
  leftAction := policy .left parents.leftSignal
  rightAction := policy .right parents.rightSignal

/-- The tempting Protocol-facing interface: one source player sees the whole
frontier view and returns the whole frontier action. -/
def BatchedPolicy := Parents → Decisions

/-- Each decision reads the parent observed only by the other decision site. -/
def crossReading : BatchedPolicy := fun parents =>
  { leftAction := parents.rightSignal
    rightAction := parents.leftSignal }

def Representable (batched : BatchedPolicy) : Prop :=
  ∃ native : NativePolicy, ∀ parents, nativeDecisions native parents = batched parents

theorem native_left_independent_of_right
    (policy : NativePolicy) (left right₁ right₂ : Bool) :
    (nativeDecisions policy ⟨left, right₁⟩).leftAction =
      (nativeDecisions policy ⟨left, right₂⟩).leftAction := rfl

theorem native_right_independent_of_left
    (policy : NativePolicy) (left₁ left₂ right : Bool) :
    (nativeDecisions policy ⟨left₁, right⟩).rightAction =
      (nativeDecisions policy ⟨left₂, right⟩).rightAction := rfl

theorem crossReading_left_depends_on_right :
    (crossReading ⟨false, false⟩).leftAction ≠
      (crossReading ⟨false, true⟩).leftAction := by
  decide

theorem crossReading_right_depends_on_left :
    (crossReading ⟨false, false⟩).rightAction ≠
      (crossReading ⟨true, false⟩).rightAction := by
  decide

/-- The combined-view batched policy space is strictly too large: it contains
an action rule with no site-local native preimage. -/
theorem crossReading_not_representable : ¬ Representable crossReading := by
  rintro ⟨policy, hpolicy⟩
  have hleft := congrArg Decisions.leftAction
    (hpolicy ⟨false, false⟩)
  have hright := congrArg Decisions.leftAction
    (hpolicy ⟨false, true⟩)
  have hindependent :=
    native_left_independent_of_right policy false false true
  exact crossReading_left_depends_on_right
    (hleft.symm.trans (hindependent.trans hright))

end GameTheory.Experimental.MAIDSameOwner
