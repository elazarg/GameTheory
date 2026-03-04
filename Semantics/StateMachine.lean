import Mathlib.Data.Set.Basic

set_option autoImplicit false

namespace Semantics
namespace Machine

universe u v

/-- Unlabeled one-step transition relation. -/
abbrev RelStep (σ : Type*) := σ → σ → Prop

/-- Labeled one-step transition relation. -/
abbrev LabeledRelStep (α σ : Type*) := α → σ → σ → Prop

/-- Unlabeled set-valued transition function. -/
abbrev SetStep (σ : Type*) := σ → Set σ

/-- Labeled set-valued transition function. -/
abbrev LabeledSetStep (α σ : Type*) := σ → α → Set σ

/-- Generic monadic one-step transition (Kleisli arrow). -/
abbrev KleisliStep (M : Type u → Type v) (σ : Type u) [Monad M] := σ → M σ

/-- Generic labeled monadic one-step transition (emits a label with next state). -/
abbrev LabeledKleisliStep (M : Type u → Type v) (α σ : Type u) [Monad M] :=
  σ → M (α × σ)

/-- Coalgebraic transition interface. -/
abbrev Coalgebra (F : Type u → Type v) (σ : Type u) := σ → F σ

/-- Minimal labeled state machine wrapper in relational form. -/
structure LSM (α σ : Type*) where
  step : LabeledRelStep α σ

variable {α σ : Type*}

/-- Erase labels from a labeled transition relation. -/
def eraseLabel (step : LabeledRelStep α σ) : RelStep σ :=
  fun s t => ∃ a, step a s t

/-- Convert a relation into a set-valued transition map. -/
def relToSet (step : RelStep σ) : SetStep σ :=
  fun s => { t | step s t }

/-- Convert a set-valued transition map into a relation. -/
def setToRel (step : SetStep σ) : RelStep σ :=
  fun s t => t ∈ step s

/-- Convert a labeled relation into a labeled set-valued map. -/
def labeledRelToSet (step : LabeledRelStep α σ) : LabeledSetStep α σ :=
  fun s a => { t | step a s t }

/-- Convert a labeled set-valued map into a labeled relation. -/
def labeledSetToRel (step : LabeledSetStep α σ) : LabeledRelStep α σ :=
  fun a s t => t ∈ step s a

@[simp] theorem setToRel_relToSet (step : RelStep σ) :
    setToRel (relToSet step) = step := rfl

@[simp] theorem relToSet_setToRel (step : SetStep σ) :
    relToSet (setToRel step) = step := by
  funext s
  ext t
  rfl

@[simp] theorem labeledSetToRel_labeledRelToSet (step : LabeledRelStep α σ) :
    labeledSetToRel (labeledRelToSet step) = step := rfl

@[simp] theorem labeledRelToSet_labeledSetToRel (step : LabeledSetStep α σ) :
    labeledRelToSet (labeledSetToRel step) = step := by
  funext s a
  ext t
  rfl

theorem eraseLabel_lsm_step (M : LSM α σ) :
    eraseLabel M.step = fun s t => ∃ a, M.step a s t := rfl

end Machine
end Semantics
