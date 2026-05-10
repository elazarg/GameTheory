import Mathlib.Data.Finset.Basic

/-!
# Generic joint actions

This module contains the optional joint-action vocabulary shared by native
machine game forms and factored-observation stochastic games.  It deliberately
does not depend on any game-language presentation.
-/

namespace GameTheory

/-- Joint action profile with optional participation for each player. -/
abbrev JointAction {ι : Type} (Act : ι → Type) : Type :=
  ∀ i, Option (Act i)

/-- Factorized legality of a joint action: every active player chooses an
available action, and inactive players choose `none`. -/
def JointActionLegal {ι W : Type}
    (Act : ι → Type)
    (active : W → Finset ι)
    (terminal : W → Prop)
    (availableActions : W → (i : ι) → Set (Act i))
    (w : W) (a : JointAction Act) : Prop :=
  ¬ terminal w ∧
    ∀ i, match a i with
      | some ai => i ∈ active w ∧ ai ∈ availableActions w i
      | none => i ∉ active w

/-- The all-`none` joint action. -/
def noopAction {ι : Type} (Act : ι → Type) : JointAction Act :=
  fun _ => none

@[simp] theorem noopAction_apply {ι : Type} (Act : ι → Type) (i : ι) :
    noopAction Act i = none := rfl

end GameTheory
