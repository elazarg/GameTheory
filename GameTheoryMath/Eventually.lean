/-
# Discrete eventual properties

The minimal order-only combinator shared by finite-horizon equilibrium
notions. It keeps the public statement in explicit threshold form and avoids
making these definitions depend on the topology-facing filter API.
-/

import Mathlib.Data.Nat.Basic

namespace GameTheoryMath

/-- `property` holds at every natural index beyond one explicit threshold. -/
def EventuallyAtAll (property : ℕ → Prop) : Prop :=
  ∃ threshold : ℕ, ∀ index, threshold ≤ index → property index

/-- Pointwise implication preserves an eventual-at-all certificate. -/
theorem EventuallyAtAll.mono {property property' : ℕ → Prop}
    (h : EventuallyAtAll property)
    (hmono : ∀ index, property index → property' index) :
    EventuallyAtAll property' := by
  obtain ⟨threshold, hthreshold⟩ := h
  exact ⟨threshold, fun index hindex => hmono index (hthreshold index hindex)⟩

end GameTheoryMath
