/-
# Discrete eventual properties

The minimal order-only combinator shared by finite-horizon equilibrium
notions. It deliberately avoids the topology-facing filter API: both current
consumers need the explicit threshold as data.
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
