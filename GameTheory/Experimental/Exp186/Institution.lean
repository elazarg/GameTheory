module

public import GameTheory.Experimental.Exp186.ContractAcceptance
public import GameTheory.Experimental.Exp186.BundleChoice

@[expose] public section

namespace GameTheory.Experimental.ContractChoice

/-- The set-based acceptance law and its finite bundle rationalization are
the same choice, not merely two examples with similar descriptions. -/
theorem quota_coe (offered : Finset (Fin 3)) :
    (quotaFinset offered : Set (Fin 3)) = quotaSet (offered : Set (Fin 3)) := by
  ext contract
  by_cases top : 0 ∈ offered ∧ 1 ∈ offered
  · simp [quotaFinset, quotaSet, top]
  · simp [quotaFinset, quotaSet, top]

theorem complement_coe (offered : Finset Bool) :
    (complementFinset offered : Set Bool) = complements (offered : Set Bool) := by
  ext contract
  by_cases pair : false ∈ offered ∧ true ∈ offered
  · simp [complementFinset, complements, pair]
  · simp [complementFinset, complements, pair]

/-- Quota acceptance supports the reduction used in contract stability. -/
theorem quota_joint_singleton {incumbent proposed : Set (Fin 3)}
    (accepted : proposed ⊆ quotaSet (incumbent ∪ proposed)) :
    ∀ contract ∈ proposed, contract ∈ quotaSet (insert contract incumbent) :=
  joint_acceptance_singleton quotaSet (fun _ _ subset => quota_chernoff subset) accepted

end GameTheory.Experimental.ContractChoice
