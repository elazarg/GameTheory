/-
# Finite histories supply a certified horizon

A finite carrier of complete legal histories has a uniform bound on trace
length. The bound is obtained only when needed and is not stored in protocol
data. Finiteness here concerns histories, so finite-state protocols with cycles
do not satisfy the premise merely because their state carrier is finite.
-/

import GameTheory.Protocol.History

namespace GameTheory.Protocol.ExecutionProtocol

universe uι us ua

variable {ι : Type uι} (E : ExecutionProtocol.{uι, us, ua} ι)

/-- Finite complete histories admit a positive certified execution bound.
Taking one more than the greatest legal trace length makes any history of
that length impossible, and in particular rules out nonterminal ones. -/
theorem exists_pos_boundedHorizon [Fintype E.History] :
    ∃ bound, 0 < bound ∧ E.BoundedHorizon bound := by
  classical
  let longest := Finset.univ.sup (fun history : E.History => history.trace.length)
  refine ⟨longest + 1, Nat.succ_pos _, ?_⟩
  intro state trace lengthBound
  have lengthUpper : trace.length ≤ longest :=
    Finset.le_sup (f := fun history : E.History => history.trace.length)
      (Finset.mem_univ (⟨state, trace⟩ : E.History))
  exact False.elim (by omega)

end GameTheory.Protocol.ExecutionProtocol
