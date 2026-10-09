import GameTheory.Math.ComplementaryPorts

/-! Endpoint and internal port controls for a dropped label. -/

namespace GameTheory.Tests.ComplementaryPorts
open GameTheory.Math.ComplementaryPorts GameTheory.Math.ComplementaryLabels
open GameTheory.Math.FiniteBasisExchange

private def endpoint : Finset (Fin 2 × Bool) := {(0, false), (1, false)}
private def internal : Finset (Fin 2 × Bool) := {(1, false), (1, true)}

example : IsComplementary endpoint := by dsimp only [IsPort, IsComplementary, CoversExcept]; decide
example : ∃! v, IsPort endpoint 0 v :=
  exists_unique_port 0 (by dsimp only [IsPort, IsComplementary, CoversExcept]; decide)
example : IsPort endpoint 0 (0, false) := by
  dsimp only [IsPort, IsComplementary, CoversExcept]; decide
example : ¬ IsPort endpoint 0 (1, false) := by
  dsimp only [IsPort, IsComplementary, CoversExcept]; decide
example : switch endpoint 0 (0, false) = (0, false) := by decide

example : CoversExcept internal 0 := by dsimp only [IsPort, IsComplementary, CoversExcept]; decide
example : ¬ IsComplementary internal := by
  dsimp only [IsPort, IsComplementary, CoversExcept]; decide
example : IsPort internal 0 (1, false) ∧ IsPort internal 0 (1, true) := by
  dsimp only [IsPort, IsComplementary, CoversExcept]; decide
example : ¬ IsPort internal 0 (0, false) := by
  dsimp only [IsPort, IsComplementary, CoversExcept]; decide
example : switch internal 0 (1, false) = (1, true) := by decide
example : switch internal 0 (switch internal 0 (1, false)) = (1, false) :=
  switch_switch _ _ _

-- The reversed exchange enters a valid endpoint port.
example : IsPort (exchange internal (1, false) (0, true)) 0 (0, true) :=
  exchange_isPort (by dsimp only [CoversExcept]; decide)
    (by dsimp only [IsPort]; decide) (by decide)

-- Removing the endpoint port can expose a duplicated-label internal vertex.
example : IsPort (exchange endpoint (0, false) (1, true)) 0 (1, true) :=
  exchange_isPort (by dsimp only [CoversExcept]; decide)
    (by dsimp only [IsPort]; decide) (by decide)

example : CoversExcept (exchange endpoint (0, false) (1, true)) 0 :=
  exchange_covers (by dsimp only [IsPort, IsComplementary, CoversExcept]; decide)
    (by dsimp only [IsPort, IsComplementary, CoversExcept]; decide)

-- Internal switching has no fixed point, justified by the endpoint criterion.
example : switch internal 0 (1, false) ≠ (1, false) := by
  intro h
  have hc := (switch_eq_self_iff_complementary (by decide : internal.card = Fintype.card (Fin 2))
    (by dsimp only [IsPort, IsComplementary, CoversExcept]; decide : CoversExcept internal 0)
    (by dsimp only [IsPort, IsComplementary, CoversExcept]; decide :
      IsPort internal 0 (1, false))).mp h
  exact (by dsimp only [IsPort, IsComplementary, CoversExcept]; decide :
    ¬ IsComplementary internal) hc

end GameTheory.Tests.ComplementaryPorts
