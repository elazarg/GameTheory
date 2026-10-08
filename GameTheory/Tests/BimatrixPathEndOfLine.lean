import GameTheory.Finite.BimatrixPathEndOfLine

/-! End-of-Line source boundary and rational solution existence in a fully tied game. -/
namespace GameTheory.Tests.BimatrixPathEndOfLine
open GameTheory.Finite GameTheory.Math
private def tied : Fin 1 → Fin 2 → ℤ := fun _ _ => 1
private theorem positive : ∀ i j, 0 < tied i j := by intro _ _; exact Int.zero_lt_one
private def dropped : Fin 3 := (finSumFinEquiv : (Fin 1 ⊕ Fin 2) ≃ Fin 3) (.inl 0)

-- The artificial source really is a directed endpoint, but its payoff block is zero.
example : EndOfLine.IsEndpoint
      (BimatrixPathPort.predecessor (by decide) (by decide) positive positive)
      (BimatrixPathPort.successor (by decide) (by decide) positive positive)
      (bimatrixSourcePort tied tied dropped) ∧
    (bimatrixSourcePort tied tied dropped).node.basis.payoffPoint = 0 := by
  constructor
  · exact (BimatrixPathPort.isEndpoint_iff _ _ _ _ _).mpr (bimatrixSource_complementary _ _)
  · exact BimatrixBasis.source_payoffPoint _ _

-- The finite graph argument supplies a nonzero rational solution without analytic existence.
example : ∃ z : Fin 1 ⊕ Fin 2 → ℚ, z ≠ 0 ∧
    LinearComplementarity.IsSolution (fun _ => 1) (bimatrixComplementaryMatrix tied tied) z :=
  BimatrixPathPort.exists_nonzero_complementary_solution (by decide) (by decide) positive positive

-- A valid port away from the dropped label has both incident edges, not an endpoint.
example (port : BimatrixPathPort tied tied dropped) (h : (ofLex port.entering).1 ≠ dropped) :
    ¬EndOfLine.IsEndpoint
      (BimatrixPathPort.predecessor (by decide) (by decide) positive positive)
      (BimatrixPathPort.successor (by decide) (by decide) positive positive) port := by
  intro he
  have hc := (BimatrixPathPort.isEndpoint_iff _ _ _ _ port).mp he
  exact h ((ComplementaryPorts.complementary_port_iff hc _).mp port.permitted).1

end GameTheory.Tests.BimatrixPathEndOfLine
