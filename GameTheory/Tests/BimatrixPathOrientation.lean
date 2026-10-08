import GameTheory.Finite.BimatrixPathOrientation

/-! The color reversal law excludes fixed switching ports. -/
namespace GameTheory.Tests.BimatrixPathOrientation
open GameTheory.Finite GameTheory.Math
private def tied : Fin 1 → Fin 2 → ℤ := fun _ _ => 1
private def dropped : Fin 3 := (finSumFinEquiv : (Fin 1 ⊕ Fin 2) ≃ Fin 3) (.inl 0)

example : (bimatrixSourcePort tied tied dropped).color = true := BimatrixPathPort.source_color

-- A terminal's switching color stays the same, so unconditional reversal would be false.
example : (bimatrixSourcePort tied tied dropped).switch.color ≠
    !(bimatrixSourcePort tied tied dropped).color := by
  rw [bimatrixSourcePort_switch, BimatrixPathPort.source_color]
  decide

-- Internal ports have nonzero orientation and reverse color when changing twins.
example (port : BimatrixPathPort tied tied dropped) (hd : (ofLex port.entering).1 ≠ dropped) :
    port.orientationScore ≠ 0 ∧ port.switch.color = !port.color := by
  refine ⟨port.orientationScore_ne_zero, port.color_switch ?_⟩
  intro he
  have hc := port.switch_eq_self_iff.mp he
  exact hd ((ComplementaryPorts.complementary_port_iff hc _).mp port.permitted).1

end GameTheory.Tests.BimatrixPathOrientation
