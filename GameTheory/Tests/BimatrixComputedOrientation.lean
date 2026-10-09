import GameTheory.Finite.BimatrixComputedOrientation

/-! Integer color agreement at the source and across both port operations. -/
namespace GameTheory.Tests.BimatrixComputedOrientation
open GameTheory.Finite
private def tied : Fin 1 → Fin 2 → ℤ := fun _ _ => 1

example : (bimatrixSourcePort tied tied 0).computedColor = true := by
  rw [BimatrixPathPort.computedColor_eq]
  exact BimatrixPathPort.source_color

example (port : BimatrixPathPort tied tied 0) :
    port.computedColor = port.color := port.computedColor_eq

example (port : BimatrixPathPort tied tied 0) (h : port.switch ≠ port) :
    port.switch.computedColor = !port.computedColor := by
  rw [BimatrixPathPort.computedColor_eq, BimatrixPathPort.computedColor_eq]
  exact port.color_switch h

example (port : BimatrixPathPort tied tied 0) :
    (port.pivot (by decide) (by decide) (by decide) (by decide)).computedColor =
      !port.computedColor := by
  rw [BimatrixPathPort.computedColor_eq, BimatrixPathPort.computedColor_eq]
  exact port.color_pivot (by decide) (by decide) (by decide) (by decide)

end GameTheory.Tests.BimatrixComputedOrientation
