import GameTheoryComplexity.Backend.GeneralBimatrixCodec
import GameTheoryComplexity.Backend.BimatrixCertificateVerifier

/-! Polynomial-time parsers for the three unary headers of a rectangular binary game. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- The initial unary row header is polynomial-time. -/
theorem generalRowRuler_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalRowRuler (v 0) := certificateDimensionWord_cobham

/-- Parsing the column header after the first delimiter is polynomial-time. -/
theorem generalColRuler_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalColRuler (v 0) := by
  have hd := Cobham.dropFn
    (Cobham.appendFn generalRowRuler_cobham (Cobham.const [false])) (.proj 0)
  exact (Cobham.comp certificateDimensionWord_cobham fun _ => hd).of_eq fun v => by
    simp only [List.length_append, List.length_singleton]
    rfl

/-- Parsing the coefficient-width header is polynomial-time. -/
theorem generalBitsRuler_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalBitsRuler (v 0) := by
  have hd := Cobham.dropFn
    (Cobham.appendFn (Cobham.appendFn generalRowRuler_cobham generalColRuler_cobham)
      (Cobham.const [false, false])) (.proj 0)
  exact (Cobham.comp certificateDimensionWord_cobham fun _ => hd).of_eq fun v => by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rfl

/-- Removing the three headers and delimiters is polynomial-time. -/
theorem generalPayload_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalPayload (v 0) := by
  exact (Cobham.dropFn
    (Cobham.appendFn
      (Cobham.appendFn (Cobham.appendFn generalRowRuler_cobham generalColRuler_cobham)
        generalBitsRuler_cobham) (Cobham.const [false, false, false]))
    (.proj 0)).of_eq fun v => by
      simp only [List.length_append, List.length_cons, List.length_nil]
      rfl

end GameTheory.Complexity.Backend
