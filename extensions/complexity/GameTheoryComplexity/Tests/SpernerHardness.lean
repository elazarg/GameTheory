import GameTheoryComplexity.Backend.GridSpernerColorMachine
import GameTheoryComplexity.Backend.GridRoutingOriginalGraph
import GameTheoryComplexity.Backend.SpernerRoutingDecoderMachine

/-! Routed color-query controls exercise extended coordinate fields, the source
entrance, disconnected endpoint components, and unconditional decoder fallback. -/

namespace GameTheory.Complexity.Tests.SpernerHardness

open GameTheory.Complexity.Backend GameTheory.Math.GridWire GameTheory.Math.Sperner
open _root_.Complexity _root_.Complexity.Cobham

private def ruler : List Bool := [false,false,false]

private def fixtureS (i : ℕ) : ℕ := if i=0 then 1 else if i=2 then 3 else i
private def fixtureP (i : ℕ) : ℕ := if i=1 then 0 else if i=3 then 2 else i
private def Pquery (word : List Bool) : List Bool :=
  Nat.toBitsLE 3 (fixtureP (Nat.fromBitsLE word))
private def Squery (word : List Bool) : List Bool :=
  Nat.toBitsLE 3 (fixtureS (Nat.fromBitsLE word))

private def query (x y : ℕ) : List Bool :=
  Nat.toBitsLE ((routingSpernerRuler ruler).length+1) x ++
    Nat.toBitsLE ((routingSpernerRuler ruler).length+1) y

private def color (x y : ℕ) : Fin 3 :=
  decodeGridColor (routingSpernerColorQuery ruler Pquery Squery (query x y))

private theorem color_agreement {x y : ℕ} (hx : x<32768) (hy : y<32768) :
    color x y=gridSpernerRoutingInterior 8
      (routingOriginalPointer ruler Pquery) (routingOriginalPointer ruler Squery) x y := by
  unfold color query
  rw [routingSpernerColorQuery_encode ruler Pquery Squery
    (by simpa [ruler] using hx) (by simpa [ruler] using hy),decodeGridColor_encode]
  rfl

example : ¬Trichromatic (color 8 8) (color 9 8) (color 9 9) := by
  rw [color_agreement (by decide) (by decide),color_agreement (by decide) (by decide),
    color_agreement (by decide) (by decide)]
  decide

example : Trichromatic (color 8 80) (color 9 80) (color 9 81) ∧
    Trichromatic (color 8 116) (color 9 116) (color 9 117) := by
  constructor <;>
    rw [color_agreement (by decide) (by decide),color_agreement (by decide) (by decide),
      color_agreement (by decide) (by decide)] <;> decide

example (word : List Bool) :
    (routingSpernerColorQuery [] (fun _ => []) (fun _ => []) word).length=2 := by
  rw [routingSpernerColorQuery_value]
  have h : ∀ c : Fin 3, (encodeGridColor c).length=2 := by decide
  exact h _

example : routingSpernerColorQuery [] (fun _ => []) (fun _ => []) []=encodeGridColor 0 := by
  rw [routingSpernerColorQuery_value]
  rfl

example : (fun z => routingSpernerColorQuery z (fun v => z ++ v)
    (fun v => v ++ z) z) ∈ FP :=
  routingSpernerColorQueryUniformFn_mem_FP (fun seed v => seed ++ v)
    (fun seed v => v ++ seed) id_mem_FP id_mem_FP id_mem_FP
    (appendFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)

example (word : List Bool) : routingSpernerDecode [] word=[] := by
  exact routingSpernerDecode_invalid (by intro h; exact h.2.1 rfl) word

example : routingSpernerLabelBits ruler
    (encodeGridNode (routingSpernerRuler ruler).length (some ⟨8,116,false⟩))=
      Nat.toBitsLE 3 3 := by
  apply routingSpernerLabelBits_eq_bits
  · apply decodeGridNode_encode
    intro t ht
    cases ht
    decide
  · rfl

end GameTheory.Complexity.Tests.SpernerHardness


