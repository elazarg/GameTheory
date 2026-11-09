module

public import GameTheoryComplexity.Backend.GridSpernerColorMachine
public import GameTheoryComplexity.Backend.GridRoutingOriginalGraph
public import GameTheoryComplexity.Backend.SpernerRoutingDecoderMachine

@[expose] public section

/-! Routed color-query controls exercise extended coordinate fields, the source
entrance, disconnected endpoint components, and unconditional decoder fallback. -/

namespace GameTheory.Complexity.Tests.SpernerHardness

open GameTheory.Complexity.Backend GameTheory.Math.GridWire GameTheory.Math.Sperner
open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString

private def ruler : List Bool := [false,false,false]

private def fixtureS (i : ℕ) : ℕ := if i=0 then 1 else if i=2 then 3 else i
private def fixtureP (i : ℕ) : ℕ := if i=1 then 0 else if i=3 then 2 else i
private def Pquery (word : List Bool) : List Bool :=
  lowBits 3 (fixtureP (lsbValue word))
private def Squery (word : List Bool) : List Bool :=
  lowBits 3 (fixtureS (lsbValue word))

private def query (x y : ℕ) : List Bool :=
  lowBits ((routingSpernerRuler ruler).length+1) x ++
    lowBits ((routingSpernerRuler ruler).length+1) y

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

example : ComputableInPolyTime (fun z => routingSpernerColorQuery z (fun v => z ++ v)
    (fun v => v ++ z) z) encBits encBits :=
  routingSpernerColorQueryUniform_polyTime (fun seed v => seed ++ v)
    (fun seed v => v ++ seed) (id' (encIn := encBits)) (id' (encIn := encBits)) (id' (encIn := encBits))
    (bitsAppend (fst encBits encBits) (snd encBits encBits))
    (bitsAppend (snd encBits encBits) (fst encBits encBits))

example (word : List Bool) : routingSpernerDecode [] word=[] := by
  exact routingSpernerDecode_invalid (by intro h; exact h.2.1 rfl) word

example : routingSpernerLabelBits ruler
    (encodeGridNode (routingSpernerRuler ruler).length (some ⟨8,116,false⟩))=
      lowBits 3 3 := by
  apply routingSpernerLabelBits_eq_bits
  · apply decodeGridNode_encode
    intro t ht
    cases ht
    decide
  · rfl

end GameTheory.Complexity.Tests.SpernerHardness
