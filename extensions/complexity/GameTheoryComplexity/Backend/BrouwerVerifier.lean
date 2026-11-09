module

public import GameTheoryComplexity.Backend.BrouwerProblem
public import GameTheoryComplexity.Backend.BrouwerPointMachine
public import GameTheoryComplexity.Backend.BrouwerResidualMachine
public import Complexity.Computability.Complexity.Classes.TFNP

@[expose] public section

/-! A polynomial-time verifier locates a rational point, queries the three
corner colors, and checks its exact affine residual. It validates both the
complete point fields before accepting the continuous-map
approximate fixed-point relation. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.Sperner GameTheory.Math.Brouwer

/-- Validate complete fixed-width point fields against the closed-square bound. -/
def brouwerPointAcceptFlag (ruler word : List Bool) : Bool :=
  decide (word.length = pointWordWidth ruler.length) &&
    ((routingLEFlag (brouwerPointXBits ruler word) (brouwerPointBoundBits ruler)).headD false &&
      (routingLEFlag (brouwerPointYBits ruler word) (brouwerPointBoundBits ruler)).headD false)

theorem brouwerPointAcceptFlag_accept (ruler word : List Bool) :
    brouwerPointAcceptFlag ruler word = true ↔
      ∃ p, decodeBrouwerPoint ruler.length word = some p := by
  simp only [brouwerPointAcceptFlag, Bool.and_eq_true, decide_eq_true_eq, routingLEFlag_value,
    List.headD_cons, brouwerPointBoundBits_value, brouwerPointXBits, brouwerPointYBits,
    brouwerPointRuler_length]
  unfold decodeBrouwerPoint
  dsimp only
  split_ifs with h <;> simp [h]

/-- Complete point validation charges native unary lengths and binary comparisons. -/
@[fun_prop] theorem brouwerPointAcceptFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => brouwerPointAcceptFlag (ruler a) (word a)) enc encBool := by
  have hpr := brouwerPointRuler_polyTime hr
  have hwidth : ComputableInPolyTime (fun a => pointWordWidth (ruler a).length) enc encUnary := by
    simpa only [Function.comp_def, List.length_append, brouwerPointRuler_length,
      pointWordWidth, two_mul] using length_bits.comp (bitsAppend hpr hpr)
  have hlen := decide_eq' (length_bits.comp hw) hwidth
  have hbound := brouwerPointBoundBits_polyTime hr
  have hhead : ComputableInPolyTime (fun bits : List Bool => bits.headD false)
      encBits encBool := .headD false
  exact bool_and' hlen (bool_and'
    (hhead.comp (routingLEFlag_polyTime (brouwerPointXBits_polyTime hr hw) hbound))
    (hhead.comp (routingLEFlag_polyTime (brouwerPointYBits_polyTime hr hw) hbound)))

/-- Query all three corner colors and check the exact local affine residual. -/
def brouwerResidualFlag (input word : List Bool) : List Bool :=
  let ruler := CircuitWords.first input
  let triangle := brouwerLocateWord ruler word
  let query := evaluateCircuitVector (CircuitWords.rest input)
  residualVerdict
    (brouwerOffsetBits ruler (brouwerPointXBits ruler word))
    (brouwerOffsetBits ruler (brouwerPointYBits ruler word))
    (gridCornerColor ruler query triangle 0)
    (gridCornerColor ruler query triangle 1)
    (gridCornerColor ruler query triangle 2)

private theorem brouwerResidualFlag_flag (input word : List Bool) :
    brouwerResidualFlag input word = [true] ∨
      brouwerResidualFlag input word = [false] := residualVerdict_flag _ _ _ _ _

private theorem brouwerResidualFlag_accept {input word : List Bool} {p : ℕ × ℕ}
    (hd : decodeBrouwerPoint (CircuitWords.first input).length word = some p) :
    brouwerResidualFlag input word = [true] ↔
      |(sixthDisplacement (spernerColor input) (2 ^ (CircuitWords.first input).length) p.1 p.2).1|
        ≤ 1 / 6 ∧
      |(sixthDisplacement (spernerColor input) (2 ^ (CircuitWords.first input).length) p.1 p.2).2|
        ≤ 1 / 6 := by
  obtain ⟨_, hx, hy, hxx, hyy⟩ := decodeBrouwerPoint_properties hd
  have hv := sixthTriangle_valid (Nat.two_pow_pos _) hx hy
  have hxx' : lsbValue (brouwerPointXBits (CircuitWords.first input) word) = p.1 := by
    simpa only [brouwerPointXBits, brouwerPointRuler_length] using hxx
  have hyy' : lsbValue (brouwerPointYBits (CircuitWords.first input) word) = p.2 := by
    simpa only [brouwerPointYBits, brouwerPointRuler_length] using hyy
  let rx : Fin 7 := ⟨sixthOffset (2 ^ (CircuitWords.first input).length) p.1,
    by have h := (sixthCellIndex_bounds (Nat.two_pow_pos _) hx).2.1; omega⟩
  let ry : Fin 7 := ⟨sixthOffset (2 ^ (CircuitWords.first input).length) p.2,
    by have h := (sixthCellIndex_bounds (Nat.two_pow_pos _) hy).2.1; omega⟩
  have hex : brouwerOffsetBits (CircuitWords.first input) (brouwerPointXBits (CircuitWords.first input) word) =
      encodeResidualOffset rx := by
    rw [brouwerOffsetBits_eq _ _ (by simpa [hxx'] using hx), hxx']
    rfl
  have hey : brouwerOffsetBits (CircuitWords.first input) (brouwerPointYBits (CircuitWords.first input) word) =
      encodeResidualOffset ry := by
    rw [brouwerOffsetBits_eq _ _ (by simpa [hyy'] using hy), hyy']
    rfl
  unfold brouwerResidualFlag
  dsimp only
  rw [brouwerLocateWord_eq hd,
    gridCornerColor_encode _ _ _ 0 hv, gridCornerColor_encode _ _ _ 1 hv,
    gridCornerColor_encode _ _ _ 2 hv, hex, hey, residualVerdict_accept]
  change SixthGridSmallResidual rx ry _ _ _ ↔ _
  unfold SixthGridSmallResidual sixthGridDisplacement sixthDisplacement sixthWeights
  dsimp only [rx, ry]
  split_ifs <;> rfl

/-- The complete verifier validates the rational point and its actual map residual. -/
def brouwerVerdict (input word : List Bool) : Bool :=
  brouwerPointAcceptFlag (CircuitWords.first input) word &&
    (brouwerResidualFlag input word).headD false

theorem brouwerVerdict_accept (input word : List Bool) :
    brouwerVerdict input word = true ↔ brouwerRelation input word := by
  have hres : (brouwerResidualFlag input word).headD false = true ↔
      brouwerResidualFlag input word = [true] := by
    rcases brouwerResidualFlag_flag input word with h | h <;> simp [h]
  rw [brouwerVerdict, Bool.and_eq_true, brouwerPointAcceptFlag_accept, hres,
    brouwerRelation_local_iff]
  constructor
  · rintro ⟨⟨p, hd⟩, hr⟩
    exact ⟨p, hd, (brouwerResidualFlag_accept hd).mp hr⟩
  · rintro ⟨p, hd, hr⟩
    exact ⟨⟨p, hd⟩, (brouwerResidualFlag_accept hd).mpr hr⟩

/-- Native source and witness producers charge all three joint circuit queries. -/
@[fun_prop] theorem brouwerResidualFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {input word : α → List Bool}
    (hi : ComputableInPolyTime input enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => brouwerResidualFlag (input a) (word a)) enc encBits := by
  have hr := CircuitWords.first_polyTime.comp hi
  have ht := brouwerLocateWord_polyTime hr hw
  have hquery : ComputableInPolyTime
      (fun p : α × List Bool => evaluateCircuitVector (CircuitWords.rest (input p.1)) p.2)
      (encPair enc encBits) encBits :=
    evaluateCircuitVector_polyTime
      (CircuitWords.rest_polyTime.comp (hi.comp (fst enc encBits))) (snd enc encBits)
  have h₀ := gridCornerColor_polyTime hr ht
    (fun a => evaluateCircuitVector (CircuitWords.rest (input a))) hquery 0
  have h₁ := gridCornerColor_polyTime hr ht
    (fun a => evaluateCircuitVector (CircuitWords.rest (input a))) hquery 1
  have h₂ := gridCornerColor_polyTime hr ht
    (fun a => evaluateCircuitVector (CircuitWords.rest (input a))) hquery 2
  exact residualVerdict_polyTime
    (brouwerOffsetBits_polyTime hr (brouwerPointXBits_polyTime hr hw))
    (brouwerOffsetBits_polyTime hr (brouwerPointYBits_polyTime hr hw)) h₀ h₁ h₂

/-- The complete Boolean verifier has one native polynomial-time machine certificate. -/
@[fun_prop] theorem brouwerVerdict_polyTime
    {α : Type} {enc : α ↪ List Bool} {input word : α → List Bool}
    (hi : ComputableInPolyTime input enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => brouwerVerdict (input a) (word a)) enc encBool := by
  have hhead : ComputableInPolyTime (fun bits : List Bool => bits.headD false)
      encBits encBool := .headD false
  exact bool_and' (brouwerPointAcceptFlag_polyTime (CircuitWords.first_polyTime.comp hi) hw)
    (hhead.comp (brouwerResidualFlag_polyTime hi hw))

/-- Linear witness balance and exact native verification give FNP membership. -/
theorem brouwerRelation_mem_FNP : brouwerRelation ∈ Cslib.Complexity.FNP encBits := by
  refine ⟨brouwerRelation_polyBalanced, fun p => brouwerVerdict p.1 p.2,
    brouwerVerdict_polyTime (fst encBits encBits) (snd encBits encBits), fun input word => ?_⟩
  exact (brouwerVerdict_accept input word).symm

end GameTheory.Complexity.Backend
