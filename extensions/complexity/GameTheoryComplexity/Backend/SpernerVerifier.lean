module

public import GameTheoryComplexity.Backend.SpernerProblem
public import Complexity.Computability.Complexity.Classes.TFNP

@[expose] public section

/-! A native Boolean verifier checks one canonical triangle word and its three
corner colors. The runtime includes the width checks and every circuit query;
witness bounds are supplied independently of the machine certificate. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime
open GameTheory.Math.Sperner

private theorem source_head (b : ℕ) :
    (encodeGridNode b none).headD false = false := by
  change (List.replicate (2 * b + 2) false).headD false = false
  rw [Nat.add_comm (2 * b) 2, List.replicate_add]
  rfl

private def triangleFlag (input word : List Bool) : Bool :=
  (gridNodeAcceptFlag (CircuitWords.first input) word).headD false && word.headD false

private theorem triangleFlag_accept (input word : List Bool) :
    triangleFlag input word = true ↔
      ∃ t, decodeGridNode (CircuitWords.first input).length word = some (some t) := by
  have ha : (gridNodeAcceptFlag (CircuitWords.first input) word).headD false = true ↔
      ∃ node, decodeGridNode (CircuitWords.first input).length word = some node := by
    simpa only [gridNodeAcceptFlag, List.headD_cons, List.cons.injEq, and_true] using
      gridNodeAcceptFlag_accept (CircuitWords.first input) word
  rw [triangleFlag, Bool.and_eq_true, ha]
  constructor
  · rintro ⟨⟨node, hd⟩, hh⟩
    cases node with
    | none =>
      rw [← encodeGridNode_decode hd, source_head] at hh
      contradiction
    | some t => exact ⟨t, hd⟩
  · rintro ⟨t, hd⟩
    refine ⟨⟨some t, hd⟩, ?_⟩
    rw [← encodeGridNode_decode hd]
    rfl

private theorem encodedColors_eq_iff (a b : Fin 3) :
    encodeGridColor a = encodeGridColor b ↔ a = b := by
  constructor
  · intro h
    simpa only [decodeGridColor_encode] using congrArg decodeGridColor h
  · rintro rfl
    rfl

private def colorFlag (input word : List Bool) : Bool :=
  let query := evaluateCircuitVector (CircuitWords.rest input)
  let a := gridCornerColor (CircuitWords.first input) query word 0
  let b := gridCornerColor (CircuitWords.first input) query word 1
  let c := gridCornerColor (CircuitWords.first input) query word 2
  !decide (a = b) && (!decide (b = c) && !decide (c = a))

private theorem colorFlag_accept {input word : List Bool} {t : GridTriangle}
    (hd : decodeGridNode (CircuitWords.first input).length word = some (some t)) :
    colorFlag input word = true ↔
      Trichromatic
        (spernerColor input (corner t 0).1 (corner t 0).2)
        (spernerColor input (corner t 1).1 (corner t 1).2)
        (spernerColor input (corner t 2).1 (corner t 2).2) := by
  have hv := decodeGridNode_valid hd t rfl
  rw [colorFlag, ← encodeGridNode_decode hd,
    gridCornerColor_encode _ _ t 0 hv, gridCornerColor_encode _ _ t 1 hv,
    gridCornerColor_encode _ _ t 2 hv]
  simp [encodedColors_eq_iff, Trichromatic, spernerColor]

/-- Check the exact triangle encoding and three distinct corner colors. -/
def spernerVerdict (input word : List Bool) : Bool :=
  let query := evaluateCircuitVector (CircuitWords.rest input)
  let a := gridCornerColor (CircuitWords.first input) query word 0
  let b := gridCornerColor (CircuitWords.first input) query word 1
  let c := gridCornerColor (CircuitWords.first input) query word 2
  ((gridNodeAcceptFlag (CircuitWords.first input) word).headD false && word.headD false) &&
    (!decide (a = b) && (!decide (b = c) && !decide (c = a)))

theorem spernerVerdict_accept (input word : List Bool) :
    spernerVerdict input word = true ↔ spernerRelation input word := by
  change (triangleFlag input word && colorFlag input word) = true ↔ _
  rw [Bool.and_eq_true, triangleFlag_accept]
  constructor
  · rintro ⟨⟨t, hd⟩, hc⟩
    exact ⟨t, hd, (colorFlag_accept hd).mp hc⟩
  · rintro ⟨t, hd, hc⟩
    exact ⟨⟨t, hd⟩, (colorFlag_accept hd).mpr hc⟩

private theorem triangleFlag_polyTime {α : Type} {enc : α ↪ List Bool}
    {input word : α → List Bool} (hi : ComputableInPolyTime input enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => triangleFlag (input a) (word a)) enc encBool :=
  bool_and'
    ((ComputableInPolyTime.headD (encA := encBool) false).comp
      (gridNodeAcceptFlag_polyTime (CircuitWords.first_polyTime.comp hi) hw))
    ((ComputableInPolyTime.headD (encA := encBool) false).comp hw)

private theorem colorFlag_polyTime {α : Type} {enc : α ↪ List Bool}
    {input word : α → List Bool} (hi : ComputableInPolyTime input enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => colorFlag (input a) (word a)) enc encBool := by
  have hr := CircuitWords.first_polyTime.comp hi
  have hquery : ComputableInPolyTime
      (fun p : α × List Bool => evaluateCircuitVector (CircuitWords.rest (input p.1)) p.2)
      (encPair enc encBits) encBits :=
    evaluateCircuitVector_polyTime
      (CircuitWords.rest_polyTime.comp (hi.comp (fst enc encBits))) (snd enc encBits)
  have h₀ := gridCornerColor_polyTime hr hw
    (fun a => evaluateCircuitVector (CircuitWords.rest (input a))) hquery 0
  have h₁ := gridCornerColor_polyTime hr hw
    (fun a => evaluateCircuitVector (CircuitWords.rest (input a))) hquery 1
  have h₂ := gridCornerColor_polyTime hr hw
    (fun a => evaluateCircuitVector (CircuitWords.rest (input a))) hquery 2
  exact bool_and' (bool_not.comp (decide_eq' h₀ h₁))
    (bool_and' (bool_not.comp (decide_eq' h₁ h₂)) (bool_not.comp (decide_eq' h₂ h₀)))

/-- Certified input and witness producers give a native polynomial-time verifier. -/
@[fun_prop] theorem spernerVerdict_polyTime {α : Type} {enc : α ↪ List Bool}
    {input word : α → List Bool} (hi : ComputableInPolyTime input enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => spernerVerdict (input a) (word a)) enc encBool := by
  change ComputableInPolyTime
    (fun a => triangleFlag (input a) (word a) && colorFlag (input a) (word a)) enc encBool
  exact bool_and' (triangleFlag_polyTime hi hw) (colorFlag_polyTime hi hw)

/-- Linear witness balance and the actual Boolean verifier give native FNP membership. -/
theorem spernerRelation_mem_FNP : spernerRelation ∈ Cslib.Complexity.FNP encBits := by
  refine ⟨spernerRelation_polyBalanced, ?_⟩
  exact ⟨(fun p : List Bool × List Bool => spernerVerdict p.1 p.2),
    spernerVerdict_polyTime (fst encBits encBits) (snd encBits encBits),
    fun input word => (spernerVerdict_accept input word).symm⟩

end GameTheory.Complexity.Backend
