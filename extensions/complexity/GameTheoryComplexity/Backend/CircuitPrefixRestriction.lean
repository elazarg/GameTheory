import Complexitylib.Circuits.Encoding.Shift
import Complexitylib.Circuits.Encoding.Fragment

/-! Raw prefix restriction uses constant gates and copies of the live inputs to
recreate the original input order. Wire relocation preserves malformed-reference
failure as well as successful evaluation. A positive live arity provides the
witness wire used by the constant gates. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity.CircuitCode
/-- Hardwire a prefix while retaining a positive number of live inputs. -/
def rawPrefixRestriction (n : ℕ) (seed : List Bool) (circuit : RawCircuit) : RawCircuit :=
  seed.map (RawGate.constant 0) ++
    (List.range n).map (fun i => RawGate.copy i false) ++ circuit.shift n
private theorem constants_eval (seed : List Bool) (wires : Array Bool)
    (h : 0 < wires.size) :
    RawCircuit.evalAux? (seed.map (RawGate.constant 0)) wires =
      some (wires ++ seed.toArray) := by
  induction seed generalizing wires with
  | nil => simp [RawCircuit.evalAux?]
  | cons bit seed ih =>
    simp only [List.map_cons, RawCircuit.evalAux?]
    have h₀ : (RawGate.constant 0 bit).input₀ = 0 := by cases bit <;> rfl
    have h₁ : (RawGate.constant 0 bit).input₁ = 0 := by cases bit <;> rfl
    rw [h₀, h₁]
    rw [Array.getElem?_eq_getElem h]
    change RawCircuit.evalAux? (seed.map (RawGate.constant 0))
      (wires.push ((RawGate.constant 0 bit).eval wires[0] wires[0])) = _
    rw [RawGate.eval_constant]
    rw [ih _ (by simp)]
    congr 1
    simp
private theorem copies_eval (input seed : List Bool) (k : ℕ) (hk : k ≤ input.length) :
    RawCircuit.evalAux? ((List.range k).map (fun i => RawGate.copy i false))
      (input.toArray ++ seed.toArray) =
      some ((input.toArray ++ seed.toArray) ++ (input.take k).toArray) := by
  induction k with
  | zero => simp [RawCircuit.evalAux?]
  | succ k ih =>
    rw [List.range_succ, List.map_append, RawCircuit.evalAux?_append, ih (by omega)]
    have hi : k < input.toArray.size := by simpa using (show k < input.length by omega)
    simp only [List.map_cons, List.map_nil, Option.bind_some, RawCircuit.evalAux?]
    change (do
      let a ← ((input.toArray ++ seed.toArray) ++ (input.take k).toArray)[k]?
      let b ← ((input.toArray ++ seed.toArray) ++ (input.take k).toArray)[k]?
      some (((input.toArray ++ seed.toArray) ++ (input.take k).toArray).push
        ((RawGate.copy k false).eval a b))) = _
    rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_left hi,
      Array.getElem?_eq_getElem hi]
    change some (((input.toArray ++ seed.toArray) ++ (input.take k).toArray).push
      ((RawGate.copy k false).eval input.toArray[k] input.toArray[k])) = _
    simp only [RawGate.eval_copy, Bool.false_xor]
    congr 1
    rw [List.take_succ_eq_append_getElem (by omega)]
    simp
/-- Prefix hardwiring adds one gate per fixed or live input. -/
@[simp] theorem rawPrefixRestriction_length (n : ℕ) (seed : List Bool)
    (circuit : RawCircuit) :
    (rawPrefixRestriction n seed circuit).length = seed.length + n + circuit.length := by
  simp [rawPrefixRestriction, Nat.add_assoc]
/-- Memo evaluation preserves the live-input prefix and reproduces original evaluation. -/
theorem rawPrefixRestriction_evalAux (n : ℕ) (seed input : List Bool)
    (circuit : RawCircuit) (hn : 0 < n) (hi : input.length = n) :
    RawCircuit.evalAux? (rawPrefixRestriction n seed circuit) input.toArray =
      (RawCircuit.evalAux? circuit (seed ++ input).toArray).map
        (fun result => input.toArray ++ result) := by
  rw [rawPrefixRestriction, RawCircuit.evalAux?_append, RawCircuit.evalAux?_append,
    constants_eval seed _ (by simpa [hi] using hn)]
  change (RawCircuit.evalAux? ((List.range n).map (fun i => RawGate.copy i false))
    (input.toArray ++ seed.toArray)).bind (RawCircuit.evalAux? (circuit.shift n)) = _
  rw [copies_eval input seed n (by omega)]
  rw [List.take_of_length_le (show input.length ≤ n by omega)]
  change RawCircuit.evalAux? (circuit.shift n)
    ((input.toArray ++ seed.toArray) ++ input.toArray) = _
  rw [Array.append_assoc]
  simpa only [List.append_toArray] using
    RawCircuit.evalAux?_shift n circuit input.toArray (seed ++ input).toArray (by simp [hi])
/-- Prefix hardwiring retains the designated output of a nonempty circuit. -/
theorem rawPrefixRestriction_eval (n : ℕ) (seed input : List Bool)
    (circuit : RawCircuit) (hn : 0 < n) (hi : input.length = n) (hc : circuit ≠ []) :
    (rawPrefixRestriction n seed circuit).eval? input = circuit.eval? (seed ++ input) := by
  have hne : rawPrefixRestriction n seed circuit ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [rawPrefixRestriction_length, List.length_nil] at hlen
    omega
  have hpos : 0 < circuit.length := List.length_pos_iff.mpr hc
  simp only [RawCircuit.eval?, List.isEmpty_iff, hne, hc, ↓reduceIte]
  rw [rawPrefixRestriction_evalAux n seed input circuit hn hi]
  cases he : RawCircuit.evalAux? circuit (seed ++ input).toArray with
  | none => rfl
  | some result =>
    change (input.toArray ++ result)[input.length +
      (rawPrefixRestriction n seed circuit).length - 1]? =
      result[(seed ++ input).length + circuit.length - 1]?
    rw [rawPrefixRestriction_length,
      Array.getElem?_append_right (by simp [hi]; omega)]
    congr 1
    simp only [List.length_append, List.size_toArray]
    omega
/-- Prefix hardwiring preserves topological validity at the reduced input width. -/
theorem rawPrefixRestriction_topological (n : ℕ) (seed : List Bool)
    (circuit : RawCircuit) (hn : 0 < n)
    (hc : circuit.TopologicallyWellFormed (seed.length + n)) :
    (rawPrefixRestriction n seed circuit).TopologicallyWellFormed n := by
  rw [rawPrefixRestriction, RawCircuit.topologicallyWellFormed_append,
    RawCircuit.topologicallyWellFormed_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    simp only [List.get_eq_getElem, List.getElem_map]
    have hconst (b : Bool) : (RawGate.constant 0 b).WellFormedAt (n + i.val) := by
      cases b <;> simp [RawGate.constant, RawGate.WellFormedAt] <;> omega
    exact hconst _
  · intro i
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    change i.val < n + (seed.map (RawGate.constant 0)).length + i.val ∧
      i.val < n + (seed.map (RawGate.constant 0)).length + i.val
    constructor <;> omega
  · simp only [List.length_append, List.length_map, List.length_range]
    convert (RawCircuit.topologicallyWellFormed_shift_iff n (seed.length + n) circuit).mpr hc
      using 1
/-- A well-formed source remains well formed after hardwiring a prefix. -/
theorem rawPrefixRestriction_wellFormed (n : ℕ) (seed : List Bool)
    (circuit : RawCircuit) (hn : 0 < n)
    (hc : circuit.WellFormed (seed.length + n)) :
    (rawPrefixRestriction n seed circuit).WellFormed n := by
  refine ⟨?_, rawPrefixRestriction_topological n seed circuit hn hc.2⟩
  intro h
  have hlen := congrArg List.length h
  simp only [rawPrefixRestriction_length, List.length_nil] at hlen
  omega
end GameTheory.Complexity.Backend
