import GameTheoryComplexity.Backend.CircuitVectorMachine
import Complexitylib.Classes.P.Cobham.Internal.Algebra
import Complexitylib.Classes.P.Cobham.Internal.PolyLen

/-! Polynomial-time emission of serialized circuit vectors from scalar code producers.
The output coordinates appear in ascending order and retain the producer's exact codes. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Emit one scalar circuit code per coordinate, querying its index in unary. -/
def emitCircuitVector (g : List Bool → List Bool) (input : List Bool) (width : ℕ) :
    List Bool :=
  encodeVectorCodes ((List.range width).map fun i => g (pair input (List.replicate i true)))

private def emitVectorAux (g : List Bool → List Bool) (input full : List Bool) :
    List Bool → List Bool
  | [] => []
  | _ :: tail => pair (g (pair input (List.replicate (full.length - (tail.length + 1)) true)))
      (emitVectorAux g input full tail)

private theorem emitVectorAux_eq (g : List Bool → List Bool) (input full ruler : List Bool)
    (h : ruler.length ≤ full.length) :
    emitVectorAux g input full ruler = encodeVectorCodes ((List.range ruler.length).map
      fun i => g (pair input (List.replicate (full.length - ruler.length + i) true))) := by
  induction ruler with
  | nil => simp [emitVectorAux, encodeVectorCodes]
  | cons b ruler ih =>
    have ht : ruler.length ≤ full.length := by simp only [List.length_cons] at h; omega
    rw [emitVectorAux, ih ht]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      encodeVectorCodes, Nat.add_zero]
    congr 1
    apply congrArg encodeVectorCodes
    apply List.map_congr_left
    intro i hi
    dsimp
    have he : full.length - ruler.length + i =
        full.length - (ruler.length + 1) + (i + 1) := by
      simp only [List.length_cons] at h
      omega
    rw [he]

private def emitVectorStep (g : List Bool → List Bool) (w : Fin 4 → List Bool) : List Bool :=
  pair (g (pair (w 2) (List.replicate ((w 3).length - ((w 0).length + 1)) true))) (w 1)

private theorem emitVectorAux_rec (g : List Bool → List Bool) (ruler : List Bool)
    (v : Fin 2 → List Bool) :
    recNotation (fun _ : Fin 2 → List Bool => []) (emitVectorStep g) (emitVectorStep g)
      ruler v = emitVectorAux g (v 0) (v 1) ruler := by
  induction ruler with
  | nil => rfl
  | cons b ruler ih =>
    cases b <;> change
      pair (g (pair (v 0) (List.replicate ((v 1).length - (ruler.length + 1)) true)))
        (recNotation (fun _ : Fin 2 → List Bool => []) (emitVectorStep g)
          (emitVectorStep g) ruler v) =
      pair (g (pair (v 0) (List.replicate ((v 1).length - (ruler.length + 1)) true)))
        (emitVectorAux g (v 0) (v 1) ruler)
    all_goals rw [ih]

private theorem emitVectorStep_mem (g : List Bool → List Bool) (hg : g ∈ FP) :
    Cobham (emitVectorStep g) := by
  have hd := dropFn (Cobham.comp (Cobham.bit false)
    (fun _ : Fin 1 => Cobham.proj (0 : Fin 4))) (Cobham.proj (3 : Fin 4))
  have hi : Cobham fun w : Fin 4 → List Bool =>
      List.replicate ((w 3).length - ((w 0).length + 1)) true :=
    (comp₂ Cobham.smash (Cobham.const [true]) hd).of_eq fun w => by
      simp [_root_.Complexity.smash]
  have hq := comp₂ Cobham.pairing (Cobham.proj (2 : Fin 4)) hi
  exact comp₂ Cobham.pairing
    (Cobham.comp (FP_subset_CobhamFP hg) (fun _ : Fin 1 => hq)) (Cobham.proj 1)

private theorem emitVectorAux_length_le (g : List Bool → List Bool)
    (p : Polynomial ℕ) (hp : ∀ z, (g z).length ≤ p.eval z.length)
    (input full ruler : List Bool) :
    (emitVectorAux g input full ruler).length ≤
      ruler.length * (2 * p.eval (pair input full).length + 2) := by
  induction ruler with
  | nil => simp [emitVectorAux]
  | cons b ruler ih =>
    have hq : (pair input
        (List.replicate (full.length - (ruler.length + 1)) true)).length ≤
        (pair input full).length := by simp only [pair_length, List.length_replicate]; omega
    have hg := (hp (pair input
      (List.replicate (full.length - (ruler.length + 1)) true))).trans
        (polynomial_eval_mono_nat p hq)
    rw [emitVectorAux, pair_length, List.length_cons]
    nlinarith

/-- A polynomial-time scalar code producer emits a polynomial-time circuit vector. -/
theorem emitCircuitVector_pair_mem_FP (g : List Bool → List Bool) (hg : g ∈ FP) :
    (fun z => emitCircuitVector g (pairFst z) (pairSnd z).length) ∈ FP := by
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hg
  have hs := emitVectorStep_mem g hg
  have hb := comp₂ Cobham.smash (Cobham.proj (0 : Fin 3))
    (appendFn (repeatFn (polyLen_mem p
      (comp₂ Cobham.pairing (Cobham.proj (1 : Fin 3)) (Cobham.proj 2))) 2)
      (Cobham.const [false, false]))
  have hr := Cobham.boundedRec (n := 2) Cobham.empty hs hs hb (fun ruler v => by
    rw [emitVectorAux_rec]
    change (emitVectorAux g (v 0) (v 1) ruler).length ≤
      (_root_.Complexity.smash ruler
        ((List.replicate 2 (polyLen p (pair (v 0) (v 1)))).flatten ++ [false, false])).length
    simpa [two_mul, Nat.add_assoc] using emitVectorAux_length_le g p hp (v 0) (v 1) ruler)
  have hinput := FP_subset_CobhamFP pairFst_mem_FP
  have hwidth := FP_subset_CobhamFP pairSnd_mem_FP
  have h := Cobham.comp hr
    (gs := fun i (v : Fin 1 → List Bool) =>
      ![pairSnd (v 0), pairFst (v 0), pairSnd (v 0)] i)
    (fun i => by fin_cases i <;> first | exact hwidth | exact hinput)
  apply CobhamFP_subset_FP
  exact h.of_eq fun v => by
    rw [emitVectorAux_rec]
    change emitVectorAux g (pairFst (v 0)) (pairSnd (v 0)) (pairSnd (v 0)) = _
    rw [emitVectorAux_eq g _ _ _ le_rfl]
    simp [emitCircuitVector]

/-- Composing the input and width producers preserves polynomial-time vector emission. -/
theorem emitCircuitVectorFn_mem_FP (g input ruler : List Bool → List Bool)
    (hg : g ∈ FP) (hi : input ∈ FP) (hr : ruler ∈ FP) :
    (fun z => emitCircuitVector g (input z) (ruler z).length) ∈ FP := by
  have h := mem_FP_comp (pairFn_mem_FP hi hr) (emitCircuitVector_pair_mem_FP g hg)
  simpa [Function.comp_def] using h

/-- Each coordinate recovers the scalar producer's exact serialized code. -/
theorem emitCircuitVector_codeAt (g : List Bool → List Bool) (input : List Bool)
    (width i : ℕ) (hi : i < width) :
    circuitVectorCodeAt (emitCircuitVector g input width) i =
      g (pair input (List.replicate i true)) := by
  simp [emitCircuitVector, circuitVectorCodeAt_encode, hi]

/-- Evaluating the emitted vector agrees coordinatewise with the scalar codes. -/
theorem evaluateCircuitVector_emit (g : List Bool → List Bool) (input vertex : List Bool) :
    evaluateCircuitVector (emitCircuitVector g input vertex.length) vertex =
      (List.range vertex.length).map fun i =>
        (CircuitCode.evalFamilyCode (g (pair input (List.replicate i true))) vertex).getD
          false := by
  unfold evaluateCircuitVector
  apply List.map_congr_left
  intro i hi
  rw [emitCircuitVector_codeAt g input vertex.length i (List.mem_range.mp hi)]

end GameTheory.Complexity.Backend
