import GameTheoryComplexity.Backend.SpernerCircuitGeneration
import GameTheoryComplexity.Backend.SpernerRoutingDecoderMachine
import GameTheoryComplexity.Backend.GridRoutingOriginalGraph
import GameTheoryComplexity.Backend.SearchReduction
import GameTheoryComplexity.Backend.GridSpernerColorMachine
import GameTheory.Math.GridSpernerRoutingBoundary
import GameTheory.Math.GridSpernerRoutingBounds

/-! Local routed color circuits and binary endpoint decoding implement the
reverse Sperner reduction. Answer decoding preserves endpoints from every
component and returns the prescribed empty answer for invalid source promises. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Math.Sperner GameTheory.Math.EndOfLine
open GameTheory.Math.GridWire

/-- Any decoded triangle identifying a bounded non-source routed endpoint gives
an original End-of-Line answer through the actual binary decoder. -/
theorem routingSpernerDecode_endpoint {input word : List Bool} {t : GridTriangle}
    (hsource : endOfLineSourceValid input)
    (hd : decodeGridNode (routingSpernerRuler (pairFst input)).length word = some (some t))
    (hi : t.y / 36 < 2 ^ (pairFst input).length) (hne : t.y / 36 ≠ 0)
    (he : IsEndpoint
      (routingOriginalPointer (pairFst input) (endOfLineNormalizedPredecessor input))
      (routingOriginalPointer (pairFst input) (endOfLineNormalizedSuccessor input))
      (t.y / 36)) : endOfLineRelation input (routingSpernerDecode input word) := by
  rw [routingSpernerDecode_valid hsource, routingSpernerLabelBits_eq_div_bits hd]
  apply Or.inl
  refine ⟨hsource, ?_, ?_, (routingNormalized_endpoint_iff input hi).mp he⟩
  · simp [endOfLineWidth]
  · intro hz
    have hv := congrArg Nat.fromBitsLE hz
    rw [Nat.fromBitsLE_toBitsLE hi] at hv
    have ho : Nat.fromBitsLE (endOfLineOrigin input) = 0 := by
      change Nat.fromBitsLE (List.replicate (endOfLineWidth input) false) = 0
      generalize endOfLineWidth input = b
      induction b with
      | zero => rfl
      | succ b ih => simp [List.replicate_succ, Nat.fromBitsLE_cons, ih]
    exact hne (hv.trans ho)

/-- Invalid source instances require no geometric assumption on the target answer. -/
theorem routingSpernerDecode_fallback {input : List Bool} (h : ¬endOfLineSourceValid input)
    (word : List Bool) : endOfLineRelation input (routingSpernerDecode input word) := by
  rw [routingSpernerDecode_invalid h]
  exact Or.inr ⟨h, rfl⟩

private theorem valid_corner_le {n : ℕ} {t : GridTriangle} (hv : ValidTriangle n t)
    (p : Fin 3) : (corner t p).1 ≤ n ∧ (corner t p).2 ≤ n := by
  obtain ⟨hx, hy⟩ := hv
  fin_cases p <;> cases h : t.upper <;> simp [corner, h] <;> omega

/-- Exact routed coloring compilation preserves every Sperner answer, including
endpoints belonging to components disconnected from the known source. -/
def endOfLineToSpernerReductionOfCircuitInstance (f : List Bool → List Bool) (hf : f ∈ FP)
    (hwidth : ∀ input, pairFst (f input) = routingSpernerRuler (pairFst input))
    (hcolor : ∀ input x y,
      x ≤ 2 ^ (routingSpernerRuler (pairFst input)).length →
      y ≤ 2 ^ (routingSpernerRuler (pairFst input)).length →
      spernerColor (f input) x y = gridSpernerRoutingColor (2 ^ (pairFst input).length)
        (routingOriginalPointer (pairFst input) (endOfLineNormalizedPredecessor input))
        (routingOriginalPointer (pairFst input) (endOfLineNormalizedSuccessor input))
        (2 ^ (routingSpernerRuler (pairFst input)).length) x y) :
    SearchReduction endOfLineRelation spernerRelation where
  instanceMap := f
  instanceMap_mem_FP := hf
  decode := fun v => routingSpernerDecode (v 0) (v 1)
  decode_mem_FPn := routingSpernerDecode_mem_FPn
  sound := by
    intro input word hw
    change endOfLineRelation input (routingSpernerDecode input word)
    by_cases hsource : endOfLineSourceValid input
    · obtain ⟨t, hd, ht⟩ := hw
      rw [hwidth input] at hd
      have hv := decodeGridNode_valid hd t rfl
      have hc (p : Fin 3) := hcolor input (corner t p).1 (corner t p).2
        (valid_corner_le hv p).1 (valid_corner_le hv p).2
      rw [hc 0, hc 1, hc 2] at ht
      obtain ⟨hp0, hs0, hlink⟩ := routingNormalized_source hsource
      have hcapacity := gridSpernerRouting_capacity (pairFst input).length
      rw [← routingSpernerRuler_length] at hcapacity
      obtain ⟨_, hi, hne, he⟩ := gridSpernerRouting_endpoint_label
        (Nat.two_pow_pos _) (routingOriginalPointer_lt _ _ (Nat.two_pow_pos _))
        hp0 hs0 hlink (fun _ hi => routingOriginalPointer_lt _ _ hi)
        (fun _ hi => routingOriginalPointer_lt _ _ hi) hcapacity.1 hcapacity.2 hv ht
      exact routingSpernerDecode_endpoint hsource hd hi hne he
    · exact routingSpernerDecode_fallback hsource word

private def normalizedRoutingColor (input vertex : List Bool) : List Bool :=
  routingSpernerColorQuery (pairFst input)
    (endOfLineNormalizedPredecessor input) (endOfLineNormalizedSuccessor input) vertex

/-- The actual FP color machine admits uniformly emitted Sperner circuits with
exact finite-grid agreement, without any source or coloring promise. -/
theorem exists_endOfLineSpernerCircuitInstance :
    ∃ f : List Bool → List Bool, f ∈ FP ∧
      (∀ input, pairFst (f input) = routingSpernerRuler (pairFst input)) ∧
      ∀ input x y,
        x ≤ 2 ^ (routingSpernerRuler (pairFst input)).length →
        y ≤ 2 ^ (routingSpernerRuler (pairFst input)).length →
        spernerColor (f input) x y = gridSpernerRoutingColor (2 ^ (pairFst input).length)
          (routingOriginalPointer (pairFst input) (endOfLineNormalizedPredecessor input))
          (routingOriginalPointer (pairFst input) (endOfLineNormalizedSuccessor input))
          (2 ^ (routingSpernerRuler (pairFst input)).length) x y := by
  have hp := normalizedPredecessorFn_mem_FP pairFst_mem_FP pairSnd_mem_FP
  have hs := normalizedSuccessorFn_mem_FP pairFst_mem_FP pairSnd_mem_FP
  have hc : (fun z => normalizedRoutingColor (pairFst z) (pairSnd z)) ∈ FP :=
    routingSpernerColorQueryUniformFn_mem_FP
      endOfLineNormalizedPredecessor endOfLineNormalizedSuccessor
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP pairSnd_mem_FP hp hs
  obtain ⟨f, hf, heval⟩ := exists_spernerColorInstance
    (fun input => routingSpernerRuler (pairFst input)) normalizedRoutingColor
    (routingSpernerRulerFn_mem_FP pairFst_mem_FP) hc
    (fun _ _ => routingSpernerColorQuery_length _ _ _ _)
  refine ⟨f, hf, fun input => (heval input).1, fun input x y hx hy => ?_⟩
  have hi : gridInteriorColor (routingSpernerRuler (pairFst input)).length
      (evaluateCircuitVector (pairSnd (f input))) x y =
      gridSpernerRoutingInterior (2 ^ (pairFst input).length)
        (routingOriginalPointer (pairFst input) (endOfLineNormalizedPredecessor input))
        (routingOriginalPointer (pairFst input) (endOfLineNormalizedSuccessor input)) x y := by
    rw [(heval input).2 x y]
    change gridInteriorColor (routingSpernerRuler (pairFst input)).length
      (routingSpernerColorQuery (pairFst input) (endOfLineNormalizedPredecessor input)
        (endOfLineNormalizedSuccessor input)) x y = _
    exact gridInteriorColor_routingSpernerColorQuery _ _ _ hx hy
  simp only [spernerColor, (heval input).1, gridSpernerRoutingColor]
  unfold standardGridColor
  split_ifs <;> first | rfl | exact hi

/-- The reverse Sperner reduction has actual FP instance compilation and actual
FPn every-answer decoding, covering arbitrary serialized source instances. -/
theorem exists_endOfLineToSpernerReduction :
    Nonempty (SearchReduction endOfLineRelation spernerRelation) := by
  obtain ⟨f, hf, hw, hc⟩ := exists_endOfLineSpernerCircuitInstance
  exact ⟨endOfLineToSpernerReductionOfCircuitInstance f hf hw hc⟩

end GameTheory.Complexity.Backend
