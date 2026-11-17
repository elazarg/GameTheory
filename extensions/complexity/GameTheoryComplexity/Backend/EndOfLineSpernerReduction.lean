module

public import GameTheoryComplexity.Backend.SpernerCircuitGeneration
public import GameTheoryComplexity.Backend.SpernerRoutingDecoderMachine
public import GameTheoryComplexity.Backend.GridRoutingOriginalGraph
public import GameTheoryComplexity.Backend.SpernerReduction
public import GameTheoryComplexity.Backend.GridSpernerColorMachine
public import GameTheory.Math.GridSpernerRoutingBoundary
public import GameTheory.Math.GridSpernerRoutingBounds

@[expose] public section

/-! Local routed color circuits and binary endpoint decoding implement the
reverse Sperner reduction. Answer decoding preserves endpoints from every
component and returns the prescribed empty answer for invalid source promises. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString
open GameTheory.Math.Sperner GameTheory.Math.EndOfLine
open GameTheory.Math.GridWire

/-- Any decoded triangle identifying a bounded non-source routed endpoint gives
an original End-of-Line answer through the actual binary decoder. -/
theorem routingSpernerDecode_endpoint {input word : List Bool} {t : GridTriangle}
    (hsource : endOfLineSourceValid input)
    (hd : decodeGridNode (routingSpernerRuler (CircuitWords.first input)).length word = some (some t))
    (hi : t.y / 36 < 2 ^ (CircuitWords.first input).length) (hne : t.y / 36 ≠ 0)
    (he : IsEndpoint
      (routingOriginalPointer (CircuitWords.first input) (endOfLineNormalizedPredecessor input))
      (routingOriginalPointer (CircuitWords.first input) (endOfLineNormalizedSuccessor input))
      (t.y / 36)) : endOfLineRelation input (routingSpernerDecode input word) := by
  rw [routingSpernerDecode_valid hsource, routingSpernerLabelBits_eq_div_bits hd]
  apply Or.inl
  refine ⟨hsource, ?_, ?_, (routingNormalized_endpoint_iff input hi).mp he⟩
  · simp [endOfLineWidth]
  · intro hz
    have hv := congrArg lsbValue hz
    rw [lsbValue_lowBits hi] at hv
    have ho : lsbValue (endOfLineOrigin input) = 0 := by
      simp only [endOfLineOrigin, lsbValue_replicate_false]
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
theorem endOfLineToSpernerReductionOfCircuitInstance (f : List Bool → List Bool)
    (hf : ComputableInPolyTime f encBits encBits)
    (hwidth : ∀ input, CircuitWords.first (f input) = routingSpernerRuler (CircuitWords.first input))
    (hcolor : ∀ input x y,
      x ≤ 2 ^ (routingSpernerRuler (CircuitWords.first input)).length →
      y ≤ 2 ^ (routingSpernerRuler (CircuitWords.first input)).length →
      spernerColor (f input) x y = gridSpernerRoutingColor (2 ^ (CircuitWords.first input).length)
        (routingOriginalPointer (CircuitWords.first input) (endOfLineNormalizedPredecessor input))
        (routingOriginalPointer (CircuitWords.first input) (endOfLineNormalizedSuccessor input))
        (2 ^ (routingSpernerRuler (CircuitWords.first input)).length) x y) :
    Cslib.Complexity.SearchReducible encBits encBits endOfLineRelation spernerRelation := by
  apply Cslib.Complexity.SearchReducible.of_isTotalSearch
    (f := f) (g := fun p : List Bool × List Bool => routingSpernerDecode p.1 p.2)
    (exists_spernerToEndOfLineReduction.isTotalSearch endOfLineRelation_total) hf
    (routingSpernerDecode_polyTime (fst encBits encBits) (snd encBits encBits))
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
    have hcapacity := gridSpernerRouting_capacity (CircuitWords.first input).length
    rw [← routingSpernerRuler_length] at hcapacity
    obtain ⟨_, hi, hne, he⟩ := gridSpernerRouting_endpoint_label
      (Nat.two_pow_pos _) (routingOriginalPointer_lt _ _ (Nat.two_pow_pos _))
      hp0 hs0 hlink (fun _ hi => routingOriginalPointer_lt _ _ hi)
      (fun _ hi => routingOriginalPointer_lt _ _ hi) hcapacity.1 hcapacity.2 hv ht
    exact routingSpernerDecode_endpoint hsource hd hi hne he
  · exact routingSpernerDecode_fallback hsource word

private def normalizedRoutingColor (input vertex : List Bool) : List Bool :=
  routingSpernerColorQuery (CircuitWords.first input)
    (endOfLineNormalizedPredecessor input) (endOfLineNormalizedSuccessor input) vertex

/-- The native polynomial-time color machine admits uniformly emitted Sperner circuits with
exact finite-grid agreement, without any source or coloring promise. -/
theorem exists_endOfLineSpernerCircuitInstance :
    ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧
      (∀ input, CircuitWords.first (f input) = routingSpernerRuler (CircuitWords.first input)) ∧
      ∀ input x y,
        x ≤ 2 ^ (routingSpernerRuler (CircuitWords.first input)).length →
        y ≤ 2 ^ (routingSpernerRuler (CircuitWords.first input)).length →
        spernerColor (f input) x y = gridSpernerRoutingColor (2 ^ (CircuitWords.first input).length)
          (routingOriginalPointer (CircuitWords.first input) (endOfLineNormalizedPredecessor input))
          (routingOriginalPointer (CircuitWords.first input) (endOfLineNormalizedSuccessor input))
          (2 ^ (routingSpernerRuler (CircuitWords.first input)).length) x y := by
  have hp := normalizedPredecessor_polyTime (fst encBits encBits) (snd encBits encBits)
  have hs := normalizedSuccessor_polyTime (fst encBits encBits) (snd encBits encBits)
  have hc : ComputableInPolyTime
      (fun p : List Bool × List Bool => normalizedRoutingColor p.1 p.2)
      (encPair encBits encBits) encBits :=
    routingSpernerColorQueryUniform_polyTime
      endOfLineNormalizedPredecessor endOfLineNormalizedSuccessor
      (CircuitWords.first_polyTime.comp (fst encBits encBits))
      (fst encBits encBits) (snd encBits encBits) hp hs
  obtain ⟨f, hf, heval⟩ := exists_spernerColorInstance
    (fun input => routingSpernerRuler (CircuitWords.first input)) normalizedRoutingColor
    (routingSpernerRuler_polyTime CircuitWords.first_polyTime) hc
    (fun _ _ => routingSpernerColorQuery_length _ _ _ _)
  refine ⟨f, hf, fun input => (heval input).1, fun input x y hx hy => ?_⟩
  have hi : gridInteriorColor (routingSpernerRuler (CircuitWords.first input)).length
      (evaluateCircuitVector (CircuitWords.rest (f input))) x y =
      gridSpernerRoutingInterior (2 ^ (CircuitWords.first input).length)
        (routingOriginalPointer (CircuitWords.first input) (endOfLineNormalizedPredecessor input))
        (routingOriginalPointer (CircuitWords.first input) (endOfLineNormalizedSuccessor input)) x y := by
    rw [(heval input).2 x y]
    change gridInteriorColor (routingSpernerRuler (CircuitWords.first input)).length
      (routingSpernerColorQuery (CircuitWords.first input) (endOfLineNormalizedPredecessor input)
        (endOfLineNormalizedSuccessor input)) x y = _
    exact gridInteriorColor_routingSpernerColorQuery _ _ _ hx hy
  simp only [spernerColor, (heval input).1, gridSpernerRoutingColor]
  unfold standardGridColor
  split_ifs <;> first | rfl | exact hi

/-- The reverse Sperner reduction has native polynomial-time instance compilation
and every-answer decoding, covering arbitrary serialized source instances. -/
theorem exists_endOfLineToSpernerReduction :
    Cslib.Complexity.SearchReducible encBits encBits endOfLineRelation spernerRelation := by
  obtain ⟨f, hf, hw, hc⟩ := exists_endOfLineSpernerCircuitInstance
  exact endOfLineToSpernerReductionOfCircuitInstance f hf hw hc

end GameTheory.Complexity.Backend
