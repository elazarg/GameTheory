module

public import GameTheoryComplexity.Backend.PointerCircuitGeneration
public import GameTheoryComplexity.Backend.SpernerProblem
public import GameTheoryComplexity.Backend.SpernerPointerMachine
public import Complexity.Computability.Complexity.Classes.TFNP

@[expose] public section

/-! Uniform circuit emission turns the local Sperner machine into an End-of-Line
instance. Every target endpoint remains the same encoded triangular cell; the
answer decoder is a certified projection and does not follow a path. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime
open GameTheory.Math.Sperner

/-- Native uniform compilation emits both pointer vectors at the exact node width. -/
theorem exists_spernerEndOfLineInstance :
    ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧
      ∀ input, endOfLineWidth (f input) = gridNodeWidth (CircuitWords.first input).length ∧
        ∀ vertex, vertex.length = gridNodeWidth (CircuitWords.first input).length →
          endOfLinePredecessor (f input) vertex = spernerPointer input true vertex ∧
          endOfLineSuccessor (f input) vertex = spernerPointer input false vertex := by
  have hn : ComputableInPolyTime
      (fun input : List Bool => gridNodeWidth (CircuitWords.first input).length)
      encBits encUnary :=
    unary_add' (unary_mul' (const 2) (length_bits.comp CircuitWords.first_polyTime)) (const 2)
  have hp : ComputableInPolyTime
      (fun p : List Bool × List Bool => spernerPointer p.1 true p.2)
      (encPair encBits encBits) encBits :=
    spernerPointer_polyTime true (fst encBits encBits) (snd encBits encBits)
  have hs : ComputableInPolyTime
      (fun p : List Bool × List Bool => spernerPointer p.1 false p.2)
      (encPair encBits encBits) encBits :=
    spernerPointer_polyTime false (fst encBits encBits) (snd encBits encBits)
  obtain ⟨f, hf, hwidth, hpointers⟩ := exists_pointerCircuitInstance hn hp hs
    (fun _ _ hu => (gridPointerMachine_length _ _ _ _).trans hu)
    (fun _ _ hu => (gridPointerMachine_length _ _ _ _).trans hu)
  exact ⟨f, hf, fun input => ⟨hwidth input, hpointers input⟩⟩

private theorem compiledSperner_source (f : List Bool → List Bool) (input : List Bool)
    (hwidth : endOfLineWidth (f input) = gridNodeWidth (CircuitWords.first input).length)
    (hptr : ∀ vertex, vertex.length = gridNodeWidth (CircuitWords.first input).length →
      endOfLinePredecessor (f input) vertex = spernerPointer input true vertex ∧
      endOfLineSuccessor (f input) vertex = spernerPointer input false vertex) :
    endOfLineSourceValid (f input) := by
  have ho : endOfLineOrigin (f input) = encodeGridNode (CircuitWords.first input).length none := by
    simp only [endOfLineOrigin, hwidth, encodeGridNode]
  have hsource := spernerPointer_source input
  have h₀ := hptr (encodeGridNode (CircuitWords.first input).length none) (encodeGridNode_length _ _)
  have h₁ := hptr (spernerPointer input false (encodeGridNode (CircuitWords.first input).length none))
    ((gridPointerMachine_length _ _ _ _).trans (encodeGridNode_length _ _))
  exact ⟨by rw [ho, h₀.1]; exact hsource.1,
    by rw [ho, h₀.2]; exact hsource.2.1,
    by rw [ho, h₀.2, h₁.1]; exact hsource.2.2⟩

/-- Exact-width pointer compilation preserves every End-of-Line answer, including
endpoints on components disconnected from the source. -/
theorem spernerToEndOfLineReductionOfCircuitInstance (f : List Bool → List Bool)
    (hf : ComputableInPolyTime f encBits encBits)
    (heval : ∀ input, endOfLineWidth (f input) = gridNodeWidth (CircuitWords.first input).length ∧
      ∀ vertex, vertex.length = gridNodeWidth (CircuitWords.first input).length →
        endOfLinePredecessor (f input) vertex = spernerPointer input true vertex ∧
        endOfLineSuccessor (f input) vertex = spernerPointer input false vertex) :
    Cslib.Complexity.SearchReducible encBits encBits spernerRelation endOfLineRelation := by
  apply Cslib.Complexity.SearchReducible.of_isTotalSearch
    (f := f) (g := Prod.snd) endOfLineRelation_total hf (snd encBits encBits)
  intro input witness hw
  change spernerRelation input witness
  obtain ⟨hwidth, hptr⟩ := heval input
  have hsource := compiledSperner_source f input hwidth hptr
  rcases hw with ⟨_, hlen, hne, hend⟩ | ⟨hbad, _⟩
  · have hlen' := hlen.trans hwidth
    have hv := hptr witness hlen'
    have hp := hptr (spernerPointer input true witness)
      ((gridPointerMachine_length _ _ _ _).trans hlen')
    have hs := hptr (spernerPointer input false witness)
      ((gridPointerMachine_length _ _ _ _).trans hlen')
    have he : GameTheory.Math.EndOfLine.IsEndpoint
        (spernerPointer input true) (spernerPointer input false) witness := by
      simpa only [GameTheory.Math.EndOfLine.IsEndpoint,
        GameTheory.Math.EndOfLine.HasPredecessor, GameTheory.Math.EndOfLine.HasSuccessor,
        hv.1, hv.2, hp.2, hs.1] using hend
    have hne' : witness ≠ encodeGridNode (CircuitWords.first input).length none := by
      simpa only [endOfLineOrigin, hwidth, encodeGridNode] using hne
    obtain ⟨t, hd, _, ht⟩ := spernerPointer_endpoint_decodes input witness hne' he
    exact ⟨t, hd, ht⟩
  · exact False.elim (hbad hsource)

/-- Efficient instance compilation and the answer projection form a native search reduction. -/
theorem exists_spernerToEndOfLineReduction :
    Cslib.Complexity.SearchReducible encBits encBits spernerRelation endOfLineRelation := by
  obtain ⟨f, hf, heval⟩ := exists_spernerEndOfLineInstance
  exact spernerToEndOfLineReductionOfCircuitInstance f hf heval

end GameTheory.Complexity.Backend
