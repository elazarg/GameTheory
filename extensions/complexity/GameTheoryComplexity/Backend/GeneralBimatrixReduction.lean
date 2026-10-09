import GameTheoryComplexity.Backend.GeneralBimatrixCircuitMachine
import GameTheoryComplexity.Backend.GeneralBimatrixPathEndpoint
import GameTheoryComplexity.Backend.RawEndOfLine
import GameTheoryComplexity.Backend.SearchReduction

/-! Polynomial reduction of exact signed rectangular Nash search to End-of-Line.
The answer machine reconstructs the dictionary of the supplied endpoint and
emits its equilibrium certificate; it never follows or enumerates a path. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

/-- Emit the supplied endpoint's certificate, with the original malformed-input fallback. -/
def generalBimatrixAnswerWord (v : Fin 2 → List Bool) : List Bool :=
  caseBit₀ (generalInstanceFlag (v 0))
    (generalBimatrixDictionaryEndpointWord (generalBimatrixNodeData v)) []

theorem generalBimatrixAnswerWord_cobham : Cobham generalBimatrixAnswerWord :=
  Cobham.iteFn (Cobham.comp generalInstanceFlag_cobham fun _ => .proj 0)
    (Cobham.comp generalBimatrixDictionaryEndpointWord_cobham generalBimatrixNodeData_cobham)
    Cobham.empty

theorem generalBimatrixAnswerWord_mem_FPn : FPn generalBimatrixAnswerWord :=
  cobham_iff_FPn.mp generalBimatrixAnswerWord_cobham

theorem generalBimatrixAnswerWord_invalid (input node : List Bool)
    (hi : ¬GeneralInstanceValid input) : generalBimatrixAnswerWord ![input, node] = [] := by
  have hf : generalInstanceFlag input = [false] := by
    rcases andBit_flag _ _ with ht | hf
    · exact (hi ((generalInstanceFlag_eq_true_iff input).mp ht)).elim
    · exact hf
  rw [generalBimatrixAnswerWord, Matrix.cons_val_zero, hf]
  rfl

theorem generalBimatrixAnswerWord_encode (input : List Bool)
    (hi : GeneralInstanceValid input)
    {d : Fin (generalRowCount input + generalColCount input)}
    (port : GeneralBimatrixShiftedPort input d) :
    generalBimatrixAnswerWord ![input, encode port] =
      generalBimatrixDictionaryEndpointWord ![input, membershipWord port.node.basis.basic,
        generalBimatrixNodeData ![input, encode port] 2] := by
  rw [generalBimatrixAnswerWord, Matrix.cons_val_zero,
    (generalInstanceFlag_eq_true_iff input).mpr hi]
  have he : generalBimatrixNodeData ![input, encode port] =
      ![input, membershipWord port.node.basis.basic,
        generalBimatrixNodeData ![input, encode port] 2] := by
    funext i
    fin_cases i
    · rfl
    · exact generalBimatrixNodeData_basis input (generalBimatrixDimensionWord_length input) port
    · rfl
  rw [he]
  rfl

private theorem compiledBimatrix_source (f : List Bool → List Bool) (input : List Bool)
    (hi : GeneralInstanceValid input)
    (hwidth : endOfLineWidth (f input) = (generalBimatrixNodeRuler input).length)
    (hptr : ∀ vertex, vertex.length = (generalBimatrixNodeRuler input).length →
      endOfLinePredecessor (f input) vertex = generalBimatrixPredecessorWord ![input, vertex] ∧
      endOfLineSuccessor (f input) vertex = generalBimatrixSuccessorWord ![input, vertex]) :
    rawEndOfLineSourceValid (f input) := by
  let d := generalBimatrixDistinguishedLabel input hi
  let origin : GeneralBimatrixShiftedPort input d := bimatrixSourcePort _ _ d
  have ho : endOfLineOrigin (f input) = encode origin := by
    rw [endOfLineOrigin, hwidth, generalBimatrixNodeRuler_length input hi]
    exact (encode_source _ _ d).symm
  have hlen : (encode origin).length = (generalBimatrixNodeRuler input).length := by
    rw [encode_length, generalBimatrixNodeRuler_length input hi]
    rfl
  have hv := hptr (encode origin) hlen
  have hp := generalBimatrixPredecessorWord_encode_of_valid input hi rfl origin
    (generalBimatrixNodeValidFlag_encode input hi rfl origin)
  have hs := generalBimatrixSuccessorWord_encode_of_valid input hi rfl origin
    (generalBimatrixNodeValidFlag_encode input hi rfl origin)
  have hsource := BimatrixPathPort.source_pointers hi.1 hi.2.1
    (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
    (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le) d
  refine ⟨?_, ?_⟩
  · rw [ho, hv.1, hp, hsource.1]
  · rw [ho, hv.2, hs]
    exact fun he => hsource.2.1 (encode_injective he)

/-- Compile the actual pointers and decode every raw End-of-Line answer. -/
def generalBimatrixToEndOfLineReductionOfCircuitInstance
    (f : List Bool → List Bool) (hf : f ∈ FP)
    (heval : ∀ input, endOfLineWidth (f input) = (generalBimatrixNodeRuler input).length ∧
      ∀ vertex, vertex.length = (generalBimatrixNodeRuler input).length →
        endOfLinePredecessor (f input) vertex = generalBimatrixPredecessorWord ![input, vertex] ∧
        endOfLineSuccessor (f input) vertex = generalBimatrixSuccessorWord ![input, vertex]) :
    SearchReduction generalBimatrixRelation rawEndOfLineRelation where
  instanceMap := f
  instanceMap_mem_FP := hf
  decode := generalBimatrixAnswerWord
  decode_mem_FPn := generalBimatrixAnswerWord_mem_FPn
  sound := by
    intro input witness hw
    by_cases hi : GeneralInstanceValid input
    · obtain ⟨hwidth, hptr⟩ := heval input
      have hsource := compiledBimatrix_source f input hi hwidth hptr
      rcases hw with ⟨_, hlen, hw⟩ | ⟨hbad, _⟩
      · have hlen' := hlen.trans hwidth
        let d := generalBimatrixDistinguishedLabel input hi
        let origin : GeneralBimatrixShiftedPort input d := bimatrixSourcePort _ _ d
        have ho : endOfLineOrigin (f input) = encode origin := by
          rw [endOfLineOrigin, hwidth, generalBimatrixNodeRuler_length input hi]
          exact (encode_source _ _ d).symm
        have hword : GameTheory.Math.EndOfLine.RawWitness
            (fun node => generalBimatrixPredecessorWord ![input, node])
            (fun node => generalBimatrixSuccessorWord ![input, node]) (encode origin) witness := by
          rw [ho] at hw
          exact (GameTheory.Math.EndOfLine.rawWitness_congrOn _ _ _ _
            (fun node => node.length = (generalBimatrixNodeRuler input).length)
            (fun node hn => (hptr node hn).1) (fun node hn => (hptr node hn).2)
            (fun node hn => (generalBimatrixPredecessorWord_length _).trans hn)
            (fun node hn => (generalBimatrixSuccessorWord_length _).trans hn)
            _ witness hlen').mp hw
        have hP : (fun node => generalBimatrixPredecessorWord ![input, node]) =
            transport (generalBimatrixPathPredecessor input hi d) :=
          funext fun node => generalBimatrixPredecessorWord_eq_transport input node hi d rfl
        have hS : (fun node => generalBimatrixSuccessorWord ![input, node]) =
            transport (generalBimatrixPathSuccessor input hi d) :=
          funext fun node => generalBimatrixSuccessorWord_eq_transport input node hi d rfl
        rw [hP, hS] at hword
        obtain ⟨port, hdecode, hport⟩ := decode_of_rawWitness
          (generalBimatrixPathPredecessor input hi d)
          (generalBimatrixPathSuccessor input hi d) origin witness hword
        rw [← encode_of_decode_eq_some hdecode, generalBimatrixAnswerWord_encode input hi port]
        exact generalBimatrixPathEndpoint_accept input hi d port _ hport
      · exact (hbad hsource).elim
    · exact Or.inr ⟨hi, generalBimatrixAnswerWord_invalid input witness hi⟩

/-- The instance mapper and endpoint decoder both have actual polynomial-time certificates. -/
theorem exists_generalBimatrixToEndOfLineReduction :
    Nonempty (SearchReduction generalBimatrixRelation rawEndOfLineRelation) := by
  obtain ⟨f, hf, heval⟩ := exists_generalBimatrixEndOfLineInstance
  exact ⟨generalBimatrixToEndOfLineReductionOfCircuitInstance f hf heval⟩

end GameTheory.Complexity.Backend
