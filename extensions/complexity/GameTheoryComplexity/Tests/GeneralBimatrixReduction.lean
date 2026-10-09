import GameTheoryComplexity.BimatrixNash

/-! Every-answer soundness and endpoint-preserving controls for signed rectangular Nash search. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixReduction
open Backend GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec
open _root_.Complexity _root_.Complexity.Cobham

private def input : List Bool :=
  encodeGeneralInstance 1 2 3 (fun _ j => if j = 0 then -3 else 2)
    (fun _ j => if j = 0 then 1 else -2)

private theorem input_valid : GeneralInstanceValid input :=
  encodeGeneralInstance_valid 1 2 3 _ _ (by decide) (by decide) (by decide)

example : generalRowCount input = 1 ∧ generalColCount input = 2 := by decide +kernel
example : FPn generalBimatrixAnswerWord := generalBimatrixAnswerWord_mem_FPn
example : generalBimatrixRelation ∈ GameTheory.Complexity.PPAD :=
  GameTheory.Complexity.bimatrixNashRelation_mem_PPAD

-- This uses the actual mapper and answer machine for every target answer,
-- including answers on components disconnected from the distinguished source.
example : ∃ f : List Bool → List Bool, f ∈ FP ∧
    ∀ instanceWord witness, rawEndOfLineRelation (f instanceWord) witness →
      generalBimatrixRelation instanceWord (generalBimatrixAnswerWord ![instanceWord, witness]) := by
  obtain ⟨f, hf, heval⟩ := exists_generalBimatrixEndOfLineInstance
  exact ⟨f, hf, (generalBimatrixToEndOfLineReductionOfCircuitInstance f hf heval).sound⟩

-- The rectangular signed endpoint is retained; the decoder does not substitute
-- another equilibrium or traverse its complementary path.
private theorem answer_eq_endpoint
    {d : Fin (generalRowCount input + generalColCount input)}
    (port : GeneralBimatrixShiftedPort input d) :
    generalBimatrixAnswerWord ![input, encode port] = generalBimatrixEndpointWord input port.node.basis := by
  rw [generalBimatrixAnswerWord_encode input input_valid port]
  exact generalBimatrixDictionaryEndpointWord_eq_endpoint input input_valid port.node.basis _

example {d : Fin (generalRowCount input + generalColCount input)}
    (port : GeneralBimatrixShiftedPort input d)
    (hfits : (port.node.basis.cramerCertificate
      ((2 : ℤ) ^ generalCoefficientBits input + 1)
      ((2 : ℤ) ^ generalCoefficientBits input + 1)).FitsWidth (generalCertificateWidth input.length)) :
    decodeGeneralCertificate (generalRowCount input) (generalColCount input)
      (generalCertificateWidth input.length) (generalBimatrixAnswerWord ![input, encode port]) =
      port.node.basis.cramerCertificate ((2 : ℤ) ^ generalCoefficientBits input + 1)
        ((2 : ℤ) ^ generalCoefficientBits input + 1) := by
  rw [answer_eq_endpoint port]
  exact decodeGeneralCertificate_encode _ hfits

-- Malformed inputs have the designated empty answer regardless of the target word.
example : generalBimatrixAnswerWord ![[], [true, false, true, false]] = [] := by decide +kernel
example : generalBimatrixAnswerWord ![[true], List.replicate 12 true] = [] := by decide +kernel
example : generalBimatrixRelation [] (generalBimatrixAnswerWord ![[], [true, false]]) :=
  Or.inr ⟨by decide, generalBimatrixAnswerWord_invalid _ _ (by decide)⟩

end GameTheory.Complexity.Tests.GeneralBimatrixReduction