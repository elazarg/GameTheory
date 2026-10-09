import GameTheoryComplexity.Backend.BimatrixProgramMachine
import GameTheoryComplexity.Backend.GeneralBimatrixProblem

/-! Every accepted answer to the written integer game is a canonical certificate
for the decoded mixed-gate program, independently of how the answer was obtained. -/
namespace GameTheory.Complexity.Backend.BimatrixProgramCorrectness
open GameTheory.Finite

/-- Every accepted serialized-game answer satisfies the canonical program game's Nash checks. -/
theorem accepted_valid (tape answer : List Bool)
    (hk : 0 < (BimatrixProgramCodec.dimension tape).length)
    (ha : generalBimatrixRelation (BimatrixProgramMachine.instanceWord tape) answer) :
    (decodeGeneralCertificate ((BimatrixProgramCodec.dimension tape).length * 2)
      ((BimatrixProgramCodec.dimension tape).length * 2)
      (generalCertificateWidth (BimatrixProgramMachine.instanceWord tape).length) answer).Valid
      (BimatrixAffineGate.rowPayoff (BimatrixProgramCodec.baseline tape)
        (2 * (BimatrixProgramCodec.dimension tape).length))
      (BimatrixGateProgram.columnPayoff (BimatrixProgramCodec.baseline tape)
        (2 * (BimatrixProgramCodec.dimension tape).length) (BimatrixProgramCodec.decode tape)) := by
  have hi := BimatrixProgramMachine.instanceWord_valid tape hk
  rcases ha with ⟨_, _, hv⟩ | ⟨hn, _⟩
  · have hr : generalRowCount (BimatrixProgramMachine.instanceWord tape) =
        (BimatrixProgramCodec.dimension tape).length * 2 := by
      simp only [BimatrixProgramMachine.instanceWord, generalRowCount,
        generalInstanceWord_row, List.length_replicate, BimatrixProgramMachine.actions_length]
    have hc : generalColCount (BimatrixProgramMachine.instanceWord tape) =
        (BimatrixProgramCodec.dimension tape).length * 2 := by
      simp only [BimatrixProgramMachine.instanceWord, generalColCount,
        generalInstanceWord_col, List.length_replicate, BimatrixProgramMachine.actions_length]
    rw [hr, hc] at hv
    have hA : (fun i j : Fin ((BimatrixProgramCodec.dimension tape).length * 2) =>
        decodeGeneralPayoff false (BimatrixProgramMachine.instanceWord tape) i.val j.val) =
        BimatrixAffineGate.rowPayoff (BimatrixProgramCodec.baseline tape)
          (2 * (BimatrixProgramCodec.dimension tape).length) := by
      funext i j
      exact BimatrixProgramMachine.instanceWord_rowPayoff tape i j
    have hB : (fun i j : Fin ((BimatrixProgramCodec.dimension tape).length * 2) =>
        decodeGeneralPayoff true (BimatrixProgramMachine.instanceWord tape) i.val j.val) =
        BimatrixGateProgram.columnPayoff (BimatrixProgramCodec.baseline tape)
          (2 * (BimatrixProgramCodec.dimension tape).length)
          (BimatrixProgramCodec.decode tape) := by
      funext i j
      exact BimatrixProgramMachine.instanceWord_columnPayoff tape i j
    rwa [hA, hB] at hv
  · exact (hn hi).elim

end GameTheory.Complexity.Backend.BimatrixProgramCorrectness
