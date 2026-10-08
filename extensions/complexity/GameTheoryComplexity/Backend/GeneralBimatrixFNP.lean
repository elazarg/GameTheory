import GameTheoryComplexity.Backend.GeneralBimatrixProblem
import GameTheoryComplexity.Backend.GeneralBimatrixVerifierMachine
import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness
import GameTheoryComplexity.Backend.PairedVerifier

/-! An actual polynomial-time paired-input decider for exact bimatrix certificates. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- The executable verifier agrees with the canonical certificate relation. -/
theorem generalBimatrixVerdict_accept_iff_relation (input certificate : List Bool) :
    generalBimatrixVerdict ![input, certificate] = [true] ↔
      generalBimatrixRelation input certificate :=
  generalBimatrixVerdict_eq_true_iff input certificate

/-- Validate the outer pair encoding and check the binary Nash certificate. -/
def generalBimatrixPairedVerdict : List Bool → List Bool :=
  canonicalPairedVerifier generalBimatrixVerdict

/-- The whole paired verifier has polynomial running time. -/
theorem generalBimatrixPairedVerdict_mem_FP : generalBimatrixPairedVerdict ∈ FP :=
  canonicalPairedVerifier_mem_FP _ generalBimatrixVerdict_mem_FPn

/-- A single deterministic machine checks every input/certificate pair. -/
theorem exists_generalBimatrixPairedVerdict_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime generalBimatrixPairedVerdict bound.eval :=
  mem_FP_iff_computesInTime_polynomial.mp generalBimatrixPairedVerdict_mem_FP

/-- Pair validation and exact arithmetic decide precisely the paired relation. -/
theorem generalBimatrixPairedVerdict_eq_true_iff_mem_pairLang (z : List Bool) :
    generalBimatrixPairedVerdict z = [true] ↔ z ∈ pairLang generalBimatrixRelation := by
  rw [generalBimatrixPairedVerdict,
    canonicalPairedVerifier_eq_true_iff _ generalBimatrixVerdict_flag]
  constructor
  · rintro ⟨hz, hc⟩
    exact ⟨pairFst z, pairSnd z, hz,
      (generalBimatrixVerdict_accept_iff_relation _ _).mp hc⟩
  · rintro ⟨input, certificate, rfl, hc⟩
    simp only [pairFst_pair, pairSnd_pair]
    exact ⟨trivial, (generalBimatrixVerdict_accept_iff_relation _ _).mpr hc⟩

/-- Exact certificate verification belongs to deterministic polynomial time. -/
theorem generalBimatrixRelation_pairLang_mem_P : pairLang generalBimatrixRelation ∈ P := by
  apply mem_P_of_decisionFn generalBimatrixPairedVerdict_mem_FP
  intro z
  rw [← generalBimatrixPairedVerdict_eq_true_iff_mem_pairLang]
  rcases canonicalPairedVerifier_flag generalBimatrixVerdict z with h | h <;>
    simp [generalBimatrixPairedVerdict, h]

/-- General signed rectangular bimatrix Nash certificates are in FNP. -/
theorem generalBimatrixRelation_mem_FNP : generalBimatrixRelation ∈ FNP :=
  ⟨generalBimatrixRelation_polyBalanced, generalBimatrixRelation_pairLang_mem_P⟩

end GameTheory.Complexity.Backend
