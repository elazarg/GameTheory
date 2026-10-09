import GameTheoryComplexity.Backend.BrouwerNashGlobalCorrectness
import GameTheoryComplexity.Backend.BrouwerNashJitterQuery
import GameTheoryComplexity.Backend.BrouwerNashExtractionQuery
import GameTheoryComplexity.Backend.BrouwerNashIncrementQuery
import GameTheoryComplexity.Backend.BrouwerNashInterpolationQuery
import GameTheoryComplexity.Backend.BrouwerNashColorQuery
import GameTheoryComplexity.Backend.BrouwerNashSelectorKind

/-! Polynomial composition of the disjoint coefficient-query regions of the Brouwer Nash program. -/
namespace GameTheory.Complexity.Backend.BrouwerNashSelector
open _root_.Complexity _root_.Complexity.Cobham

private def queries : List ((Fin 5 → List Bool) → List Bool) :=
  [BrouwerNashGlobalQuery.coefficientWord, BrouwerNashJitterQuery.coefficientWord,
    BrouwerNashExtractionQuery.coefficientWord, BrouwerNashIncrementQuery.allCoefficientWord,
    BrouwerNashInterpolationQuery.coefficientWord, BrouwerNashColorQuery.coefficientWord]

/-- Add the six disjoint canonical coefficient regions before fixed-width serialization. -/
def coefficientWord : (Fin 5 → List Bool) → List Bool := binarySignedQuerySum queries

/-- The entire coefficient selector has an actual polynomial-time certificate. -/
theorem coefficientWord_cobham : Cobham coefficientWord := by
  apply binarySignedQuerySum_cobham
  intro query hq
  simp only [queries, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq <;> subst query
  · exact BrouwerNashGlobalQuery.coefficientWord_cobham
  · exact BrouwerNashJitterQuery.coefficientWord_cobham
  · exact BrouwerNashExtractionQuery.coefficientWord_cobham
  · exact BrouwerNashIncrementQuery.allCoefficientWord_cobham
  · exact BrouwerNashInterpolationQuery.coefficientWord_cobham
  · exact BrouwerNashColorQuery.coefficientWord_cobham

theorem coefficientWord_mem_FPn : FPn coefficientWord := cobham_iff_FPn.mp coefficientWord_cobham

/-- All region contributions add exactly, including aliases and signed constants. -/
theorem coefficientWord_expansion (v : Fin 5 → List Bool) :
    binarySignedValue (coefficientWord v) =
      binarySignedValue (BrouwerNashGlobalQuery.coefficientWord v) +
        (binarySignedValue (BrouwerNashJitterQuery.coefficientWord v) +
          (binarySignedValue (BrouwerNashExtractionQuery.coefficientWord v) +
            (binarySignedValue (BrouwerNashIncrementQuery.allCoefficientWord v) +
              (binarySignedValue (BrouwerNashInterpolationQuery.coefficientWord v) +
                binarySignedValue (BrouwerNashColorQuery.coefficientWord v))))) := by
  simp only [coefficientWord, binarySignedQuerySum_value, queries, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- Specialize the uniform selector to the two source-dependent compiled color circuits. -/
def coefficientQuery (codes : Fin 2 → List Bool → List Bool)
    (v : Fin 3 → List Bool) : List Bool :=
  coefficientWord ![v 0, v 1, v 2, codes 0 (v 2), codes 1 (v 2)]

/-- Actual FP color-code producers compose with the uniform selector. -/
theorem coefficientQuery_cobham (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ flag, codes flag ∈ FP) : Cobham (coefficientQuery codes) := by
  have hcode (flag : Fin 2) : Cobham fun v : Fin 3 → List Bool => codes flag (v 2) :=
    (Cobham.comp (FP_subset_CobhamFP (hc flag)) fun _ : Fin 1 => .proj 2).of_eq fun _ => rfl
  have hv : ∀ i : Fin 5, Cobham fun v : Fin 3 → List Bool =>
      (![v 0, v 1, v 2, codes 0 (v 2), codes 1 (v 2)] : Fin 5 → List Bool) i := by
    intro i
    fin_cases i
    · exact .proj 0
    · exact .proj 1
    · exact .proj 2
    · exact hcode 0
    · exact hcode 1
  exact (Cobham.comp coefficientWord_cobham hv).of_eq fun _ => rfl

theorem coefficientQuery_mem_FPn (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ flag, codes flag ∈ FP) : FPn (coefficientQuery codes) :=
  cobham_iff_FPn.mp (coefficientQuery_cobham codes hc)

/-- Specialize the complete comparator flag to compiled source-dependent color circuits. -/
def kindQuery (codes : Fin 2 → List Bool → List Bool)
    (v : Fin 2 → List Bool) : List Bool :=
  BrouwerNashSelectorKind.kindWord ![v 0, [], v 1, codes 0 (v 1), codes 1 (v 1)]

/-- Actual FP color-code producers compose with the complete comparator flag. -/
theorem kindQuery_cobham (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ flag, codes flag ∈ FP) : Cobham (kindQuery codes) := by
  have hcode (flag : Fin 2) : Cobham fun v : Fin 2 → List Bool => codes flag (v 1) :=
    (Cobham.comp (FP_subset_CobhamFP (hc flag)) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hv : ∀ i : Fin 5, Cobham fun v : Fin 2 → List Bool =>
      (![v 0, [], v 1, codes 0 (v 1), codes 1 (v 1)] : Fin 5 → List Bool) i := by
    intro i
    fin_cases i
    · exact .proj 0
    · exact .const []
    · exact .proj 1
    · exact hcode 0
    · exact hcode 1
  exact (Cobham.comp BrouwerNashSelectorKind.kindWord_cobham hv).of_eq fun _ => rfl

theorem kindQuery_mem_FPn (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ flag, codes flag ∈ FP) : FPn (kindQuery codes) :=
  cobham_iff_FPn.mp (kindQuery_cobham codes hc)

end GameTheory.Complexity.Backend.BrouwerNashSelector
