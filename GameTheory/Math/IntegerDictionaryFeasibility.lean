import GameTheory.Math.IntegerDictionaryComputation
import GameTheory.Math.FiniteLexicographicCompare

/-! Executable integer Cramer checks characterize strict lexicographic
feasibility of the rational symbolic dictionary with unit right-hand side.
The sign-adjusted numerator test uses no rational arithmetic. -/

namespace GameTheory.Math

/-- Integer Cramer checks for invertibility and strict symbolic feasibility. -/
def IntegerFeasible {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) : Prop :=
  IntegerCramerComputation.determinant M ≠ 0 ∧ ∀ i,
    FiniteLexicographicCompare.lexLT (fun _ => 0)
      (IntegerDictionaryComputation.coefficients M (fun _ => 1) i) = true

instance {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) : Decidable (IntegerFeasible M) := by
  unfold IntegerFeasible; infer_instance

private theorem cast_lex_pos_iff {k : ℕ} (c : Fin k → ℤ) :
    0 < toLex (fun j => (c j : ℚ)) ↔ 0 < toLex c := by
  constructor <;> rintro ⟨i, hpre, hpos⟩
  · refine ⟨i, fun j hj => ?_, ?_⟩
    · have he := hpre j hj
      change (0 : ℚ) = (c j : ℚ) at he
      change (0 : ℤ) = c j
      exact_mod_cast he
    · change (0 : ℚ) < (c i : ℚ) at hpos
      change (0 : ℤ) < c i
      exact_mod_cast hpos
  · refine ⟨i, fun j hj => ?_, ?_⟩
    · have he := hpre j hj
      change (0 : ℤ) = c j at he
      change (0 : ℚ) = (c j : ℚ)
      exact_mod_cast he
    · change (0 : ℤ) < c i at hpos
      change (0 : ℚ) < (c i : ℚ)
      exact_mod_cast hpos

/-- The executable integer checks characterize the canonical rational invariant. -/
theorem integerFeasible_iff {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) :
    IntegerFeasible M ↔ (M.map (fun z : ℤ => (z : ℚ))).det ≠ 0 ∧
      ∀ i, 0 < toLex (PerturbedDictionary.dictionaryCoefficients
        (M.map (fun z : ℤ => (z : ℚ))) (fun _ => 1) i) := by
  have hdet : (M.map (fun z : ℤ => (z : ℚ))).det ≠ 0 ↔ M.det ≠ 0 := by
    rw [← Int.cast_det, Int.cast_ne_zero]
  rw [IntegerFeasible, IntegerCramerComputation.determinant_eq, hdet]
  constructor
  · rintro ⟨hd, hf⟩
    refine ⟨hd, fun i => ?_⟩
    have hp := (FiniteLexicographicCompare.lexLT_eq_true _ _).mp (hf i)
    have hq := (cast_lex_pos_iff _).mpr hp
    have hD : (0 : ℚ) < IntegerCramerComputation.denominator M := by
      rw [IntegerCramerComputation.denominator_eq]
      exact_mod_cast IntegerCramerEncoding.denominator_pos M hd
    have hx := (FiniteLexicographic.div_lt_div_iff (x := fun _ => (0 : ℚ))
      (y := fun j => (IntegerDictionaryComputation.coefficients M (fun _ => 1) i j : ℚ)) hD).mpr hq
    simp only [zero_div, IntegerDictionaryComputation.coefficients_decode M (fun _ => 1) hd,
      Int.cast_one] at hx
    exact hx
  · rintro ⟨hd, hf⟩
    refine ⟨hd, fun i => ?_⟩
    apply (FiniteLexicographicCompare.lexLT_eq_true _ _).mpr
    apply (cast_lex_pos_iff _).mp
    have hD : (0 : ℚ) < IntegerCramerComputation.denominator M := by
      rw [IntegerCramerComputation.denominator_eq]
      exact_mod_cast IntegerCramerEncoding.denominator_pos M hd
    apply (FiniteLexicographic.div_lt_div_iff (x := fun _ => (0 : ℚ))
      (y := fun j => (IntegerDictionaryComputation.coefficients M (fun _ => 1) i j : ℚ)) hD).mp
    have hx := hf i
    change toLex (fun _ => (0 : ℚ)) < toLex _ at hx
    simpa only [zero_div, IntegerDictionaryComputation.coefficients_decode M (fun _ => 1) hd,
      Int.cast_one] using hx

end GameTheory.Math
