import GameTheoryComplexity.Backend.BrouwerNashProgram
import GameTheoryComplexity.Backend.BrouwerNashColor
import GameTheoryComplexity.Backend.BrouwerNashRewardMachine
import GameTheoryComplexity.Backend.SpernerProblem
import GameTheory.Finite.BimatrixBrouwerGateBounds
import GameTheory.Math.GridBrouwerErrorBudget
import GameTheory.Math.GridBrouwerColorSample
import GameTheory.Math.GridBrouwerJitter
import Mathlib.Data.Rat.BigOperators

/-! Every accepted certificate for the concrete sampled Brouwer program yields a small
canonical source-map residual. The proof connects the allocated extraction, color, interpolation,
averaging, and cyclic feedback gates; the emitted reward schedule supplies their error budget. -/

namespace GameTheory.Complexity.Backend.BrouwerNashProgramCorrectness
open GameTheory.Complexity.Backend
open _root_.Complexity.CircuitCode
open GameTheory.Finite GameTheory.Finite.BimatrixGateProgram
open BrouwerNashLayout BrouwerNashProgram
open scoped BigOperators

section
variable (b : ℕ) (raw₀ raw₁ : RawCircuit)
local notation "k" => dimension b raw₀.length raw₁.length
local notation "g" => program b raw₀ raw₁

private theorem one_placement :
    g (slot b raw₀.length raw₁.length one) =
      BimatrixArithmeticGate.gate (fun _ => 0) 2 := by
  rw [program_global b raw₀ raw₁ one (by simp only [one, globalCount]; omega), globalGate_one]

private theorem alpha_placement (j : ℕ) (hj : j < precision b) :
    g (slot b raw₀.length raw₁.length (alpha (j + 1))) =
      BimatrixDyadicGate.halvingGate (slot b raw₀.length raw₁.length (alpha j)) := by
  have hi : alpha (j + 1) < globalCount b := by
    simp only [alpha, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, globalCount]
    omega
  rw [program_global b raw₀ raw₁ _ hi, globalGate_alpha b raw₀.length raw₁.length j hj]

/-- Every accepted program certificate computes each clipped jitter coordinate accurately. -/
theorem jitter_error (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (t : Fin 41) (axis : Fin 2) :
    |(k : ℚ) * BimatrixAffineGate.value c
        (sampleRef b raw₀.length raw₁.length t (jitter axis)) -
      GameTheory.Math.gridJitterSample
        (max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
          (slot b raw₀.length raw₁.length (coordinate axis)))))
        (1 / 2 ^ precision b) 20 t| ≤ 43 * δ := by
  have hj : jitter axis < sampleWidth b raw₀.length raw₁.length := by
    have ha := axis.isLt
    simp only [jitter, sampleWidth]
    omega
  have hplace := program_sample b raw₀ raw₁ t (jitter axis) hj
  rw [sampleGate_jitter] at hplace
  apply BimatrixBrouwerGateBounds.jitter_error_of_halving_chain H (100 * (k : ℤ))
    (dimension_pos _ _ _) g c hc (by positivity) (coefficients_bound b raw₀ raw₁) hscale
    (slot b raw₀.length raw₁.length (coordinate axis))
    (sampleRef b raw₀.length raw₁.length t (jitter axis)) t
    (fun j => slot b raw₀.length raw₁.length (alpha j)) (precision b)
    (by simp only [precision]; omega) _ (alpha_placement b raw₀ raw₁)
    hplace δ hδ0 hδ
  simpa only [alpha, ite_true] using one_placement b raw₀ raw₁

private theorem digit_placement (t : Fin 41) (axis : Fin 2) (j : ℕ) (hj : j < b) :
    g (sampleRef b raw₀.length raw₁.length t (digit b axis j)) =
      BimatrixBinaryExtraction.digitGate
        (sampleRef b raw₀.length raw₁.length t (remainder b axis j)) := by
  have ha := axis.isLt
  have hlocal : digit b axis j + (0 : Fin 2).val < sampleWidth b raw₀.length raw₁.length := by
    simp only [digit, sampleWidth, Fin.val_zero]
    have hm := Nat.mul_le_mul_left (2 * b) (show axis.val ≤ 1 by omega)
    omega
  have he := program_sample b raw₀ raw₁ t (digit b axis j + (0 : Fin 2).val) hlocal
  rw [sampleGate_extraction b raw₀ raw₁ t axis j hj 0] at he
  simpa only [Fin.val_zero, Nat.add_zero, ite_true] using he

private theorem next_placement (t : Fin 41) (axis : Fin 2) (j : ℕ) (hj : j < b) :
    g (sampleRef b raw₀.length raw₁.length t (remainder b axis (j + 1))) =
      BimatrixBinaryExtraction.remainderGate
        (sampleRef b raw₀.length raw₁.length t (remainder b axis j))
        (sampleRef b raw₀.length raw₁.length t (digit b axis j)) := by
  have ha := axis.isLt
  have hlocal : digit b axis j + (1 : Fin 2).val < sampleWidth b raw₀.length raw₁.length := by
    simp only [digit, sampleWidth, Fin.val_one]
    have hm := Nat.mul_le_mul_left (2 * b) (show axis.val ≤ 1 by omega)
    omega
  have he := program_sample b raw₀ raw₁ t (digit b axis j + (1 : Fin 2).val) hlocal
  rw [sampleGate_extraction b raw₀ raw₁ t axis j hj 1] at he
  have hr : remainder b axis (j + 1) = digit b axis j + 1 := by
    simp only [remainder, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel, digit]
    omega
  rw [hr]
  simpa only [Fin.val_one, Nat.one_ne_zero, ite_false] using he

/-- Clear actual program samples emit exact binary digits and controlled final remainders. -/
theorem clear_sample_extraction (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ β : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hbudget : 50 * δ ≤ β) (t : Fin 41) (axis : Fin 2)
    (hgrid : ∀ l : ℕ, 0 < l → l < 2 ^ b → β <
      |GameTheory.Math.gridJitterSample
        (max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
          (slot b raw₀.length raw₁.length (coordinate axis)))))
        (1 / 2 ^ precision b) 20 t - (l : ℚ) / (2 : ℚ) ^ b|) :
    let sample := GameTheory.Math.gridJitterSample
      (max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
        (slot b raw₀.length raw₁.length (coordinate axis)))))
      (1 / 2 ^ precision b) 20 t
    (∀ j ≤ b, |(k : ℚ) * BimatrixAffineGate.value c
        (sampleRef b raw₀.length raw₁.length t (remainder b axis j)) -
          GameTheory.Math.binaryRemainder j sample| ≤ 46 * (2 : ℚ) ^ j * δ) ∧
    (∀ j < b, |(k : ℚ) * BimatrixAffineGate.value c
        (sampleRef b raw₀.length raw₁.length t (digit b axis j)) -
          (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j sample)
            then 1 else 0)| ≤ δ) := by
  have hj : jitter axis < sampleWidth b raw₀.length raw₁.length := by
    have ha := axis.isLt
    simp only [jitter, sampleWidth]
    omega
  have hplace := program_sample b raw₀ raw₁ t (jitter axis) hj
  rw [sampleGate_jitter] at hplace
  apply BimatrixBrouwerGateBounds.jitter_extraction_errors H (100 * (k : ℤ))
    (dimension_pos _ _ _) g c hc (by positivity) (coefficients_bound b raw₀ raw₁) hscale
    (slot b raw₀.length raw₁.length (coordinate axis)) t
    (fun j => slot b raw₀.length raw₁.length (alpha j))
    (fun j => sampleRef b raw₀.length raw₁.length t (remainder b axis j))
    (fun j => sampleRef b raw₀.length raw₁.length t (digit b axis j))
    (precision b) b (by simp only [precision]; omega) _ (alpha_placement b raw₀ raw₁)
    hplace (digit_placement b raw₀ raw₁ t axis) (next_placement b raw₀ raw₁ t axis)
    δ β hδ0 hδ hbudget hgrid
  simpa only [alpha, ite_true] using one_placement b raw₀ raw₁

/-- Interpolation is uniformly accurate relative to clipped actual remainders. -/
theorem sample_weights_error (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (t : Fin 41) :
    let u := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (remainder b 0 b))))
    let v := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (remainder b 1 b))))
    ∀ corner : Fin 4, |(((k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (weight b corner)) : ℚ) : ℝ) -
        GameTheory.Math.Brouwer.fourCornerWeights (u : ℝ) (v : ℝ) corner| ≤
          ((8 * δ : ℚ) : ℝ) := by
  let ref := sampleRef b raw₀.length raw₁.length t
  have hstage (s : Fin 8) : g (ref (weightBase b + s.val)) =
      interpolationGate b raw₀.length raw₁.length t s := by
    have hi : weightBase b + s.val < sampleWidth b raw₀.length raw₁.length := by
      have hs := s.isLt
      simp only [weightBase, sampleWidth]
      omega
    rw [program_sample b raw₀ raw₁ t _ hi, sampleGate_interpolation]
  have he := BimatrixBrouwerGateBounds.clipped_interpolation_error H (100 * (k : ℤ))
    (dimension_pos _ _ _) g c hc (by positivity) (coefficients_bound b raw₀ raw₁) hscale
    (ref (remainder b 0 b)) (ref (remainder b 1 b))
    (ref (weightBase b + 0)) (ref (weightBase b + 1))
    (ref (weightBase b + 2)) (ref (weightBase b + 3))
    (ref (weightBase b + 4)) (ref (weightBase b + 5))
    (ref (weightBase b + 6)) (ref (weightBase b + 7))
    (by simpa [interpolationGate, ref, complement, weightTemporary] using hstage 0)
    (by simpa [interpolationGate, ref, complement, weightTemporary] using hstage 1)
    (by simpa [interpolationGate, ref, complement, weightTemporary] using hstage 2)
    (by simpa [interpolationGate, ref, complement, weightTemporary] using hstage 3)
    (by simpa [interpolationGate, ref, complement, weightTemporary] using hstage 4)
    (by simpa [interpolationGate, ref, complement, weightTemporary] using hstage 5)
    (by simpa [interpolationGate, ref, complement, weightTemporary] using hstage 6)
    (by simpa [interpolationGate, ref, complement, weightTemporary] using hstage 7)
    δ hδ0 hδ
  dsimp only at he ⊢
  intro corner
  have h := he corner
  fin_cases corner <;> simpa [weight, ref] using h

private theorem minimum_placement (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (temporary : Bool) :
    g (sampleRef b raw₀.length raw₁.length t
      (minimumTemporary b raw₀.length raw₁.length corner flag +
        if temporary then 0 else 1)) =
      minimumGate b raw₀.length raw₁.length t corner flag temporary := by
  rw [program_sample b raw₀ raw₁ t _
    (minimum_lt_sampleWidth b raw₀.length raw₁.length corner flag temporary), sampleGate_minimum]

/-- Actual weighted-flag blocks uniformly approximate minima of clipped color wires. -/
theorem sample_minimum_error (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    let u := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (remainder b 0 b))))
    let v := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (remainder b 1 b))))
    let colorLength := if flag.val = 0 then raw₀.length else raw₁.length
    |(k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (minimum b raw₀.length raw₁.length corner flag)) -
      min (GameTheory.Math.Brouwer.fourCornerWeights u v corner)
        (max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
          (sampleRef b raw₀.length raw₁.length t
            (colorGate b raw₀.length raw₁.length corner flag + (colorLength - 1))))))| ≤
      19 * δ := by
  let ref := sampleRef b raw₀.length raw₁.length t
  let u : ℚ := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c (ref (remainder b 0 b))))
  let v : ℚ := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c (ref (remainder b 1 b))))
  let w : ℚ := GameTheory.Math.Brouwer.fourCornerWeights u v corner
  have hw0 : 0 ≤ w := GameTheory.Math.Brouwer.fourCornerWeights_nonneg
    (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _))
    (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _)) corner
  have hsum := GameTheory.Math.Brouwer.fourCornerWeights_sum u v
  have hw1 : w ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => GameTheory.Math.Brouwer.fourCornerWeights_nonneg
      (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _))
      (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _)) j) (Finset.mem_univ corner)
  have hwR0 : (0 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw0
  have hwR1 : (w : ℝ) ≤ 1 := by exact_mod_cast hw1
  have hweight : |(((k : ℚ) * BimatrixAffineGate.value c (ref (weight b corner)) : ℚ) : ℝ) -
      (w : ℝ)| ≤ ((8 * δ : ℚ) : ℝ) := by
    simpa only [w, GameTheory.Math.Brouwer.fourCornerWeights_rat_cast] using
      sample_weights_error b raw₀ raw₁ H c hc hscale δ hδ0 hδ t corner
  have ht := minimum_placement b raw₀ raw₁ t corner flag true
  have ho := minimum_placement b raw₀ raw₁ t corner flag false
  simp only [ite_true, Nat.add_zero, minimumGate] at ht
  simp only [Bool.false_eq_true, ite_false, minimumGate] at ho
  have he := BimatrixBrouwerGateBounds.clipped_color_min_error H (100 * (k : ℤ))
    (dimension_pos _ _ _) g c hc (by positivity) (coefficients_bound b raw₀ raw₁) hscale
    _ _ _ _ ht ho (w : ℝ) hwR0 hwR1 δ hδ hweight
  exact_mod_cast he

/-- Ideal sample weights use the clipped actual remainder wires and canonical interpolation. -/
def sampleWeights (c : BimatrixCertificate (k * 2) (k * 2)) (t : Fin 41) : Fin 4 → ℚ :=
  GameTheory.Math.Brouwer.fourCornerWeights
    (max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (remainder b 0 b)))))
    (max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (remainder b 1 b)))))

/-- Each scalar color observation is clipped to the unit interval before ideal averaging. -/
def sampleColor (c : BimatrixCertificate (k * 2) (k * 2)) (t : Fin 41)
    (corner : Fin 4) (flag : Fin 2) : ℚ :=
  let colorLength := if flag.val = 0 then raw₀.length else raw₁.length
  max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
    (sampleRef b raw₀.length raw₁.length t
      (colorGate b raw₀.length raw₁.length corner flag + (colorLength - 1)))))

/-- Actual averaging wires approximate canonical clipped sample means uniformly. -/
theorem mean_error (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (axis : Fin 2) :
    |(k : ℚ) * BimatrixAffineGate.value c (slot b raw₀.length raw₁.length (average b axis)) -
      (∑ t : Fin 41, ∑ a : Fin 4,
        (2 * min (sampleWeights b raw₀ raw₁ c t a) (sampleColor b raw₀ raw₁ c t a axis) +
          min (sampleWeights b raw₀ raw₁ c t a)
            (sampleColor b raw₀ raw₁ c t a ((![1, 0] : Fin 2 → Fin 2) axis)))) / 123| ≤
      77 * δ := by
  have hi : average b axis < globalCount b := by
    have ha := axis.isLt
    simp only [average, globalCount]
    omega
  have hplace := program_global b raw₀ raw₁ (average b axis) hi
  rw [globalGate_average, averageGate_eq_meanGate] at hplace
  have hw0 (t : Fin 41) (a : Fin 4) : 0 ≤ sampleWeights b raw₀ raw₁ c t a := by
    apply GameTheory.Math.Brouwer.fourCornerWeights_nonneg
    all_goals first | exact le_max_left _ _ | exact max_le (by norm_num) (min_le_left _ _)
  have hsum (t : Fin 41) : ∑ a, sampleWeights b raw₀ raw₁ c t a = 1 :=
    GameTheory.Math.Brouwer.fourCornerWeights_sum _ _
  have hmean := BimatrixColorMeanGate.mean_gate_error (units b raw₀.length raw₁.length)
    (by simp only [units]; omega) rfl H (100 * (k : ℤ)) g c hc (by positivity)
    (coefficients_bound b raw₀ raw₁) hscale _ _ _ hplace (sampleWeights b raw₀ raw₁ c)
    (fun t a => sampleColor b raw₀ raw₁ c t a axis)
    (fun t a => sampleColor b raw₀ raw₁ c t a ((![1, 0] : Fin 2 → Fin 2) axis))
    (19 * δ) hw0 hsum (fun _ _ => le_max_left _ _) (fun _ _ => le_max_left _ _)
    (fun t a => sample_minimum_error b raw₀ raw₁ H c hc hscale δ hδ0 hδ t a axis)
    (fun t a => sample_minimum_error b raw₀ raw₁ H c hc hscale δ hδ0 hδ t a _)
  simp only [dimension] at hmean hδ ⊢
  linarith only [hmean, hδ]

/-- The negative component mean averages the two canonical minimum-weight channels. -/
def negativeMean (c : BimatrixCertificate (k * 2) (k * 2)) (axis : Fin 2) : ℚ :=
  (∑ t : Fin 41, ∑ a : Fin 4,
    (2 * min (sampleWeights b raw₀ raw₁ c t a) (sampleColor b raw₀ raw₁ c t a axis) +
      min (sampleWeights b raw₀ raw₁ c t a)
        (sampleColor b raw₀ raw₁ c t a ((![1, 0] : Fin 2 → Fin 2) axis)))) / 123

private theorem negative_placement (axis : Fin 2) (j : ℕ) (hj : j < precision b) :
    g (slot b raw₀.length raw₁.length (negative b axis (j + 1))) =
      BimatrixDyadicGate.halvingGate (slot b raw₀.length raw₁.length (negative b axis j)) := by
  have hi : negative b axis (j + 1) < globalCount b := by
    have ha := axis.isLt
    have hm := Nat.mul_le_mul_right (precision b) (show axis.val ≤ 1 by omega)
    simp only [negative, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel, globalCount]
    omega
  rw [program_global b raw₀ raw₁ _ hi, globalGate_negative b raw₀.length raw₁.length j axis hj]

private theorem feedback_placement (axis : Fin 2) (stage : Fin 2) :
    g (slot b raw₀.length raw₁.length (feedbackHalf b axis + stage.val)) =
      if stage.val = 0 then BimatrixFeedbackGate.halfAddGate
        (slot b raw₀.length raw₁.length (coordinate axis))
        (slot b raw₀.length raw₁.length (positive b))
      else BimatrixFeedbackGate.subtractHalfGate
        (slot b raw₀.length raw₁.length (feedbackHalf b axis))
        (slot b raw₀.length raw₁.length (negative b axis (precision b))) := by
  have hi : feedbackHalf b axis + stage.val < globalCount b := by
    have ha := axis.isLt
    have hs := stage.isLt
    simp only [feedbackHalf, globalCount]
    omega
  rw [program_global b raw₀ raw₁ _ hi, globalGate_feedback]

/-- Actual program scaling and cyclic feedback enforce an approximately projected update. -/
theorem feedback_error (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (axis : Fin 2) :
    let x := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
      (slot b raw₀.length raw₁.length (coordinate axis))))
    |x - max 0 (min 1 (x + (1 / (2 : ℚ) ^ precision b) / 3 -
      negativeMean b raw₀ raw₁ c axis / 2 ^ precision b))| ≤ 12 * δ := by
  have hw0 (t : Fin 41) (a : Fin 4) : 0 ≤ sampleWeights b raw₀ raw₁ c t a := by
    apply GameTheory.Math.Brouwer.fourCornerWeights_nonneg
    all_goals first | exact le_max_left _ _ | exact max_le (by norm_num) (min_le_left _ _)
  have hsum (t : Fin 41) : ∑ a, sampleWeights b raw₀ raw₁ c t a = 1 :=
    GameTheory.Math.Brouwer.fourCornerWeights_sum _ _
  have hunit := BimatrixColorMeanGate.min_mean_mem_unit (sampleWeights b raw₀ raw₁ c)
    (fun t a => sampleColor b raw₀ raw₁ c t a axis)
    (fun t a => sampleColor b raw₀ raw₁ c t a ((![1, 0] : Fin 2 → Fin 2) axis)) hw0 hsum
    (fun _ _ => le_max_left _ _) (fun _ _ => le_max_left _ _)
  have hpositive := program_global b raw₀ raw₁ (positive b)
    (by simp only [positive, globalCount]; omega)
  rw [globalGate_positive] at hpositive
  have hcoordinate := program_global b raw₀ raw₁ (coordinate axis)
    (by have ha := axis.isLt; simp only [coordinate, globalCount]; omega)
  rw [globalGate_coordinate] at hcoordinate
  have hhalf := feedback_placement b raw₀ raw₁ axis 0
  have hsub := feedback_placement b raw₀ raw₁ axis 1
  simp only [Fin.val_zero, Nat.add_zero, ite_true] at hhalf
  simp only [Fin.val_one, Nat.one_ne_zero, ite_false] at hsub
  have hone : g (slot b raw₀.length raw₁.length (alpha 0)) =
      BimatrixArithmeticGate.gate (fun _ => 0) 2 := by
    simpa only [alpha, ite_true] using one_placement b raw₀ raw₁
  have he := BimatrixBrouwerGateBounds.scaled_mean_feedback_error H (100 * (k : ℤ))
    (units b raw₀.length raw₁.length) (by simp only [units]; omega) rfl g c hc
    (by positivity) (coefficients_bound b raw₀ raw₁) hscale
    (fun j => slot b raw₀.length raw₁.length (alpha j))
    (fun j => slot b raw₀.length raw₁.length (negative b axis j))
    (precision b) (by simp only [precision]; omega) hone (alpha_placement b raw₀ raw₁)
    (negative_placement b raw₀ raw₁ axis)
    (slot b raw₀.length raw₁.length (coordinate axis))
    (slot b raw₀.length raw₁.length (positive b))
    (slot b raw₀.length raw₁.length (feedbackHalf b axis))
    (slot b raw₀.length raw₁.length (feedbackSub b axis))
    hpositive hhalf hsub hcoordinate (negativeMean b raw₀ raw₁ c axis) δ hunit.1 hunit.2
    hδ0 hδ (mean_error b raw₀ raw₁ H c hc hscale δ hδ0 hδ axis)
  exact he

/-- The ideal sample signal is the canonical minimum-weight color signal on real casts. -/
def sampleSignal (c : BimatrixCertificate (k * 2) (k * 2)) (t : Fin 41) : ℝ × ℝ :=
  GameTheory.Math.Brouwer.fourCornerColorSignal
    (fun a => (sampleWeights b raw₀ raw₁ c t a : ℝ))
    (fun a => (sampleColor b raw₀ raw₁ c t a 0 : ℝ))
    (fun a => (sampleColor b raw₀ raw₁ c t a 1 : ℝ))

/-- The mean color displacement and the scaled negative mean have identical coordinates. -/
theorem sampleSignal_mean (c : BimatrixCertificate (k * 2) (k * 2)) (axis : Fin 2) :
    (∑ t : Fin 41, (![(sampleSignal b raw₀ raw₁ c t).1,
      (sampleSignal b raw₀ raw₁ c t).2] : Fin 2 → ℝ) axis) / 41 =
      1 - 3 * (negativeMean b raw₀ raw₁ c axis : ℝ) := by
  fin_cases axis <;> dsimp only [sampleSignal, GameTheory.Math.Brouwer.fourCornerColorSignal,
    negativeMean] <;> push_cast
  all_goals
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

/-- Ideal clipped sample signals remain bounded even at unreliable extraction samples. -/
theorem sampleSignal_abs_le_two (c : BimatrixCertificate (k * 2) (k * 2)) (t : Fin 41) :
    |(sampleSignal b raw₀ raw₁ c t).1| ≤ 2 ∧ |(sampleSignal b raw₀ raw₁ c t).2| ≤ 2 := by
  have hw0 (a : Fin 4) : 0 ≤ (sampleWeights b raw₀ raw₁ c t a : ℝ) := by
    exact_mod_cast (GameTheory.Math.Brouwer.fourCornerWeights_nonneg
      (le_max_left _ _) (max_le (by norm_num : (0 : ℚ) ≤ 1) (min_le_left _ _))
      (le_max_left _ _) (max_le (by norm_num : (0 : ℚ) ≤ 1) (min_le_left _ _)) a :
        (0 : ℚ) ≤ sampleWeights b raw₀ raw₁ c t a)
  have hsum : ∑ a, (sampleWeights b raw₀ raw₁ c t a : ℝ) = 1 := by
    exact_mod_cast (GameTheory.Math.Brouwer.fourCornerWeights_sum _ _ :
      (∑ a, sampleWeights b raw₀ raw₁ c t a) = 1)
  have hz (f : Fin 2) (a : Fin 4) : 0 ≤ (sampleColor b raw₀ raw₁ c t a f : ℝ) := by
    exact Rat.cast_nonneg.mpr (le_max_left (0 : ℚ) _ :
      0 ≤ sampleColor b raw₀ raw₁ c t a f)
  exact GameTheory.Math.Brouwer.fourCornerColorSignal_abs_le_two _ _ _ hw0 hsum (hz 0) (hz 1)

/-- Canonical sample averaging is exactly the displacement used by actual cyclic feedback. -/
theorem feedback_signal_error (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (axis : Fin 2) :
    let x := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
      (slot b raw₀.length raw₁.length (coordinate axis))))
    let θ : ℝ := ((1 / (2 : ℚ) ^ precision b) / 3 : ℚ)
    |(x : ℝ) - max 0 (min 1 ((x : ℝ) + θ *
      ((∑ t : Fin 41, (![(sampleSignal b raw₀ raw₁ c t).1,
        (sampleSignal b raw₀ raw₁ c t).2] : Fin 2 → ℝ) axis) / 41)))| ≤ ((12 * δ : ℚ) : ℝ) := by
  dsimp only
  rw [sampleSignal_mean]
  have he := feedback_error b raw₀ raw₁ H c hc hscale δ hδ0 hδ axis
  let x : ℚ := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
    (slot b raw₀.length raw₁.length (coordinate axis))))
  have heR : |(x : ℝ) - max 0 (min 1 ((x : ℝ) +
      ((1 / (2 : ℚ) ^ precision b / 3 : ℚ) : ℝ) -
      ((negativeMean b raw₀ raw₁ c axis / 2 ^ precision b : ℚ) : ℝ)))| ≤
        ((12 * δ : ℚ) : ℝ) := by exact_mod_cast he
  have hid : ((1 / (2 : ℚ) ^ precision b / 3 : ℚ) : ℝ) *
      (1 - 3 * (negativeMean b raw₀ raw₁ c axis : ℝ)) =
      ((1 / (2 : ℚ) ^ precision b / 3 : ℚ) : ℝ) -
        ((negativeMean b raw₀ raw₁ c axis / 2 ^ precision b : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hid]
  simpa only [add_sub_assoc] using heR

/-- The four canonical cell colors at the exact binary-selected grid cell. -/
def cornerColors (color : ℕ → ℕ → Fin 3) (qx qy : ℚ) : Fin 4 → Fin 3 :=
  ![color (GameTheory.Math.binaryPrefix b qx) (GameTheory.Math.binaryPrefix b qy),
    color (GameTheory.Math.binaryPrefix b qx + 1) (GameTheory.Math.binaryPrefix b qy + 1),
    color (GameTheory.Math.binaryPrefix b qx + 1) (GameTheory.Math.binaryPrefix b qy),
    color (GameTheory.Math.binaryPrefix b qx) (GameTheory.Math.binaryPrefix b qy + 1)]

/-- Correctly evaluated flags and clear extraction bound the actual ideal sample signal. -/
theorem sampleSignal_error_of_flags (c : BimatrixCertificate (k * 2) (k * 2))
    (color : ℕ → ℕ → Fin 3) (t : Fin 41) (qx qy δ : ℚ)
    (hqx0 : 0 ≤ qx) (hqx1 : qx ≤ 1) (hqy0 : 0 ≤ qy) (hqy1 : qy ≤ 1) (hδ0 : 0 ≤ δ)
    (hr : ∀ axis : Fin 2, |(k : ℚ) * BimatrixAffineGate.value c
      (sampleRef b raw₀.length raw₁.length t (remainder b axis b)) -
        GameTheory.Math.binaryRemainder b (if axis.val = 0 then qx else qy)| ≤
      46 * (2 : ℚ) ^ b * δ)
    (hflags : ∀ a : Fin 4, ∀ flag : Fin 2,
      let colorLength := if flag.val = 0 then raw₀.length else raw₁.length
      |(k : ℚ) * BimatrixAffineGate.value c (sampleRef b raw₀.length raw₁.length t
        (colorGate b raw₀.length raw₁.length a flag + (colorLength - 1))) -
        (if cornerColors b color qx qy a = (![1, 2] : Fin 2 → Fin 3) flag then 1 else 0)| ≤
          2 * δ) :
    |(sampleSignal b raw₀ raw₁ c t).1 -
      ((GameTheory.Math.Brouwer.globalGridMap color (2 ^ b)
        ((2 ^ b : ℕ) * (qx : ℝ), (2 ^ b : ℕ) * (qy : ℝ))).1 -
          (2 ^ b : ℕ) * (qx : ℝ))| ≤ (2000 * (2 : ℚ) ^ b * δ : ℚ) ∧
    |(sampleSignal b raw₀ raw₁ c t).2 -
      ((GameTheory.Math.Brouwer.globalGridMap color (2 ^ b)
        ((2 ^ b : ℕ) * (qx : ℝ), (2 ^ b : ℕ) * (qy : ℝ))).2 -
          (2 ^ b : ℕ) * (qy : ℝ))| ≤ (2000 * (2 : ℚ) ^ b * δ : ℚ) := by
  let uv (axis : Fin 2) : ℚ := max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
    (sampleRef b raw₀.length raw₁.length t (remainder b axis b))))
  have hb (axis : Fin 2) : 0 ≤ GameTheory.Math.binaryRemainder b
      (if axis.val = 0 then qx else qy) ∧ GameTheory.Math.binaryRemainder b
      (if axis.val = 0 then qx else qy) ≤ 1 := by
    split_ifs <;> exact GameTheory.Math.binaryRemainder_bounds (by assumption) (by assumption) b
  have he (axis : Fin 2) : |(uv axis : ℝ) -
      (GameTheory.Math.binaryRemainder b (if axis.val = 0 then qx else qy) : ℝ)| ≤
        ((46 * (2 : ℚ) ^ b * δ : ℚ) : ℝ) := by
    have h := GameTheory.Math.unitClamp_nonexpansive
      ((k : ℚ) * BimatrixAffineGate.value c
        (sampleRef b raw₀.length raw₁.length t (remainder b axis b)))
      (GameTheory.Math.binaryRemainder b (if axis.val = 0 then qx else qy))
    rw [GameTheory.Math.unitClamp_eq_self (hb axis).1 (hb axis).2] at h
    exact_mod_cast h.trans (hr axis)
  have hz (a : Fin 4) (flag : Fin 2) : |(sampleColor b raw₀ raw₁ c t a flag : ℝ) -
      (if cornerColors b color qx qy a = (![1, 2] : Fin 2 → Fin 3) flag then 1 else 0)| ≤
        ((2 * δ : ℚ) : ℝ) := by
    let bit : ℚ := if cornerColors b color qx qy a = (![1, 2] : Fin 2 → Fin 3) flag
      then 1 else 0
    have h := GameTheory.Math.unitClamp_nonexpansive
      ((k : ℚ) * BimatrixAffineGate.value c (sampleRef b raw₀.length raw₁.length t
        (colorGate b raw₀.length raw₁.length a flag +
          ((if flag.val = 0 then raw₀.length else raw₁.length) - 1)))) bit
    rw [GameTheory.Math.unitClamp_eq_self
      (show 0 ≤ bit by dsimp [bit]; split_ifs <;> norm_num)
      (show bit ≤ 1 by dsimp [bit]; split_ifs <;> norm_num)] at h
    have hh := h.trans (hflags a flag)
    have hq : |sampleColor b raw₀ raw₁ c t a flag - bit| ≤ 2 * δ := by
      simpa [sampleColor, Fin.val_eq_zero_iff] using hh
    have hR := (Rat.cast_le (K := ℝ)).mpr hq
    dsimp only [bit] at hR
    push_cast at hR
    by_cases hbit : cornerColors b color qx qy a = (![1, 2] : Fin 2 → Fin 3) flag
    · simpa only [hbit, ite_true, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat] using hR
    · simpa only [hbit, ite_false, Rat.cast_zero, Rat.cast_mul, Rat.cast_ofNat] using hR
  have hqx := GameTheory.Math.binaryRemainder_bounds hqx0 hqx1 b
  have hqy := GameTheory.Math.binaryRemainder_bounds hqy0 hqy1 b
  have he' := GameTheory.Math.Brouwer.clipped_color_signal_error
    (show (0 : ℝ) ≤ GameTheory.Math.binaryRemainder b qx by exact_mod_cast hqx.1)
    (show (GameTheory.Math.binaryRemainder b qx : ℝ) ≤ 1 by exact_mod_cast hqx.2)
    (show (0 : ℝ) ≤ GameTheory.Math.binaryRemainder b qy by exact_mod_cast hqy.1)
    (show (GameTheory.Math.binaryRemainder b qy : ℝ) ≤ 1 by exact_mod_cast hqy.2)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := b))
    (show (0 : ℝ) ≤ δ by exact_mod_cast hδ0)
    (by simpa using he 0) (by simpa using he 1) (cornerColors b color qx qy)
    (fun a => (sampleColor b raw₀ raw₁ c t a 0 : ℝ))
    (fun a => (sampleColor b raw₀ raw₁ c t a 1 : ℝ))
    (fun a => by convert hz a 0 using 1 <;> first | rfl | norm_num)
    (fun a => by convert hz a 1 using 1 <;> first | rfl | norm_num)
  have hex : ((2 ^ b : ℕ) : ℝ) * (qx : ℝ) =
      (GameTheory.Math.binaryPrefix b qx : ℝ) + (GameTheory.Math.binaryRemainder b qx : ℝ) := by
    exact_mod_cast GameTheory.Math.binary_decomposition b qx
  have hey : ((2 ^ b : ℕ) : ℝ) * (qy : ℝ) =
      (GameTheory.Math.binaryPrefix b qy : ℝ) + (GameTheory.Math.binaryRemainder b qy : ℝ) := by
    exact_mod_cast GameTheory.Math.binary_decomposition b qy
  rw [hex, hey, GameTheory.Math.Brouwer.globalGridMap_fourCorners_fst_sub color
    (GameTheory.Math.binaryPrefix_lt b qx) (GameTheory.Math.binaryPrefix_lt b qy)
    (by exact_mod_cast hqx.1) (by exact_mod_cast hqx.2)
    (by exact_mod_cast hqy.1) (by exact_mod_cast hqy.2),
    GameTheory.Math.Brouwer.globalGridMap_fourCorners_snd_sub color
    (GameTheory.Math.binaryPrefix_lt b qx) (GameTheory.Math.binaryPrefix_lt b qy)
    (by exact_mod_cast hqx.1) (by exact_mod_cast hqx.2)
    (by exact_mod_cast hqy.1) (by exact_mod_cast hqy.2)]
  simpa [sampleSignal, sampleWeights, GameTheory.Math.Brouwer.fourCornerWeights_rat_cast,
    uv, cornerColors, Fin.sum_univ_succ] using he'

/-- Each answer coordinate is the unit-clipped value of its actual cyclic output wire. -/
def coordinateValue (c : BimatrixCertificate (k * 2) (k * 2)) (axis : Fin 2) : ℚ :=
  max 0 (min 1 ((k : ℚ) * BimatrixAffineGate.value c
    (slot b raw₀.length raw₁.length (coordinate axis))))

/-- The exact source query point uses the canonical centered clipped jitter progression. -/
def samplePoint (c : BimatrixCertificate (k * 2) (k * 2)) (t : Fin 41) : ℚ × ℚ :=
  (GameTheory.Math.gridJitterSample (coordinateValue b raw₀ raw₁ c 0)
      (1 / 2 ^ precision b) 20 t,
    GameTheory.Math.gridJitterSample (coordinateValue b raw₀ raw₁ c 1)
      (1 / 2 ^ precision b) 20 t)

private theorem zero_error (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H) :
    |(k : ℚ) * BimatrixAffineGate.value c (slot b raw₀.length raw₁.length zero)| ≤
      (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) := by
  have hplace := program_global b raw₀ raw₁ zero
    (by simp only [zero, globalCount]; omega)
  rw [globalGate_zero] at hplace
  have hC : 0 < 2 * (k : ℤ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) (dimension_pos _ _ _)
  have he := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) (100 * (k : ℤ))
    (fun _ => 0) 0 g c hc hC (by positivity) (coefficients_bound b raw₀ raw₁)
    hscale _ hplace
  simpa using he

/-- Clear samples evaluate their actual relocated raw color circuits at the exact corners. -/
theorem clear_sample_color_error (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ β : ℚ) (hδ0 : 0 ≤ δ) (hsmall : 2 * δ < 1 / 4)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hbudget : 50 * δ ≤ β) (color : ℕ → ℕ → Fin 3) (t : Fin 41)
    (hgrid : ∀ l : ℕ, 0 < l → l < 2 ^ b →
      β < |(samplePoint b raw₀ raw₁ c t).1 - (l : ℚ) / (2 : ℚ) ^ b| ∧
      β < |(samplePoint b raw₀ raw₁ c t).2 - (l : ℚ) / (2 : ℚ) ^ b|)
    (hraw : ∀ flag : Fin 2, (if flag.val = 0 then raw₀ else raw₁).WellFormed (arity b))
    (hquery : ∀ a : Fin 4, ∀ flag : Fin 2,
      (if flag.val = 0 then raw₀ else raw₁).eval?
        (BrouwerNashColor.cornerVertex b (samplePoint b raw₀ raw₁ c t).1
          (samplePoint b raw₀ raw₁ c t).2 a) =
      some (decide (cornerColors b color (samplePoint b raw₀ raw₁ c t).1
        (samplePoint b raw₀ raw₁ c t).2 a = (![1, 2] : Fin 2 → Fin 3) flag))) :
    ∀ a : Fin 4, ∀ flag : Fin 2,
      let colorLength := if flag.val = 0 then raw₀.length else raw₁.length
      |(k : ℚ) * BimatrixAffineGate.value c (sampleRef b raw₀.length raw₁.length t
        (colorGate b raw₀.length raw₁.length a flag + (colorLength - 1))) -
        (if cornerColors b color (samplePoint b raw₀ raw₁ c t).1
          (samplePoint b raw₀ raw₁ c t).2 a = (![1, 2] : Fin 2 → Fin 3) flag then 1 else 0)| ≤
          2 * δ := by
  have hone := (BimatrixBrouwerGateBounds.one_error H (100 * (k : ℤ))
    (dimension_pos _ _ _) g c hc (by positivity) (coefficients_bound b raw₀ raw₁)
    hscale _ (one_placement b raw₀ raw₁)).trans hδ
  have hzero := (zero_error b raw₀ raw₁ H c hc hscale).trans hδ
  have hdigit (axis : Fin 2) (j : ℕ) (hj : j < b) :
      |(k : ℚ) * BimatrixAffineGate.value c
        (sampleRef b raw₀.length raw₁.length t (digit b axis j)) -
        (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j
          (if axis.val = 0 then (samplePoint b raw₀ raw₁ c t).1
            else (samplePoint b raw₀ raw₁ c t).2)) then 1 else 0)| ≤ δ := by
    have hclear : ∀ l : ℕ, 0 < l → l < 2 ^ b → β <
        |GameTheory.Math.gridJitterSample (coordinateValue b raw₀ raw₁ c axis)
          (1 / 2 ^ precision b) 20 t - (l : ℚ) / (2 : ℚ) ^ b| := by
      fin_cases axis
      · exact fun l hl hln => (hgrid l hl hln).1
      · exact fun l hl hln => (hgrid l hl hln).2
    have he := (clear_sample_extraction b raw₀ raw₁ H c hc hscale δ β hδ0 hδ
      hbudget t axis hclear).2 j hj
    fin_cases axis <;> exact he
  intro a flag
  have he := BrouwerNashColor.colorOutput_error_of_digits b raw₀ raw₁ H (100 * (k : ℤ)) c hc
    (by positivity) (coefficients_bound b raw₀ raw₁) hscale δ hsmall hδ t a
    (samplePoint b raw₀ raw₁ c t).1 (samplePoint b raw₀ raw₁ c t).2 hone hzero hdigit
    flag _ (hraw flag) (hquery a flag)
  simp only [decide_eq_true_eq] at he
  fin_cases flag <;> exact he

/-- Every accepted actual program certificate has a small canonical source-map residual. -/
theorem canonical_residual (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ : ℚ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hprecision : δ ≤ 1 / (2 : ℚ) ^ (100 * (b + k + 10)))
    (color : ℕ → ℕ → Fin 3) (hboundary : GameTheory.Math.Sperner.GridBoundary color (2 ^ b))
    (hraw : ∀ flag : Fin 2, (if flag.val = 0 then raw₀ else raw₁).WellFormed (arity b))
    (hquery : ∀ qx qy : ℚ, ∀ a : Fin 4, ∀ flag : Fin 2,
      (if flag.val = 0 then raw₀ else raw₁).eval? (BrouwerNashColor.cornerVertex b qx qy a) =
        some (decide (cornerColors b color qx qy a = (![1, 2] : Fin 2 → Fin 3) flag))) :
    let x := coordinateValue b raw₀ raw₁ c 0
    let y := coordinateValue b raw₀ raw₁ c 1
    |(GameTheory.Math.Brouwer.globalGridMap color (2 ^ b)
      ((2 ^ b : ℕ) * (x : ℝ), (2 ^ b : ℕ) * (y : ℝ))).1 - (2 ^ b : ℕ) * (x : ℝ)| ≤ 1 / 6 ∧
    |(GameTheory.Math.Brouwer.globalGridMap color (2 ^ b)
      ((2 ^ b : ℕ) * (x : ℝ), (2 ^ b : ℕ) * (y : ℝ))).2 - (2 ^ b : ℕ) * (y : ℝ)| ≤ 1 / 6 := by
  have hH : (0 : ℤ) < H := lt_of_le_of_lt (by positivity) hscale
  have hHq : (0 : ℚ) < H := by exact_mod_cast hH
  have hδ0 : 0 ≤ δ := (by positivity :
    0 ≤ (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H)).trans hδ
  let x := coordinateValue b raw₀ raw₁ c 0
  let y := coordinateValue b raw₀ raw₁ c 1
  let α : ℚ := 1 / 2 ^ precision b
  let β : ℚ := α / 4
  let ε : ℝ := ((2000 * (2 : ℚ) ^ b * δ : ℚ) : ℝ)
  let θ : ℝ := ((α / 3 : ℚ) : ℝ)
  let ρ : ℝ := ((100 * δ : ℚ) : ℝ)
  have hx0 : 0 ≤ x := le_max_left _ _
  have hx1 : x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hy0 : 0 ≤ y := le_max_left _ _
  have hy1 : y ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hk : 1 ≤ k := (dimension_pos _ _ _)
  have hbud := GameTheory.Math.gridBrouwer_dyadic_error_budget b k hk δ hδ0 hprecision
  have hjit := GameTheory.Math.gridJitter_fortyOne_dyadic_bounds b
  change 0 < α ∧ 0 ≤ β ∧ 2 * β < α ∧
    40 * α + 2 * β < 1 / (2 : ℚ) ^ b ∧
    2 * (2 : ℚ) ^ b * ((2 : ℚ) ^ b + 1) ^ 2 * (20 * α) ≤ 1 / 1024 at hjit
  obtain ⟨bad, hbad, hclear⟩ := GameTheory.Math.exists_gridJitter_pair_clearance
    (m := 41) (N := 2 ^ b) x y α 20 β (by decide) (by positivity)
    hjit.2.1 hjit.2.2.1 (by exact_mod_cast hjit.2.2.2.1)
  have hp4 : (16 : ℚ) ≤ 2 ^ (100 * (b + k + 10)) := by
    exact (show (16 : ℚ) ≤ 2 ^ (4 : ℕ) by norm_num).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hsmall : 2 * δ < 1 / 4 := by
    have he := hprecision.trans (one_div_le_one_div_of_le (by norm_num) hp4)
    linarith only [he]
  have hδR : (0 : ℝ) ≤ δ := by exact_mod_cast hδ0
  have hgood (t : Fin 41) (ht : t ∉ bad) := by
    have hgrid : ∀ l : ℕ, 0 < l → l < 2 ^ b →
        β < |(samplePoint b raw₀ raw₁ c t).1 - (l : ℚ) / (2 : ℚ) ^ b| ∧
        β < |(samplePoint b raw₀ raw₁ c t).2 - (l : ℚ) / (2 : ℚ) ^ b| := by
      intro l hl hln
      exact_mod_cast hclear t ht l hl hln
    have hflags := clear_sample_color_error b raw₀ raw₁ H c hc hscale δ β hδ0 hsmall hδ
      hbud.1 color t hgrid hraw (hquery _ _)
    have hr (axis : Fin 2) : |(k : ℚ) * BimatrixAffineGate.value c
        (sampleRef b raw₀.length raw₁.length t (remainder b axis b)) -
          GameTheory.Math.binaryRemainder b
            (if axis.val = 0 then (samplePoint b raw₀ raw₁ c t).1
              else (samplePoint b raw₀ raw₁ c t).2)| ≤ 46 * (2 : ℚ) ^ b * δ := by
      have hgrid' : ∀ l : ℕ, 0 < l → l < 2 ^ b → β <
          |GameTheory.Math.gridJitterSample (coordinateValue b raw₀ raw₁ c axis)
            α 20 t - (l : ℚ) / (2 : ℚ) ^ b| := by
        fin_cases axis
        · exact fun l hl hln => (hgrid l hl hln).1
        · exact fun l hl hln => (hgrid l hl hln).2
      have he := (clear_sample_extraction b raw₀ raw₁ H c hc hscale δ β hδ0 hδ
        hbud.1 t axis hgrid').1 b le_rfl
      fin_cases axis <;> exact he
    exact sampleSignal_error_of_flags b raw₀ raw₁ c color t
      (samplePoint b raw₀ raw₁ c t).1 (samplePoint b raw₀ raw₁ c t).2 δ
      (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _))
      (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _)) hδ0 hr hflags
  have hcenter := GameTheory.Math.Brouwer.globalGridMap_dyadic_displacement_abs_le_one
    color b x y hx0 hx1 hy0 hy1
  have hbaderr (t : Fin 41) (_ht : t ∈ bad) :
      |(sampleSignal b raw₀ raw₁ c t).1 -
        ((GameTheory.Math.Brouwer.globalGridMap color (2 ^ b)
          ((2 ^ b : ℕ) * (x : ℝ), (2 ^ b : ℕ) * (y : ℝ))).1 -
            (2 ^ b : ℕ) * (x : ℝ))| ≤ 25 / 8 ∧
      |(sampleSignal b raw₀ raw₁ c t).2 -
        ((GameTheory.Math.Brouwer.globalGridMap color (2 ^ b)
          ((2 ^ b : ℕ) * (x : ℝ), (2 ^ b : ℕ) * (y : ℝ))).2 -
            (2 ^ b : ℕ) * (y : ℝ))| ≤ 25 / 8 := by
    have hs := sampleSignal_abs_le_two b raw₀ raw₁ c t
    constructor
    · exact (abs_sub _ _).trans ((add_le_add hs.1 hcenter.1).trans (by norm_num))
    · exact (abs_sub _ _).trans ((add_le_add hs.2 hcenter.2).trans (by norm_num))
  have hfeed (axis : Fin 2) := feedback_signal_error b raw₀ raw₁ H c hc hscale δ hδ0 hδ axis
  have hfeedbudget : ((12 * δ : ℚ) : ℝ) ≤ ρ := by
    dsimp only [ρ]
    exact_mod_cast (show 12 * δ ≤ 100 * δ by linarith only [hδ0])
  have hε : ε ≤ 1 / 1024 := by
    dsimp only [ε]
    have he := (Rat.cast_le (K := ℝ)).mpr hbud.2.1
    convert he using 1; push_cast; rfl
  have hvariation : 2 * ((2 ^ b : ℕ) : ℝ) * ((2 ^ b : ℕ) + 1) ^ 2 *
      (20 * (α : ℝ)) ≤ 1 / 1024 := by
    push_cast
    have he := (Rat.cast_le (K := ℝ)).mpr hjit.2.2.2.2
    convert he using 1 <;> push_cast <;> rfl
  have hround : ρ / θ + 2 * ((2 ^ b : ℕ) : ℝ) * ((2 ^ b : ℕ) + 1) ^ 2 * ρ ≤
      1 / 512 := by
    dsimp only [ρ, θ, α, precision]
    push_cast
    have he := (Rat.cast_le (K := ℝ)).mpr hbud.2.2
    convert he using 1 <;> push_cast <;> rfl
  apply GameTheory.Math.Brouwer.gridJitter_feedback_residual hboundary (by positivity)
    x y α hx0 hx1 hy0 hy1 hjit.1.le bad hbad
    (fun t => (sampleSignal b raw₀ raw₁ c t).1)
    (fun t => (sampleSignal b raw₀ raw₁ c t).2) ε θ ρ
    (by dsimp [ε]; positivity) (by dsimp [θ]; exact_mod_cast (div_pos hjit.1 (by norm_num)))
    hgood hbaderr _ (by linarith only [hε, hvariation]) hround
  exact ⟨(hfeed 0).trans hfeedbudget, (hfeed 1).trans hfeedbudget⟩

private theorem encoded_color_bit (color : Fin 3) (flag : Fin 2) :
    _root_.Complexity.bitOf (encodeGridColor color) flag =
      decide (color = (![1, 2] : Fin 2 → Fin 3) flag) := by
  fin_cases flag <;> rfl

/-- Compiled source-color queries specialize the residual theorem to the source coloring. -/
theorem source_residual (source : List Bool)
    (hb : (_root_.Complexity.pairFst source).length = b)
    (H : ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H (2 * (k : ℤ)))
      (columnPayoff H (2 * (k : ℤ)) g))
    (hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H)
    (δ : ℚ)
    (hδ : (k : ℚ) * (((100 * (k : ℤ) + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hprecision : δ ≤ 1 / (2 : ℚ) ^ (100 * (b + k + 10)))
    (hraw : ∀ flag : Fin 2, (if flag.val = 0 then raw₀ else raw₁).WellFormed (arity b))
    (hquery : ∀ flag : Fin 2, ∀ x y : ℕ, x ≤ 2 ^ b → y ≤ 2 ^ b →
      (if flag.val = 0 then raw₀ else raw₁).eval?
        (Nat.toBitsLE (b + 1) x ++ Nat.toBitsLE (b + 1) y) =
          some (_root_.Complexity.bitOf (encodeGridColor (spernerColor source x y)) flag)) :
    let x := coordinateValue b raw₀ raw₁ c 0
    let y := coordinateValue b raw₀ raw₁ c 1
    |(GameTheory.Math.Brouwer.globalGridMap (spernerColor source) (2 ^ b)
      ((2 ^ b : ℕ) * (x : ℝ), (2 ^ b : ℕ) * (y : ℝ))).1 - (2 ^ b : ℕ) * (x : ℝ)| ≤ 1 / 6 ∧
    |(GameTheory.Math.Brouwer.globalGridMap (spernerColor source) (2 ^ b)
      ((2 ^ b : ℕ) * (x : ℝ), (2 ^ b : ℕ) * (y : ℝ))).2 - (2 ^ b : ℕ) * (y : ℝ)| ≤ 1 / 6 := by
  have hboundary : GameTheory.Math.Sperner.GridBoundary (spernerColor source) (2 ^ b) := by
    rw [← hb]
    exact GameTheory.Math.Sperner.standardGridColor_boundary _ _ (Nat.two_pow_pos _)
  apply canonical_residual b raw₀ raw₁ H c hc hscale δ hδ hprecision
    (spernerColor source) hboundary hraw
  intro qx qy a flag
  have he := BrouwerNashColor.cornerVertex_eval source
    (if flag.val = 0 then raw₀ else raw₁) flag
    (by simpa only [hb] using hquery flag) qx qy a
  rw [hb, encoded_color_bit] at he
  exact he

/-- The reward schedule makes every accepted source program answer a small-residual point. -/
theorem reward_source_residual (source : List Bool)
    (hb : (_root_.Complexity.pairFst source).length = b)
    (rulers : Fin 2 → List Bool) (hdepth : (rulers 0).length = b)
    (hsize : (rulers 1).length = k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid
      (BimatrixAffineGate.rowPayoff (binarySignedValue (BrouwerNashRewardMachine.reward rulers))
        (2 * (k : ℤ)))
      (columnPayoff (binarySignedValue (BrouwerNashRewardMachine.reward rulers))
        (2 * (k : ℤ)) g))
    (hraw : ∀ flag : Fin 2, (if flag.val = 0 then raw₀ else raw₁).WellFormed (arity b))
    (hquery : ∀ flag : Fin 2, ∀ x y : ℕ, x ≤ 2 ^ b → y ≤ 2 ^ b →
      (if flag.val = 0 then raw₀ else raw₁).eval?
        (Nat.toBitsLE (b + 1) x ++ Nat.toBitsLE (b + 1) y) =
          some (_root_.Complexity.bitOf (encodeGridColor (spernerColor source x y)) flag)) :
    let x := coordinateValue b raw₀ raw₁ c 0
    let y := coordinateValue b raw₀ raw₁ c 1
    |(GameTheory.Math.Brouwer.globalGridMap (spernerColor source) (2 ^ b)
      ((2 ^ b : ℕ) * (x : ℝ), (2 ^ b : ℕ) * (y : ℝ))).1 - (2 ^ b : ℕ) * (x : ℝ)| ≤ 1 / 6 ∧
    |(GameTheory.Math.Brouwer.globalGridMap (spernerColor source) (2 ^ b)
      ((2 ^ b : ℕ) * (x : ℝ), (2 ^ b : ℕ) * (y : ℝ))).2 - (2 ^ b : ℕ) * (y : ℝ)| ≤ 1 / 6 := by
  let H := binarySignedValue (BrouwerNashRewardMachine.reward rulers)
  let δ : ℚ := (k : ℚ) * (102 * k) / (H : ℚ)
  have hscale : (k : ℤ) * (100 * (k : ℤ) + 2 * (k : ℤ)) < H := by
    simpa only [hsize] using BrouwerNashRewardMachine.reward_dominates rulers
  have hk : 1 ≤ (rulers 1).length := by
    rw [hsize]
    exact dimension_pos b raw₀.length raw₁.length
  have hbud := BrouwerNashRewardMachine.reward_error_bound rulers hk
  rw [hdepth, hsize] at hbud
  apply source_residual b raw₀ raw₁ source hb H c hc hscale δ _ hbud.2 hraw hquery
  dsimp only [δ]
  push_cast
  ring_nf
  exact le_rfl

end
end GameTheory.Complexity.Backend.BrouwerNashProgramCorrectness
