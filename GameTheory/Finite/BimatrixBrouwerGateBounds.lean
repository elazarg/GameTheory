import GameTheory.Finite.BimatrixDyadicGate
import GameTheory.Finite.BimatrixFeedbackGate
import GameTheory.Finite.BimatrixColorMeanGate
import GameTheory.Finite.BimatrixBinaryExtraction
import GameTheory.Finite.BimatrixInterpolationGate
import GameTheory.Finite.BimatrixGateProgramBounds
import GameTheory.Math.GridJitter

/-!
# Error propagation through jittered grid-evaluation gates

Actual accepted certificates supply the equations for constant, halving, extraction,
interpolation and feedback blocks. These bounds compose those equations while retaining the
canonical gate semantics. Clear samples follow the exact binary recurrence; interpolation
uses clipped actual remainders even at samples where extraction is unreliable.
-/

namespace GameTheory.Finite.BimatrixBrouwerGateBounds
open BimatrixAffineGate BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

private theorem jitter_signal (hk : 0 < k)
    (c : BimatrixCertificate (k * 2) (k * 2)) (q alpha : Fin k) (t : Fin 41) :
    (∑ j, (((if j = q then 2 * (k : ℤ) else 0) +
      (if j = alpha then 2 * (k : ℤ) * ((t.val : ℤ) - 20) else 0) : ℤ) : ℚ) /
      ((2 * (k : ℤ) : ℤ) : ℚ) * ((k : ℚ) * value c j)) +
      (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      (k : ℚ) * value c q + ((t.val : ℚ) - 20) * ((k : ℚ) * value c alpha) := by
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  simp only [add_div, add_mul, Finset.sum_add_distrib, ite_div, zero_div,
    ite_mul, zero_mul, mul_zero, add_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp

/-- A dyadic input approximation controls the actual clipped affine jitter block. -/
theorem jitter_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (q alpha out : Fin k) (t : Fin 41)
    (hout : g out = BimatrixArithmeticGate.gate (fun j =>
      (if j = q then 2 * (k : ℤ) else 0) +
      (if j = alpha then 2 * (k : ℤ) * ((t.val : ℤ) - 20) else 0)) 0)
    (T : ℕ) (hT : 5 ≤ T) (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (halpha : |(k : ℚ) * value c alpha - 1 / (2 : ℚ) ^ T| ≤
      2 * δ + δ / 2 ^ T) :
    |(k : ℚ) * value c out - GameTheory.Math.gridJitterSample
      (max 0 (min 1 ((k : ℚ) * value c q))) (1 / 2 ^ T) 20 t| ≤ 43 * δ := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have ha := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (fun j => (if j = q then 2 * (k : ℤ) else 0) +
      (if j = alpha then 2 * (k : ℤ) * ((t.val : ℤ) - 20) else 0)) 0
    g c hc hC hM hg hscale out hout
  rw [jitter_signal hk c q alpha t] at ha
  have hq := (BimatrixGateProgramBounds.normalized_value_clipping_error H
    (2 * (k : ℤ)) M g c hc hC.le hM hg hscale q).trans hδ
  have hp : (20 : ℚ) ≤ 2 ^ T := by
    exact (show (20 : ℚ) ≤ 2 ^ (5 : ℕ) by norm_num).trans
      (pow_le_pow_right₀ (by norm_num) hT)
  have hsmall : δ / 2 ^ T ≤ δ / 20 := div_le_div_of_nonneg_left hδ0 (by norm_num) hp
  have ht0 : (0 : ℚ) ≤ t.val := Nat.cast_nonneg _
  have ht40 : (t.val : ℚ) ≤ 40 := by exact_mod_cast (show t.val ≤ 40 by omega)
  have ht : |(t.val : ℚ) - 20| ≤ 20 := by rw [abs_le]; constructor <;> linarith
  have hab : |((t.val : ℚ) - 20) *
      ((k : ℚ) * value c alpha - 1 / 2 ^ T)| ≤ 41 * δ := by
    rw [abs_mul]
    have hprod := mul_le_mul ht halpha (abs_nonneg _) (by norm_num : (0 : ℚ) ≤ 20)
    nlinarith only [hprod, hsmall]
  have herr : |((k : ℚ) * value c q + ((t.val : ℚ) - 20) *
      ((k : ℚ) * value c alpha)) - (max 0 (min 1 ((k : ℚ) * value c q)) +
        ((t.val : ℚ) - 20) * (1 / 2 ^ T))| ≤ 42 * δ := by
    have hid : ((k : ℚ) * value c q + ((t.val : ℚ) - 20) *
        ((k : ℚ) * value c alpha)) - (max 0 (min 1 ((k : ℚ) * value c q)) +
          ((t.val : ℚ) - 20) * (1 / 2 ^ T)) =
        ((k : ℚ) * value c q - max 0 (min 1 ((k : ℚ) * value c q))) +
          ((t.val : ℚ) - 20) * ((k : ℚ) * value c alpha - 1 / 2 ^ T) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans ((add_le_add hq hab).trans_eq (by ring))
  have hcl := GameTheory.Math.unitClamp_nonexpansive
    ((k : ℚ) * value c q + ((t.val : ℚ) - 20) * ((k : ℚ) * value c alpha))
    (max 0 (min 1 ((k : ℚ) * value c q)) + ((t.val : ℚ) - 20) * (1 / 2 ^ T))
  change |_ - max 0 (min 1 _)| ≤ _
  exact (abs_sub_le _ _ _).trans ((add_le_add (ha.trans hδ) (hcl.trans herr)).trans_eq
    (by ring))

/-- A canonical constant-one block has normalized error bounded by the game budget. -/
theorem one_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (one : Fin k)
    (hone : g one = BimatrixArithmeticGate.gate (fun _ => 0) 2) :
    |(k : ℚ) * value c one - 1| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have ha := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (fun _ => 0) 2 g c hc hC hM hg hscale one hone
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hs : (∑ _j : Fin k, ((0 : ℤ) : ℚ) / ((2 * (k : ℤ) : ℤ) : ℚ) *
      ((k : ℚ) * value c _j)) + (k : ℚ) * (2 : ℤ) /
      ((2 * (k : ℤ) : ℤ) : ℚ) = 1 := by
    simp only [Int.cast_zero, zero_div, zero_mul, Finset.sum_const_zero, zero_add]
    push_cast
    field_simp
  rw [hs] at ha
  simpa only [min_self, max_eq_right (by norm_num : (0 : ℚ) ≤ 1)] using ha

/-- Actual constant and halving blocks discharge the dyadic-input premise of jitter. -/
theorem jitter_error_of_halving_chain (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (q out : Fin k) (t : Fin 41)
    (r : ℕ → Fin k) (T : ℕ) (hT : 5 ≤ T)
    (hone : g (r 0) = BimatrixArithmeticGate.gate (fun _ => 0) 2)
    (hchain : ∀ j < T, g (r (j + 1)) = BimatrixDyadicGate.halvingGate (r j))
    (hout : g out = BimatrixArithmeticGate.gate (fun j =>
      (if j = q then 2 * (k : ℤ) else 0) +
      (if j = r T then 2 * (k : ℤ) * ((t.val : ℤ) - 20) else 0)) 0)
    (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ) :
    |(k : ℚ) * value c out - GameTheory.Math.gridJitterSample
      (max 0 (min 1 ((k : ℚ) * value c q))) (1 / 2 ^ T) 20 t| ≤ 43 * δ := by
  have hone' := (one_error H M hk g c hc hM hg hscale (r 0) hone).trans hδ
  have halpha := BimatrixDyadicGate.halving_chain_error H M hk g c hc hM hg hscale
    r T 1 δ δ (by norm_num) (by norm_num) hδ0 hδ hchain hone' T le_rfl
  exact jitter_error H M hk g c hc hM hg hscale q (r T) out t hout T hT δ hδ0 hδ halpha

/-- A clear jitter sample follows the exact binary recurrence and emits correct digits. -/
theorem jitter_extraction_errors (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (q : Fin k) (t : Fin 41)
    (alpha r digits : ℕ → Fin k) (T b : ℕ) (hT : 5 ≤ T)
    (hone : g (alpha 0) = BimatrixArithmeticGate.gate (fun _ => 0) 2)
    (hchain : ∀ j < T, g (alpha (j + 1)) = BimatrixDyadicGate.halvingGate (alpha j))
    (hjitter : g (r 0) = BimatrixArithmeticGate.gate (fun j =>
      (if j = q then 2 * (k : ℤ) else 0) +
      (if j = alpha T then 2 * (k : ℤ) * ((t.val : ℤ) - 20) else 0)) 0)
    (hdigit : ∀ j < b, g (digits j) = BimatrixBinaryExtraction.digitGate (r j))
    (hnext : ∀ j < b, g (r (j + 1)) = BimatrixBinaryExtraction.remainderGate (r j) (digits j))
    (δ β : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hbudget : 50 * δ ≤ β)
    (hgrid : ∀ l : ℕ, 0 < l → l < 2 ^ b → β <
      |GameTheory.Math.gridJitterSample (max 0 (min 1 ((k : ℚ) * value c q)))
        (1 / 2 ^ T) 20 t - (l : ℚ) / (2 : ℚ) ^ b|) :
    let sample := GameTheory.Math.gridJitterSample (max 0 (min 1 ((k : ℚ) * value c q)))
      (1 / 2 ^ T) 20 t
    (∀ j ≤ b, |(k : ℚ) * value c (r j) - GameTheory.Math.binaryRemainder j sample| ≤
      46 * (2 : ℚ) ^ j * δ) ∧
    (∀ j < b, |(k : ℚ) * value c (digits j) -
      (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j sample)
        then 1 else 0)| ≤ δ) := by
  dsimp only
  have hinit := jitter_error_of_halving_chain H M hk g c hc hM hg hscale q (r 0) t
    alpha T hT hone hchain hjitter δ hδ0 hδ
  have hs0 : 0 ≤ GameTheory.Math.gridJitterSample
      (max 0 (min 1 ((k : ℚ) * value c q))) (1 / 2 ^ T) 20 t := le_max_left _ _
  have hs1 : GameTheory.Math.gridJitterSample
      (max 0 (min 1 ((k : ℚ) * value c q))) (1 / 2 ^ T) 20 t ≤ 1 :=
    max_le (by norm_num) (min_le_left _ _)
  have he := BimatrixBinaryExtraction.trajectory_errors_of_grid_clearance H M hk g c hc
    hM hg hscale r digits b _ (43 * δ) δ β hs0 hs1 hδ0 hδ hdigit hnext hinit
    (by linarith only [hbudget, hδ0]) hgrid
  refine ⟨?_, he.2⟩
  intro j hj
  have hpδ : 0 ≤ (2 : ℚ) ^ j * δ := mul_nonneg (by positivity) hδ0
  have h := he.1 j hj
  nlinarith only [h, hδ0, hpδ]

/-- Clipping the actual remainders gives uniformly accurate convex interpolation weights. -/
theorem clipped_interpolation_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (iu iv cu cv t00 w00 t11 w11 w10 w01 : Fin k)
    (hcu : g cu = BimatrixInterpolationGate.complementGate iu)
    (hcv : g cv = BimatrixInterpolationGate.complementGate iv)
    (ht00 : g t00 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) cu cv)
    (hw00 : g w00 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) cu t00)
    (ht11 : g t11 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iu iv)
    (hw11 : g w11 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iu t11)
    (hw10 : g w10 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iu iv)
    (hw01 : g w01 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iv iu)
    (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ) :
    let u := max 0 (min 1 ((k : ℚ) * value c iu))
    let v := max 0 (min 1 ((k : ℚ) * value c iv))
    ∀ i : Fin 4, |(((k : ℚ) * value c (![w00, w11, w10, w01] i) : ℚ) : ℝ) -
      GameTheory.Math.Brouwer.fourCornerWeights (u : ℝ) (v : ℝ) i| ≤ ((8 * δ : ℚ) : ℝ) := by
  dsimp only
  have hC : 0 ≤ 2 * (k : ℤ) := by positivity
  have hu := (BimatrixGateProgramBounds.normalized_value_clipping_error H
    (2 * (k : ℤ)) M g c hc hC hM hg hscale iu).trans hδ
  have hv := (BimatrixGateProgramBounds.normalized_value_clipping_error H
    (2 * (k : ℤ)) M g c hc hC hM hg hscale iv).trans hδ
  have he := BimatrixInterpolationGate.fourCornerWeights_error H M hk g c hc hM hg hscale
    iu iv cu cv t00 w00 t11 w11 w10 w01 hcu hcv ht00 hw00 ht11 hw11 hw10 hw01
    (max 0 (min 1 ((k : ℚ) * value c iu))) (max 0 (min 1 ((k : ℚ) * value c iv))) δ δ
    (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _))
    (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _)) hδ0 hδ hu hv
  simpa only [show 5 * δ + 3 * δ = 8 * δ by ring] using he

/-- Two actual minimum blocks use clipped color wires without any exclusivity assumption. -/
theorem clipped_color_min_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (iw iz it out : Fin k)
    (ht : g it = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iw iz)
    (hout : g out = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iw it)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (δ : ℚ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hw : |(((k : ℚ) * value c iw : ℚ) : ℝ) - w| ≤ ((8 * δ : ℚ) : ℝ)) :
    |(((k : ℚ) * value c out : ℚ) : ℝ) -
      min w (((max 0 (min 1 ((k : ℚ) * value c iz)) : ℚ) : ℝ))| ≤
        ((19 * δ : ℚ) : ℝ) := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have ht' := (BimatrixMinGate.subtraction_error H (2 * (k : ℤ)) M g c hc
    hC hM hg hscale iw iz it ht).trans hδ
  have ho' := (BimatrixMinGate.subtraction_error H (2 * (k : ℤ)) M g c hc
    hC hM hg hscale iw it out hout).trans hδ
  have hz := (BimatrixGateProgramBounds.normalized_value_clipping_error H
    (2 * (k : ℤ)) M g c hc hC.le hM hg hscale iz).trans hδ
  have hz' : |(((k : ℚ) * value c iz : ℚ) : ℝ) -
      (((max 0 (min 1 ((k : ℚ) * value c iz)) : ℚ) : ℝ))| ≤ (δ : ℝ) := by
    exact_mod_cast hz
  have htR : |(((k : ℚ) * value c it : ℚ) : ℝ) - max 0 (min 1
      ((((k : ℚ) * value c iw : ℚ) : ℝ) - (((k : ℚ) * value c iz : ℚ) : ℝ)))| ≤
      (δ : ℝ) := by exact_mod_cast ht'
  have hoR : |(((k : ℚ) * value c out : ℚ) : ℝ) - max 0 (min 1
      ((((k : ℚ) * value c iw : ℚ) : ℝ) - (((k : ℚ) * value c it : ℚ) : ℝ)))| ≤
      (δ : ℝ) := by exact_mod_cast ho'
  have z0 : (0 : ℝ) ≤ (((max 0 (min 1 ((k : ℚ) * value c iz)) : ℚ) : ℝ)) := by
    exact_mod_cast (le_max_left (0 : ℚ) (min 1 ((k : ℚ) * value c iz)))
  have z1 : (((max 0 (min 1 ((k : ℚ) * value c iz)) : ℚ) : ℝ)) ≤ 1 := by
    exact_mod_cast (max_le (by norm_num : (0 : ℚ) ≤ 1)
      (min_le_left (1 : ℚ) ((k : ℚ) * value c iz)))
  have he := GameTheory.Math.clippedSub_min_error w
    (((max 0 (min 1 ((k : ℚ) * value c iz)) : ℚ) : ℝ))
    (((k : ℚ) * value c iw : ℚ) : ℝ) (((k : ℚ) * value c iz : ℚ) : ℝ)
    (((k : ℚ) * value c it : ℚ) : ℝ) (((k : ℚ) * value c out : ℚ) : ℝ)
    ((8 * δ : ℚ) : ℝ) (δ : ℝ) (δ : ℝ) hw0 hw1 z0 z1 hw hz' htR hoR
  push_cast at he ⊢
  linarith only [he]

private theorem third_scale_signal (u : ℕ) (hu : 0 < u) (hk : k = 123 * u)
    (c : BimatrixCertificate (k * 2) (k * 2)) (alpha : Fin k) :
    (∑ j, (((if j = alpha then 82 * (u : ℤ) else 0) : ℤ) : ℚ) /
      ((2 * (k : ℤ) : ℤ) : ℚ) * ((k : ℚ) * value c j)) +
      (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      ((k : ℚ) * value c alpha) / 3 := by
  have huq : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu.ne'
  push_cast
  simp only [ite_div, zero_div, ite_mul, zero_mul, mul_zero, add_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hkq : (k : ℚ) = 123 * (u : ℚ) := by exact_mod_cast hk
  rw [hkq]
  field_simp
  ring

/-- Integer third-scaling converts a dyadic one chain into positive feedback. -/
theorem positive_scale_error (H M : ℤ) (u : ℕ) (hu : 0 < u) (hk : k = 123 * u)
    (g : Fin k → Gate k) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (alpha out : Fin k)
    (hout : g out = BimatrixArithmeticGate.gate
      (fun j => if j = alpha then 82 * (u : ℤ) else 0) 0)
    (T : ℕ) (δ : ℚ) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (halpha : |(k : ℚ) * value c alpha - 1 / (2 : ℚ) ^ T| ≤
      2 * δ + δ / 2 ^ T) :
    |(k : ℚ) * value c out - (1 / (2 : ℚ) ^ T) / 3| ≤ 2 * δ := by
  have hkpos : 0 < k := by omega
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hkpos
  have ha := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (fun j => if j = alpha then 82 * (u : ℤ) else 0) 0 g c hc hC hM hg hscale out hout
  rw [third_scale_signal u hu hk c alpha] at ha
  have hp : (1 : ℚ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  have hsmall : δ / 2 ^ T ≤ δ := by
    exact (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ T)).mpr
      (by nlinarith only [hp, hδ0])
  have hα0 : (0 : ℚ) ≤ (1 / (2 : ℚ) ^ T) / 3 := by positivity
  have hα1 : (1 / (2 : ℚ) ^ T) / 3 ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hp
    simp only [div_one] at hh
    linarith only [hh]
  have he : |((k : ℚ) * value c alpha) / 3 - (1 / (2 : ℚ) ^ T) / 3| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 3)]
    apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 3)).mpr
    linarith only [halpha, hsmall]
  have hcl := GameTheory.Math.unitClamp_nonexpansive
    (((k : ℚ) * value c alpha) / 3) ((1 / (2 : ℚ) ^ T) / 3)
  rw [GameTheory.Math.unitClamp_eq_self hα0 hα1] at hcl
  exact (abs_sub_le _ _ _).trans ((add_le_add (ha.trans hδ) (hcl.trans he)).trans_eq
    (by ring))

/-- Mean scaling and the actual cyclic feedback blocks give a projected update residual. -/
theorem scaled_mean_feedback_error (H M : ℤ) (u : ℕ) (hu : 0 < u) (hk : k = 123 * u)
    (g : Fin k → Gate k) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (alpha negative : ℕ → Fin k) (T : ℕ) (hT : 7 ≤ T)
    (hone : g (alpha 0) = BimatrixArithmeticGate.gate (fun _ => 0) 2)
    (ha : ∀ j < T, g (alpha (j + 1)) = BimatrixDyadicGate.halvingGate (alpha j))
    (hn : ∀ j < T, g (negative (j + 1)) = BimatrixDyadicGate.halvingGate (negative j))
    (iq ip ih is : Fin k)
    (hp : g ip = BimatrixArithmeticGate.gate
      (fun j => if j = alpha T then 82 * (u : ℤ) else 0) 0)
    (hh : g ih = BimatrixFeedbackGate.halfAddGate iq ip)
    (hs : g is = BimatrixFeedbackGate.subtractHalfGate ih (negative T))
    (hq : g iq = BimatrixFeedbackGate.doubleGate is)
    (μ δ : ℚ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hmean : |(k : ℚ) * value c (negative 0) - μ| ≤ 77 * δ) :
    let x := max 0 (min 1 ((k : ℚ) * value c iq))
    |x - max 0 (min 1 (x + (1 / (2 : ℚ) ^ T) / 3 - μ / 2 ^ T))| ≤ 12 * δ := by
  have hkpos : 0 < k := by omega
  have hone' := (one_error H M hkpos g c hc hM hg hscale (alpha 0) hone).trans hδ
  have halpha := BimatrixDyadicGate.halving_chain_error H M hkpos g c hc hM hg hscale
    alpha T 1 δ δ (by norm_num) (by norm_num) hδ0 hδ ha hone' T le_rfl
  have hpositive := positive_scale_error H M u hu hk g c hc hM hg hscale
    (alpha T) ip hp T δ hδ0 hδ halpha
  have hnegative := BimatrixDyadicGate.halving_chain_error H M hkpos g c hc hM hg hscale
    negative T μ (77 * δ) δ hμ0 hμ1 hδ0 hδ hn hmean T le_rfl
  have hpow : (77 : ℚ) ≤ 2 ^ T := by
    exact (show (77 : ℚ) ≤ 2 ^ (7 : ℕ) by norm_num).trans
      (pow_le_pow_right₀ (by norm_num) hT)
  have hsmall : 77 * δ / 2 ^ T ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ T)).mpr
    exact_mod_cast (show 77 * δ ≤ δ * (2 : ℚ) ^ T from
      (mul_le_mul_of_nonneg_right hpow hδ0).trans_eq (by ring))
  have hnerr : |(k : ℚ) * value c (negative T) - μ / 2 ^ T| ≤ 3 * δ := by
    linarith only [hnegative, hsmall]
  have hp0 : (0 : ℚ) ≤ (1 / (2 : ℚ) ^ T) / 3 := by positivity
  have hp1 : (1 / (2 : ℚ) ^ T) / 3 ≤ 1 := by
    have hp := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1)
      (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2) (n := T))
    simp only [div_one] at hp
    linarith only [hp]
  have he := BimatrixFeedbackGate.cyclic_feedback_error H M hkpos g c hc hM hg hscale
    iq ip (negative T) ih is hh hs hq ((1 / (2 : ℚ) ^ T) / 3) (μ / 2 ^ T)
    (2 * δ) (3 * δ) δ hp0 hp1 (by positivity) hδ hpositive hnerr
  dsimp only at he ⊢
  linarith only [he]

/-- Actual minimum blocks and the canonical mean block propagate uniform sample errors. -/
theorem clipped_mean_error (H M : ℤ) (u : ℕ) (hu : 0 < u) (hk : k = 123 * u)
    (g : Fin k → Gate k) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (weight : Fin 41 → Fin 4 → Fin k)
    (color temporary minimum : Fin 2 → Fin 41 → Fin 4 → Fin k)
    (ht : ∀ f t a, g (temporary f t a) =
      BimatrixMinGate.subtractionGate (2 * (k : ℤ)) (weight t a) (color f t a))
    (hm : ∀ f t a, g (minimum f t a) =
      BimatrixMinGate.subtractionGate (2 * (k : ℤ)) (weight t a) (temporary f t a))
    (out : Fin k) (hout : g out = BimatrixColorMeanGate.meanGate u (minimum 0) (minimum 1))
    (w : Fin 41 → Fin 4 → ℚ) (δ : ℚ)
    (hw0 : ∀ t a, 0 ≤ w t a) (hsum : ∀ t, ∑ a, w t a = 1)
    (hweight : ∀ t a, |(k : ℚ) * value c (weight t a) - w t a| ≤ 8 * δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ) :
    |(k : ℚ) * value c out -
      (∑ t, ∑ a, (2 * min (w t a) (max 0 (min 1 ((k : ℚ) * value c (color 0 t a)))) +
        min (w t a) (max 0 (min 1 ((k : ℚ) * value c (color 1 t a)))))) / 123| ≤
      77 * δ := by
  have hkpos : 0 < k := by omega
  have hw1 (t : Fin 41) (a : Fin 4) : w t a ≤ 1 := by
    rw [← hsum t]
    exact Finset.single_le_sum (fun j _ => hw0 t j) (Finset.mem_univ a)
  have he (f : Fin 2) (t : Fin 41) (a : Fin 4) :
      |(k : ℚ) * value c (minimum f t a) -
        min (w t a) (max 0 (min 1 ((k : ℚ) * value c (color f t a))))| ≤ 19 * δ := by
    have hwR : (0 : ℝ) ≤ (w t a : ℝ) := by exact_mod_cast hw0 t a
    have hwR1 : (w t a : ℝ) ≤ 1 := by exact_mod_cast hw1 t a
    have hweightR : |(((k : ℚ) * value c (weight t a) : ℚ) : ℝ) - (w t a : ℝ)| ≤
        ((8 * δ : ℚ) : ℝ) := by exact_mod_cast hweight t a
    have h := clipped_color_min_error H M hkpos g c hc hM hg hscale
      (weight t a) (color f t a) (temporary f t a) (minimum f t a) (ht f t a)
      (hm f t a) (w t a : ℝ) hwR hwR1 δ hδ hweightR
    exact_mod_cast h
  have hmean := BimatrixColorMeanGate.mean_gate_error u hu hk H M g c hc hM hg hscale
    (minimum 0) (minimum 1) out hout w
    (fun t a => max 0 (min 1 ((k : ℚ) * value c (color 0 t a))))
    (fun t a => max 0 (min 1 ((k : ℚ) * value c (color 1 t a)))) (19 * δ)
    hw0 hsum (fun _ _ => le_max_left _ _) (fun _ _ => le_max_left _ _) (he 0) (he 1)
  linarith only [hmean, hδ]

end GameTheory.Finite.BimatrixBrouwerGateBounds
