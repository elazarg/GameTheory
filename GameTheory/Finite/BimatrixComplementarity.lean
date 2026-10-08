import GameTheory.Math.LinearComplementarity
import GameTheory.Finite.BimatrixCertificate
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact rational complementary points for independent rectangular payoff matrices.
The zero point is the artificial source. Every other complementary point encoded
by nonnegative numerators and positive denominators yields a Nash certificate,
without a nondegeneracy assumption. -/
namespace GameTheory.Finite
open scoped BigOperators
open GameTheory.Math.LinearComplementarity

/-- Off-diagonal negative payoff blocks of the bimatrix complementarity problem. -/
def bimatrixComplementaryMatrix {m n : ℕ} (A B : Fin m → Fin n → ℤ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℚ
  | .inl i, .inr j => -(A i j : ℚ)
  | .inr j, .inl i => -(B i j : ℚ)
  | _, _ => 0

/-- Rational coordinates are scaled independently for the two action blocks. -/
def bimatrixComplementaryPoint {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (Dx Dy : ℕ) : Fin m ⊕ Fin n → ℚ
  | .inl i => (r i : ℚ) / Dx
  | .inr j => (s j : ℚ) / Dy

/-- Normalize complementary coordinates by their mass, retaining cleared utilities. -/
def complementaryNashCertificate {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (Dx Dy : ℕ) : BimatrixCertificate m n :=
  ⟨r, s, ∑ i, r i, ∑ j, s j, (Dy : ℤ), (Dx : ℤ)⟩

/-- The row slack is the cleared row-score inequality divided by its scale. -/
theorem bimatrixComplementarySlack_row {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (r : Fin m → ℕ) (s : Fin n → ℕ) (Dx Dy : ℕ) (i : Fin m) :
    slack (fun _ => 1) (bimatrixComplementaryMatrix A B)
      (bimatrixComplementaryPoint r s Dx Dy) (.inl i) =
      1 - (BimatrixCertificate.rowScore A (complementaryNashCertificate r s Dx Dy) i : ℚ) /
        Dy := by
  simp only [slack, Fintype.sum_sum_type, bimatrixComplementaryMatrix,
    bimatrixComplementaryPoint, zero_mul, Finset.sum_const_zero, zero_add,
    BimatrixCertificate.rowScore, complementaryNashCertificate, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast]
  rw [Finset.sum_div]
  simp only [neg_mul, mul_div_assoc, ← Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The column slack uses the independent column matrix with row coordinates. -/
theorem bimatrixComplementarySlack_col {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (r : Fin m → ℕ) (s : Fin n → ℕ) (Dx Dy : ℕ) (j : Fin n) :
    slack (fun _ => 1) (bimatrixComplementaryMatrix A B)
      (bimatrixComplementaryPoint r s Dx Dy) (.inr j) =
      1 - (BimatrixCertificate.colScore B (complementaryNashCertificate r s Dx Dy) j : ℚ) /
        Dx := by
  simp only [slack, Fintype.sum_sum_type, bimatrixComplementaryMatrix,
    bimatrixComplementaryPoint, zero_mul, Finset.sum_const_zero, add_zero,
    BimatrixCertificate.colScore, complementaryNashCertificate, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast]
  rw [Finset.sum_div]
  simp only [neg_mul, mul_div_assoc, ← Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem rational_complementarity_iff (w Dx Dy : ℕ) (score : ℤ)
    (hx : 0 < Dx) (hy : 0 < Dy) :
    (0 ≤ (w : ℚ) / Dx ∧ 0 ≤ 1 - (score : ℚ) / Dy ∧
      (w : ℚ) / Dx * (1 - (score : ℚ) / Dy) = 0) ↔
      score ≤ (Dy : ℤ) ∧ (0 < w → score = (Dy : ℤ)) := by
  have hdx : (0 : ℚ) < Dx := by exact_mod_cast hx
  have hdy : (0 : ℚ) < Dy := by exact_mod_cast hy
  have hn : 0 ≤ (w : ℚ) / Dx := div_nonneg (Nat.cast_nonneg _) hdx.le
  have hs : 0 ≤ 1 - (score : ℚ) / Dy ↔ score ≤ (Dy : ℤ) := by
    rw [sub_nonneg, div_le_one hdy]
    exact_mod_cast (Iff.rfl : (score : ℚ) ≤ Dy ↔ (score : ℚ) ≤ Dy)
  have he : 1 - (score : ℚ) / Dy = 0 ↔ score = (Dy : ℤ) := by
    rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hdy.ne']
    exact_mod_cast (Iff.rfl : (score : ℚ) = Dy ↔ (score : ℚ) = Dy)
  have hz : (w : ℚ) / Dx = 0 ↔ w = 0 := by simp [div_eq_zero_iff, hdx.ne']
  constructor
  · rintro ⟨_, hs', hp⟩
    refine ⟨hs.mp hs', ?_⟩
    intro hw
    rcases mul_eq_zero.mp hp with hw' | hs''
    · have := hz.mp hw'; omega
    · exact he.mp hs''
  · rintro ⟨hs', he'⟩
    refine ⟨hn, hs.mpr hs', ?_⟩
    by_cases hw : w = 0
    · rw [hz.mpr hw, zero_mul]
    · rw [he.mpr (he' (by omega)), mul_zero]

/-- The rational block problem is exactly the two cleared best-response systems. -/
theorem bimatrixComplementarity_iff {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (r : Fin m → ℕ) (s : Fin n → ℕ) (Dx Dy : ℕ) (hx : 0 < Dx) (hy : 0 < Dy) :
    IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B)
      (bimatrixComplementaryPoint r s Dx Dy) ↔
    (∀ i, BimatrixCertificate.rowScore A (complementaryNashCertificate r s Dx Dy) i ≤ Dy ∧
      (0 < r i → BimatrixCertificate.rowScore A (complementaryNashCertificate r s Dx Dy) i = Dy)) ∧
    (∀ j, BimatrixCertificate.colScore B (complementaryNashCertificate r s Dx Dy) j ≤ Dx ∧
      (0 < s j → BimatrixCertificate.colScore B (complementaryNashCertificate r s Dx Dy) j = Dx)) := by
  rw [isSolution_iff_pointwise, Sum.forall]
  simp only [bimatrixComplementarySlack_row, bimatrixComplementarySlack_col,
    bimatrixComplementaryPoint]
  exact and_congr
    (forall_congr' fun i => rational_complementarity_iff (r i) Dx Dy _ hx hy)
    (forall_congr' fun j => rational_complementarity_iff (s j) Dy Dx _ hy hx)

/-- Every nonzero complementary point has positive mass in both action blocks. -/
theorem bimatrixComplementaryPoint_masses_pos {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (r : Fin m → ℕ) (s : Fin n → ℕ) (Dx Dy : ℕ)
    (h : IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B)
      (bimatrixComplementaryPoint r s Dx Dy))
    (hne : bimatrixComplementaryPoint r s Dx Dy ≠ 0) :
    0 < ∑ i, r i ∧ 0 < ∑ j, s j := by
  constructor
  · by_contra hn
    have hsum : ∑ i, r i = 0 := by omega
    have hr (i : Fin m) : r i = 0 := by
      have hi := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (r k))
        (Finset.mem_univ i)
      omega
    apply hne
    funext k
    cases k with
    | inl i => simp [bimatrixComplementaryPoint, hr]
    | inr j =>
      have hsl : slack (fun _ => 1) (bimatrixComplementaryMatrix A B)
          (bimatrixComplementaryPoint r s Dx Dy) (.inr j) = 1 := by
        simp [bimatrixComplementarySlack_col, BimatrixCertificate.colScore,
          complementaryNashCertificate, hr]
      have hc := h.complementary (.inr j)
      rw [hsl, mul_one] at hc
      exact hc
  · by_contra hn
    have hsum : ∑ j, s j = 0 := by omega
    have hs (j : Fin n) : s j = 0 := by
      have hj := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (s k))
        (Finset.mem_univ j)
      omega
    apply hne
    funext k
    cases k with
    | inr j => simp [bimatrixComplementaryPoint, hs]
    | inl i =>
      have hsl : slack (fun _ => 1) (bimatrixComplementaryMatrix A B)
          (bimatrixComplementaryPoint r s Dx Dy) (.inl i) = 1 := by
        simp [bimatrixComplementarySlack_row, BimatrixCertificate.rowScore,
          complementaryNashCertificate, hs]
      have hc := h.complementary (.inl i)
      rw [hsl, mul_one] at hc
      exact hc

/-- Normalization yields a valid Nash certificate exactly for non-source
complementary points. Empty dimensions and degenerate matrices need no exceptions. -/
theorem complementaryNashCertificate_valid_iff {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (r : Fin m → ℕ) (s : Fin n → ℕ) (Dx Dy : ℕ) (hx : 0 < Dx) (hy : 0 < Dy) :
    (complementaryNashCertificate r s Dx Dy).Valid A B ↔
      IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B)
        (bimatrixComplementaryPoint r s Dx Dy) ∧
      bimatrixComplementaryPoint r s Dx Dy ≠ 0 := by
  constructor
  · intro hc
    refine ⟨(bimatrixComplementarity_iff A B r s Dx Dy hx hy).mpr ⟨hc.2.2.2.2.1, hc.2.2.2.2.2⟩,
      ?_⟩
    intro hz
    have hr (i : Fin m) : r i = 0 := by
      have hi := congrFun hz (.inl i)
      change (r i : ℚ) / Dx = 0 at hi
      have hdx : (Dx : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
      simpa [div_eq_zero_iff, hdx] using hi
    have hsum : (∑ i, r i) = 0 := by simp [hr]
    have hpos := hc.1
    change 0 < ∑ i, r i at hpos
    omega
  · rintro ⟨h, hn⟩
    obtain ⟨hr, hs⟩ := bimatrixComplementarity_iff A B r s Dx Dy hx hy |>.mp h
    obtain ⟨hm, hn⟩ := bimatrixComplementaryPoint_masses_pos A B r s Dx Dy h hn
    exact ⟨hm, hn, rfl, rfl, hr, hs⟩

end GameTheory.Finite
