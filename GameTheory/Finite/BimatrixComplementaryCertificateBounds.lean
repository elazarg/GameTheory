import GameTheory.Finite.BimatrixComplementarity
import GameTheory.Finite.BimatrixCertificateShift

/-! Binary width bounds for normalized complementary coordinates and shifted
utilities. The estimates apply to every supplied integer representation. -/
namespace GameTheory.Finite
open scoped BigOperators

private theorem sum_binary_bound {r : ℕ} (f : Fin r → ℕ) (t k : ℕ)
    (hf : ∀ i, f i ≤ 2 ^ t) (hr : r ≤ k) :
    (∑ i, f i) ≤ 2 ^ (t + k) := by
  calc
    (∑ i, f i) ≤ ∑ _ : Fin r, 2 ^ t := Finset.sum_le_sum fun i _ => hf i
    _ = r * 2 ^ t := by simp
    _ ≤ 2 ^ k * 2 ^ t := Nat.mul_le_mul_right _ (hr.trans (Nat.lt_two_pow_self.le))
    _ = 2 ^ (t + k) := by rw [pow_add, Nat.mul_comm]

private theorem shifted_utility_binary_bound (D mass : ℕ) (a : ℤ) (t k s : ℕ)
    (hD : D ≤ 2 ^ t) (hmass : mass ≤ 2 ^ (t + k)) (ha : a.natAbs ≤ 2 ^ s) :
    ((D : ℤ) + -a * mass).natAbs ≤ 2 ^ (t + k + s + 1) := by
  have hD' : D ≤ 2 ^ (t + k + s) := hD.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hmul : a.natAbs * mass ≤ 2 ^ (t + k + s) := by
    calc
      a.natAbs * mass ≤ 2 ^ s * 2 ^ (t + k) := Nat.mul_le_mul ha hmass
      _ = 2 ^ (t + k + s) := by simp only [pow_add]; ac_rfl
  calc
    ((D : ℤ) + -a * mass).natAbs ≤ D + a.natAbs * mass := by
      simpa only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_neg] using
        Int.natAbs_add_le (D : ℤ) (-a * mass)
    _ ≤ 2 ^ (t + k + s) + 2 ^ (t + k + s) := Nat.add_le_add hD' hmul
    _ = 2 ^ (t + k + s + 1) := by rw [pow_succ]; omega

/-- Coordinate and common-denominator bounds control every certificate field,
including signed utility shifts. Empty dimensions and invalid inputs are covered. -/
theorem complementaryNashCertificate_fitsWidth {m n : ℕ}
    (r : Fin m → ℕ) (c : Fin n → ℕ) (D : ℕ) (a b : ℤ) (W s : ℕ)
    (hr : ∀ i, r i ≤ 2 ^ W) (hc : ∀ j, c j ≤ 2 ^ W) (hD : D ≤ 2 ^ W)
    (ha : a.natAbs ≤ 2 ^ s) (hb : b.natAbs ≤ 2 ^ s) :
    ((complementaryNashCertificate r c D D).shiftPayoffs (-a) (-b)).FitsWidth
      (W + (m + n) + s + 2) := by
  have hrSum := sum_binary_bound r W (m + n) hr (by omega)
  have hcSum := sum_binary_bound c W (m + n) hc (by omega)
  have hu := shifted_utility_binary_bound D _ a W (m + n) s hD hcSum ha
  have hv := shifted_utility_binary_bound D _ b W (m + n) s hD hrSum hb
  have hup : 2 ^ (W + (m + n) + s + 1) < 2 ^ (W + (m + n) + s + 2) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hsmall : 2 ^ (W + (m + n)) < 2 ^ (W + (m + n) + s + 2) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hcoord : 2 ^ W < 2 ^ (W + (m + n) + s + 2) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨hrSum.trans_lt hsmall, hcSum.trans_lt hsmall,
    fun i => (hr i).trans_lt hcoord, fun j => (hc j).trans_lt hcoord,
    hu.trans_lt hup, hv.trans_lt hup⟩

end GameTheory.Finite
