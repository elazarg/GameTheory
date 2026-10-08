import GameTheory.Finite.BimatrixPathCertificate
import GameTheory.Math.FiniteRationalEncoding

/-! Binary width bounds for the certificate decoded from a supplied rational
endpoint. Bounds cover the same endpoint, including the effect of payoff shifts. -/

namespace GameTheory.Finite
open scoped BigOperators

/-- A common width for endpoint coordinates, normalized masses and shifted utilities. -/
def bimatrixEndpointWidth (m n h s : ℕ) : ℕ :=
  h * (m + n + 1) + (m + n) + s + 2

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

/-- Reduced coordinate bounds yield a width bound for the directly decoded
certificate. Validity and nonnegative coordinates are unnecessary for this bound. -/
theorem bimatrixEndpointCertificate_fitsWidth {m n : ℕ}
    (z : Fin m ⊕ Fin n → ℚ) (a b : ℤ) (h s : ℕ)
    (hN : ∀ k, (z k).num.natAbs ≤ 2 ^ h) (hD : ∀ k, (z k).den ≤ 2 ^ h)
    (ha : a.natAbs ≤ 2 ^ s) (hb : b.natAbs ≤ 2 ^ s) :
    (bimatrixEndpointCertificate z a b).FitsWidth (bimatrixEndpointWidth m n h s) := by
  let t := h * (m + n + 1)
  let k := m + n
  have hnum (i) : Math.FiniteRationalEncoding.numerator z i ≤ 2 ^ t := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Math.FiniteRationalEncoding.numerator_le_two_pow z h hN hD i
  have hden : Math.FiniteRationalEncoding.denominator z ≤ 2 ^ t := by
    have hd := Math.FiniteRationalEncoding.denominator_le_two_pow z h hD
    simp only [Fintype.card_sum, Fintype.card_fin] at hd
    exact hd.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left h (by omega : m + n ≤ m + n + 1)))
  have hr := sum_binary_bound (fun i : Fin m => Math.FiniteRationalEncoding.numerator z (.inl i))
    t k (fun i => hnum (.inl i)) (by dsimp [k]; omega)
  have hc := sum_binary_bound (fun j : Fin n => Math.FiniteRationalEncoding.numerator z (.inr j))
    t k (fun j => hnum (.inr j)) (by dsimp [k]; omega)
  have hu := shifted_utility_binary_bound _ _ a t k s hden hc ha
  have hv := shifted_utility_binary_bound _ _ b t k s hden hr hb
  have hexp : t + k + s + 1 < bimatrixEndpointWidth m n h s := by
    dsimp [t, k, bimatrixEndpointWidth]; omega
  have hup : 2 ^ (t + k + s + 1) < 2 ^ bimatrixEndpointWidth m n h s :=
    Nat.pow_lt_pow_right (by decide) hexp
  have hsmall : 2 ^ (t + k) < 2 ^ bimatrixEndpointWidth m n h s :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hcoord : 2 ^ t < 2 ^ bimatrixEndpointWidth m n h s :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨hr.trans_lt hsmall, hc.trans_lt hsmall, fun i => (hnum (.inl i)).trans_lt hcoord,
    fun j => (hnum (.inr j)).trans_lt hcoord, hu.trans_lt hup, hv.trans_lt hup⟩

end GameTheory.Finite
