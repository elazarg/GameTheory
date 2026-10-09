import GameTheory.Finite.BimatrixPathCertificate
import GameTheory.Math.FiniteRationalEncoding
import GameTheory.Finite.BimatrixComplementaryCertificateBounds

/-! Binary width bounds for the certificate decoded from a supplied rational
endpoint. Bounds cover the same endpoint, including the effect of payoff shifts. -/

namespace GameTheory.Finite
open scoped BigOperators

/-- A common width for endpoint coordinates, normalized masses and shifted utilities. -/
def bimatrixEndpointWidth (m n h s : ℕ) : ℕ :=
  h * (m + n + 1) + (m + n) + s + 2

/-- Reduced coordinate bounds yield a width bound for the directly decoded
certificate. Validity and nonnegative coordinates are unnecessary for this bound. -/
theorem bimatrixEndpointCertificate_fitsWidth {m n : ℕ}
    (z : Fin m ⊕ Fin n → ℚ) (a b : ℤ) (h s : ℕ)
    (hN : ∀ k, (z k).num.natAbs ≤ 2 ^ h) (hD : ∀ k, (z k).den ≤ 2 ^ h)
    (ha : a.natAbs ≤ 2 ^ s) (hb : b.natAbs ≤ 2 ^ s) :
    (bimatrixEndpointCertificate z a b).FitsWidth (bimatrixEndpointWidth m n h s) := by
  let t := h * (m + n + 1)
  have hnum (i) : Math.FiniteRationalEncoding.numerator z i ≤ 2 ^ t := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Math.FiniteRationalEncoding.numerator_le_two_pow z h hN hD i
  have hden : Math.FiniteRationalEncoding.denominator z ≤ 2 ^ t := by
    have hd := Math.FiniteRationalEncoding.denominator_le_two_pow z h hD
    simp only [Fintype.card_sum, Fintype.card_fin] at hd
    exact hd.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left h (by omega : m + n ≤ m + n + 1)))
  exact complementaryNashCertificate_fitsWidth _ _ _ a b t s
    (fun i => hnum (.inl i)) (fun j => hnum (.inr j)) hden ha hb

end GameTheory.Finite
