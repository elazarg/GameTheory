import GameTheory.Finite.BimatrixPathEndOfLine
import GameTheory.Finite.BimatrixComplementarityCorrectness
import GameTheory.Finite.BimatrixCertificateCompleteness
import GameTheory.Math.FiniteRationalEncoding

/-! Rational complementary endpoints give exact Nash certificates.
Clearing denominators preserves every coordinate of the supplied endpoint.
Payoff shifts undo positivity normalization, while independent support-system
bounds provide polynomial-width certificates for the original signed game.
-/

namespace GameTheory.Finite

open GameTheory.Math.LinearComplementarity

private theorem complementaryPoint_decode {m n : ℕ} (z : Fin m ⊕ Fin n → ℚ)
    (hz : ∀ k, 0 ≤ z k) :
    bimatrixComplementaryPoint
      (fun i => Math.FiniteRationalEncoding.numerator z (.inl i))
      (fun j => Math.FiniteRationalEncoding.numerator z (.inr j))
      (Math.FiniteRationalEncoding.denominator z)
      (Math.FiniteRationalEncoding.denominator z) = z := by
  funext k
  cases k with
  | inl i => exact Math.FiniteRationalEncoding.decode z hz (.inl i)
  | inr j => exact Math.FiniteRationalEncoding.decode z hz (.inr j)

/-- Clear the endpoint coordinates and undo the two independent payoff shifts. -/
def bimatrixEndpointCertificate {m n : ℕ} (z : Fin m ⊕ Fin n → ℚ) (a b : ℤ) :
    BimatrixCertificate m n :=
  (complementaryNashCertificate
    (fun i => Math.FiniteRationalEncoding.numerator z (.inl i))
    (fun j => Math.FiniteRationalEncoding.numerator z (.inr j))
    (Math.FiniteRationalEncoding.denominator z)
    (Math.FiniteRationalEncoding.denominator z)).shiftPayoffs (-a) (-b)

/-- Every nonzero rational solution of the shifted game certifies the original game. -/
theorem bimatrixEndpointCertificate_valid {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (a b : ℤ) (z : Fin m ⊕ Fin n → ℚ)
    (hsol : IsSolution (fun _ => 1)
      (bimatrixComplementaryMatrix (fun i j => A i j + a) (fun i j => B i j + b)) z)
    (hne : z ≠ 0) : (bimatrixEndpointCertificate z a b).Valid A B := by
  have hd := Math.FiniteRationalEncoding.denominator_pos z
  have he := complementaryPoint_decode z hsol.nonneg
  apply unshiftedComplementaryCertificate_valid A B a b _ _ _ _ hd hd
  · rwa [he]
  · rwa [he]

/-- Positive nonempty integer games have exact certificates by finite graph totality. -/
theorem exists_bimatrixCertificate_of_positive {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (hm : 0 < m) (hn : 0 < n)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    ∃ c : BimatrixCertificate m n, c.Valid A B := by
  obtain ⟨z, hne, hsol⟩ :=
    BimatrixPathPort.exists_nonzero_complementary_solution hm hn hA hB
  refine ⟨bimatrixEndpointCertificate z 0 0, ?_⟩
  apply bimatrixEndpointCertificate_valid A B 0 0 z
  · simpa only [add_zero] using hsol
  · exact hne

/-- Signed games admit exact certificates after a bounded positive payoff shift. -/
theorem exists_bimatrixCertificate_via_path {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (h : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h)
    (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h) :
    ∃ c : BimatrixCertificate m n, c.Valid A B := by
  let shift : ℤ := 2 ^ h + 1
  obtain ⟨z, hne, hsol⟩ := BimatrixPathPort.exists_nonzero_complementary_solution
    (A := fun i j => A i j + shift) (B := fun i j => B i j + shift) hm hn
    (fun i j => payoff_add_pow_positive (A i j) h (hA i j))
    (fun i j => payoff_add_pow_positive (B i j) h (hB i j))
  exact ⟨bimatrixEndpointCertificate z shift shift,
    bimatrixEndpointCertificate_valid A B shift shift z hsol hne⟩

/-- Finite complementary paths imply bounded certificates without analytic existence.
The bounded witness need not use the same coordinate representation as the endpoint. -/
theorem exists_bounded_bimatrixCertificate_via_path {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (h : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h)
    (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h) :
    ∃ c : BimatrixCertificate m n, c.Valid A B ∧
      c.FitsWidth (GameTheory.bimatrixCertificateWidth m n h) := by
  obtain ⟨c, hc⟩ := exists_bimatrixCertificate_via_path A B h hm hn hA hB
  obtain ⟨p, q, hnash⟩ := c.hasNash_of_valid A B hc
  exact GameTheory.exists_bounded_bimatrixCertificate A B h hA hB p q hnash

end GameTheory.Finite
