import GameTheoryComplexity.Backend.NashRealSupport
import GameTheoryComplexity.Backend.BoundedSupportWitness
import GameTheory.Finite.BimatrixNashCertificateCorrectness

/-! Payoff-constrained mixed Nash equilibria admit exact integer numerator
certificates with a polynomial number of bits per field. -/

noncomputable section

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Probability
open GameTheory.Finite
open scoped BigOperators

/-- Bounded integer tables have polynomial-width certificates for every
canonical constrained Nash existence witness. -/
theorem exists_bounded_nashNumerators {q L : ℕ} (A : Fin q → Fin q → ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ q + 2) (hqL : q ≤ L)
    (h : (MatrixGame.bimatrixGame (fun i j => (A i j : ℝ))
      (fun i j => (A j i : ℝ))).HasNashWithPayoffAtLeast (fun _ => 1)) :
    ∃ c : NumeratorCertificate q, c.Valid A ∧
      c.rowDenominator < 2 ^ (14 * L ^ 2 + 36 * L + 23) ∧
      c.colDenominator < 2 ^ (14 * L ^ 2 + 36 * L + 23) ∧
      c.rowUtilityNumerator < 2 ^ (14 * L ^ 2 + 36 * L + 23) ∧
      c.colUtilityNumerator < 2 ^ (14 * L ^ 2 + 36 * L + 23) ∧
      (∀ i, c.rowWeights i < 2 ^ (14 * L ^ 2 + 36 * L + 23)) ∧
      (∀ j, c.colWeights j < 2 ^ (14 * L ^ 2 + 36 * L + 23)) := by
  classical
  obtain ⟨p, r, hnash, hp, hr⟩ :=
    (MatrixGame.hasNashWithPayoffAtLeast_iff _ _).mp h
  obtain ⟨hfrow, hfcol⟩ := nash_realSupportFeasible A p r hnash hp hr
  obtain ⟨Dq, Nq, hDq, hbDq, hbNq, heqQ⟩ :=
    exists_bounded_support_solution_of_le A (nashSupport p) (nashSupport r)
      hA hqL _ _ hfrow
  obtain ⟨Dp, Np, hDp, hbDp, hbNp, heqP⟩ :=
    exists_bounded_support_solution_of_le A (nashSupport r) (nashSupport p)
      hA hqL _ _ hfcol
  obtain ⟨hsQ, htQ, hiQ, heQ, hzQ⟩ :=
    natural_solution_constraints A (nashSupport p) (nashSupport r) Nq Dq heqQ
  obtain ⟨hsP, htP, hiP, heP, hzP⟩ :=
    natural_solution_constraints A (nashSupport r) (nashSupport p) Np Dp heqP
  let c : NumeratorCertificate q :=
    ⟨fun i => Np (.inl i), fun j => Nq (.inl j), Dp, Dq,
      Nq (.inr (.inl PUnit.unit)), Np (.inr (.inl PUnit.unit))⟩
  refine ⟨c, ?_, hbDp, hbDq, hbNq _, hbNp _,
    fun i => hbNp (.inl i), fun j => hbNq (.inl j)⟩
  refine ⟨hDp, hDq, hsP, hsQ, htQ, htP, ?_, ?_⟩
  · intro i
    refine ⟨hiQ i, ?_⟩
    intro hi
    apply heQ i
    by_cases hs : nashSupport p i = true
    · exact hs
    · have hz := hzP i (Bool.eq_false_iff.mpr hs)
      exact False.elim ((Nat.ne_of_gt hi) hz)
  · intro j
    refine ⟨hiP j, ?_⟩
    intro hj
    apply heP j
    by_cases hs : nashSupport r j = true
    · exact hs
    · have hz := hzQ j (Bool.eq_false_iff.mpr hs)
      exact False.elim ((Nat.ne_of_gt hj) hz)

/-- The actual total table decoder admits bounded certificates for every
member of its constrained-equilibrium language. -/
theorem exists_bounded_decoded_nashNumerators (input : List Bool)
    (h : input ∈ BimatrixTable.unitPayoffLanguage) :
    ∃ c : NumeratorCertificate (BimatrixTable.decodeDimension input),
      c.Valid (fun i j => BimatrixTable.decodedPayoff input i j) ∧
      c.rowDenominator < 2 ^ (14 * input.length ^ 2 + 36 * input.length + 23) ∧
      c.colDenominator < 2 ^ (14 * input.length ^ 2 + 36 * input.length + 23) ∧
      c.rowUtilityNumerator < 2 ^ (14 * input.length ^ 2 + 36 * input.length + 23) ∧
      c.colUtilityNumerator < 2 ^ (14 * input.length ^ 2 + 36 * input.length + 23) ∧
      (∀ i, c.rowWeights i < 2 ^ (14 * input.length ^ 2 + 36 * input.length + 23)) ∧
      (∀ j, c.colWeights j < 2 ^ (14 * input.length ^ 2 + 36 * input.length + 23)) :=
  exists_bounded_nashNumerators _
    (fun i j => BimatrixTable.decodedPayoff_natAbs_le input i j)
    (BimatrixTable.decodeDimension_le_length input) h

end GameTheory.Complexity.Backend
