/- Transfer fixed bivariate relations between prime germs and real sequences. -/
import Math.GateGAlgebraicRelation
import Math.GateGGermComponent
import Math.GateGLocalRootIsolation

set_option autoImplicit false

noncomputable section

open Filter Set

namespace Math
namespace GateGGermRelationScratch

open GateGGermComponentScratch

/-- Substitute an affine parameter polynomial into the coefficients of a
bivariate polynomial, and an arbitrary multivariate objective polynomial
into its outer (value) variable. -/
def realizeBivariate
    {σ : Type*} (parameter : σ)
    (objective : MvPolynomial σ ℝ)
    (Q : Polynomial (Polynomial ℝ)) :
    MvPolynomial σ ℝ :=
  Polynomial.eval₂
    (Polynomial.aeval
      (MvPolynomial.X parameter)).toRingHom
    objective Q

@[simp]
theorem eval_realizeBivariate
    {σ : Type*} (parameter : σ)
    (objective : MvPolynomial σ ℝ)
    (Q : Polynomial (Polynomial ℝ))
    (x : σ → ℝ) :
    MvPolynomial.eval x
        (realizeBivariate parameter objective Q) =
      bivEval Q (x parameter)
        (MvPolynomial.eval x objective) := by
  rw [realizeBivariate, Polynomial.hom_eval₂]
  congr 2
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

/-- The real zero set of an affine ideal. -/
def realZeroSet
    {σ : Type*} (J : Ideal (MvPolynomial σ ℝ)) :
    Set (σ → ℝ) :=
  {x | ∀ P ∈ J, MvPolynomial.eval x P = 0}

theorem realizeBivariate_eq_zero_on_realZeroSet
    {σ : Type*} {J : Ideal (MvPolynomial σ ℝ)}
    {parameter : σ}
    {objective : MvPolynomial σ ℝ}
    {Q : Polynomial (Polynomial ℝ)}
    (hQ : realizeBivariate parameter objective Q ∈ J) :
    ∀ x ∈ realZeroSet J,
      bivEval Q (x parameter)
        (MvPolynomial.eval x objective) = 0 := by
  intro x hx
  rw [← eval_realizeBivariate]
  exact hx _ hQ

/-- On an ultrafilter germ, nonmembership of the realized derivative
polynomial is equivalent to eventual nonvanishing after passing to the
ultrafilter side of the dichotomy. -/
theorem eventually_ne_zero_of_not_mem_sequenceGermIdeal
    {σ : Type*} (x : ℕ → (σ → ℝ))
    (P : MvPolynomial σ ℝ)
    (hP : P ∉ sequenceGermIdeal x) :
    ∀ᶠ m in
        (sequenceUltrafilter : Filter ℕ),
      MvPolynomial.eval (x m) P ≠ 0 := by
  let Z : Set ℕ :=
    {m | MvPolynomial.eval (x m) P = 0}
  have hZ : Z ∉ sequenceUltrafilter := by
    intro hZ
    apply hP
    rw [mem_sequenceGermIdeal_iff]
    exact hZ
  have hZc : Zᶜ ∈ sequenceUltrafilter :=
    (Ultrafilter.compl_mem_iff_notMem).2 hZ
  exact hZc

/-- A relation polynomial in the sequence germ ideal vanishes eventually;
if its realized value derivative is not in the prime ideal, that derivative
is eventually nonzero.  These are exactly the two pointwise hypotheses for
local root isolation at all terms of a thinned selected sequence. -/
theorem eventually_relation_and_derivative_ne_zero
    {σ : Type*}
    (x : ℕ → (σ → ℝ)) (parameter : σ)
    (objective : MvPolynomial σ ℝ)
    (Q : Polynomial (Polynomial ℝ))
    (hrelation :
      realizeBivariate parameter objective Q ∈
        sequenceGermIdeal x)
    (hderiv :
      realizeBivariate parameter objective Q.derivative ∉
        sequenceGermIdeal x) :
    (∀ᶠ m in
        (sequenceUltrafilter : Filter ℕ),
      bivEval Q (x m parameter)
        (MvPolynomial.eval (x m) objective) = 0) ∧
    (∀ᶠ m in
        (sequenceUltrafilter : Filter ℕ),
      bivEval Q.derivative (x m parameter)
        (MvPolynomial.eval (x m) objective) ≠ 0) := by
  constructor
  · have h :=
      (mem_sequenceGermIdeal_iff x
        (realizeBivariate parameter objective Q)).mp
        hrelation
    simpa only [eval_realizeBivariate] using h
  · have h :=
      eventually_ne_zero_of_not_mem_sequenceGermIdeal
        x (realizeBivariate parameter objective Q.derivative)
        hderiv
    simpa only [eval_realizeBivariate] using h

end GateGGermRelationScratch
end Math
