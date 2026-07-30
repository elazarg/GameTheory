import Math.WeierstrassCurve
import Mathlib.Algebra.Polynomial.Taylor

set_option autoImplicit false

noncomputable section

open Polynomial

namespace Math
namespace CurveSelection.TerminationScratch

variable {K : Type*} [Field K]

/-- The tail of a formal series after deleting its first `n` coefficients. -/
def formalTail (n : ℕ) (s : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun i => PowerSeries.coeff (i + n) s

/-- A series is its polynomial truncation plus `X^n` times its tail. -/
theorem eq_X_pow_mul_formalTail_add_trunc
    (n : ℕ) (s : PowerSeries K) :
    s =
      PowerSeries.X ^ n * formalTail n s +
        (s.trunc n : PowerSeries K) := by
  simpa [formalTail] using
    PowerSeries.eq_X_pow_mul_shift_add_trunc n s

/-- Exact division by `X^n`, with an arbitrary value away from the proved
divisibility locus. -/
noncomputable def divByXPow
    (n : ℕ) (a : PowerSeries K) : PowerSeries K := by
  classical
  exact if h : (PowerSeries.X : PowerSeries K) ^ n ∣ a then
    Classical.choose h
  else 0

theorem X_pow_mul_divByXPow
    (n : ℕ) (a : PowerSeries K)
    (h : (PowerSeries.X : PowerSeries K) ^ n ∣ a) :
    PowerSeries.X ^ n * divByXPow n a = a := by
  rw [divByXPow, dif_pos h]
  exact (Classical.choose_spec h).symm

/-- Every power below the order of a series divides it. -/
theorem X_pow_dvd_of_le_order_toNat
    (a : PowerSeries K) (m : ℕ)
    (h : m ≤ a.order.toNat) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ a := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  exact PowerSeries.coeff_of_lt_order_toNat i (hi.trans_le h)

theorem X_pow_dvd_sub_trunc
    (n : ℕ) (s : PowerSeries K) :
    (PowerSeries.X : PowerSeries K) ^ n ∣
      s - (s.trunc n : PowerSeries K) := by
  refine ⟨formalTail n s, ?_⟩
  have h := eq_X_pow_mul_formalTail_add_trunc n s
  linear_combination h

/-- Polynomial evaluation preserves congruence modulo the truncation power. -/
theorem X_pow_dvd_eval_sub_eval_trunc
    (f : Polynomial (PowerSeries K))
    (n : ℕ) (s : PowerSeries K) :
    (PowerSeries.X : PowerSeries K) ^ n ∣
      f.eval s - f.eval (s.trunc n : PowerSeries K) := by
  exact dvd_trans (X_pow_dvd_sub_trunc n s)
    (Polynomial.sub_dvd_eval_sub s
      (s.trunc n : PowerSeries K) f)

/-- If `D=f'(s)` has order `k<n`, then `f'` evaluated at the polynomial
truncation is still divisible by `X^k`. -/
theorem X_pow_dvd_derivative_eval_trunc
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hk : k ≤ (f.derivative.eval s).order.toNat)
    (hkn : k ≤ n) :
    (PowerSeries.X : PowerSeries K) ^ k ∣
      f.derivative.eval (s.trunc n : PowerSeries K) := by
  have hD :
      (PowerSeries.X : PowerSeries K) ^ k ∣
        f.derivative.eval s :=
    X_pow_dvd_of_le_order_toNat _ _ hk
  have hdiffn :
      (PowerSeries.X : PowerSeries K) ^ n ∣
        f.derivative.eval s -
          f.derivative.eval (s.trunc n : PowerSeries K) :=
    X_pow_dvd_eval_sub_eval_trunc f.derivative n s
  have hdiffk :
      (PowerSeries.X : PowerSeries K) ^ k ∣
        f.derivative.eval s -
          f.derivative.eval (s.trunc n : PowerSeries K) :=
    dvd_trans (pow_dvd_pow PowerSeries.X hkn) hdiffn
  have hsub := dvd_sub hD hdiffk
  simpa only [sub_sub_cancel] using hsub

/-- The outer-variable Taylor transform `Y = A + X^n Z`. -/
def scaledTaylorTransform
    (f : Polynomial (PowerSeries K))
    (A : PowerSeries K) (n : ℕ) :
    Polynomial (PowerSeries K) :=
  (Polynomial.taylor A f).comp
    (Polynomial.C (PowerSeries.X ^ n) * Polynomial.X)

theorem coeff_scaledTaylorTransform
    (f : Polynomial (PowerSeries K))
    (A : PowerSeries K) (n i : ℕ) :
    (scaledTaylorTransform f A n).coeff i =
      (Polynomial.taylor A f).coeff i *
        (PowerSeries.X ^ n) ^ i := by
  exact Polynomial.comp_C_mul_X_coeff

/-- Every positive outer coefficient of the Taylor transform carries the
common factor `X^(n+k)` once `n>k` and `f'(s)` has order at least `k`. -/
theorem X_pow_add_dvd_coeff_scaledTaylorTransform_of_pos
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K)
    (k n i : ℕ)
    (hkn : k < n)
    (hk : k ≤ (f.derivative.eval s).order.toNat)
    (hi : 0 < i) :
    (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
      (scaledTaylorTransform f
        (s.trunc n : PowerSeries K) n).coeff i := by
  rw [coeff_scaledTaylorTransform]
  by_cases hi1 : i = 1
  · subst i
    rw [Polynomial.taylor_coeff_one, pow_one]
    obtain ⟨u, hu⟩ :=
      X_pow_dvd_derivative_eval_trunc
        f s k n hk hkn.le
    refine ⟨u, ?_⟩
    rw [hu, pow_add]
    ring
  · have hi2 : 2 ≤ i := by omega
    have hexponent : n + k ≤ n * i := by
      calc
        n + k ≤ n + n := Nat.add_le_add_left hkn.le n
        _ = n * 2 := by omega
        _ ≤ n * i := Nat.mul_le_mul_left n hi2
    have hpow :
        (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
          (PowerSeries.X ^ n) ^ i := by
      simpa [pow_mul] using
        (pow_dvd_pow (PowerSeries.X : PowerSeries K) hexponent)
    exact dvd_mul_of_dvd_right hpow _

theorem eval_scaledTaylorTransform_formalTail
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K) (n : ℕ) :
    (scaledTaylorTransform f
        (s.trunc n : PowerSeries K) n).eval (formalTail n s) =
      f.eval s := by
  calc
    (scaledTaylorTransform f
        (s.trunc n : PowerSeries K) n).eval (formalTail n s) =
        f.eval
          (PowerSeries.X ^ n * formalTail n s +
            (s.trunc n : PowerSeries K)) := by
      simp [scaledTaylorTransform, Polynomial.eval_comp,
        Polynomial.taylor_eval]
    _ = f.eval s := by
      rw [← eq_X_pow_mul_formalTail_add_trunc n s]

/-- The constant coefficient gains the same factor because the selected
formal tail is a root and every positive outer coefficient already has it. -/
theorem X_pow_add_dvd_coeff_zero_scaledTaylorTransform
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hk : k ≤ (f.derivative.eval s).order.toNat)
    (hroot : f.IsRoot s) :
    (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
      (scaledTaylorTransform f
        (s.trunc n : PowerSeries K) n).coeff 0 := by
  let g :=
    scaledTaylorTransform f
      (s.trunc n : PowerSeries K) n
  have hpoly :
      Polynomial.C
          ((PowerSeries.X : PowerSeries K) ^ (n + k)) ∣
        g - Polynomial.C (g.coeff 0) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    cases i with
    | zero => simp
    | succ i =>
        simpa using
            (X_pow_add_dvd_coeff_scaledTaylorTransform_of_pos
              f s k n (i + 1) hkn hk (by omega))
  have heval :=
    map_dvd (Polynomial.evalRingHom (formalTail n s)) hpoly
  have hgeval : g.eval (formalTail n s) = 0 := by
    rw [show g =
        scaledTaylorTransform f
          (s.trunc n : PowerSeries K) n by rfl,
      eval_scaledTaylorTransform_formalTail]
    exact hroot
  have heval' :
      (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
        g.eval (formalTail n s) - g.coeff 0 := by
    simpa using heval
  rw [hgeval, zero_sub] at heval'
  exact dvd_neg.mp heval'

/-- All coefficients of the transform have the forced common factor. -/
theorem X_pow_add_dvd_coeff_scaledTaylorTransform
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hk : k ≤ (f.derivative.eval s).order.toNat)
    (hroot : f.IsRoot s) :
    ∀ i : ℕ,
      (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
        (scaledTaylorTransform f
          (s.trunc n : PowerSeries K) n).coeff i := by
  intro i
  by_cases hi : i = 0
  · subst i
    exact
      X_pow_add_dvd_coeff_zero_scaledTaylorTransform
        f s k n hkn hk hroot
  · exact
      X_pow_add_dvd_coeff_scaledTaylorTransform_of_pos
        f s k n i hkn hk (Nat.pos_of_ne_zero hi)

/-- Chain rule at the formal tail. -/
theorem eval_derivative_scaledTaylorTransform_formalTail
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K) (n : ℕ) :
    (scaledTaylorTransform f
        (s.trunc n : PowerSeries K) n).derivative.eval
          (formalTail n s) =
      PowerSeries.X ^ n * f.derivative.eval s := by
  rw [scaledTaylorTransform, Polynomial.derivative_comp]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [zero_add, mul_one]
  rw [Polynomial.taylor_apply, Polynomial.derivative_comp]
  simp only [Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, add_zero, one_mul,
    Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [← eq_X_pow_mul_formalTail_add_trunc n s]

/-- Normalize the Taylor transform by a common parameter power. -/
noncomputable def normalizedTaylorTransform
    (f : Polynomial (PowerSeries K))
    (A : PowerSeries K) (n k : ℕ) :
    Polynomial (PowerSeries K) :=
  ∑ i ∈ Finset.range (f.natDegree + 1),
    Polynomial.monomial i
      (divByXPow (n + k)
        ((scaledTaylorTransform f A n).coeff i))

theorem coeff_normalizedTaylorTransform_of_le
    (f : Polynomial (PowerSeries K))
    (A : PowerSeries K) (n k : ℕ)
    {i : ℕ} (hi : i ≤ f.natDegree) :
    (normalizedTaylorTransform f A n k).coeff i =
      divByXPow (n + k)
        ((scaledTaylorTransform f A n).coeff i) := by
  classical
  simp [normalizedTaylorTransform, Polynomial.coeff_monomial, hi]

theorem coeff_normalizedTaylorTransform_of_lt
    (f : Polynomial (PowerSeries K))
    (A : PowerSeries K) (n k : ℕ)
    {i : ℕ} (hi : f.natDegree < i) :
    (normalizedTaylorTransform f A n k).coeff i = 0 := by
  classical
  simp [normalizedTaylorTransform, Polynomial.coeff_monomial,
    Nat.not_le_of_gt hi]

/-- The normalized transform satisfies its defining polynomial identity. -/
theorem C_X_pow_mul_normalizedTaylorTransform
    (f : Polynomial (PowerSeries K))
    (A : PowerSeries K) (n k : ℕ)
    (hdiv :
      ∀ i : ℕ, i ≤ f.natDegree →
        (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
          (scaledTaylorTransform f A n).coeff i) :
    Polynomial.C (PowerSeries.X ^ (n + k)) *
        normalizedTaylorTransform f A n k =
      scaledTaylorTransform f A n := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_C_mul]
  by_cases hi : i ≤ f.natDegree
  · rw [coeff_normalizedTaylorTransform_of_le f A n k hi]
    exact X_pow_mul_divByXPow _ _ (hdiv i hi)
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    rw [coeff_normalizedTaylorTransform_of_lt f A n k hlt]
    have htaylor :
        (Polynomial.taylor A f).coeff i = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa [Polynomial.natDegree_taylor] using hlt
    rw [coeff_scaledTaylorTransform, htaylor]
    simp

/-- Normalization at any order `k<n` of the nonzero derivative preserves the
chosen formal root, and divides its derivative by exactly `X^k`. -/
theorem normalizedTaylorTransform_root_and_derivative
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hroot : f.IsRoot s)
    (horder : (f.derivative.eval s).order.toNat = k) :
    let H :=
      normalizedTaylorTransform f
        (s.trunc n : PowerSeries K) n k
    H.IsRoot (formalTail n s) ∧
      PowerSeries.X ^ k *
          H.derivative.eval (formalTail n s) =
        f.derivative.eval s := by
  let A : PowerSeries K := (s.trunc n : PowerSeries K)
  let H := normalizedTaylorTransform f A n k
  let g := scaledTaylorTransform f A n
  have hdiv :
      ∀ i : ℕ, i ≤ f.natDegree →
        (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
          g.coeff i := by
    intro i _hi
    exact
      X_pow_add_dvd_coeff_scaledTaylorTransform
        f s k n hkn horder.ge hroot i
  have hidentity :
      Polynomial.C (PowerSeries.X ^ (n + k)) * H = g := by
    exact
      C_X_pow_mul_normalizedTaylorTransform
        f A n k hdiv
  have hgroot : g.IsRoot (formalTail n s) := by
    change g.eval (formalTail n s) = 0
    rw [show g =
        scaledTaylorTransform f
          (s.trunc n : PowerSeries K) n by rfl,
      eval_scaledTaylorTransform_formalTail]
    exact hroot
  have hHroot : H.IsRoot (formalTail n s) := by
    have heval :=
      congrArg (Polynomial.eval (formalTail n s)) hidentity
    change g.eval (formalTail n s) = 0 at hgroot
    rw [hgroot] at heval
    have hproduct :
        PowerSeries.X ^ (n + k) *
            H.eval (formalTail n s) = 0 := by
      simpa using heval
    exact
      (mul_eq_zero.mp hproduct).resolve_left
        (pow_ne_zero _ (PowerSeries.X_ne_zero (R := K)))
  have hderivative :
      Polynomial.C (PowerSeries.X ^ (n + k)) * H.derivative =
        g.derivative := by
    calc
      Polynomial.C (PowerSeries.X ^ (n + k)) * H.derivative =
          (Polynomial.C (PowerSeries.X ^ (n + k)) * H).derivative := by
            rw [Polynomial.derivative_C_mul]
      _ = g.derivative := congrArg Polynomial.derivative hidentity
  have hderivative_eval :
      PowerSeries.X ^ (n + k) *
          H.derivative.eval (formalTail n s) =
        PowerSeries.X ^ n * f.derivative.eval s := by
    have h := congrArg (Polynomial.eval (formalTail n s)) hderivative
    rw [show g =
        scaledTaylorTransform f
          (s.trunc n : PowerSeries K) n by rfl,
      eval_derivative_scaledTaylorTransform_formalTail] at h
    simpa using h
  refine ⟨hHroot, ?_⟩
  apply mul_left_cancel₀
    (a := PowerSeries.X ^ n)
    (pow_ne_zero _ (PowerSeries.X_ne_zero (R := K)))
  calc
    PowerSeries.X ^ n *
          (PowerSeries.X ^ k *
            H.derivative.eval (formalTail n s)) =
        PowerSeries.X ^ (n + k) *
            H.derivative.eval (formalTail n s) := by
          rw [pow_add]
          ring
    _ = PowerSeries.X ^ n * f.derivative.eval s :=
      hderivative_eval

/-- The derivative relation detects a simple root after reducing the
normalized transform at `X=0`. -/
theorem simple_specialFiber_of_normalized_derivative
    (H : Polynomial (PowerSeries K))
    (s : PowerSeries K)
    (k : ℕ)
    (D : PowerSeries K)
    (hD : D ≠ 0)
    (horder : D.order.toNat = k)
    (hderivative :
      PowerSeries.X ^ k * H.derivative.eval s = D) :
    (H.derivative.map PowerSeries.constantCoeff).eval
        s.constantCoeff ≠ 0 := by
  rw [Polynomial.eval_map_apply]
  have hcoeff := congrArg (PowerSeries.coeff k) hderivative
  rw [PowerSeries.coeff_X_pow_mul'] at hcoeff
  simp only [le_refl, ↓reduceIte, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff] at hcoeff
  have hlead : PowerSeries.coeff k D ≠ 0 := by
    simpa [← horder] using PowerSeries.coeff_order hD
  rw [hcoeff]
  exact hlead

/-- Arbitrary-truncation form of one-shot finite-tail termination.  Any
truncation strictly beyond the derivative order produces a simple residual
root. -/
theorem normalizedTaylorTransform_has_simple_specialFiber_of_lt
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hroot : f.IsRoot s)
    (hD : f.derivative.eval s ≠ 0)
    (horder : (f.derivative.eval s).order.toNat = k) :
    let tail := formalTail n s
    let H :=
      normalizedTaylorTransform f
        (s.trunc n : PowerSeries K) n k
    H.IsRoot tail ∧
      (H.map PowerSeries.constantCoeff).IsRoot tail.constantCoeff ∧
      (H.derivative.map PowerSeries.constantCoeff).eval
          tail.constantCoeff ≠ 0 := by
  let tail := formalTail n s
  let H :=
    normalizedTaylorTransform f
      (s.trunc n : PowerSeries K) n k
  obtain ⟨hHroot, hHderivative⟩ :=
    normalizedTaylorTransform_root_and_derivative
      f s k n hkn hroot horder
  have hspecialRoot :
      (H.map PowerSeries.constantCoeff).IsRoot tail.constantCoeff := by
    rw [Polynomial.IsRoot, Polynomial.eval_map_apply]
    exact congrArg PowerSeries.constantCoeff hHroot
  have hsimple :
      (H.derivative.map PowerSeries.constantCoeff).eval
          tail.constantCoeff ≠ 0 :=
    simple_specialFiber_of_normalized_derivative
      H tail k (f.derivative.eval s) hD horder hHderivative
  exact ⟨hHroot, hspecialRoot, hsimple⟩

/-- One-shot finite-tail termination.

For a formal root whose `Y`-derivative is nonzero, truncate immediately after
the derivative order.  Translation by that polynomial truncation, scaling
the residual variable by `X^n`, and dividing by `X^(n+k)` produces a
normalized polynomial whose selected residual root is simple modulo `X`.
No iteration or separate Newton-polygon termination argument is needed.
-/
theorem normalizedTaylorTransform_has_simple_specialFiber
    (f : Polynomial (PowerSeries K))
    (s : PowerSeries K)
    (hroot : f.IsRoot s)
    (hD : f.derivative.eval s ≠ 0) :
    let k := (f.derivative.eval s).order.toNat
    let n := k + 1
    let tail := formalTail n s
    let H :=
      normalizedTaylorTransform f
        (s.trunc n : PowerSeries K) n k
    H.IsRoot tail ∧
      (H.map PowerSeries.constantCoeff).IsRoot tail.constantCoeff ∧
      (H.derivative.map PowerSeries.constantCoeff).eval
          tail.constantCoeff ≠ 0 := by
  let k := (f.derivative.eval s).order.toNat
  let n := k + 1
  let tail := formalTail n s
  let H :=
    normalizedTaylorTransform f
      (s.trunc n : PowerSeries K) n k
  obtain ⟨hHroot, hHderivative⟩ :=
    normalizedTaylorTransform_root_and_derivative
      f s k n (by simp [n]) hroot rfl
  have hspecialRoot :
      (H.map PowerSeries.constantCoeff).IsRoot tail.constantCoeff := by
    rw [Polynomial.IsRoot, Polynomial.eval_map_apply]
    exact congrArg PowerSeries.constantCoeff hHroot
  have hsimple :
      (H.derivative.map PowerSeries.constantCoeff).eval
          tail.constantCoeff ≠ 0 :=
    simple_specialFiber_of_normalized_derivative
      H tail k (f.derivative.eval s) hD rfl hHderivative
  exact ⟨hHroot, hspecialRoot, hsimple⟩

/-! ## Polynomial-coefficient bridge -/

/-- The same Taylor substitution before embedding parameter polynomials into
formal power series. -/
def scaledBivPolynomialTaylorTransform
    (Q : Polynomial (Polynomial K))
    (A : Polynomial K) (n : ℕ) :
    Polynomial (Polynomial K) :=
  (Polynomial.taylor A Q).comp
    (Polynomial.C (Polynomial.X ^ n) * Polynomial.X)

theorem map_scaledBivPolynomialTaylorTransform
    (Q : Polynomial (Polynomial K))
    (A : Polynomial K) (n : ℕ) :
    bivPolynomialToPowerSeriesPolynomial
        (scaledBivPolynomialTaylorTransform Q A n) =
      scaledTaylorTransform
        (bivPolynomialToPowerSeriesPolynomial Q)
        (A : PowerSeries K) n := by
  simp [bivPolynomialToPowerSeriesPolynomial,
    scaledBivPolynomialTaylorTransform, scaledTaylorTransform,
    Polynomial.taylor_apply, Polynomial.map_comp]

/-- Divisibility by a parameter monomial can be reflected from formal power
series back to honest polynomials. -/
theorem polynomial_X_pow_dvd_of_powerSeries_X_pow_dvd
    (a : Polynomial K) (m : ℕ)
    (h :
      (PowerSeries.X : PowerSeries K) ^ m ∣
        (a : PowerSeries K)) :
    (Polynomial.X : Polynomial K) ^ m ∣ a := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  have hcoeff :=
    (PowerSeries.X_pow_dvd_iff.mp h) i hi
  simpa only [Polynomial.coeff_coe] using hcoeff

/-- Exact polynomial division by the forced parameter power. -/
noncomputable def polynomialDivByXPow
    (m : ℕ) (a : Polynomial K) : Polynomial K := by
  classical
  exact if h : (Polynomial.X : Polynomial K) ^ m ∣ a then
    Classical.choose h
  else 0

theorem polynomial_X_pow_mul_divByXPow
    (m : ℕ) (a : Polynomial K)
    (h : (Polynomial.X : Polynomial K) ^ m ∣ a) :
    Polynomial.X ^ m * polynomialDivByXPow m a = a := by
  rw [polynomialDivByXPow, dif_pos h]
  exact (Classical.choose_spec h).symm

/-- The honest bivariate polynomial obtained by coefficientwise exact
division of the translated transform. -/
noncomputable def normalizedBivPolynomialTaylorTransform
    (Q : Polynomial (Polynomial K))
    (A : Polynomial K) (n k : ℕ) :
    Polynomial (Polynomial K) :=
  ∑ i ∈ Finset.range (Q.natDegree + 1),
    Polynomial.monomial i
      (polynomialDivByXPow (n + k)
        ((scaledBivPolynomialTaylorTransform Q A n).coeff i))

theorem coeff_normalizedBivPolynomialTaylorTransform_of_le
    (Q : Polynomial (Polynomial K))
    (A : Polynomial K) (n k : ℕ)
    {i : ℕ} (hi : i ≤ Q.natDegree) :
    (normalizedBivPolynomialTaylorTransform Q A n k).coeff i =
      polynomialDivByXPow (n + k)
        ((scaledBivPolynomialTaylorTransform Q A n).coeff i) := by
  classical
  simp [normalizedBivPolynomialTaylorTransform,
    Polynomial.coeff_monomial, hi]

theorem coeff_normalizedBivPolynomialTaylorTransform_of_lt
    (Q : Polynomial (Polynomial K))
    (A : Polynomial K) (n k : ℕ)
    {i : ℕ} (hi : Q.natDegree < i) :
    (normalizedBivPolynomialTaylorTransform Q A n k).coeff i = 0 := by
  classical
  simp [normalizedBivPolynomialTaylorTransform,
    Polynomial.coeff_monomial, Nat.not_le_of_gt hi]

theorem C_X_pow_mul_normalizedBivPolynomialTaylorTransform
    (Q : Polynomial (Polynomial K))
    (A : Polynomial K) (n k : ℕ)
    (hdiv :
      ∀ i : ℕ, i ≤ Q.natDegree →
        (Polynomial.X : Polynomial K) ^ (n + k) ∣
          (scaledBivPolynomialTaylorTransform Q A n).coeff i) :
    Polynomial.C (Polynomial.X ^ (n + k)) *
        normalizedBivPolynomialTaylorTransform Q A n k =
      scaledBivPolynomialTaylorTransform Q A n := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_C_mul]
  by_cases hi : i ≤ Q.natDegree
  · rw [coeff_normalizedBivPolynomialTaylorTransform_of_le Q A n k hi]
    exact polynomial_X_pow_mul_divByXPow _ _ (hdiv i hi)
  · have hlt : Q.natDegree < i := Nat.lt_of_not_ge hi
    rw [coeff_normalizedBivPolynomialTaylorTransform_of_lt Q A n k hlt]
    have htaylor :
        (Polynomial.taylor A Q).coeff i = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa [Polynomial.natDegree_taylor] using hlt
    rw [show
        (scaledBivPolynomialTaylorTransform Q A n).coeff i =
          (Polynomial.taylor A Q).coeff i *
            (Polynomial.X ^ n) ^ i by
        exact Polynomial.comp_C_mul_X_coeff,
      htaylor]
    simp

/-- A formal root with derivative order `k<n` forces polynomial, not merely
formal-series, divisibility of the finite Taylor transform. -/
theorem polynomial_X_pow_add_dvd_scaledTaylor_coeff_of_formalRoot
    (Q : Polynomial (Polynomial K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hroot : (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (horder :
      ((bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s).order.toNat =
        k) :
    ∀ i : ℕ,
      (Polynomial.X : Polynomial K) ^ (n + k) ∣
        (scaledBivPolynomialTaylorTransform
          Q (s.trunc n) n).coeff i := by
  intro i
  have hformal :
      (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
        (scaledTaylorTransform
          (bivPolynomialToPowerSeriesPolynomial Q)
          (s.trunc n : PowerSeries K) n).coeff i :=
    X_pow_add_dvd_coeff_scaledTaylorTransform
      (bivPolynomialToPowerSeriesPolynomial Q)
      s k n hkn horder.ge hroot i
  have hmap :=
    congrArg (fun p : Polynomial (PowerSeries K) => p.coeff i)
      (map_scaledBivPolynomialTaylorTransform
        Q (s.trunc n) n)
  have hcoe :
      ((scaledBivPolynomialTaylorTransform
          Q (s.trunc n) n).coeff i : PowerSeries K) =
        (scaledTaylorTransform
          (bivPolynomialToPowerSeriesPolynomial Q)
          (s.trunc n : PowerSeries K) n).coeff i := by
    simpa [bivPolynomialToPowerSeriesPolynomial] using hmap
  apply polynomial_X_pow_dvd_of_powerSeries_X_pow_dvd
  rw [hcoe]
  exact hformal

theorem normalizedBivPolynomialTaylorTransform_identity_of_formalRoot
    (Q : Polynomial (Polynomial K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hroot : (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (horder :
      ((bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s).order.toNat =
        k) :
    Polynomial.C (Polynomial.X ^ (n + k)) *
        normalizedBivPolynomialTaylorTransform
          Q (s.trunc n) n k =
      scaledBivPolynomialTaylorTransform Q (s.trunc n) n := by
  apply C_X_pow_mul_normalizedBivPolynomialTaylorTransform
  intro i hi
  exact
    polynomial_X_pow_add_dvd_scaledTaylor_coeff_of_formalRoot
      Q s k n hkn hroot horder i

/-- Exact polynomial normalization agrees with formal-series normalization
after embedding coefficients. -/
theorem map_normalizedBivPolynomialTaylorTransform_of_formalRoot
    (Q : Polynomial (Polynomial K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hroot : (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (horder :
      ((bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s).order.toNat =
        k) :
    bivPolynomialToPowerSeriesPolynomial
        (normalizedBivPolynomialTaylorTransform
          Q (s.trunc n) n k) =
      normalizedTaylorTransform
        (bivPolynomialToPowerSeriesPolynomial Q)
        (s.trunc n : PowerSeries K) n k := by
  let f := bivPolynomialToPowerSeriesPolynomial Q
  let A : PowerSeries K := (s.trunc n : PowerSeries K)
  let H := normalizedTaylorTransform f A n k
  let R :=
    normalizedBivPolynomialTaylorTransform Q (s.trunc n) n k
  let g := scaledTaylorTransform f A n
  have hRidentity :
      Polynomial.C (Polynomial.X ^ (n + k)) * R =
        scaledBivPolynomialTaylorTransform Q (s.trunc n) n :=
    normalizedBivPolynomialTaylorTransform_identity_of_formalRoot
      Q s k n hkn hroot horder
  have hmapR :
      Polynomial.C (PowerSeries.X ^ (n + k)) *
          bivPolynomialToPowerSeriesPolynomial R =
        g := by
    have h :=
      congrArg
        (Polynomial.map Polynomial.coeToPowerSeries.ringHom)
        hRidentity
    have hscaled :
        Polynomial.map Polynomial.coeToPowerSeries.ringHom
            (scaledBivPolynomialTaylorTransform Q (s.trunc n) n) =
          g := by
      simpa [bivPolynomialToPowerSeriesPolynomial, g, f, A] using
        (map_scaledBivPolynomialTaylorTransform
          Q (s.trunc n) n)
    rw [hscaled] at h
    simpa [bivPolynomialToPowerSeriesPolynomial, R] using h
  have hdiv :
      ∀ i : ℕ, i ≤ f.natDegree →
        (PowerSeries.X : PowerSeries K) ^ (n + k) ∣
          g.coeff i := by
    intro i _hi
    exact
      X_pow_add_dvd_coeff_scaledTaylorTransform
        f s k n hkn horder.ge hroot i
  have hmapH :
      Polynomial.C (PowerSeries.X ^ (n + k)) * H = g :=
    C_X_pow_mul_normalizedTaylorTransform f A n k hdiv
  apply mul_left_cancel₀
    (a := Polynomial.C (PowerSeries.X ^ (n + k)))
    (Polynomial.C_ne_zero.mpr
      (pow_ne_zero _ (PowerSeries.X_ne_zero (R := K))))
  exact hmapR.trans hmapH.symm

/-- Generic evaluation of an outer polynomial in `Y` with polynomial
coefficients in `X`. -/
def bivEvalAt
    (Q : Polynomial (Polynomial K)) (x y : K) : K :=
  Polynomial.eval₂ (Polynomial.evalRingHom x) y Q

theorem bivEvalAt_scaledBivPolynomialTaylorTransform
    (Q : Polynomial (Polynomial K))
    (A : Polynomial K) (n : ℕ) (x z : K) :
    bivEvalAt (scaledBivPolynomialTaylorTransform Q A n) x z =
      bivEvalAt Q x (A.eval x + x ^ n * z) := by
  have hCX :
      Polynomial.eval₂ (Polynomial.evalRingHom x) z
          ((Polynomial.C Polynomial.X :
            Polynomial (Polynomial K)) ^ n) =
        x ^ n := by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_C]
    simp
  simp [bivEvalAt, scaledBivPolynomialTaylorTransform,
    Polynomial.taylor_apply, Polynomial.eval₂_comp, hCX,
    add_comm, mul_comm]

/-- Evaluation form of the exact polynomial transform identity. -/
theorem bivEvalAt_normalizedBivPolynomialTaylorTransform_of_formalRoot
    (Q : Polynomial (Polynomial K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hroot : (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (horder :
      ((bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s).order.toNat =
        k)
    (x z : K) :
    bivEvalAt Q x ((s.trunc n).eval x + x ^ n * z) =
      x ^ (n + k) *
        bivEvalAt
          (normalizedBivPolynomialTaylorTransform
            Q (s.trunc n) n k) x z := by
  let R :=
    normalizedBivPolynomialTaylorTransform
      Q (s.trunc n) n k
  have hid :=
    normalizedBivPolynomialTaylorTransform_identity_of_formalRoot
      Q s k n hkn hroot horder
  have heval :=
    congrArg
      (Polynomial.eval₂ (Polynomial.evalRingHom x) z) hid
  have hCX :
      Polynomial.eval₂ (Polynomial.evalRingHom x) z
          ((Polynomial.C Polynomial.X :
            Polynomial (Polynomial K)) ^ (n + k)) =
        x ^ (n + k) := by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_C]
    simp
  calc
    bivEvalAt Q x ((s.trunc n).eval x + x ^ n * z) =
        bivEvalAt
          (scaledBivPolynomialTaylorTransform Q (s.trunc n) n)
          x z :=
      (bivEvalAt_scaledBivPolynomialTaylorTransform
        Q (s.trunc n) n x z).symm
    _ =
        Polynomial.eval₂ (Polynomial.evalRingHom x) z
          (Polynomial.C (Polynomial.X ^ (n + k)) * R) := by
      exact heval.symm
    _ = x ^ (n + k) * bivEvalAt R x z := by
      simp [bivEvalAt, hCX]

/-- Concrete bivariate-polynomial certificate produced by the one-shot
finite-tail argument. -/
theorem normalizedBivPolynomialTaylorTransform_has_simple_specialFiber
    (Q : Polynomial (Polynomial K))
    (s : PowerSeries K)
    (hroot : (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (hD :
      (bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s ≠ 0) :
    let f := bivPolynomialToPowerSeriesPolynomial Q
    let k := (f.derivative.eval s).order.toNat
    let n := k + 1
    let A := s.trunc n
    let tail := formalTail n s
    let c := tail.constantCoeff
    let R := normalizedBivPolynomialTaylorTransform Q A n k
    A.eval 0 = s.constantCoeff ∧
      (∀ x z : K,
        bivEvalAt Q x (A.eval x + x ^ n * z) =
          x ^ (n + k) * bivEvalAt R x z) ∧
      bivEvalAt R 0 c = 0 ∧
      bivEvalAt R.derivative 0 c ≠ 0 := by
  let f := bivPolynomialToPowerSeriesPolynomial Q
  let k := (f.derivative.eval s).order.toNat
  let n := k + 1
  let A := s.trunc n
  let tail := formalTail n s
  let c := tail.constantCoeff
  let R := normalizedBivPolynomialTaylorTransform Q A n k
  let H :=
    normalizedTaylorTransform f
      (A : PowerSeries K) n k
  obtain ⟨_hHroot, hspecialRoot, hsimple⟩ :=
    normalizedTaylorTransform_has_simple_specialFiber
      f s hroot hD
  have hspecialRootH :
      (H.map PowerSeries.constantCoeff).IsRoot c := by
    simpa [H, f, k, n, A, tail, c] using hspecialRoot
  have hsimpleH :
      (H.derivative.map PowerSeries.constantCoeff).eval c ≠ 0 := by
    simpa [H, f, k, n, A, tail, c] using hsimple
  have hmap : bivPolynomialToPowerSeriesPolynomial R = H := by
    exact
      map_normalizedBivPolynomialTaylorTransform_of_formalRoot
        Q s k n (by simp [n]) hroot rfl
  have hA0 : A.eval 0 = s.constantCoeff := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      show A = s.trunc n by rfl,
      PowerSeries.coeff_trunc, if_pos (by simp [n]),
      PowerSeries.coeff_zero_eq_constantCoeff]
  have htransform :
      ∀ x z : K,
        bivEvalAt Q x (A.eval x + x ^ n * z) =
          x ^ (n + k) * bivEvalAt R x z := by
    intro x z
    exact
      bivEvalAt_normalizedBivPolynomialTaylorTransform_of_formalRoot
        Q s k n (by simp [n]) hroot rfl x z
  have hhom :
      PowerSeries.constantCoeff.comp
          Polynomial.coeToPowerSeries.ringHom =
        Polynomial.evalRingHom (0 : K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp [← PowerSeries.coeff_zero_eq_constantCoeff]
  have hspecialRoot' : bivEvalAt R 0 c = 0 := by
    rw [Polynomial.IsRoot] at hspecialRootH
    rw [← hmap] at hspecialRootH
    rw [bivPolynomialToPowerSeriesPolynomial,
      Polynomial.map_map, hhom, Polynomial.eval_map] at hspecialRootH
    exact hspecialRootH
  have hsimple' : bivEvalAt R.derivative 0 c ≠ 0 := by
    rw [← hmap] at hsimpleH
    rw [bivPolynomialToPowerSeriesPolynomial,
      Polynomial.derivative_map, Polynomial.map_map,
      hhom, Polynomial.eval_map] at hsimpleH
    exact hsimpleH
  exact ⟨hA0, htransform, hspecialRoot', hsimple'⟩

/-- Concrete bivariate version with an arbitrary truncation exponent strictly
beyond the derivative order. -/
theorem
    normalizedBivPolynomialTaylorTransform_has_simple_specialFiber_of_lt
    (Q : Polynomial (Polynomial K))
    (s : PowerSeries K)
    (k n : ℕ)
    (hkn : k < n)
    (hroot : (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (hD :
      (bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s ≠ 0)
    (horder :
      ((bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s).order.toNat =
        k) :
    let A := s.trunc n
    let tail := formalTail n s
    let c := tail.constantCoeff
    let R := normalizedBivPolynomialTaylorTransform Q A n k
    A.eval 0 = s.constantCoeff ∧
      (∀ x z : K,
        bivEvalAt Q x (A.eval x + x ^ n * z) =
          x ^ (n + k) * bivEvalAt R x z) ∧
      bivEvalAt R 0 c = 0 ∧
      bivEvalAt R.derivative 0 c ≠ 0 := by
  let f := bivPolynomialToPowerSeriesPolynomial Q
  let A := s.trunc n
  let tail := formalTail n s
  let c := tail.constantCoeff
  let R := normalizedBivPolynomialTaylorTransform Q A n k
  let H :=
    normalizedTaylorTransform f
      (A : PowerSeries K) n k
  obtain ⟨_hHroot, hspecialRoot, hsimple⟩ :=
    normalizedTaylorTransform_has_simple_specialFiber_of_lt
      f s k n hkn hroot hD horder
  have hspecialRootH :
      (H.map PowerSeries.constantCoeff).IsRoot c := by
    simpa [H, f, A, tail, c] using hspecialRoot
  have hsimpleH :
      (H.derivative.map PowerSeries.constantCoeff).eval c ≠ 0 := by
    simpa [H, f, A, tail, c] using hsimple
  have hmap : bivPolynomialToPowerSeriesPolynomial R = H :=
    map_normalizedBivPolynomialTaylorTransform_of_formalRoot
      Q s k n hkn hroot horder
  have hA0 : A.eval 0 = s.constantCoeff := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      show A = s.trunc n by rfl,
      PowerSeries.coeff_trunc, if_pos (Nat.zero_lt_of_lt hkn),
      PowerSeries.coeff_zero_eq_constantCoeff]
  have htransform :
      ∀ x z : K,
        bivEvalAt Q x (A.eval x + x ^ n * z) =
          x ^ (n + k) * bivEvalAt R x z :=
    fun x z =>
      bivEvalAt_normalizedBivPolynomialTaylorTransform_of_formalRoot
        Q s k n hkn hroot horder x z
  have hhom :
      PowerSeries.constantCoeff.comp
          Polynomial.coeToPowerSeries.ringHom =
        Polynomial.evalRingHom (0 : K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp [← PowerSeries.coeff_zero_eq_constantCoeff]
  have hspecialRoot' : bivEvalAt R 0 c = 0 := by
    rw [Polynomial.IsRoot] at hspecialRootH
    rw [← hmap] at hspecialRootH
    rw [bivPolynomialToPowerSeriesPolynomial,
      Polynomial.map_map, hhom, Polynomial.eval_map] at hspecialRootH
    exact hspecialRootH
  have hsimple' : bivEvalAt R.derivative 0 c ≠ 0 := by
    rw [← hmap] at hsimpleH
    rw [bivPolynomialToPowerSeriesPolynomial,
      Polynomial.derivative_map, Polynomial.map_map,
      hhom, Polynomial.eval_map] at hsimpleH
    exact hsimpleH
  exact ⟨hA0, htransform, hspecialRoot', hsimple'⟩

/-- Order of the derivative along a selected formal branch. -/
def finiteTailDerivativeOrder
    (Q : Polynomial (Polynomial K)) (s : PowerSeries K) : ℕ :=
  ((bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s).order.toNat

/-- The first truncation exponent strictly beyond the derivative order. -/
def finiteTailExponent
    (Q : Polynomial (Polynomial K)) (s : PowerSeries K) : ℕ :=
  finiteTailDerivativeOrder Q s + 1

/-- Polynomial part of the selected formal branch retained for the final
implicit-function step. -/
def finiteTailTruncation
    (Q : Polynomial (Polynomial K)) (s : PowerSeries K) : Polynomial K :=
  s.trunc (finiteTailExponent Q s)

/-- Constant term of the remaining normalized formal tail. -/
def finiteTailResidualRoot
    (Q : Polynomial (Polynomial K)) (s : PowerSeries K) : K :=
  (formalTail (finiteTailExponent Q s) s).constantCoeff

/-- Honest bivariate residual polynomial with a simple special-fiber root. -/
noncomputable def finiteTailResidualPolynomial
    (Q : Polynomial (Polynomial K)) (s : PowerSeries K) :
    Polynomial (Polynomial K) :=
  normalizedBivPolynomialTaylorTransform Q
    (finiteTailTruncation Q s)
    (finiteTailExponent Q s)
    (finiteTailDerivativeOrder Q s)

/-- Named form of the concrete finite-tail certificate. -/
theorem finiteTailResidualPolynomial_spec
    (Q : Polynomial (Polynomial K))
    (s : PowerSeries K)
    (hroot : (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (hD :
      (bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s ≠ 0) :
    (finiteTailTruncation Q s).eval 0 = s.constantCoeff ∧
      (∀ x z : K,
        bivEvalAt Q x
            ((finiteTailTruncation Q s).eval x +
              x ^ (finiteTailExponent Q s) * z) =
          x ^ (finiteTailExponent Q s +
              finiteTailDerivativeOrder Q s) *
            bivEvalAt (finiteTailResidualPolynomial Q s) x z) ∧
      bivEvalAt (finiteTailResidualPolynomial Q s) 0
          (finiteTailResidualRoot Q s) = 0 ∧
      bivEvalAt (finiteTailResidualPolynomial Q s).derivative 0
          (finiteTailResidualRoot Q s) ≠ 0 := by
  simpa [finiteTailDerivativeOrder, finiteTailExponent,
    finiteTailTruncation, finiteTailResidualRoot,
    finiteTailResidualPolynomial] using
      (normalizedBivPolynomialTaylorTransform_has_simple_specialFiber
        Q s hroot hD)


end CurveSelection.TerminationScratch
end Math
