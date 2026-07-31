/- Production Newton--Puiseux implementation used by analytic curve
selection. -/
import Math.RamifiedWeierstrass
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

noncomputable section

open Polynomial
open scoped PowerSeries.WithPiTopology

namespace Math

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- A unit formal power series over an algebraically closed characteristic-zero
field has an `m`-th root.  This is the simple-root Hensel step used in the
binomial case of Newton--Puiseux. -/
theorem exists_pow_eq_of_constantCoeff_ne_zero
    (u : PowerSeries K) (hu : u.constantCoeff ≠ 0)
    {m : ℕ} (hm : 0 < m) :
    ∃ v : PowerSeries K, v ^ m = u := by
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  obtain ⟨c, hc⟩ :=
    IsAlgClosed.exists_pow_nat_eq u.constantCoeff hm
  have hc0 : c ≠ 0 := by
    intro h
    apply hu
    rw [← hc, h, zero_pow (Nat.ne_of_gt hm)]
  let f : Polynomial (PowerSeries K) :=
    Polynomial.X ^ m - Polynomial.C u
  have hf : f.Monic := by
    simpa [f] using Polynomial.monic_X_pow_sub_C u (Nat.ne_of_gt hm)
  have heval :
      f.eval (PowerSeries.C c) ∈
        IsLocalRing.maximalIdeal (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
      PowerSeries.X_dvd_iff]
    simp [f, hc]
  have hderiv :
      IsUnit
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries K))
          (f.derivative.eval (PowerSeries.C c))) := by
    apply IsUnit.map
    have hunit :
        IsUnit
          (Polynomial.eval (PowerSeries.C c)
            (Polynomial.derivative
              ((Polynomial.X :
                Polynomial (PowerSeries K)) ^ m))) := by
      rw [PowerSeries.isUnit_iff_constantCoeff,
        Polynomial.derivative_X_pow]
      simp only [Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, map_mul,
        PowerSeries.constantCoeff_C, map_pow]
      exact isUnit_iff_ne_zero.mpr
        (mul_ne_zero
          (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
          (pow_ne_zero _ hc0))
    simpa [f] using hunit
  obtain ⟨v, hv, _⟩ :=
    HenselianRing.is_henselian f hf (PowerSeries.C c) heval hderiv
  exact ⟨v, sub_eq_zero.mp (by simpa [f, Polynomial.IsRoot] using hv)⟩

/-- Every formal series acquires an `m`-th root after the parameter
ramification `X ↦ X ^ m`. -/
theorem exists_pow_eq_expand
    (a : PowerSeries K) {m : ℕ} (hm : 0 < m) :
    ∃ s : PowerSeries K,
      s ^ m = PowerSeries.expand m (Nat.ne_of_gt hm) a := by
  by_cases ha : a = 0
  · subst a
    exact ⟨0, by simp [Nat.ne_of_gt hm]⟩
  let d : ℕ := a.order.toNat
  let u : PowerSeries K := PowerSeries.divXPowOrder a
  have hu0 : u.constantCoeff ≠ 0 := by
    exact
      (not_congr
        (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff
          (f := a))).mpr (by simpa [u] using ha)
  have huexp0 :
      (PowerSeries.expand m (Nat.ne_of_gt hm) u).constantCoeff ≠ 0 := by
    simpa using hu0
  obtain ⟨v, hv⟩ :=
    exists_pow_eq_of_constantCoeff_ne_zero
      (PowerSeries.expand m (Nat.ne_of_gt hm) u) huexp0 hm
  refine ⟨PowerSeries.X ^ d * v, ?_⟩
  rw [mul_pow, hv]
  rw [← pow_mul]
  change
    PowerSeries.X ^ (d * m) *
        PowerSeries.expand m (Nat.ne_of_gt hm) u =
      PowerSeries.expand m (Nat.ne_of_gt hm) a
  rw [Nat.mul_comm d m, pow_mul]
  change
    (PowerSeries.X ^ m) ^ d *
        PowerSeries.expand m (Nat.ne_of_gt hm) u =
      PowerSeries.expand m (Nat.ne_of_gt hm) a
  rw [← PowerSeries.expand_X m (Nat.ne_of_gt hm),
    ← map_pow, ← map_mul]
  exact congrArg (PowerSeries.expand m (Nat.ne_of_gt hm))
    (PowerSeries.X_pow_order_mul_divXPowOrder (f := a))

/-- Formal Newton--Puiseux for a binomial: `Y ^ m - a(X)` has a root
after the single ramification `X ↦ X ^ m`. -/
theorem exists_ramifiedRoot_X_pow_sub_C
    (a : PowerSeries K) {m : ℕ} (hm : 0 < m) :
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial p hp
        (Polynomial.X ^ m - Polynomial.C a)).IsRoot s := by
  let hp : m ≠ 0 := Nat.ne_of_gt hm
  obtain ⟨s, hs⟩ := exists_pow_eq_expand a hm
  refine ⟨m, hp, s, ?_⟩
  simpa [ramifyPowerSeriesPolynomial, Polynomial.IsRoot] using
    sub_eq_zero.mpr hs

end Math

namespace Math
namespace CurveSelection.PuiseuxDegreeScratch

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- The quadratic formula in a commutative ring in which two is invertible. -/
theorem quadratic_formula
    (b c d half : PowerSeries K)
    (hhalf : (2 : PowerSeries K) * half = 1)
    (hd : d ^ 2 = b ^ 2 - 4 * c) :
    (half * (-b + d)) ^ 2 +
        b * (half * (-b + d)) + c = 0 := by
  have hh : (2 : PowerSeries K) * half ^ 2 = half := by
    calc
      (2 : PowerSeries K) * half ^ 2 =
          ((2 : PowerSeries K) * half) * half := by ring
      _ = half := by rw [hhalf, one_mul]
  have hfour : (4 : PowerSeries K) * half ^ 2 = 1 := by
    calc
      (4 : PowerSeries K) * half ^ 2 =
          2 * ((2 : PowerSeries K) * half ^ 2) := by ring
      _ = 2 * half := by rw [hh]
      _ = 1 := hhalf
  calc
    (half * (-b + d)) ^ 2 +
          b * (half * (-b + d)) + c =
        half ^ 2 *
          ((-b + d) ^ 2 + 2 * b * (-b + d) + 4 * c) := by
            linear_combination
              -(b * (-b + d)) * hh - c * hfour
    _ = half ^ 2 * (d ^ 2 - b ^ 2 + 4 * c) := by ring
    _ = 0 := by rw [hd]; ring

/--
Every monic quadratic over formal power series has a formal root after the
single ramification `X ↦ X²`.
-/
theorem exists_ramifiedRoot_quadratic
    (b c : PowerSeries K) :
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial p hp
        (Polynomial.X ^ 2 +
          Polynomial.C b * Polynomial.X + Polynomial.C c)).IsRoot s := by
  let hp : (2 : ℕ) ≠ 0 := by norm_num
  let B : PowerSeries K := PowerSeries.expand 2 hp b
  let C : PowerSeries K := PowerSeries.expand 2 hp c
  let discriminant : PowerSeries K := b ^ 2 - 4 * c
  obtain ⟨d, hd⟩ :=
    exists_pow_eq_expand discriminant (m := 2) (by norm_num)
  let half : PowerSeries K := PowerSeries.C ((2 : K)⁻¹)
  have hhalf : (2 : PowerSeries K) * half = 1 := by
    change
      PowerSeries.C (2 : K) * PowerSeries.C ((2 : K)⁻¹) =
        PowerSeries.C (1 : K)
    rw [← map_mul]
    congr 1
    exact mul_inv_cancel₀ (by norm_num)
  let s : PowerSeries K := half * (-B + d)
  have hdisc : d ^ 2 = B ^ 2 - 4 * C := by
    rw [hd]
    simp only [discriminant, map_sub, map_pow, map_mul,
      map_ofNat, B, C]
  have hs : s ^ 2 + B * s + C = 0 := by
    exact quadratic_formula B C d half hhalf hdisc
  refine ⟨2, hp, s, ?_⟩
  simpa [ramifyPowerSeriesPolynomial, Polynomial.IsRoot, B, C] using hs

/-- A monic polynomial of degree two has the standard quadratic shape. -/
theorem monic_natDegree_two_eq
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (hdegree : f.natDegree = 2) :
    f = Polynomial.X ^ 2 +
      Polynomial.C (f.coeff 1) * Polynomial.X +
        Polynomial.C (f.coeff 0) := by
  apply Polynomial.ext
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp
  by_cases hn2 : n = 2
  · subst n
    have hlead : f.coeff 2 = 1 := by
      simpa [hdegree] using hf.coeff_natDegree
    simp [hlead]
  have hn : f.natDegree < n := by omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  have h1n : 1 ≠ n := Ne.symm hn1
  simp only [coeff_add, coeff_X_pow, coeff_C_mul]
  rw [Polynomial.coeff_C, if_neg hn0]
  simp [hn2, Polynomial.coeff_X, h1n]

/-- Full ramified-root property for every monic quadratic. -/
theorem exists_ramifiedRoot_of_monic_natDegree_two
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (hdegree : f.natDegree = 2) :
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial p hp f).IsRoot s := by
  rw [monic_natDegree_two_eq f hf hdegree]
  exact exists_ramifiedRoot_quadratic (f.coeff 1) (f.coeff 0)

/-- A monic linear polynomial already has a power-series root. -/
theorem exists_ramifiedRoot_of_monic_natDegree_one
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (hdegree : f.natDegree = 1) :
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial p hp f).IsRoot s := by
  have hshape := hf.eq_X_add_C hdegree
  let s : PowerSeries K := -(f.coeff 0)
  refine ⟨1, one_ne_zero, s, ?_⟩
  rw [hshape]
  simp [ramifyPowerSeriesPolynomial, Polynomial.IsRoot, s]

/--
Newton--Puiseux root extraction is complete in outer degrees one and two.
-/
theorem exists_ramifiedRoot_of_monic_natDegree_le_two
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (hpositive : 0 < f.natDegree) (hdegree : f.natDegree ≤ 2) :
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial p hp f).IsRoot s := by
  have hcases : f.natDegree = 1 ∨ f.natDegree = 2 := by omega
  rcases hcases with hdegree_one | hdegree_two
  · exact exists_ramifiedRoot_of_monic_natDegree_one f hf hdegree_one
  · exact exists_ramifiedRoot_of_monic_natDegree_two f hf hdegree_two

/-- Over formal power series, a monic quadratic with one root already
splits.  This is the one-step degree drop used after the quadratic formula. -/
theorem splits_of_monic_natDegree_two_of_isRoot
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (hdegree : f.natDegree = 2) (s : PowerSeries K)
    (hs : f.IsRoot s) :
    f.Splits := by
  let lin : Polynomial (PowerSeries K) :=
    Polynomial.X - Polynomial.C s
  let q : Polynomial (PowerSeries K) := f /ₘ lin
  have hlin_monic : lin.Monic := by
    simpa [lin] using Polynomial.monic_X_sub_C s
  have hfactor : lin * q = f := by
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hs
  have hdegree_le : lin.degree ≤ f.degree := by
    exact Polynomial.degree_le_of_dvd
      ⟨q, hfactor.symm⟩ hf.ne_zero
  have hq_monic : q.Monic := by
    rw [Polynomial.Monic,
      Polynomial.leadingCoeff_divByMonic_of_monic hlin_monic hdegree_le]
    exact hf
  have hq_degree : q.natDegree = 1 := by
    change (f /ₘ lin).natDegree = 1
    rw [Polynomial.natDegree_divByMonic f hlin_monic, hdegree]
    simp [lin]
  rw [← hfactor]
  exact (Polynomial.Splits.X_sub_C s).mul
    (Polynomial.Splits.of_natDegree_le_one_of_monic hq_degree.le hq_monic)

/-- Every monic polynomial of outer degree at most two splits after a finite
ramification of the parameter. -/
theorem hasRamifiedPowerSeriesSplitting_of_monic_natDegree_le_two
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (hdegree : f.natDegree ≤ 2) :
    HasRamifiedPowerSeriesSplitting f := by
  by_cases hzero : f.natDegree = 0
  · have hf_one : f = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero hf hzero
    rw [hf_one]
    exact HasRamifiedPowerSeriesSplitting.of_splits Polynomial.Splits.one
  have hpositive : 0 < f.natDegree := Nat.pos_of_ne_zero hzero
  obtain ⟨p, hp, s, hs⟩ :=
    exists_ramifiedRoot_of_monic_natDegree_le_two
      f hf hpositive hdegree
  refine ⟨p, hp, ?_⟩
  let F := ramifyPowerSeriesPolynomial p hp f
  have hF_monic : F.Monic := hf.map _
  have hF_degree : F.natDegree = f.natDegree := hf.natDegree_map _
  have hcases : f.natDegree = 1 ∨ f.natDegree = 2 := by omega
  rcases hcases with hdegree_one | hdegree_two
  · exact Polynomial.Splits.of_natDegree_le_one_of_monic
      (hF_degree.trans hdegree_one).le hF_monic
  · exact splits_of_monic_natDegree_two_of_isRoot
      F hF_monic (hF_degree.trans hdegree_two) s hs

/--
The regular Hensel branch of Newton--Puiseux: a simple root of the
constant-coefficient reduction lifts to an honest formal power-series root,
without any ramification.
-/
theorem exists_powerSeries_root_of_simple_constant_root
    (f : Polynomial (PowerSeries K)) (hf : f.Monic) (c : K)
    (hroot :
      (f.map PowerSeries.constantCoeff).eval c = 0)
    (hsimple :
      (f.derivative.map PowerSeries.constantCoeff).eval c ≠ 0) :
    ∃ s : PowerSeries K, f.IsRoot s := by
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have heval :
      f.eval (PowerSeries.C c) ∈
        IsLocalRing.maximalIdeal (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
      PowerSeries.X_dvd_iff]
    rw [← Polynomial.eval_map_apply]
    simpa using hroot
  have hderiv :
      IsUnit
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries K))
          (f.derivative.eval (PowerSeries.C c))) := by
    apply IsUnit.map
    rw [PowerSeries.isUnit_iff_constantCoeff]
    apply isUnit_iff_ne_zero.mpr
    rw [← Polynomial.eval_map_apply]
    simpa using hsimple
  obtain ⟨s, hs, _⟩ :=
    HenselianRing.is_henselian f hf (PowerSeries.C c) heval hderiv
  exact ⟨s, hs⟩

/--
In particular, a monic polynomial whose reduction has a simple root has the
ramified-root property with ramification index one.
-/
theorem exists_ramifiedRoot_of_simple_constant_root
    (f : Polynomial (PowerSeries K)) (hf : f.Monic) (c : K)
    (hroot :
      (f.map PowerSeries.constantCoeff).eval c = 0)
    (hsimple :
      (f.derivative.map PowerSeries.constantCoeff).eval c ≠ 0) :
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial p hp f).IsRoot s := by
  obtain ⟨s, hs⟩ :=
    exists_powerSeries_root_of_simple_constant_root
      f hf c hroot hsimple
  refine ⟨1, one_ne_zero, s, ?_⟩
  simpa [ramifyPowerSeriesPolynomial] using hs

/--
A centered root of the distinguished factor in a Weierstrass factorization
is a root of the original polynomial.  This is the root-transfer step needed
after a Newton translation produces a lower-degree Weierstrass factor.
-/
theorem isRoot_of_isWeierstrassFactorization
    (g f : Polynomial (PowerSeries K))
    (h : PowerSeries (PowerSeries K))
    (H :
      (g : PowerSeries (PowerSeries K)).IsWeierstrassFactorization f h)
    (s : PowerSeries K) (hs0 : s.constantCoeff = 0)
    (hs : f.IsRoot s) :
    g.IsRoot s := by
  letI : UniformSpace K := ⊥
  have hsub : PowerSeries.HasSubst s :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hs0
  have heval : PowerSeries.HasEval s := hsub.hasEval
  have heq := congrArg (PowerSeries.aeval heval) H.eq_mul
  rw [map_mul, PowerSeries.aeval_coe, PowerSeries.aeval_coe] at heq
  have hs' : f.eval s = 0 := hs
  have hs'' :
      f.eval₂ (algebraMap (PowerSeries K) (PowerSeries K)) s = 0 := by
    simpa using hs'
  rw [Polynomial.aeval_def, Polynomial.aeval_def] at heq
  rw [hs'', zero_mul] at heq
  simpa using heq

/-- Ramifying the coefficient parameter commutes with translation of the
outer variable by a constant from the ground field. -/
theorem ramify_comp_X_add_C_constant
    (p : ℕ) (hp : p ≠ 0)
    (g : Polynomial (PowerSeries K)) (c : K) :
    ramifyPowerSeriesPolynomial p hp
        (g.comp
          (Polynomial.X +
            Polynomial.C (PowerSeries.C c))) =
      (ramifyPowerSeriesPolynomial p hp g).comp
        (Polynomial.X +
          Polynomial.C (PowerSeries.C c)) := by
  unfold ramifyPowerSeriesPolynomial
  rw [Polynomial.map_comp]
  congr 1
  simp [PowerSeries.expand_C]

/-- Ramification of an outer polynomial agrees with ramification of its
coercion to an iterated formal power series. -/
theorem ramifyIteratedPowerSeries_coe
    (p : ℕ) (hp : p ≠ 0)
    (g : Polynomial (PowerSeries K)) :
    ramifyIteratedPowerSeries p hp
        (g : PowerSeries (PowerSeries K)) =
      (ramifyPowerSeriesPolynomial p hp g :
        PowerSeries (PowerSeries K)) := by
  simp [ramifyIteratedPowerSeries, ramifyPowerSeriesPolynomial,
    Polynomial.polynomial_map_coe]

/--
The strict degree-drop induction step in the Newton--Puiseux proof.

After translating by a residue-field root `c`, assume that Weierstrass
preparation sees a positive outer order strictly below the original degree.
If ramified roots are already available in all smaller degrees, then the
original polynomial has a ramified root.
-/
theorem exists_ramifiedRoot_of_weierstrass_order_drop
    (g : Polynomial (PowerSeries K)) (hg : g.Monic) (c : K)
    (hred :
      ((g.comp
          (Polynomial.X +
            Polynomial.C (PowerSeries.C c)) :
          Polynomial (PowerSeries K)) :
        PowerSeries (PowerSeries K)).map
          (IsLocalRing.residue (PowerSeries K)) ≠ 0)
    (horder_pos :
      0 <
        (((g.comp
            (Polynomial.X +
              Polynomial.C (PowerSeries.C c)) :
            Polynomial (PowerSeries K)) :
          PowerSeries (PowerSeries K)).map
            (IsLocalRing.residue (PowerSeries K))).order.toNat)
    (horder_lt :
      (((g.comp
          (Polynomial.X +
            Polynomial.C (PowerSeries.C c)) :
          Polynomial (PowerSeries K)) :
        PowerSeries (PowerSeries K)).map
          (IsLocalRing.residue (PowerSeries K))).order.toNat <
        g.natDegree)
    (Hlower :
      ∀ f : Polynomial (PowerSeries K),
        f.Monic → 0 < f.natDegree → f.natDegree < g.natDegree →
          ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
            (ramifyPowerSeriesPolynomial p hp f).IsRoot s) :
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial p hp g).IsRoot s := by
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  let G : Polynomial (PowerSeries K) :=
    g.comp
      (Polynomial.X +
        Polynomial.C (PowerSeries.C c))
  obtain ⟨f, h, H⟩ :=
    PowerSeries.exists_isWeierstrassFactorization
      (g := (G : PowerSeries (PowerSeries K))) hred
  have hf_degree :
      f.natDegree =
        ((G : PowerSeries (PowerSeries K)).map
          (IsLocalRing.residue (PowerSeries K))).order.toNat :=
    H.natDegree_eq_toNat_order_map
  obtain ⟨p, hp, s, hs⟩ :=
    Hlower f H.isDistinguishedAt.monic
      (hf_degree.symm ▸ horder_pos)
      (hf_degree.trans_lt horder_lt)
  have Hram :
      (ramifyPowerSeriesPolynomial p hp G :
          PowerSeries (PowerSeries K)).IsWeierstrassFactorization
        (ramifyPowerSeriesPolynomial p hp f)
        (ramifyIteratedPowerSeries p hp h) := by
    simpa only [← ramifyIteratedPowerSeries_coe] using
      isWeierstrassFactorization_ramify H p hp
  have hs0 : s.constantCoeff = 0 :=
    constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
      (isDistinguishedAt_ramifyPowerSeriesPolynomial
        H.isDistinguishedAt p hp) hs
  have hsG :
      (ramifyPowerSeriesPolynomial p hp G).IsRoot s :=
    isRoot_of_isWeierstrassFactorization
      (ramifyPowerSeriesPolynomial p hp G)
      (ramifyPowerSeriesPolynomial p hp f)
      (ramifyIteratedPowerSeries p hp h)
      Hram s hs0 hs
  refine ⟨p, hp, s + PowerSeries.C c, ?_⟩
  rw [show G =
      g.comp
        (Polynomial.X +
          Polynomial.C (PowerSeries.C c)) by rfl,
    ramify_comp_X_add_C_constant] at hsG
  simpa [Polynomial.IsRoot, Polynomial.eval_comp] using hsG

/-- A chosen exact quotient by `X^n`; it is used only together with a proof
that the divisibility holds. -/
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

theorem divByXPow_zero (n : ℕ) :
    divByXPow n (0 : PowerSeries K) = 0 := by
  apply mul_left_cancel₀
    (a := (PowerSeries.X : PowerSeries K) ^ n)
    (pow_ne_zero n (PowerSeries.X_ne_zero (R := K)))
  rw [X_pow_mul_divByXPow]
  · simp
  · exact dvd_zero _

/-- Any exponent bounded by the order of a series divides that series. -/
theorem X_pow_dvd_of_le_order_toNat
    (a : PowerSeries K) (n : ℕ)
    (h : n ≤ a.order.toNat) :
    (PowerSeries.X : PowerSeries K) ^ n ∣ a := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  exact PowerSeries.coeff_of_lt_order_toNat m (hm.trans_le h)

/-- Dividing a nonzero series by exactly its order leaves a unit. -/
theorem constantCoeff_divByXPow_ne_zero_of_order
    (a : PowerSeries K) (n : ℕ) (ha : a ≠ 0)
    (horder : a.order.toNat = n) :
    (divByXPow n a).constantCoeff ≠ 0 := by
  have hdiv :
      (PowerSeries.X : PowerSeries K) ^ n ∣ a :=
    X_pow_dvd_of_le_order_toNat a n horder.ge
  have heq := X_pow_mul_divByXPow n a hdiv
  have hcoeff := congrArg (PowerSeries.coeff n) heq
  rw [PowerSeries.coeff_X_pow_mul'] at hcoeff
  simp only [le_refl, ↓reduceIte, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff] at hcoeff
  rw [hcoeff]
  simpa [horder] using PowerSeries.coeff_order ha

/-- A monic polynomial over an algebraically closed field which has a
non-leading nonzero coefficient has a nonzero root. -/
theorem exists_nonzero_isRoot_of_monic_of_coeff_ne_zero
    (P : Polynomial K) (hP : P.Monic)
    {k : ℕ} (hk : k < P.natDegree)
    (hcoeff : P.coeff k ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ P.IsRoot c := by
  have hsplit : P.Splits := IsAlgClosed.splits P
  by_contra hexists
  have hall : ∀ c : K, P.IsRoot c → c = 0 := by
    intro c hc
    by_contra hc0
    exact hexists ⟨c, hc0, hc⟩
  have hroots_mem : ∀ c ∈ P.roots, c = 0 := by
    intro c hc
    exact hall c ((Polynomial.mem_roots hP.ne_zero).mp hc)
  have hroots :
      P.roots = Multiset.replicate P.roots.card 0 :=
    Multiset.eq_replicate_card.mpr hroots_mem
  have hPpow : P = Polynomial.X ^ P.natDegree := by
    calc
      P = (P.roots.map
          (fun c : K => Polynomial.X - Polynomial.C c)).prod :=
        hsplit.eq_prod_roots_of_monic hP
      _ = Polynomial.X ^ P.natDegree := by
        rw [hroots, ← hsplit.natDegree_eq_card_roots]
        simp
  rw [hPpow, Polynomial.coeff_X_pow, if_neg hk.ne] at hcoeff
  exact hcoeff rfl

/-- The finite Newton polygon has a lowest slope.  Denominators are kept
unreduced, which is enough for the subsequent ramification. -/
theorem exists_newton_slope
    (f : Polynomial (PowerSeries K)) (d : ℕ)
    (hlower :
      ∃ i : ℕ, i < d ∧ f.coeff i ≠ 0) :
    ∃ k : ℕ,
      k < d ∧ f.coeff k ≠ 0 ∧
      ∀ i : ℕ, i < d → f.coeff i ≠ 0 →
        (d - k) * (f.coeff i).order.toNat ≥
          (f.coeff k).order.toNat * (d - i) := by
  classical
  let I : Finset ℕ := f.support.filter (fun i => i < d)
  have hI : I.Nonempty := by
    obtain ⟨i, hi, hcoeff⟩ := hlower
    refine ⟨i, ?_⟩
    simp [I, hi, hcoeff]
  let slope : ℕ → ℚ :=
    fun i =>
      ((f.coeff i).order.toNat : ℚ) / (d - i : ℕ)
  obtain ⟨k, hkI, hkmin⟩ :=
    Finset.exists_min_image I slope hI
  have hk : k < d := (Finset.mem_filter.mp hkI).2
  have hkcoeff : f.coeff k ≠ 0 := by
    exact Polynomial.mem_support_iff.mp
      (Finset.mem_filter.mp hkI).1
  refine ⟨k, hk, hkcoeff, ?_⟩
  intro i hi hicoeff
  have hiI : i ∈ I := by
    simp [I, hi, hicoeff]
  have hslope := hkmin i hiI
  have hdk : (0 : ℚ) < (d - k : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hk
  have hdi : (0 : ℚ) < (d - i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hi
  have hcross :
      ((f.coeff k).order.toNat : ℚ) * (d - i : ℕ) ≤
        ((f.coeff i).order.toNat : ℚ) * (d - k : ℕ) := by
    exact (div_le_div_iff₀ hdk hdi).mp hslope
  have hcrossNat :
      (f.coeff k).order.toNat * (d - i) ≤
        (f.coeff i).order.toNat * (d - k) := by
    exact_mod_cast hcross
  simpa [mul_comm] using hcrossNat

/-- Ramification multiplies the finite order of a coefficient by the
ramification index (and the same formula also holds for zero). -/
theorem order_toNat_expand
    (q : ℕ) (hq : q ≠ 0) (a : PowerSeries K) :
    (PowerSeries.expand q hq a).order.toNat =
      q * a.order.toNat := by
  rw [PowerSeries.order_expand]
  simp [nsmul_eq_mul]

/-- A coefficient of the Newton transform after removing its forced common
power of the parameter. -/
noncomputable def newtonCoefficient
    (f : Polynomial (PowerSeries K))
    (d p q : ℕ) (hq : q ≠ 0) (i : ℕ) : PowerSeries K :=
  divByXPow (p * (d - i))
    (PowerSeries.expand q hq (f.coeff i))

/-- The polynomial obtained by ramifying `X ↦ X^q`, scaling the outer
variable by `X^p`, and dividing the total expression by `X^(p*d)`. -/
noncomputable def newtonTransform
    (f : Polynomial (PowerSeries K))
    (d p q : ℕ) (hq : q ≠ 0) :
    Polynomial (PowerSeries K) :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.monomial i (newtonCoefficient f d p q hq i)

theorem coeff_newtonTransform_of_le
    (f : Polynomial (PowerSeries K))
    (d p q : ℕ) (hq : q ≠ 0)
    {i : ℕ} (hi : i ≤ d) :
    (newtonTransform f d p q hq).coeff i =
      newtonCoefficient f d p q hq i := by
  classical
  simp [newtonTransform, Polynomial.coeff_monomial, hi]

theorem coeff_newtonTransform_of_lt
    (f : Polynomial (PowerSeries K))
    (d p q : ℕ) (hq : q ≠ 0)
    {i : ℕ} (hi : d < i) :
    (newtonTransform f d p q hq).coeff i = 0 := by
  classical
  simp [newtonTransform, Polynomial.coeff_monomial,
    Nat.not_le_of_gt hi]

/-- The normalized Newton transform remains monic. -/
theorem newtonTransform_monic
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (d p q : ℕ) (hq : q ≠ 0)
    (hdegree : f.natDegree = d)
    (hdiv :
      ∀ i : ℕ, i ≤ d →
        (PowerSeries.X : PowerSeries K) ^ (p * (d - i)) ∣
          PowerSeries.expand q hq (f.coeff i)) :
    (newtonTransform f d p q hq).Monic := by
  have hfd : f.coeff d = 1 := by
    simpa [hdegree] using hf.coeff_natDegree
  have hcoeffd :
      newtonCoefficient f d p q hq d = 1 := by
    have heq :=
      X_pow_mul_divByXPow
        (p * (d - d))
        (PowerSeries.expand q hq (f.coeff d))
        (hdiv d le_rfl)
    simpa [newtonCoefficient, hfd, PowerSeries.expand_C] using heq
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    exact coeff_newtonTransform_of_lt f d p q hq hi
  · rw [coeff_newtonTransform_of_le f d p q hq le_rfl]
    exact hcoeffd

/--
The defining polynomial identity for the Newton transform:

`X^(p*d) G(Y) = f(X^q, X^p Y)`.
-/
theorem C_X_pow_mul_newtonTransform
    (f : Polynomial (PowerSeries K))
    (d p q : ℕ) (hq : q ≠ 0)
    (hdegree : f.natDegree = d)
    (hdiv :
      ∀ i : ℕ, i ≤ d →
        (PowerSeries.X : PowerSeries K) ^ (p * (d - i)) ∣
          PowerSeries.expand q hq (f.coeff i)) :
    Polynomial.C (PowerSeries.X ^ (p * d)) *
        newtonTransform f d p q hq =
      (ramifyPowerSeriesPolynomial q hq f).comp
        (Polynomial.C (PowerSeries.X ^ p) * Polynomial.X) := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_C_mul,
    Polynomial.comp_C_mul_X_coeff]
  rw [ramifyPowerSeriesPolynomial, Polynomial.coeff_map]
  change
    PowerSeries.X ^ (p * d) *
        (newtonTransform f d p q hq).coeff i =
      PowerSeries.expand q hq (f.coeff i) *
        (PowerSeries.X ^ p) ^ i
  by_cases hi : i ≤ d
  · rw [coeff_newtonTransform_of_le f d p q hq hi]
    have hquot :=
      X_pow_mul_divByXPow
        (p * (d - i))
        (PowerSeries.expand q hq (f.coeff i))
        (hdiv i hi)
    have hquot' :
        PowerSeries.X ^ (p * (d - i)) *
            newtonCoefficient f d p q hq i =
          PowerSeries.expand q hq (f.coeff i) := by
      simpa [newtonCoefficient] using hquot
    have hexponent :
        p * d = p * (d - i) + p * i := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hi]
    have hpow :
        (PowerSeries.X : PowerSeries K) ^ (p * d) =
          (PowerSeries.X : PowerSeries K) ^ (p * (d - i)) *
            ((PowerSeries.X : PowerSeries K) ^ p) ^ i := by
      calc
        (PowerSeries.X : PowerSeries K) ^ (p * d) =
            PowerSeries.X ^ (p * (d - i) + p * i) := by
              rw [hexponent]
        _ = PowerSeries.X ^ (p * (d - i)) *
              PowerSeries.X ^ (p * i) :=
            pow_add _ _ _
        _ = PowerSeries.X ^ (p * (d - i)) *
              (PowerSeries.X ^ p) ^ i := by
            exact congrArg
              (fun z : PowerSeries K =>
                PowerSeries.X ^ (p * (d - i)) * z)
              (pow_mul (PowerSeries.X : PowerSeries K) p i)
    calc
      PowerSeries.X ^ (p * d) *
            newtonCoefficient f d p q hq i =
          (PowerSeries.X ^ (p * (d - i)) *
              (PowerSeries.X ^ p) ^ i) *
            newtonCoefficient f d p q hq i := by rw [hpow]
      _ = (PowerSeries.X ^ (p * (d - i)) *
              newtonCoefficient f d p q hq i) *
            (PowerSeries.X ^ p) ^ i := by ring
      _ = PowerSeries.expand q hq (f.coeff i) *
            (PowerSeries.X ^ p) ^ i := by rw [hquot']
  · have hid : d < i := Nat.lt_of_not_ge hi
    rw [coeff_newtonTransform_of_lt f d p q hq hid]
    have hfi : f.coeff i = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa [hdegree] using hid
    simp [hfi]

/-- Translation by `c` adds `degree • c` to the coefficient immediately
below the leading term. -/
theorem nextCoeff_comp_X_add_C_of_monic
    (P : Polynomial K) (hP : P.Monic) (c : K) :
    (P.comp (Polynomial.X + Polynomial.C c)).nextCoeff =
      P.nextCoeff + P.natDegree • c := by
  have hsplit : P.Splits := IsAlgClosed.splits P
  have htranslated_monic :
      (P.comp (Polynomial.X + Polynomial.C c)).Monic :=
    hP.comp (Polynomial.monic_X_add_C c) (by simp)
  have htranslated_split :
      (P.comp (Polynomial.X + Polynomial.C c)).Splits :=
    hsplit.comp_X_add_C c
  have hroots :
      (P.comp (Polynomial.X + Polynomial.C c)).roots =
        P.roots.map (fun x => x - c) := by
    simpa using
      (Polynomial.roots_comp_C_mul_X_add_C
        P 1 c isUnit_one)
  have hsum :
      (P.roots.map (fun x => x - c)).sum =
        P.roots.sum - P.roots.card • c := by
    induction P.roots using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons,
          Multiset.card_cons, ih, succ_nsmul]
        abel
  calc
    (P.comp (Polynomial.X + Polynomial.C c)).nextCoeff =
        -(P.comp
          (Polynomial.X + Polynomial.C c)).roots.sum :=
      htranslated_split.nextCoeff_eq_neg_sum_roots_of_monic
        htranslated_monic
    _ = -(P.roots.sum - P.roots.card • c) := by
      rw [hroots, hsum]
    _ = P.nextCoeff + P.natDegree • c := by
      rw [hsplit.nextCoeff_eq_neg_sum_roots_of_monic hP,
        hsplit.natDegree_eq_card_roots]
      abel

/-- A ramified root of the Newton transform gives a ramified root of the
original polynomial after the inverse monomial scaling. -/
theorem ramifiedRoot_of_newtonTransform
    (f : Polynomial (PowerSeries K))
    (d p q : ℕ) (hq : q ≠ 0)
    (hdegree : f.natDegree = d)
    (hdiv :
      ∀ i : ℕ, i ≤ d →
        (PowerSeries.X : PowerSeries K) ^ (p * (d - i)) ∣
          PowerSeries.expand q hq (f.coeff i))
    (r : ℕ) (hr : r ≠ 0) (s : PowerSeries K)
    (hs :
      (ramifyPowerSeriesPolynomial r hr
        (newtonTransform f d p q hq)).IsRoot s) :
    (ramifyPowerSeriesPolynomial (r * q)
      (r.mul_ne_zero hr hq) f).IsRoot
        (PowerSeries.X ^ (r * p) * s) := by
  have hidentity :=
    C_X_pow_mul_newtonTransform f d p q hq hdegree hdiv
  have heval :=
    congrArg
      (Polynomial.eval₂
        (PowerSeries.expand r hr).toRingHom s)
      hidentity
  have hs' :
      (newtonTransform f d p q hq).eval₂
          (PowerSeries.expand r hr).toRingHom s = 0 := by
    simpa [ramifyPowerSeriesPolynomial, Polynomial.IsRoot,
      Polynomial.eval_map] using hs
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_comp, Polynomial.eval₂_X] at heval
  rw [hs', mul_zero] at heval
  have hscaled :
      PowerSeries.expand r hr (PowerSeries.X ^ p) * s =
        PowerSeries.X ^ (r * p) * s := by
    rw [map_pow, PowerSeries.expand_X, pow_mul]
  have hroot :
      (ramifyPowerSeriesPolynomial r hr
        (ramifyPowerSeriesPolynomial q hq f)).IsRoot
          (PowerSeries.X ^ (r * p) * s) := by
    rw [Polynomial.IsRoot, ← hscaled]
    simpa [ramifyPowerSeriesPolynomial, Polynomial.eval_map] using heval.symm
  rw [ramifyPowerSeriesPolynomial_comp] at hroot
  exact hroot

/-- The translation formula for the next coefficient over formal power
series; unlike the field version above, this is used to depress a general
Weierstrass polynomial before taking its Newton polygon. -/
theorem nextCoeff_comp_X_add_C_of_monic_powerSeries
    (P : Polynomial (PowerSeries K)) (hP : P.Monic)
    (hpositive : 0 < P.natDegree) (a : PowerSeries K) :
    (P.comp (Polynomial.X + Polynomial.C a)).nextCoeff =
      P.nextCoeff + P.natDegree • a := by
  let d := P.natDegree
  have hd : 0 < d := hpositive
  have hlead : P.coeff d = 1 := hP.coeff_natDegree
  have hchoose : d.choose (d - 1) = d := by
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    rw [he]
    simp
  have hhasse :
      Polynomial.hasseDeriv (d - 1) P =
        Polynomial.C (P.coeff (d - 1)) +
          Polynomial.C (d : PowerSeries K) * Polynomial.X := by
    apply Polynomial.ext
    intro n
    rcases n with _ | _ | n
    · simp [Polynomial.hasseDeriv_coeff]
    · simp [Polynomial.hasseDeriv_coeff, Nat.one_add,
        Nat.sub_add_cancel hd, hlead, hchoose]
    · rw [Polynomial.hasseDeriv_coeff]
      have hindex :
          d < (n + 2) + (d - 1) := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simpa [d] using hindex)]
      simp
  have hcomp_degree :
      (P.comp (Polynomial.X + Polynomial.C a)).natDegree = d := by
    rw [Polynomial.natDegree_comp]
    simp [d]
  rw [Polynomial.nextCoeff_of_natDegree_pos
      (hcomp_degree.symm ▸ hd),
    hcomp_degree]
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff, hhasse]
  simp [Polynomial.nextCoeff_of_natDegree_pos hpositive, d]

/--
After translating a normalized Newton face by a nonzero residue root, the
special-fiber order is positive and strictly smaller than the original
degree.
-/
theorem translated_specialFiber_order_drop
    (G : Polynomial (PowerSeries K)) (hG : G.Monic)
    (d : ℕ) (hdegree : G.natDegree = d) (hd : 0 < d)
    (hnext : G.nextCoeff = 0)
    (c : K) (hc0 : c ≠ 0)
    (hc : (G.map PowerSeries.constantCoeff).IsRoot c) :
    let T :=
      (((G.comp
          (Polynomial.X + Polynomial.C (PowerSeries.C c)) :
            Polynomial (PowerSeries K)) :
          PowerSeries (PowerSeries K)).map
        (IsLocalRing.residue (PowerSeries K)))
    T ≠ 0 ∧ 0 < T.order.toNat ∧ T.order.toNat < d := by
  dsimp only
  let H : Polynomial (PowerSeries K) :=
    G.comp (Polynomial.X + Polynomial.C (PowerSeries.C c))
  let T : PowerSeries
      (IsLocalRing.ResidueField (PowerSeries K)) :=
    (H : PowerSeries (PowerSeries K)).map
      (IsLocalRing.residue (PowerSeries K))
  change T ≠ 0 ∧ 0 < T.order.toNat ∧ T.order.toNat < d
  have hHmonic : H.Monic :=
    hG.comp (Polynomial.monic_X_add_C (PowerSeries.C c)) (by simp)
  have hHdegree : H.natDegree = d := by
    dsimp only [H]
    rw [Polynomial.natDegree_comp, hdegree]
    simp
  have hTd : PowerSeries.coeff d T = 1 := by
    simp only [T, PowerSeries.coeff_map, Polynomial.coeff_coe]
    rw [show H.coeff d = 1 by
      simpa [hHdegree] using hHmonic.coeff_natDegree]
    simp
  have hTne : T ≠ 0 := by
    intro h
    rw [h, map_zero] at hTd
    exact one_ne_zero hTd.symm
  have hT0 : PowerSeries.coeff 0 T = 0 := by
    simp only [T, PowerSeries.coeff_map, Polynomial.coeff_coe]
    change
      IsLocalRing.residue (PowerSeries K)
          (H.coeff 0) = 0
    apply not_ne_iff.mp
    rw [IsLocalRing.residue_ne_zero_iff_isUnit,
      PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
      not_not]
    change PowerSeries.constantCoeff (H.coeff 0) = 0
    have hmapH :
        H.map PowerSeries.constantCoeff =
          (G.map PowerSeries.constantCoeff).comp
            (Polynomial.X + Polynomial.C c) := by
      simp [H, Polynomial.map_comp]
    rw [← Polynomial.coeff_map, hmapH,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    simpa [Polynomial.IsRoot] using hc
  have hTorder_pos : 0 < T.order.toNat := by
    by_contra h
    have hz : T.order.toNat = 0 := by omega
    have hnonzero := PowerSeries.coeff_order hTne
    rw [hz] at hnonzero
    exact hnonzero hT0
  have hnext_map :
      (G.map PowerSeries.constantCoeff).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_map_of_leadingCoeff_ne_zero]
    · simp [hnext]
    · simpa [hG.leadingCoeff]
  have hRmonic :
      (G.map PowerSeries.constantCoeff).Monic :=
    hG.map _
  have hRdegree :
      (G.map PowerSeries.constantCoeff).natDegree = d := by
    simpa [hdegree] using hG.natDegree_map
      PowerSeries.constantCoeff
  have htranslated_next :
      ((G.map PowerSeries.constantCoeff).comp
        (Polynomial.X + Polynomial.C c)).nextCoeff =
          d • c := by
    rw [nextCoeff_comp_X_add_C_of_monic _ hRmonic, hnext_map,
      hRdegree, zero_add]
  have htranslated_degree :
      ((G.map PowerSeries.constantCoeff).comp
        (Polynomial.X + Polynomial.C c)).natDegree = d := by
    rw [Polynomial.natDegree_comp, hRdegree]
    simp
  have hdc : d • c ≠ 0 := by
    simpa [nsmul_eq_mul] using
      mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)) hc0
  have hTprev : PowerSeries.coeff (d - 1) T ≠ 0 := by
    have hcoeff :
        ((G.map PowerSeries.constantCoeff).comp
          (Polynomial.X + Polynomial.C c)).coeff (d - 1) ≠ 0 := by
      intro hzero
      apply hdc
      rw [← htranslated_next]
      rw [Polynomial.nextCoeff, htranslated_degree,
        if_neg (Nat.ne_of_gt hd)]
      exact hzero
    simp only [T, PowerSeries.coeff_map, Polynomial.coeff_coe]
    rw [IsLocalRing.residue_ne_zero_iff_isUnit,
      PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    change PowerSeries.constantCoeff (H.coeff (d - 1)) ≠ 0
    have hmapH :
        H.map PowerSeries.constantCoeff =
          (G.map PowerSeries.constantCoeff).comp
            (Polynomial.X + Polynomial.C c) := by
      simp [H, Polynomial.map_comp]
    rw [← Polynomial.coeff_map, hmapH]
    exact hcoeff
  have horder_le :
      T.order.toNat ≤ d - 1 := by
    have hle := PowerSeries.order_le (φ := T) (d - 1) hTprev
    rw [← PowerSeries.coe_toNat_order hTne] at hle
    exact ENat.coe_le_coe.mp hle
  exact
    ⟨hTne, hTorder_pos,
      horder_le.trans_lt (Nat.sub_lt hd (by omega))⟩

/-- The normalized Newton transform has exactly the original degree. -/
theorem newtonTransform_natDegree
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (d p q : ℕ) (hq : q ≠ 0)
    (hdegree : f.natDegree = d)
    (hdiv :
      ∀ i : ℕ, i ≤ d →
        (PowerSeries.X : PowerSeries K) ^ (p * (d - i)) ∣
          PowerSeries.expand q hq (f.coeff i)) :
    (newtonTransform f d p q hq).natDegree = d := by
  have hfd : f.coeff d = 1 := by
    simpa [hdegree] using hf.coeff_natDegree
  have hcoeffd :
      (newtonTransform f d p q hq).coeff d = 1 := by
    rw [coeff_newtonTransform_of_le f d p q hq le_rfl]
    have heq :=
      X_pow_mul_divByXPow
        (p * (d - d))
        (PowerSeries.expand q hq (f.coeff d))
        (hdiv d le_rfl)
    simpa [newtonCoefficient, hfd, PowerSeries.expand_C] using heq
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    exact coeff_newtonTransform_of_lt f d p q hq hi
  · simpa [hcoeffd]

/-- Depression is preserved by a normalized Newton transform. -/
theorem newtonTransform_nextCoeff_eq_zero
    (f : Polynomial (PowerSeries K))
    (d p q : ℕ) (hq : q ≠ 0)
    (hdegree : f.natDegree = d) (hd : 0 < d)
    (hnext : f.nextCoeff = 0)
    (hGdegree :
      (newtonTransform f d p q hq).natDegree = d) :
    (newtonTransform f d p q hq).nextCoeff = 0 := by
  have hprev : f.coeff (d - 1) = 0 := by
    rw [Polynomial.nextCoeff, hdegree,
      if_neg (Nat.ne_of_gt hd)] at hnext
    exact hnext
  rw [Polynomial.nextCoeff, hGdegree,
    if_neg (Nat.ne_of_gt hd)]
  rw [coeff_newtonTransform_of_le f d p q hq
    (Nat.sub_le d 1)]
  simp [newtonCoefficient, hprev, divByXPow_zero]

/--
The Newton-polygon induction step for a depressed monic polynomial.  The
chosen edge is normalized, a nonzero residue root translates its special
fiber to positive order, and Weierstrass preparation strictly lowers the
outer degree.
-/
theorem exists_ramifiedRoot_of_depressed_monic
    (f : Polynomial (PowerSeries K)) (hf : f.Monic)
    (d : ℕ) (hdegree : f.natDegree = d) (hd : 0 < d)
    (hnext : f.nextCoeff = 0)
    (Hlower :
      ∀ g : Polynomial (PowerSeries K),
        g.Monic → 0 < g.natDegree → g.natDegree < d →
          ∃ (r : ℕ) (hr : r ≠ 0) (s : PowerSeries K),
            (ramifyPowerSeriesPolynomial r hr g).IsRoot s) :
    ∃ (r : ℕ) (hr : r ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial r hr f).IsRoot s := by
  classical
  by_cases hlower :
      ∃ i : ℕ, i < d ∧ f.coeff i ≠ 0
  · obtain ⟨k, hk, hfk, hslope⟩ :=
      exists_newton_slope f d hlower
    let p : ℕ := (f.coeff k).order.toNat
    let q : ℕ := d - k
    have hqpos : 0 < q := by
      simpa [q] using Nat.sub_pos_of_lt hk
    have hq : q ≠ 0 := Nat.ne_of_gt hqpos
    have hdiv :
        ∀ i : ℕ, i ≤ d →
          (PowerSeries.X : PowerSeries K) ^ (p * (d - i)) ∣
            PowerSeries.expand q hq (f.coeff i) := by
      intro i hi
      by_cases hid : i = d
      · subst i
        simp
      have hil : i < d := lt_of_le_of_ne hi hid
      by_cases hfi : f.coeff i = 0
      · simp [hfi]
      apply X_pow_dvd_of_le_order_toNat
      rw [order_toNat_expand q hq]
      simpa [p, q] using hslope i hil hfi
    let G : Polynomial (PowerSeries K) :=
      newtonTransform f d p q hq
    have hGmonic : G.Monic := by
      dsimp only [G]
      exact newtonTransform_monic f hf d p q hq hdegree hdiv
    have hGdegree : G.natDegree = d := by
      dsimp only [G]
      exact newtonTransform_natDegree f hf d p q hq hdegree hdiv
    have hGnext : G.nextCoeff = 0 := by
      dsimp only [G]
      exact newtonTransform_nextCoeff_eq_zero
        f d p q hq hdegree hd hnext hGdegree
    have hexpandk :
        PowerSeries.expand q hq (f.coeff k) ≠ 0 := by
      intro hzero
      have hcoeff :=
        congrArg
          (PowerSeries.coeff
            (q * (f.coeff k).order.toNat))
          hzero
      rw [PowerSeries.coeff_expand_mul] at hcoeff
      exact PowerSeries.coeff_order hfk hcoeff
    have horderk :
        (PowerSeries.expand q hq (f.coeff k)).order.toNat =
          p * (d - k) := by
      rw [order_toNat_expand q hq]
      simp [p, q, mul_comm]
    have hGcoeffk :
        PowerSeries.constantCoeff (G.coeff k) ≠ 0 := by
      dsimp only [G]
      rw [coeff_newtonTransform_of_le f d p q hq hk.le]
      exact constantCoeff_divByXPow_ne_zero_of_order
        (PowerSeries.expand q hq (f.coeff k))
        (p * (d - k)) hexpandk horderk
    let R : Polynomial K := G.map PowerSeries.constantCoeff
    have hRmonic : R.Monic := by
      dsimp only [R]
      exact hGmonic.map _
    have hRdegree : R.natDegree = d := by
      dsimp only [R]
      simpa [hGdegree] using
        hGmonic.natDegree_map PowerSeries.constantCoeff
    have hRcoeffk : R.coeff k ≠ 0 := by
      dsimp only [R]
      simpa using hGcoeffk
    obtain ⟨c, hc0, hc⟩ :=
      exists_nonzero_isRoot_of_monic_of_coeff_ne_zero
        R hRmonic (by simpa [hRdegree] using hk) hRcoeffk
    have hcG :
        (G.map PowerSeries.constantCoeff).IsRoot c := by
      simpa [R] using hc
    obtain ⟨hred, horder_pos, horder_lt⟩ :=
      translated_specialFiber_order_drop
        G hGmonic d hGdegree hd hGnext c hc0 hcG
    obtain ⟨r, hr, s, hs⟩ :=
      exists_ramifiedRoot_of_weierstrass_order_drop
        G hGmonic c hred horder_pos
          (by simpa [hGdegree] using horder_lt)
        (by
          intro g hg hgpos hglt
          exact Hlower g hg hgpos
            (by simpa [hGdegree] using hglt))
    exact
      ⟨r * q, r.mul_ne_zero hr hq,
        PowerSeries.X ^ (r * p) * s,
        ramifiedRoot_of_newtonTransform
          f d p q hq hdegree hdiv r hr s hs⟩
  · push Not at hlower
    refine ⟨1, one_ne_zero, 0, ?_⟩
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero]
    simp [ramifyPowerSeriesPolynomial, hlower 0 hd]

/-- Ramification commutes with translation by an arbitrary coefficient
series, expanding that translating series by the same index. -/
theorem ramify_comp_X_add_C
    (r : ℕ) (hr : r ≠ 0)
    (f : Polynomial (PowerSeries K)) (a : PowerSeries K) :
    ramifyPowerSeriesPolynomial r hr
        (f.comp (Polynomial.X + Polynomial.C a)) =
      (ramifyPowerSeriesPolynomial r hr f).comp
        (Polynomial.X +
          Polynomial.C (PowerSeries.expand r hr a)) := by
  unfold ramifyPowerSeriesPolynomial
  rw [Polynomial.map_comp]
  congr 1
  simp

/-- Division by a positive natural number, embedded as a constant series,
gives the translation which kills the next coefficient. -/
theorem nsmul_depressShift
    (d : ℕ) (hd : 0 < d) (b : PowerSeries K) :
    d • (-PowerSeries.C ((d : K)⁻¹) * b) = -b := by
  rw [nsmul_eq_mul]
  change
    PowerSeries.C (d : K) *
        (-PowerSeries.C ((d : K)⁻¹) * b) = -b
  calc
    PowerSeries.C (d : K) *
          (-PowerSeries.C ((d : K)⁻¹) * b) =
        -PowerSeries.C ((d : K) * (d : K)⁻¹) * b := by
          rw [map_mul]
          ring
    _ = -b := by
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))]
      simp

/--
Formal Newton--Puiseux root extraction in arbitrary outer degree over an
algebraically closed characteristic-zero field.
-/
theorem hasRamifiedRootProperty_algClosed :
    HasRamifiedRootProperty K := by
  intro f hf hpositive
  generalize hdegree : f.natDegree = d
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
      have hd : 0 < d := by
        simpa [← hdegree] using hpositive
      let a : PowerSeries K :=
        -PowerSeries.C ((d : K)⁻¹) * f.nextCoeff
      let F : Polynomial (PowerSeries K) :=
        f.comp (Polynomial.X + Polynomial.C a)
      have hFmonic : F.Monic := by
        dsimp only [F]
        exact hf.comp (Polynomial.monic_X_add_C a) (by simp)
      have hFdegree : F.natDegree = d := by
        dsimp only [F]
        rw [Polynomial.natDegree_comp, hdegree]
        simp
      have hFnext : F.nextCoeff = 0 := by
        calc
          F.nextCoeff =
              f.nextCoeff + f.natDegree • a :=
            nextCoeff_comp_X_add_C_of_monic_powerSeries
              f hf hpositive a
          _ = f.nextCoeff + d • a := by rw [hdegree]
          _ = 0 := by
            rw [show d • a = -f.nextCoeff by
              simpa [a] using
                nsmul_depressShift d hd f.nextCoeff]
            simp
      obtain ⟨r, hr, s, hs⟩ :=
        exists_ramifiedRoot_of_depressed_monic
          F hFmonic d hFdegree hd hFnext
          (by
            intro g hg hgpos hglt
            exact ih g.natDegree hglt g hg hgpos rfl)
      refine
        ⟨r, hr, s + PowerSeries.expand r hr a, ?_⟩
      rw [show F =
          f.comp (Polynomial.X + Polynomial.C a) by rfl,
        ramify_comp_X_add_C] at hs
      simpa [Polynomial.IsRoot, Polynomial.eval_comp] using hs

end CurveSelection.PuiseuxDegreeScratch
end Math
