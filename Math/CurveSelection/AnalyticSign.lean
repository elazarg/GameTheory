import GameTheory.Concepts.Stochastic.BellmanCurveGate
import Math.AlgebraicSelection
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter Set Topology
open Math.PolynomialSignCell

namespace Math
namespace CurveSelection.AnalyticSignScratch

variable {ι σ : Type*}

/--
An analytic curve which visits one complete polynomial sign cell
arbitrarily close to its endpoint stays in that cell on a whole sufficiently
small positive interval.

This is the sign-recovery bridge needed after an algebraic/Puiseux
parametrization has been selected from the original accumulating branch.
-/
theorem eventually_mem_signCell_of_analyticAt_of_frequently
    [Finite ι]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (γ : ℝ → Assignment σ)
    (hγ : ∀ v, AnalyticAt ℝ (fun t => γ t v) 0)
    (hfrequent :
      ∃ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ signCell P τ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      γ t ∈ signCell P τ := by
  have hcoordinate :
      ∀ i,
        AnalyticAt ℝ
          (fun t => MvPolynomial.eval (γ t) (P i)) 0 := by
    intro i
    simpa [MvPolynomial.aeval_def] using
      (AnalyticAt.aeval_mvPolynomial hγ (P i))
  have hi :
      ∀ i,
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
          SignType.sign (MvPolynomial.eval (γ t) (P i)) = τ i := by
    intro i
    rcases analyticAt_eventually_eq_or_lt_or_gt
        (hcoordinate i) analyticAt_const with hzero | hneg | hpos
    · have hsign :
          ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
            SignType.sign (MvPolynomial.eval (γ t) (P i)) = 0 := by
        filter_upwards [hzero] with t ht
        exact sign_eq_zero_iff.mpr ht
      obtain ⟨t, htcell, htsign⟩ :=
        (hfrequent.and_eventually hsign).exists
      have hτ : τ i = 0 := by
        exact (congrFun htcell i).symm.trans htsign
      simpa [hτ] using hsign
    · have hsign :
          ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
            SignType.sign (MvPolynomial.eval (γ t) (P i)) = -1 := by
        filter_upwards [hneg] with t ht
        exact sign_eq_neg_one_iff.mpr ht
      obtain ⟨t, htcell, htsign⟩ :=
        (hfrequent.and_eventually hsign).exists
      have hτ : τ i = -1 := by
        exact (congrFun htcell i).symm.trans htsign
      simpa [hτ] using hsign
    · have hsign :
          ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
            SignType.sign (MvPolynomial.eval (γ t) (P i)) = 1 := by
        filter_upwards [hpos] with t ht
        exact sign_eq_one_iff.mpr ht
      obtain ⟨t, htcell, htsign⟩ :=
        (hfrequent.and_eventually hsign).exists
      have hτ : τ i = 1 := by
        exact (congrFun htcell i).symm.trans htsign
      simpa [hτ] using hsign
  filter_upwards [Filter.eventually_all.mpr hi] with t ht
  exact funext ht

/--
Once an analytic parametrization is known to accumulate through a complete
sign cell, eventual positivity of the distinguished coordinate upgrades it
directly to the positive-coordinate arc used by the Bellman gate.
-/
theorem hasPositiveCoordinateAnalyticArcAt_signCell_of_frequently
    [Finite ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : Assignment σ →L[ℝ] ℝ)
    (x₀ : Assignment σ)
    (γ : ℝ → Assignment σ)
    (hγ : AnalyticAt ℝ γ 0)
    (hγ0 : γ 0 = x₀)
    (hcoordinate0 : coordinate x₀ = 0)
    (hfrequent :
      ∃ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ signCell P τ)
    (hpositive :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        0 < coordinate (γ t)) :
    HasPositiveCoordinateAnalyticArcAt
      (signCell P τ) coordinate x₀ := by
  have hγ_coordinate :
      ∀ v, AnalyticAt ℝ (fun t => γ t v) 0 := by
    have hγ' := hγ
    rw [analyticAt_pi_iff] at hγ'
    exact hγ'
  have hcell :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ signCell P τ :=
    eventually_mem_signCell_of_analyticAt_of_frequently
      P τ γ hγ_coordinate hfrequent
  have hgood :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ signCell P τ ∧ 0 < coordinate (γ t) :=
    hcell.and hpositive
  obtain ⟨eta, heta, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  exact
    ⟨γ, eta, heta, hγ, hγ0, hcoordinate0,
      fun t ht => hinterval ht⟩

/--
Exact-power version of
`hasPositiveCoordinateAnalyticArcAt_signCell_of_frequently`. This is the
form produced by a ramified algebraic branch and consumed directly by an
analytic Bellman germ.
-/
theorem hasAnalyticPowerCurveAt_signCell_of_frequently
    [Finite ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : Assignment σ →L[ℝ] ℝ)
    (x₀ : Assignment σ)
    (q : ℕ)
    (γ : ℝ → Assignment σ)
    (hq : 0 < q)
    (hγ : AnalyticAt ℝ γ 0)
    (hγ0 : γ 0 = x₀)
    (hfrequent :
      ∃ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ signCell P τ)
    (hpower :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        coordinate (γ t) = t ^ q) :
    HasAnalyticPowerCurveAt (signCell P τ) coordinate x₀ := by
  have hγ_coordinate :
      ∀ v, AnalyticAt ℝ (fun t => γ t v) 0 := by
    have hγ' := hγ
    rw [analyticAt_pi_iff] at hγ'
    exact hγ'
  have hcell :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ signCell P τ :=
    eventually_mem_signCell_of_analyticAt_of_frequently
      P τ γ hγ_coordinate hfrequent
  have hgood :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        γ t ∈ signCell P τ ∧ coordinate (γ t) = t ^ q :=
    hcell.and hpower
  obtain ⟨eta, heta, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  exact
    ⟨q, γ, eta, hq, heta, hγ, hγ0,
      fun t ht => hinterval ht⟩

/--
Finite branch synchronization.

Suppose each coordinate of a convergent sequence in a sign cell is, after
one common ramification, one of finitely many analytic branches. A single
tuple of branches occurs frequently. The coupled tuple is therefore an
analytic exact-power curve through the endpoint, and analytic sign
stabilization upgrades its frequent returns to eventual cell membership.
-/
theorem hasAnalyticPowerCurveAt_of_finite_analytic_branches
    {κ : σ → Type*}
    [Fintype ι] [Fintype σ] [∀ v, Fintype (κ v)]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : Assignment σ →L[ℝ] ℝ)
    (x₀ : Assignment σ)
    (q : ℕ)
    (hq : 0 < q)
    (branch : ∀ v, κ v → ℝ → ℝ)
    (hbranch_analytic :
      ∀ v k, AnalyticAt ℝ (branch v k) 0)
    (hbranch_zero :
      ∀ v k, branch v k 0 = x₀ v)
    (hbranch_coordinate :
      ∀ (k : ∀ v, κ v) t,
        coordinate (fun v => branch v (k v) t) = t ^ q)
    (x : ℕ → Assignment σ)
    (t : ℕ → ℝ)
    (hx : ∀ n, x n ∈ signCell P τ)
    (ht :
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hcovered :
      ∀ n v, ∃ k, branch v k (t n) = x n v) :
    HasAnalyticPowerCurveAt (signCell P τ) coordinate x₀ := by
  classical
  choose selected hselected using hcovered
  let choiceTuple : ℕ → (∀ v, κ v) := fun n v => selected n v
  have hsome :
      ∃ᶠ n in atTop, ∃ k : ∀ v, κ v, choiceTuple n = k :=
    Filter.Frequently.of_forall fun n => ⟨choiceTuple n, rfl⟩
  rw [Filter.frequently_exists] at hsome
  obtain ⟨k, hk⟩ := hsome
  let γ : ℝ → Assignment σ :=
    fun u v => branch v (k v) u
  have hγ : AnalyticAt ℝ γ 0 := by
    rw [analyticAt_pi_iff]
    exact fun v => hbranch_analytic v (k v)
  have hγ0 : γ 0 = x₀ := by
    funext v
    exact hbranch_zero v (k v)
  have hmatch :
      ∃ᶠ n in atTop, γ (t n) = x n := by
    apply hk.mono
    intro n hn
    funext v
    change branch v (k v) (t n) = x n v
    rw [← congrFun hn v]
    exact hselected n v
  have hfrequent_sequence :
      ∃ᶠ n in atTop, γ (t n) ∈ signCell P τ :=
    hmatch.mono fun n hn => hn.symm ▸ hx n
  have hfrequent :
      ∃ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0),
        γ u ∈ signCell P τ :=
    ht.frequently hfrequent_sequence
  have hpower :
      ∀ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0),
        coordinate (γ u) = u ^ q :=
    Filter.Eventually.of_forall fun u =>
      hbranch_coordinate k u
  exact
    hasAnalyticPowerCurveAt_signCell_of_frequently
      P τ coordinate x₀ q γ hq hγ hγ0 hfrequent hpower

/--
Complex Newton--Puiseux branches suffice for a real sign cell.

After a common ramification, choose one finite tuple of complex branches
whose real parts match the selected real sequence frequently. Their real
parts form a coupled real-analytic curve. No separate conjugation or
real-root argument is needed: frequent agreement with the real sign cell
forces all polynomial equalities and strict signs to stabilize analytically.
-/
theorem hasAnalyticPowerCurveAt_of_finite_complexAnalytic_branches
    {κ : σ → Type*}
    [Fintype ι] [Fintype σ] [∀ v, Fintype (κ v)]
    (P : ι → MvPolynomial σ ℝ)
    (τ : SignPattern ι)
    (coordinate : Assignment σ →L[ℝ] ℝ)
    (x₀ : Assignment σ)
    (q : ℕ)
    (hq : 0 < q)
    (branch : ∀ v, κ v → ℂ → ℂ)
    (hbranch_analytic :
      ∀ v k, AnalyticAt ℂ (branch v k) 0)
    (hbranch_zero :
      ∀ v k, (branch v k 0).re = x₀ v)
    (hbranch_coordinate :
      ∀ (k : ∀ v, κ v) (t : ℝ),
        coordinate (fun v => (branch v (k v) t).re) = t ^ q)
    (x : ℕ → Assignment σ)
    (t : ℕ → ℝ)
    (hx : ∀ n, x n ∈ signCell P τ)
    (ht :
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hcovered :
      ∀ n v, ∃ k, (branch v k (t n)).re = x n v) :
    HasAnalyticPowerCurveAt (signCell P τ) coordinate x₀ := by
  classical
  choose selected hselected using hcovered
  let choiceTuple : ℕ → (∀ v, κ v) := fun n v => selected n v
  have hsome :
      ∃ᶠ n in atTop, ∃ k : ∀ v, κ v, choiceTuple n = k :=
    Filter.Frequently.of_forall fun n => ⟨choiceTuple n, rfl⟩
  rw [Filter.frequently_exists] at hsome
  obtain ⟨k, hk⟩ := hsome
  let γ : ℝ → Assignment σ :=
    fun u v => (branch v (k v) u).re
  have hγ : AnalyticAt ℝ γ 0 := by
    rw [analyticAt_pi_iff]
    exact fun v => (hbranch_analytic v (k v)).re_ofReal
  have hγ0 : γ 0 = x₀ := by
    funext v
    exact hbranch_zero v (k v)
  have hmatch :
      ∃ᶠ n in atTop, γ (t n) = x n := by
    apply hk.mono
    intro n hn
    funext v
    change (branch v (k v) (t n)).re = x n v
    rw [← congrFun hn v]
    exact hselected n v
  have hfrequent_sequence :
      ∃ᶠ n in atTop, γ (t n) ∈ signCell P τ :=
    hmatch.mono fun n hn => hn.symm ▸ hx n
  have hfrequent :
      ∃ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0),
        γ u ∈ signCell P τ :=
    ht.frequently hfrequent_sequence
  have hpower :
      ∀ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0),
        coordinate (γ u) = u ^ q :=
    Filter.Eventually.of_forall fun u =>
      hbranch_coordinate k u
  exact
    hasAnalyticPowerCurveAt_signCell_of_frequently
      P τ coordinate x₀ q γ hq hγ hγ0 hfrequent hpower

end CurveSelection.AnalyticSignScratch
end Math
