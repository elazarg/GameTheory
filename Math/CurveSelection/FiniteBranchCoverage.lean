import Math.CurveSelection.Convergence
import Math.CurveSelection.RootCoverage
import Math.CurveSelection.PositiveRoot

set_option autoImplicit false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter Polynomial Set Topology

namespace Math
namespace CurveSelection.FiniteBranchCoverage

open CurveSelection.ConvergenceScratch
open CurveSelection.RootCoverage
open CurveSelection.PositiveRootScratch

theorem natDegree_trunc_lt_of_pos
    (s : PowerSeries ℂ) {n : ℕ} (hn : 0 < n) :
    (s.trunc n).natDegree < n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact PowerSeries.natDegree_trunc_lt s m

/--
One-coordinate finite-branch exhaustion, conditional only on the
duplicate-freeness of the split formal roots.
-/
theorem exists_finite_analytic_branches_covering_sequence
    (Q : Polynomial (Polynomial ℝ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (f : Polynomial (PowerSeries ℝ))
    (unit : PowerSeries (PowerSeries ℝ))
    (H :
      (bivPolynomialToIteratedPowerSeries Q).IsWeierstrassFactorization
        f unit)
    (p : ℕ) (hp : p ≠ 0)
    (hsplit :
      (ramifyPowerSeriesPolynomial p hp
        (mapPowerSeriesPolynomial Complex.ofRealHom f)).Splits)
    (hnodup :
      (ramifyPowerSeriesPolynomial p hp
        (mapPowerSeriesPolynomial Complex.ofRealHom f)).roots.Nodup)
    (x y : ℕ → ℝ)
    (hxpos : ∀ i, 0 < x i)
    (hx : Tendsto x atTop (𝓝 0))
    (hy : Tendsto y atTop (𝓝 0))
    (hxyroot :
      ∀ i, CurveSelection.TerminationScratch.bivEvalAt
        Q (x i) (y i) = 0) :
    ∃ (n : ℕ) (branches : List (ℂ → ℂ))
        (t : ℕ → ℝ),
      0 < n ∧
      branches.length =
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial Complex.ofRealHom f)).natDegree ∧
      (∀ γ ∈ branches,
        AnalyticAt ℂ γ 0 ∧
        γ 0 = 0 ∧
        ∀ᶠ z in 𝓝 (0 : ℂ),
          CurveSelection.TerminationScratch.bivEvalAt
            ((ramifyBivPolynomial p Q).map
              (Polynomial.mapRingHom Complex.ofRealHom))
            z (γ z) = 0) ∧
      (∀ i, t i = positiveNatRoot p (x i)) ∧
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      (∀ i, t i ^ p = x i) ∧
      (∀ᶠ i in atTop,
        ∃ γ ∈ branches, (y i : ℂ) = γ (t i)) := by
  classical
  let F : Polynomial (PowerSeries ℂ) :=
    ramifyPowerSeriesPolynomial p hp
      (mapPowerSeriesPolynomial Complex.ofRealHom f)
  let roots : List (PowerSeries ℂ) := F.roots.toList
  have hFnodup : roots.Nodup := by
    rw [← Multiset.coe_nodup]
    simpa [roots, F] using hnodup
  let Qram : Polynomial (Polynomial ℂ) :=
    (ramifyBivPolynomial p Q).map
      (Polynomial.mapRingHom Complex.ofRealHom)
  let branchOrder : PowerSeries ℂ → ℕ :=
    fun s =>
      ((bivPolynomialToPowerSeriesPolynomial Qram).derivative.eval s).order.toNat
  obtain ⟨n, hn, htruncNodup, hnlarge⟩ :=
    exists_common_separating_truncation
      roots hFnodup branchOrder
  let Good (s : PowerSeries ℂ) (z : ℂ → ℂ) : Prop :=
    AnalyticAt ℂ z 0 ∧
    z 0 =
      (CurveSelection.TerminationScratch.formalTail n s).constantCoeff ∧
    AnalyticAt ℂ
      (fun a => (s.trunc n).eval a + a ^ n * z a) 0 ∧
    (fun a => (s.trunc n).eval a + a ^ n * z a) 0 =
      s.constantCoeff ∧
    (∀ᶠ a in 𝓝 (0 : ℂ),
      CurveSelection.TerminationScratch.bivEvalAt Qram a
        ((s.trunc n).eval a + a ^ n * z a) = 0)
  have hFmonic : F.Monic := by
    exact
      (isDistinguishedAt_ramifyPowerSeriesPolynomial
        (isDistinguishedAt_mapPowerSeriesPolynomial
          Complex.ofRealHom H.isDistinguishedAt)
        p hp).monic
  have hFne : F ≠ 0 := hFmonic.ne_zero
  have hFormalQroot :
      ∀ s ∈ roots,
        (ramifyPowerSeriesPolynomial p hp
          (mappedBivPolynomialToPowerSeriesPolynomial
            Complex.ofRealHom Q)).IsRoot s := by
    intro s hs
    have hsF : F.IsRoot s := by
      rw [← Polynomial.mem_roots hFne]
      simpa [roots] using hs
    have hs0 : s.constantCoeff = 0 :=
      constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
        (isDistinguishedAt_ramifyPowerSeriesPolynomial
          (isDistinguishedAt_mapPowerSeriesPolynomial
            Complex.ofRealHom H.isDistinguishedAt)
          p hp)
        hsF
    exact ramified_mapped_biv_isRoot_of_weierstrass_root
      Q H p hp s hs0 (by simpa [F] using hsF)
  have hexists : ∀ s : PowerSeries ℂ, ∃ z, s ∈ roots → Good s z := by
    intro s
    by_cases hs : s ∈ roots
    · have hsQ := hFormalQroot s hs
      have hlarge :
          ((bivPolynomialToPowerSeriesPolynomial Qram).derivative.eval s).order.toNat <
            n := by
        exact hnlarge s hs
      obtain ⟨z, hz⟩ :=
        exists_analytic_complexBranch_of_real_irreducible_ramified_formalRoot_of_lt
          Q hQirr hQdegree p hp s hsQ n (by
            simpa [Qram] using hlarge)
      exact ⟨z, fun _ => by simpa [Good, Qram] using hz⟩
    · exact ⟨0, fun hs' => (hs hs').elim⟩
  choose z hz using hexists
  let γ : PowerSeries ℂ → ℂ → ℂ :=
    fun s a => (s.trunc n).eval a + a ^ n * z s a
  let branches : List (ℂ → ℂ) := roots.map γ
  let t : ℕ → ℝ := fun i => positiveNatRoot p (x i)
  have hpPos : 0 < p := Nat.pos_of_ne_zero hp
  have ht :
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    tendsto_positiveNatRoot hpPos hxpos hx
  have htPow : ∀ i, t i ^ p = x i :=
    positiveNatRoot_parameter hpPos hxpos
  have htReal : Tendsto t atTop (𝓝 (0 : ℝ)) :=
    ht.mono_right nhdsWithin_le_nhds
  have htComplex :
      Tendsto (fun i => (t i : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    exact Filter.Tendsto.comp
      Complex.continuous_ofReal.continuousAt htReal
  have htPunctured :
      Tendsto (fun i => (t i : ℂ)) atTop
        (𝓝[({0}ᶜ : Set ℂ)] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact htComplex
    · exact Filter.Eventually.of_forall fun i => by
        have hti : 0 < t i := positiveNatRoot_pos (hxpos i)
        simp [ne_of_gt hti]
  have hyComplex :
      Tendsto (fun i => (y i : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    exact Filter.Tendsto.comp
      Complex.continuous_ofReal.continuousAt hy
  have hBranchData :
      ∀ s ∈ roots, Good s (z s) :=
    fun s hs => hz s hs
  have hBranches :
      ∀ b ∈ branches,
        AnalyticAt ℂ b 0 ∧
        b 0 = 0 ∧
        ∀ᶠ a in 𝓝 (0 : ℂ),
          CurveSelection.TerminationScratch.bivEvalAt Qram a (b a) = 0 := by
    intro b hb
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
    have hsData := hBranchData s hs
    have hs0 : s.constantCoeff = 0 := by
      have hsF : F.IsRoot s := by
        rw [← Polynomial.mem_roots hFne]
        simpa [roots] using hs
      exact constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
        (isDistinguishedAt_ramifyPowerSeriesPolynomial
          (isDistinguishedAt_mapPowerSeriesPolynomial
            Complex.ofRealHom H.isDistinguishedAt)
          p hp)
        hsF
    exact
      ⟨hsData.2.2.1,
        hsData.2.2.2.1.trans hs0,
        hsData.2.2.2.2⟩
  have hBranchLimits :
      ∀ b ∈ branches,
        Tendsto (fun i => b (t i)) atTop (𝓝 (0 : ℂ)) := by
    intro b hb
    have hbData := hBranches b hb
    have hbcont : ContinuousAt b 0 := hbData.1.continuousAt
    simpa [Function.comp_def, hbData.2.1] using
      Filter.Tendsto.comp hbcont htComplex
  have hPair :
      ∀ s ∈ roots, ∀ r ∈ roots, s ≠ r →
        ∀ᶠ i in atTop, γ s (t i) ≠ γ r (t i) := by
    intro s hs r hr hsr
    have hjet : s.trunc n ≠ r.trunc n := by
      intro heq
      have hinj :=
        List.inj_on_of_nodup_map htruncNodup
      exact hsr (hinj hs hr heq)
    have hne :=
      eventually_ne_of_distinct_polynomial_jets
        (s.trunc n) (r.trunc n) n (z s) (z r)
        (natDegree_trunc_lt_of_pos s hn)
        (natDegree_trunc_lt_of_pos r hn)
        hjet
        (hBranchData s hs).1.continuousAt
        (hBranchData r hr).1.continuousAt
    exact htPunctured.eventually hne
  have hBranchesNodup :
      ∀ᶠ i in atTop,
        (branches.map fun b => b (t i)).Nodup := by
    have h :=
      eventually_nodup_map_apply_indexed
        (l := atTop) roots hFnodup
        (fun s i => γ s (t i)) hPair
    simpa [branches, List.map_map, Function.comp_def] using h
  have hBranchRoots :
      ∀ᶠ i in atTop, ∀ b ∈ branches,
        CurveSelection.TerminationScratch.bivEvalAt Qram
          (t i) (b (t i)) = 0 := by
    apply eventually_forall_mem_list
      (l := atTop) branches
      (fun b i =>
        CurveSelection.TerminationScratch.bivEvalAt Qram
          (t i) (b (t i)) = 0)
    intro b hb
    exact htComplex.eventually (hBranches b hb).2.2
  have hSampleRoot :
      ∀ i,
        CurveSelection.TerminationScratch.bivEvalAt Qram
          (t i) (y i) = 0 := by
    intro i
    have hram :
        CurveSelection.TerminationScratch.bivEvalAt
          (ramifyBivPolynomial p Q) (t i) (y i) = 0 := by
      rw [bivEvalAt_ramifyBivPolynomial, htPow i]
      exact hxyroot i
    calc
      CurveSelection.TerminationScratch.bivEvalAt Qram
          (t i) (y i) =
          Complex.ofReal
            (CurveSelection.TerminationScratch.bivEvalAt
              (ramifyBivPolynomial p Q) (t i) (y i)) := by
        have hevalHom :
            (Polynomial.evalRingHom (t i : ℂ)).comp
                (Polynomial.mapRingHom Complex.ofRealHom) =
              Complex.ofRealHom.comp
                (Polynomial.evalRingHom (t i)) := by
          apply Polynomial.ringHom_ext
          · intro a
            simp
          · simp
        dsimp [Qram, CurveSelection.TerminationScratch.bivEvalAt]
        rw [Polynomial.eval₂_map]
        rw [hevalHom]
        symm
        exact Polynomial.hom_eval₂
          (p := ramifyBivPolynomial p Q)
          (Polynomial.evalRingHom (t i))
          Complex.ofRealHom (y i)
      _ = 0 := by simp [hram]
  have Hmap :=
    isWeierstrassFactorization_map Complex.ofRealHom H
  have Hram := isWeierstrassFactorization_ramify Hmap p hp
  have hQramSeries :
      bivPolynomialToIteratedPowerSeries Qram =
        ramifyIteratedPowerSeries p hp
          ((bivPolynomialToIteratedPowerSeries Q).map
            (PowerSeries.map Complex.ofRealHom)) := by
    calc
      bivPolynomialToIteratedPowerSeries Qram =
          (mappedBivPolynomialToPowerSeriesPolynomial
            Complex.ofRealHom (ramifyBivPolynomial p Q) :
              PowerSeries (PowerSeries ℂ)) := by
            exact congrArg
              (fun g : Polynomial (PowerSeries ℂ) =>
                (g : PowerSeries (PowerSeries ℂ)))
              (by
                simpa [Qram] using
                  (mappedBivPolynomialToPowerSeriesPolynomial_eq
                    Complex.ofRealHom (ramifyBivPolynomial p Q)).symm)
      _ =
          (ramifyPowerSeriesPolynomial p hp
            (mappedBivPolynomialToPowerSeriesPolynomial
              Complex.ofRealHom Q) :
                PowerSeries (PowerSeries ℂ)) := by
            exact congrArg
              (fun g : Polynomial (PowerSeries ℂ) =>
                (g : PowerSeries (PowerSeries ℂ)))
              (mapped_ramifyBivPolynomial
                Complex.ofRealHom p hp Q)
      _ =
          ramifyIteratedPowerSeries p hp
            (mappedBivPolynomialToPowerSeriesPolynomial
              Complex.ofRealHom Q :
                PowerSeries (PowerSeries ℂ)) := by
            symm
            exact ramifyIteratedPowerSeries_coe' p hp _
      _ =
          ramifyIteratedPowerSeries p hp
            ((bivPolynomialToIteratedPowerSeries Q).map
              (PowerSeries.map Complex.ofRealHom)) := by
            rw [map_bivPolynomialToIteratedPowerSeries]
  have HramQ :
      (bivPolynomialToIteratedPowerSeries Qram).IsWeierstrassFactorization
        F
        (ramifyIteratedPowerSeries p hp
          (unit.map (PowerSeries.map Complex.ofRealHom))) := by
    rw [hQramSeries]
    exact Hram
  have hResidualF :=
    residual_ne_zero_of_isWeierstrassFactorization
      Qram F
      (ramifyIteratedPowerSeries p hp
        (unit.map (PowerSeries.map Complex.ofRealHom)))
      HramQ
  have hLength :
      branches.length = F.natDegree := by
    dsimp [branches]
    rw [List.length_map]
    dsimp [roots]
    rw [Multiset.length_toList]
    exact hsplit.natDegree_eq_card_roots.symm
  have hResidual :
      (peelLinearFactors
        (specializeBivPolynomial Qram 0)
        (List.replicate branches.length 0)).eval 0 ≠ 0 := by
    simpa [hLength] using hResidualF
  have hCovered :
      ∀ᶠ i in atTop,
        ∃ b ∈ branches, (y i : ℂ) = b (t i) := by
    have hcov :=
      eventually_eq_branch_of_finite_centered_roots
        Qram
        (fun i => (t i : ℂ))
        (branches.map fun b i => b (t i))
        (fun i => (y i : ℂ))
        0 0 htComplex
        (by
          intro g hg
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
          exact hBranchLimits b hb)
        hyComplex
        (by
          simpa [List.map_map, Function.comp_def] using hBranchRoots)
        (Filter.Eventually.of_forall hSampleRoot)
        (by
          simpa [List.map_map, Function.comp_def] using hBranchesNodup)
        (by
          simpa using hResidual)
    filter_upwards [hcov] with i hi
    obtain ⟨g, hg, hyg⟩ := hi
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    exact ⟨b, hb, hyg⟩
  exact
    ⟨n, branches, t, hn, by simpa [F] using hLength,
      by simpa [Qram] using hBranches,
      fun _ => rfl, ht, htPow, hCovered⟩

/--
Unconditional one-coordinate Newton--Puiseux coverage.  Irreducibility makes
the ramified Weierstrass roots duplicate-free, so the preceding finite
branch exhaustion theorem applies without an extra separability hypothesis.
-/
theorem
    exists_finite_analytic_branches_covering_sequence_of_irreducible
    (Q : Polynomial (Polynomial ℝ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (f : Polynomial (PowerSeries ℝ))
    (unit : PowerSeries (PowerSeries ℝ))
    (H :
      (bivPolynomialToIteratedPowerSeries Q).IsWeierstrassFactorization
        f unit)
    (p : ℕ) (hp : p ≠ 0)
    (hsplit :
      (ramifyPowerSeriesPolynomial p hp
        (mapPowerSeriesPolynomial Complex.ofRealHom f)).Splits)
    (x y : ℕ → ℝ)
    (hxpos : ∀ i, 0 < x i)
    (hx : Tendsto x atTop (𝓝 0))
    (hy : Tendsto y atTop (𝓝 0))
    (hxyroot :
      ∀ i, CurveSelection.TerminationScratch.bivEvalAt
        Q (x i) (y i) = 0) :
    ∃ (n : ℕ) (branches : List (ℂ → ℂ))
        (t : ℕ → ℝ),
      0 < n ∧
      branches.length =
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial Complex.ofRealHom f)).natDegree ∧
      (∀ γ ∈ branches,
        AnalyticAt ℂ γ 0 ∧
        γ 0 = 0 ∧
        ∀ᶠ z in 𝓝 (0 : ℂ),
          CurveSelection.TerminationScratch.bivEvalAt
            ((ramifyBivPolynomial p Q).map
              (Polynomial.mapRingHom Complex.ofRealHom))
            z (γ z) = 0) ∧
      (∀ i, t i = positiveNatRoot p (x i)) ∧
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      (∀ i, t i ^ p = x i) ∧
      (∀ᶠ i in atTop,
        ∃ γ ∈ branches, (y i : ℂ) = γ (t i)) := by
  exact
    exists_finite_analytic_branches_covering_sequence
      Q hQirr hQdegree f unit H p hp hsplit
      (roots_nodup_ramified_map_weierstrassFactor_of_irreducible
        Q hQirr hQdegree H p hp)
      x y hxpos hx hy hxyroot

/--
Finite-coordinate version of
`exists_finite_analytic_branches_covering_sequence_of_irreducible`.

All coordinates use the same ramification exponent, hence the positive real
parameter can be chosen canonically as `positiveNatRoot p (x i)`.  The
eventual branch-covering statements can therefore be intersected over the
finite coordinate type.
-/
theorem
    exists_coordinatewise_finite_analytic_branches_covering_sequence
    {J : Type*} [Fintype J]
    (Q : J → Polynomial (Polynomial ℝ))
    (hQirr : ∀ j, Irreducible (Q j))
    (hQdegree : ∀ j, (Q j).natDegree ≠ 0)
    (f : J → Polynomial (PowerSeries ℝ))
    (unit : J → PowerSeries (PowerSeries ℝ))
    (H :
      ∀ j,
        (bivPolynomialToIteratedPowerSeries (Q j)).IsWeierstrassFactorization
          (f j) (unit j))
    (p : ℕ) (hp : p ≠ 0)
    (hsplit :
      ∀ j,
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).Splits)
    (x : ℕ → ℝ)
    (y : ℕ → J → ℝ)
    (hxpos : ∀ i, 0 < x i)
    (hx : Tendsto x atTop (𝓝 0))
    (hy : ∀ j, Tendsto (fun i => y i j) atTop (𝓝 0))
    (hxyroot :
      ∀ i j,
        CurveSelection.TerminationScratch.bivEvalAt
          (Q j) (x i) (y i j) = 0) :
    ∃ (n : J → ℕ) (branches : J → List (ℂ → ℂ))
        (t : ℕ → ℝ),
      (∀ j,
        0 < n j ∧
        (branches j).length =
          (ramifyPowerSeriesPolynomial p hp
            (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).natDegree ∧
        ∀ γ ∈ branches j,
          AnalyticAt ℂ γ 0 ∧
          γ 0 = 0 ∧
          ∀ᶠ z in 𝓝 (0 : ℂ),
            CurveSelection.TerminationScratch.bivEvalAt
              ((ramifyBivPolynomial p (Q j)).map
                (Polynomial.mapRingHom Complex.ofRealHom))
              z (γ z) = 0) ∧
      (∀ i, t i = positiveNatRoot p (x i)) ∧
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      (∀ i, t i ^ p = x i) ∧
      (∀ᶠ i in atTop,
        ∀ j, ∃ γ ∈ branches j, (y i j : ℂ) = γ (t i)) := by
  classical
  have hcoordinate :
      ∀ j,
        ∃ (n : ℕ) (branches : List (ℂ → ℂ))
            (t : ℕ → ℝ),
          0 < n ∧
          branches.length =
            (ramifyPowerSeriesPolynomial p hp
              (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).natDegree ∧
          (∀ γ ∈ branches,
            AnalyticAt ℂ γ 0 ∧
            γ 0 = 0 ∧
            ∀ᶠ z in 𝓝 (0 : ℂ),
              CurveSelection.TerminationScratch.bivEvalAt
                ((ramifyBivPolynomial p (Q j)).map
                  (Polynomial.mapRingHom Complex.ofRealHom))
                z (γ z) = 0) ∧
          (∀ i, t i = positiveNatRoot p (x i)) ∧
          Tendsto t atTop
            (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
          (∀ i, t i ^ p = x i) ∧
          (∀ᶠ i in atTop,
            ∃ γ ∈ branches, (y i j : ℂ) = γ (t i)) := by
    intro j
    exact
      exists_finite_analytic_branches_covering_sequence_of_irreducible
        (Q j) (hQirr j) (hQdegree j)
        (f j) (unit j) (H j) p hp (hsplit j)
        x (fun i => y i j) hxpos hx (hy j)
        (fun i => hxyroot i j)
  choose n branches t' hn hlength hbranches ht' ht'tend ht'pow
    hcovered using hcoordinate
  let t : ℕ → ℝ := fun i => positiveNatRoot p (x i)
  have ht :
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    exact tendsto_positiveNatRoot (Nat.pos_of_ne_zero hp) hxpos hx
  have htpow : ∀ i, t i ^ p = x i := by
    exact positiveNatRoot_parameter (Nat.pos_of_ne_zero hp) hxpos
  have hcovered' :
      ∀ j,
        ∀ᶠ i in atTop,
          ∃ γ ∈ branches j, (y i j : ℂ) = γ (t i) := by
    intro j
    filter_upwards [hcovered j] with i hi
    obtain ⟨γ, hγ, hi⟩ := hi
    refine ⟨γ, hγ, ?_⟩
    simpa [t, ht' j i] using hi
  exact
    ⟨n, branches, t,
      fun j => ⟨hn j, hlength j, hbranches j⟩,
      fun _ => rfl, ht, htpow,
      Filter.eventually_all.mpr hcovered'⟩

/--
Full centered algebraic-sequence package.  From one primitive bivariate
relation in every coordinate, first pass to a common subsequence on which
one positive-degree irreducible factor in each coordinate vanishes.  Prepare
those factors, split them after one common complex ramification, and exhaust
the sampled roots by finite analytic branch lists.
-/
theorem
    exists_factorTuple_finite_analytic_branches_covering_sequence
    {J : Type*} [Fintype J]
    (Hroot : HasRamifiedRootProperty ℂ)
    (Q : J → Polynomial (Polynomial ℝ))
    (hQ : ∀ j, Q j ≠ 0)
    (hprimitive : ∀ j, (Q j).IsPrimitive)
    (x : ℕ → ℝ)
    (y : ℕ → J → ℝ)
    (hxpos : ∀ i, 0 < x i)
    (hx : Tendsto x atTop (𝓝 0))
    (hy : ∀ j, Tendsto (fun i => y i j) atTop (𝓝 0))
    (hxyroot :
      ∀ i j,
        CurveSelection.TerminationScratch.bivEvalAt
          (Q j) (x i) (y i j) = 0) :
    ∃ (q : J → Polynomial (Polynomial ℝ))
        (ns : ℕ → ℕ)
        (f : J → Polynomial (PowerSeries ℝ))
        (unit : J → PowerSeries (PowerSeries ℝ))
        (p : ℕ) (hp : p ≠ 0)
        (n : J → ℕ)
        (branches : J → List (ℂ → ℂ))
        (t : ℕ → ℝ),
      (∀ j,
        q j ∈ CurveSelection.FactorCoverageScratch.irreducibleFactors (Q j) ∧
        Irreducible (q j) ∧
        0 < (q j).natDegree ∧
        q j ∣ Q j) ∧
      Tendsto
        (fun i => (x (ns i), y (ns i)))
        atTop
        (𝓝 ((0 : ℝ), (0 : J → ℝ))) ∧
      (∀ i j,
        CurveSelection.TerminationScratch.bivEvalAt
          (q j) (x (ns i)) (y (ns i) j) = 0) ∧
      (∀ j,
        (bivPolynomialToIteratedPowerSeries (q j)).IsWeierstrassFactorization
          (f j) (unit j)) ∧
      (∀ j,
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).Splits) ∧
      (∀ j,
        0 < n j ∧
        (branches j).length =
          (ramifyPowerSeriesPolynomial p hp
            (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).natDegree ∧
        ∀ γ ∈ branches j,
          AnalyticAt ℂ γ 0 ∧
          γ 0 = 0 ∧
          ∀ᶠ z in 𝓝 (0 : ℂ),
            CurveSelection.TerminationScratch.bivEvalAt
              ((ramifyBivPolynomial p (q j)).map
                (Polynomial.mapRingHom Complex.ofRealHom))
              z (γ z) = 0) ∧
      (∀ i, t i = positiveNatRoot p (x (ns i))) ∧
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      (∀ i, t i ^ p = x (ns i)) ∧
      (∀ᶠ i in atTop,
        ∀ j, ∃ γ ∈ branches j,
          (y (ns i) j : ℂ) = γ (t i)) := by
  classical
  have hyAll :
      Tendsto y atTop (𝓝 (0 : J → ℝ)) := by
    rw [tendsto_pi_nhds]
    intro j
    simpa using hy j
  have hpair :
      Tendsto (fun i => (x i, y i)) atTop
        (𝓝 ((0 : ℝ), (0 : J → ℝ))) :=
    hx.prodMk_nhds hyAll
  obtain
      ⟨q, ns, f, unit, p, hp, hq, hpairSub, hqroot,
        H, hsplit, _hformalBranches⟩ :=
    exists_factorTuple_commonRamified_analyticBranches
      Hroot Q hQ hprimitive x y hpair hxyroot
  have hxSub :
      Tendsto (fun i => x (ns i)) atTop (𝓝 0) := by
    exact
      (continuous_fst.tendsto
        (x := ((0 : ℝ), (0 : J → ℝ)))).comp hpairSub
  have hySubAll :
      Tendsto (fun i => y (ns i)) atTop
        (𝓝 (0 : J → ℝ)) := by
    exact
      (continuous_snd.tendsto
        (x := ((0 : ℝ), (0 : J → ℝ)))).comp hpairSub
  have hySub :
      ∀ j,
        Tendsto (fun i => y (ns i) j) atTop (𝓝 0) := by
    intro j
    exact (tendsto_pi_nhds.mp hySubAll) j
  obtain
      ⟨n, branches, t, hbranchData, htCanonical,
        ht, htPow, hcovered⟩ :=
    exists_coordinatewise_finite_analytic_branches_covering_sequence
      q (fun j => (hq j).2.1)
      (fun j => Nat.ne_of_gt (hq j).2.2.1)
      f unit H p hp hsplit
      (fun i => x (ns i)) (fun i => y (ns i))
      (fun i => hxpos (ns i)) hxSub hySub hqroot
  exact
    ⟨q, ns, f, unit, p, hp, n, branches, t,
      hq, hpairSub, hqroot, H, hsplit, hbranchData,
      htCanonical, ht, htPow, hcovered⟩

end CurveSelection.FiniteBranchCoverage
end Math
