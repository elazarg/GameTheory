import Math.CurveSelection.Termination
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial

noncomputable section

open Filter Finset Polynomial Set Topology

namespace Math
namespace CurveSelection.RootCoverage

variable {K : Type*} [Field K]

/-- Repeated synthetic division by the listed linear factors. -/
def peelLinearFactors (p : Polynomial K) : List K → Polynomial K
  | [] => p
  | a :: l => peelLinearFactors (p /ₘ (Polynomial.X - Polynomial.C a)) l

@[simp]
theorem peelLinearFactors_nil (p : Polynomial K) :
    peelLinearFactors p [] = p :=
  rfl

@[simp]
theorem peelLinearFactors_cons
    (p : Polynomial K) (a : K) (l : List K) :
    peelLinearFactors p (a :: l) =
      peelLinearFactors
        (p /ₘ (Polynomial.X - Polynomial.C a)) l :=
  rfl

theorem natDegree_peelLinearFactors_le
    (p : Polynomial K) (l : List K) :
    (peelLinearFactors p l).natDegree ≤ p.natDegree := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih =>
      exact
        (ih (p /ₘ (Polynomial.X - Polynomial.C a))).trans
          (by
            rw [Polynomial.natDegree_divByMonic p
              (Polynomial.monic_X_sub_C a)]
            exact Nat.sub_le _ _)

theorem coeff_peelLinearFactors_replicate_zero
    (p : Polynomial K) (d n : ℕ) :
    (peelLinearFactors p (List.replicate d 0)).coeff n =
      p.coeff (n + d) := by
  induction d generalizing p with
  | zero => simp
  | succ d ih =>
      rw [List.replicate_succ, peelLinearFactors_cons, ih]
      rw [Polynomial.coeff_divByMonic_X_sub_C_rec]
      simp [Nat.add_assoc]

theorem eval_zero_peelLinearFactors_replicate_zero
    (p : Polynomial K) (d : ℕ) :
    (peelLinearFactors p (List.replicate d 0)).eval 0 =
      p.coeff d := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simpa using
    (coeff_peelLinearFactors_replicate_zero p d 0)

/--
After removing pairwise-distinct listed roots, every other root remains a
root of the synthetic quotient.
-/
theorem isRoot_peelLinearFactors_of_not_mem
    (p : Polynomial K) (l : List K) (y : K)
    (hl : l.Nodup)
    (hroots : ∀ a ∈ l, p.IsRoot a)
    (hy : p.IsRoot y)
    (hymem : y ∉ l) :
    (peelLinearFactors p l).IsRoot y := by
  induction l generalizing p with
  | nil => simpa using hy
  | cons a l ih =>
      have hnodup := List.nodup_cons.mp hl
      have hynot := (by
        simpa only [List.mem_cons, not_or] using hymem :
          y ≠ a ∧ y ∉ l)
      have ha : p.IsRoot a := hroots a (by simp)
      have hfactor :
          (Polynomial.X - Polynomial.C a) *
              (p /ₘ (Polynomial.X - Polynomial.C a)) = p :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
      have hay : y - a ≠ 0 := sub_ne_zero.mpr (by
        intro h
        apply hymem
        simp [h])
      have hyquot :
          (p /ₘ (Polynomial.X - Polynomial.C a)).IsRoot y := by
        have hev := congrArg (fun q : Polynomial K => q.eval y) hfactor
        simp only [Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C] at hev
        exact (mul_eq_zero.mp (hev.trans hy)).resolve_left hay
      have htailroots :
          ∀ b ∈ l,
            (p /ₘ (Polynomial.X - Polynomial.C a)).IsRoot b := by
        intro b hb
        have hbroot : p.IsRoot b := hroots b (by simp [hb])
        have hab : b - a ≠ 0 := sub_ne_zero.mpr (by
          intro h
          subst b
          exact hnodup.1 hb)
        have hev := congrArg (fun q : Polynomial K => q.eval b) hfactor
        simp only [Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C] at hev
        exact (mul_eq_zero.mp (hev.trans hbroot)).resolve_left hab
      exact ih (p /ₘ (Polynomial.X - Polynomial.C a))
        hnodup.2 htailroots hyquot hynot.2

theorem coeff_divByMonic_X_sub_C_eq_sum_Icc_of_natDegree_le
    (p : Polynomial K) (a : K) (n D : ℕ)
    (hdegree : p.natDegree ≤ D) :
    (p /ₘ (Polynomial.X - Polynomial.C a)).coeff n =
      ∑ i ∈ Finset.Icc (n + 1) D,
        a ^ (i - (n + 1)) * p.coeff i := by
  rw [Polynomial.coeff_divByMonic_X_sub_C]
  apply Finset.sum_subset
  · exact Finset.Icc_subset_Icc_right hdegree
  · intro i hi hnot
    have hiLower : n + 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hiDegree : p.natDegree < i := by
      by_contra hle
      exact hnot (Finset.mem_Icc.mpr ⟨hiLower, Nat.le_of_not_gt hle⟩)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hiDegree, mul_zero]

section ComplexContinuity

variable {α : Type*} {l : Filter α}

/-- Synthetic division by a moving linear factor is coefficientwise
continuous on any uniformly degree-bounded family of polynomials. -/
theorem tendsto_coeff_divByMonic_X_sub_C
    (p : α → Polynomial ℂ) (p₀ : Polynomial ℂ)
    (a : α → ℂ) (a₀ : ℂ) (D n : ℕ)
    (hp :
      ∀ i, Tendsto (fun x => (p x).coeff i) l (𝓝 (p₀.coeff i)))
    (hdegree : ∀ᶠ x in l, (p x).natDegree ≤ D)
    (hdegree₀ : p₀.natDegree ≤ D)
    (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto
      (fun x =>
        (p x /ₘ (Polynomial.X - Polynomial.C (a x))).coeff n)
      l
      (𝓝
        ((p₀ /ₘ (Polynomial.X - Polynomial.C a₀)).coeff n)) := by
  have hsum :
      Tendsto
        (fun x =>
          ∑ i ∈ Finset.Icc (n + 1) D,
            a x ^ (i - (n + 1)) * (p x).coeff i)
        l
        (𝓝
          (∑ i ∈ Finset.Icc (n + 1) D,
            a₀ ^ (i - (n + 1)) * p₀.coeff i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (ha.pow _).mul (hp i)
  rw [← coeff_divByMonic_X_sub_C_eq_sum_Icc_of_natDegree_le
    p₀ a₀ n D hdegree₀] at hsum
  apply hsum.congr'
  filter_upwards [hdegree] with x hx
  exact
    (coeff_divByMonic_X_sub_C_eq_sum_Icc_of_natDegree_le
      (p x) (a x) n D hx).symm

/-- Repeated synthetic division is coefficientwise continuous when all
moving roots tend to the same center. -/
theorem tendsto_coeff_peelLinearFactors_map
    (p : α → Polynomial ℂ) (p₀ : Polynomial ℂ)
    (γ : List (α → ℂ)) (y₀ : ℂ) (D n : ℕ)
    (hp :
      ∀ i, Tendsto (fun x => (p x).coeff i) l (𝓝 (p₀.coeff i)))
    (hdegree : ∀ᶠ x in l, (p x).natDegree ≤ D)
    (hdegree₀ : p₀.natDegree ≤ D)
    (hγ : ∀ f ∈ γ, Tendsto f l (𝓝 y₀)) :
    Tendsto
      (fun x =>
        (peelLinearFactors (p x) (γ.map fun f => f x)).coeff n)
      l
      (𝓝
        ((peelLinearFactors p₀
          (List.replicate γ.length y₀)).coeff n)) := by
  induction γ generalizing p p₀ with
  | nil =>
      simpa using hp n
  | cons f γ ih =>
      have hf : Tendsto f l (𝓝 y₀) :=
        hγ f (by simp)
      have hpdiv :
          ∀ i,
            Tendsto
              (fun x =>
                (p x /ₘ
                    (Polynomial.X - Polynomial.C (f x))).coeff i)
              l
              (𝓝
                ((p₀ /ₘ
                    (Polynomial.X - Polynomial.C y₀)).coeff i)) :=
        fun i =>
          tendsto_coeff_divByMonic_X_sub_C
            p p₀ f y₀ D i hp hdegree hdegree₀ hf
      have hdegreeDiv :
          ∀ᶠ x in l,
            (p x /ₘ
              (Polynomial.X - Polynomial.C (f x))).natDegree ≤ D := by
        filter_upwards [hdegree] with x hx
        rw [Polynomial.natDegree_divByMonic
          (p x) (Polynomial.monic_X_sub_C (f x))]
        exact (Nat.sub_le _ _).trans hx
      have hdegree₀Div :
          (p₀ /ₘ
              (Polynomial.X - Polynomial.C y₀)).natDegree ≤ D := by
        rw [Polynomial.natDegree_divByMonic
          p₀ (Polynomial.monic_X_sub_C y₀)]
        exact (Nat.sub_le _ _).trans hdegree₀
      have htail :
          ∀ g ∈ γ, Tendsto g l (𝓝 y₀) := by
        intro g hg
        exact hγ g (by simp [hg])
      simpa [peelLinearFactors, List.replicate_succ] using
        ih
          (p := fun x =>
            p x /ₘ (Polynomial.X - Polynomial.C (f x)))
          (p₀ := p₀ /ₘ
            (Polynomial.X - Polynomial.C y₀))
          hpdiv hdegreeDiv hdegree₀Div htail

/-- Evaluation is continuous for a coefficientwise-convergent family with a
uniform degree bound. -/
theorem tendsto_eval_of_tendsto_coeff_of_natDegree_le
    (p : α → Polynomial ℂ) (p₀ : Polynomial ℂ)
    (y : α → ℂ) (y₀ : ℂ) (D : ℕ)
    (hp :
      ∀ i, Tendsto (fun x => (p x).coeff i) l (𝓝 (p₀.coeff i)))
    (hdegree : ∀ᶠ x in l, (p x).natDegree ≤ D)
    (hdegree₀ : p₀.natDegree ≤ D)
    (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun x => (p x).eval (y x)) l
      (𝓝 (p₀.eval y₀)) := by
  have hsum :
      Tendsto
        (fun x =>
          ∑ i ∈ Finset.range (D + 1),
            (p x).coeff i * y x ^ i)
        l
        (𝓝
          (∑ i ∈ Finset.range (D + 1),
            p₀.coeff i * y₀ ^ i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (hp i).mul (hy.pow i)
  rw [← Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le hdegree₀) y₀] at hsum
  apply hsum.congr'
  filter_upwards [hdegree] with x hx
  exact
    (Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le hx) (y x)).symm

/-- Specialize the parameter of a concrete bivariate polynomial. -/
def specializeBivPolynomial
    (Q : Polynomial (Polynomial ℂ)) (x : ℂ) :
    Polynomial ℂ :=
  Q.map (Polynomial.evalRingHom x)

@[simp]
theorem coeff_specializeBivPolynomial
    (Q : Polynomial (Polynomial ℂ)) (x : ℂ) (i : ℕ) :
    (specializeBivPolynomial Q x).coeff i =
      (Q.coeff i).eval x := by
  simp [specializeBivPolynomial]

@[simp]
theorem eval_specializeBivPolynomial
    (Q : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    (specializeBivPolynomial Q x).eval y =
      CurveSelection.TerminationScratch.bivEvalAt Q x y := by
  simp [specializeBivPolynomial,
    CurveSelection.TerminationScratch.bivEvalAt,
    Polynomial.eval_map]

theorem tendsto_coeff_specializeBivPolynomial
    (Q : Polynomial (Polynomial ℂ))
    (x : α → ℂ) (x₀ : ℂ)
    (hx : Tendsto x l (𝓝 x₀)) (i : ℕ) :
    Tendsto
      (fun u => (specializeBivPolynomial Q (x u)).coeff i)
      l
      (𝓝 ((specializeBivPolynomial Q x₀).coeff i)) := by
  simp only [coeff_specializeBivPolynomial]
  exact Filter.Tendsto.comp
    (Polynomial.continuous_eval₂
      (Q.coeff i) (RingHom.id ℂ)).continuousAt hx

/-- Weierstrass preparation identifies the number of centered local branches
with the exact multiplicity of the specialized concrete polynomial at zero.
Equivalently, peeling that many zero linear factors leaves a nonzero
residual at zero. -/
theorem residual_ne_zero_of_isWeierstrassFactorization
    (Q : Polynomial (Polynomial ℂ))
    (f : Polynomial (PowerSeries ℂ))
    (unit : PowerSeries (PowerSeries ℂ))
    (H :
      (bivPolynomialToIteratedPowerSeries Q).IsWeierstrassFactorization
        f unit) :
    (peelLinearFactors
      (specializeBivPolynomial Q 0)
      (List.replicate f.natDegree 0)).eval 0 ≠ 0 := by
  rw [eval_zero_peelLinearFactors_replicate_zero,
    coeff_specializeBivPolynomial]
  have hmap :
      (bivPolynomialToIteratedPowerSeries Q).map
        (IsLocalRing.residue (PowerSeries ℂ)) ≠ 0 :=
    H.map_ne_zero
  have hcoeff :=
    PowerSeries.coeff_order hmap
  rw [← H.natDegree_eq_toNat_order_map] at hcoeff
  intro hzero
  apply hcoeff
  rw [PowerSeries.coeff_map,
    IsLocalRing.residue_eq_zero_iff,
    PowerSeries.maximalIdeal_eq_span_X,
    Ideal.mem_span_singleton,
    PowerSeries.X_dvd_iff]
  simpa [bivPolynomialToIteratedPowerSeries,
    bivPolynomialToPowerSeriesPolynomial,
    Polynomial.eval] using hzero

/--
Two analytic tails attached after distinct polynomial jets of degree below
`n` are distinct on a punctured neighborhood of zero.

The proof divides the jet difference by its lowest nonzero monomial.  The
normalized difference has a nonzero value at zero, while the two tails carry
a strictly higher power of the parameter.
-/
theorem eventually_ne_of_distinct_polynomial_jets
    (A B : Polynomial ℂ) (n : ℕ)
    (z w : ℂ → ℂ)
    (hAdegree : A.natDegree < n)
    (hBdegree : B.natDegree < n)
    (hAB : A ≠ B)
    (hz : ContinuousAt z 0)
    (hw : ContinuousAt w 0) :
    ∀ᶠ x in 𝓝[({0}ᶜ : Set ℂ)] (0 : ℂ),
      A.eval x + x ^ n * z x ≠
        B.eval x + x ^ n * w x := by
  let D : Polynomial ℂ := A - B
  have hD : D ≠ 0 := sub_ne_zero.mpr hAB
  let m := D.natTrailingDegree
  let E : Polynomial ℂ := D /ₘ (Polynomial.X ^ m)
  have hmDegree : m ≤ D.natDegree :=
    Polynomial.natTrailingDegree_le_natDegree D
  have hDDegree : D.natDegree < n := by
    exact
      (Polynomial.natDegree_sub_le A B).trans_lt
        (max_lt hAdegree hBdegree)
  have hmn : m < n := hmDegree.trans_lt hDDegree
  have hmle : m ≤ n := hmn.le
  have hfactor :
      Polynomial.X ^ m * E = D := by
    have h :=
      Polynomial.pow_mul_divByMonic_rootMultiplicity_eq D (0 : ℂ)
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree'] at h
    simpa [m, E] using h
  have hEzero : E.eval 0 ≠ 0 := by
    have h :=
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero
        (p := D) (0 : ℂ) hD
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree'] at h
    simpa [m, E] using h
  let bracket : ℂ → ℂ :=
    fun x => E.eval x + x ^ (n - m) * (z x - w x)
  have hbracketContinuous : ContinuousAt bracket 0 := by
    dsimp [bracket]
    exact
      (Polynomial.continuous_eval₂ E (RingHom.id ℂ)).continuousAt.add
        ((continuousAt_id.pow (n - m)).mul (hz.sub hw))
  have hnmpos : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hbracketZero : bracket 0 ≠ 0 := by
    simpa [bracket, zero_pow (Nat.ne_of_gt hnmpos)] using hEzero
  have hbracketNe :
      ∀ᶠ x in 𝓝 (0 : ℂ), bracket x ≠ 0 :=
    hbracketContinuous.eventually_ne hbracketZero
  filter_upwards
    [hbracketNe.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin]
    with x hxBracket hxpunctured
  have hx : x ≠ 0 := by simpa using hxpunctured
  have hxpow : x ^ m ≠ 0 := pow_ne_zero _ hx
  intro heq
  have hsub :
      A.eval x + x ^ n * z x -
          (B.eval x + x ^ n * w x) = 0 :=
    sub_eq_zero.mpr heq
  have hpow : x ^ n = x ^ m * x ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmle]
  have hnormalized :
      A.eval x + x ^ n * z x -
          (B.eval x + x ^ n * w x) =
        x ^ m * bracket x := by
    have hfactorEval :=
      congrArg (fun p : Polynomial ℂ => p.eval x) hfactor
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X] at hfactorEval
    dsimp [D] at hfactorEval
    rw [Polynomial.eval_sub] at hfactorEval
    dsimp [bracket]
    rw [hpow]
    calc
      A.eval x + x ^ m * x ^ (n - m) * z x -
            (B.eval x + x ^ m * x ^ (n - m) * w x) =
          (A.eval x - B.eval x) +
            x ^ m * x ^ (n - m) * (z x - w x) := by ring
      _ =
          x ^ m * E.eval x +
            x ^ m * x ^ (n - m) * (z x - w x) := by
            rw [← hfactorEval]
      _ = x ^ m *
          (E.eval x + x ^ (n - m) * (z x - w x)) := by ring
  rw [hnormalized] at hsub
  exact hxBracket ((mul_eq_zero.mp hsub).resolve_left hxpow)

theorem eventually_not_mem_map_apply
    {β : Type*} (f : α → β) (γ : List (α → β))
    (h :
      ∀ g ∈ γ, ∀ᶠ x in l, f x ≠ g x) :
    ∀ᶠ x in l, f x ∉ γ.map fun g => g x := by
  induction γ with
  | nil => simp
  | cons g γ ih =>
      have hfg : ∀ᶠ x in l, f x ≠ g x :=
        h g (by simp)
      have htail :
          ∀ᶠ x in l, f x ∉ γ.map fun k => k x :=
        ih (fun k hk => h k (by simp [hk]))
      filter_upwards [hfg, htail] with x hxg hxtail
      simp [hxg, hxtail]

/-- A finite list of functions that are pairwise eventually unequal becomes
pointwise duplicate-free eventually. -/
theorem eventually_nodup_map_apply
    {β : Type*} (γ : List (α → β))
    (hγ : γ.Nodup)
    (hpair :
      ∀ f ∈ γ, ∀ g ∈ γ, f ≠ g →
        ∀ᶠ x in l, f x ≠ g x) :
    ∀ᶠ x in l, (γ.map fun f => f x).Nodup := by
  induction γ with
  | nil => simp
  | cons f γ ih =>
      have hnodup := List.nodup_cons.mp hγ
      have hhead :
          ∀ᶠ x in l, f x ∉ γ.map fun g => g x := by
        apply eventually_not_mem_map_apply f γ
        intro g hg
        apply hpair f (by simp) g (by simp [hg])
        intro hfg
        subst g
        exact hnodup.1 hg
      have htail :
          ∀ᶠ x in l, (γ.map fun g => g x).Nodup := by
        apply ih hnodup.2
        intro g hg k hk hgk
        exact hpair g (by simp [hg]) k (by simp [hk]) hgk
      filter_upwards [hhead, htail] with x hxhead hxtail
      simpa using List.nodup_cons.mpr ⟨hxhead, hxtail⟩

/-- Indexed version of finite eventual pointwise injectivity. -/
theorem eventually_nodup_map_apply_indexed
    {β ι : Type*} (items : List ι)
    (hitems : items.Nodup)
    (f : ι → α → β)
    (hpair :
      ∀ i ∈ items, ∀ j ∈ items, i ≠ j →
        ∀ᶠ x in l, f i x ≠ f j x) :
    ∀ᶠ x in l, (items.map fun i => f i x).Nodup := by
  induction items with
  | nil => simp
  | cons i items ih =>
      have hnodup := List.nodup_cons.mp hitems
      have hhead :
          ∀ᶠ x in l, f i x ∉ items.map fun j => f j x := by
        have htmp :
            ∀ᶠ x in l,
              f i x ∉ (items.map f).map fun g => g x := by
          apply eventually_not_mem_map_apply
            (l := l) (f i) (items.map f)
          intro g hg
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
          apply hpair i (by simp) j (by simp [hj])
          intro hij
          subst j
          exact hnodup.1 hj
        simpa [List.map_map, Function.comp_def] using htmp
      have htail :
          ∀ᶠ x in l,
            (items.map fun j => f j x).Nodup := by
        apply ih hnodup.2
        intro j hj k hk hjk
        exact hpair j (by simp [hj]) k (by simp [hk]) hjk
      filter_upwards [hhead, htail] with x hxhead hxtail
      simpa using List.nodup_cons.mpr ⟨hxhead, hxtail⟩

theorem eventually_forall_mem_list
    {ι : Type*} (items : List ι) (P : ι → α → Prop)
    (h : ∀ i ∈ items, ∀ᶠ x in l, P i x) :
    ∀ᶠ x in l, ∀ i ∈ items, P i x := by
  induction items with
  | nil => simp
  | cons i items ih =>
      have hi : ∀ᶠ x in l, P i x :=
        h i (by simp)
      have htail :
          ∀ᶠ x in l, ∀ j ∈ items, P j x :=
        ih fun j hj => h j (by simp [hj])
      filter_upwards [hi, htail] with x hix htailx
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hix
      · exact htailx j hj

/-- Distinct formal power series have distinct sufficiently long polynomial
truncations. -/
theorem eventually_trunc_ne_of_ne
    (s t : PowerSeries ℂ) (hst : s ≠ t) :
    ∀ᶠ n in atTop, s.trunc n ≠ t.trunc n := by
  have hcoeff :
      ∃ k, PowerSeries.coeff k s ≠ PowerSeries.coeff k t := by
    by_contra h
    push Not at h
    apply hst
    ext k
    exact h k
  obtain ⟨k, hk⟩ := hcoeff
  filter_upwards [eventually_gt_atTop k] with n hn
  intro htrunc
  have hcoeffTrunc :=
    congrArg (fun p : Polynomial ℂ => p.coeff k) htrunc
  simp only [PowerSeries.coeff_trunc,
    if_pos hn] at hcoeffTrunc
  exact hk hcoeffTrunc

/-- A finite duplicate-free family of formal branches admits one truncation
length that both separates every branch and exceeds any prescribed
branchwise order. -/
theorem exists_common_separating_truncation
    (roots : List (PowerSeries ℂ))
    (hroots : roots.Nodup)
    (order : PowerSeries ℂ → ℕ) :
    ∃ n : ℕ,
      0 < n ∧
      (roots.map fun s => s.trunc n).Nodup ∧
      ∀ s ∈ roots, order s < n := by
  have hseparate :
      ∀ᶠ n in atTop,
        (roots.map fun s => s.trunc n).Nodup := by
    apply eventually_nodup_map_apply_indexed
      (l := atTop) roots hroots (fun s n => s.trunc n)
    intro s hs t ht hst
    exact eventually_trunc_ne_of_ne s t hst
  have hlarge :
      ∀ᶠ n in atTop, ∀ s ∈ roots, order s < n := by
    apply eventually_forall_mem_list
      (l := atTop) roots (fun s n => order s < n)
    intro s hs
    exact eventually_gt_atTop (order s)
  have hpositive : ∀ᶠ n in atTop, 0 < n :=
    eventually_gt_atTop 0
  obtain ⟨n, hn, hnsep, hnlarge⟩ :=
    (hpositive.and (hseparate.and hlarge)).exists
  exact ⟨n, hn, hnsep, hnlarge⟩

set_option maxHeartbeats 800000 in
-- Explicit specialization creates a large but entirely routine elaboration.
/-- The residual obtained after peeling a finite family of centered moving
roots from a concrete bivariate polynomial converges at every convergent
moving evaluation point. -/
theorem tendsto_eval_peelLinearFactors_specialize
    (Q : Polynomial (Polynomial ℂ))
    (x : α → ℂ) (γ : List (α → ℂ)) (y : α → ℂ)
    (x₀ y₀ : ℂ)
    (hx : Tendsto x l (𝓝 x₀))
    (hγ : ∀ f ∈ γ, Tendsto f l (𝓝 y₀))
    (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto
      (fun u =>
        (peelLinearFactors
          (specializeBivPolynomial Q (x u))
          (γ.map fun f => f u)).eval (y u))
      l
      (𝓝
        ((peelLinearFactors
          (specializeBivPolynomial Q x₀)
          (List.replicate γ.length y₀)).eval y₀)) := by
  apply tendsto_eval_of_tendsto_coeff_of_natDegree_le
      (fun u =>
        peelLinearFactors
          (specializeBivPolynomial Q (x u))
          (γ.map fun f => f u))
      (peelLinearFactors
        (specializeBivPolynomial Q x₀)
        (List.replicate γ.length y₀))
      y y₀ Q.natDegree
  · intro i
    apply tendsto_coeff_peelLinearFactors_map
        (fun u => specializeBivPolynomial Q (x u))
        (specializeBivPolynomial Q x₀)
        γ y₀ Q.natDegree i
    · intro j
      exact tendsto_coeff_specializeBivPolynomial Q x x₀ hx j
    · exact Filter.Eventually.of_forall fun _ =>
        Polynomial.natDegree_map_le
    · exact Polynomial.natDegree_map_le
    · exact hγ
  · exact Filter.Eventually.of_forall fun u =>
      (natDegree_peelLinearFactors_le
        (specializeBivPolynomial Q (x u))
        (γ.map fun f => f u)).trans
          Polynomial.natDegree_map_le
  · exact
      (natDegree_peelLinearFactors_le
        (specializeBivPolynomial Q x₀)
        (List.replicate γ.length y₀)).trans
          Polynomial.natDegree_map_le
  · exact hy

/--
Finite local root coverage.

If finitely many centered moving roots are pairwise distinct off the center
and peeling their linear factors leaves a residual nonzero at the center,
then every other root converging to that center is eventually one of those
moving roots.
-/
theorem eventually_eq_branch_of_finite_centered_roots
    (Q : Polynomial (Polynomial ℂ))
    (x : α → ℂ) (γ : List (α → ℂ)) (y : α → ℂ)
    (x₀ y₀ : ℂ)
    (hx : Tendsto x l (𝓝 x₀))
    (hγ : ∀ f ∈ γ, Tendsto f l (𝓝 y₀))
    (hy : Tendsto y l (𝓝 y₀))
    (hroots :
      ∀ᶠ u in l, ∀ f ∈ γ,
        CurveSelection.TerminationScratch.bivEvalAt
          Q (x u) (f u) = 0)
    (hyroot :
      ∀ᶠ u in l,
        CurveSelection.TerminationScratch.bivEvalAt
          Q (x u) (y u) = 0)
    (hnodup :
      ∀ᶠ u in l, (γ.map fun f => f u).Nodup)
    (hresidual :
      (peelLinearFactors
        (specializeBivPolynomial Q x₀)
        (List.replicate γ.length y₀)).eval y₀ ≠ 0) :
    ∀ᶠ u in l, ∃ f ∈ γ, y u = f u := by
  have hresTendsto :=
    tendsto_eval_peelLinearFactors_specialize
      Q x γ y x₀ y₀ hx hγ hy
  have hresne :
      ∀ᶠ u in l,
        (peelLinearFactors
          (specializeBivPolynomial Q (x u))
          (γ.map fun f => f u)).eval (y u) ≠ 0 :=
    hresTendsto.eventually_ne hresidual
  filter_upwards [hresne, hroots, hyroot, hnodup]
    with u hres hbranch hyQ hdistinct
  by_contra hcovered
  push Not at hcovered
  have hymem : y u ∉ γ.map fun f => f u := by
    intro hmem
    obtain ⟨f, hf, hfy⟩ := List.mem_map.mp hmem
    exact hcovered f hf hfy.symm
  have hlisted :
      ∀ a ∈ γ.map (fun f => f u),
        (specializeBivPolynomial Q (x u)).IsRoot a := by
    intro a ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    simpa [Polynomial.IsRoot] using hbranch f hf
  have hyQ' :
      (specializeBivPolynomial Q (x u)).IsRoot (y u) := by
    simpa [Polynomial.IsRoot] using hyQ
  have hquotientRoot :=
    isRoot_peelLinearFactors_of_not_mem
      (specializeBivPolynomial Q (x u))
      (γ.map fun f => f u) (y u)
      hdistinct hlisted hyQ' hymem
  exact hres hquotientRoot

end ComplexContinuity

end CurveSelection.RootCoverage
end Math
