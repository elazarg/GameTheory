/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Algebra.Order.Field

/-!
# Comparing the analytic orders of several germs at `0`

`Mathlib.Analysis.Analytic.Order` measures the order of vanishing of a *single* analytic
germ.  This file compares the orders of *several* germs at `0` and turns the comparison
into limit statements along `t ↓ 0`.

## Main results

* `Math.eventuallyEq_zero_nhdsGT_iff_nhds`: for a germ analytic at `0`, vanishing on a right
  neighbourhood of `0` is the same as vanishing on a full neighbourhood.  This is what lets a
  consumer phrase its nondegeneracy hypothesis on the right half-line only.
* `Math.tendsto_div_nhdsGT_zero_of_analyticOrderAt_lt`: strictly larger order means the ratio
  tends to `0`.
* `Math.analyticOrderNatAt_trichotomy`: the three-way comparison of two orders, each branch
  packaged with its ratio limit.
* `Math.LeadingOrderJet`: the leading-order factorization of a whole family,
  `f i t = t ^ order * cofactor i t`, with at least one `cofactor i 0 ≠ 0`.
* `Math.exists_leadingOrderJet`: such a jet exists as soon as one member is not eventually
  zero on the right.
* `Math.familyAnalyticOrder`, `Math.leadingSet`: the least order of the family and the set of
  members realizing it; `Math.leadingSet_nonempty`.
* `Math.LeadingOrderJet.cofactor_pos`: **nonnegativity on the right forces the leading
  coefficients to be positive**.  This is what rules out cancellation in the denominator below.
* `Math.LeadingOrderJet.tendsto_div_sum`: the normalized family converges (not merely
  subsequentially) to a limit supported exactly on the leading set;
  `Math.LeadingOrderJet.tendsto_div_sum_nhds_zero` and
  `Math.LeadingOrderJet.tendsto_div_sum_pos` split that limit along the leading set, and
  `Math.LeadingOrderJet.sum_cofactor_leadingSet` identifies the denominator with the sum over
  the leading set.
* `Math.LeadingOrderJet.tendsto_pow_div_sum_nhds_zero`,
  `Math.LeadingOrderJet.tendsto_pow_div_sum_nhds_inv`,
  `Math.LeadingOrderJet.tendsto_pow_div_sum_atTop`: the comparison of the family against an
  external scale `t ^ q` is decided by comparing the two natural numbers `q` and `order`.
* `Math.exists_leadingOrder_normalization`: the whole package as one existential statement.

## `ℕ` versus `ℕ∞`

`ℕ∞` is needed exactly where a germ may vanish identically: `analyticOrderAt` is `⊤` there, and
`familyAnalyticOrder` is an infimum over all members, some of which may be `⊤`.  Everything
downstream of `LeadingOrderJet` uses the `ℕ`-valued `order`, which is legitimate because the
existence of a jet already forces the minimum to be finite.

## Hypotheses the consumer must discharge

Beyond analyticity, the family statements need

* `∀ i, ∀ᶠ t in 𝓝[>] 0, 0 ≤ f i t` — nonnegativity **on the right only**; and
* `∃ i, ¬ ∀ᶠ t in 𝓝[>] 0, f i t = 0` — some member is not identically zero as a right germ.

The second hypothesis is genuinely necessary: without it the family may be the zero family, the
denominator `∑ i, f i t` is identically `0`, and no normalized limit exists.  Nonnegativity is
also genuinely necessary for `cofactor_pos` and hence for the positivity of the denominator; with
signs allowed, `f = ![t, -t]` has `∑ i, f i t = 0`.
-/

noncomputable section

open Filter Set Topology

namespace Math

/-! ### A single germ -/

variable {f g : ℝ → ℝ}

/-- For a germ analytic at `0`, vanishing on a right neighbourhood of `0` is equivalent to
vanishing on a full neighbourhood of `0`.  Consequently a consumer that only controls the right
half-line still gets access to the two-sided `analyticOrderAt` API. -/
theorem eventuallyEq_zero_nhdsGT_iff_nhds (hf : AnalyticAt ℝ f 0) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), f t = 0) ↔ ∀ᶠ t in 𝓝 (0 : ℝ), f t = 0 := by
  refine ⟨fun h => ?_, fun h => h.filter_mono nhdsWithin_le_nhds⟩
  by_contra hcon
  obtain ⟨n, c, hc, hc0, hfac⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hcon
  have hcne : ∀ᶠ t in 𝓝 (0 : ℝ), c t ≠ 0 := hc.continuousAt.eventually_ne hc0
  have hfalse : ∀ᶠ _t in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [h, self_mem_nhdsWithin, hfac.filter_mono nhdsWithin_le_nhds,
      hcne.filter_mono nhdsWithin_le_nhds] with t hzero ht hfa hcn
    rw [hzero] at hfa
    simp only [sub_zero, smul_eq_mul] at hfa
    exact mul_ne_zero (pow_ne_zero n (ne_of_gt ht)) hcn hfa.symm
  simpa using hfalse.exists

/-- Finiteness of the analytic order, expressed by a right-germ hypothesis. -/
theorem analyticOrderAt_ne_top_iff_nhdsGT (hf : AnalyticAt ℝ f 0) :
    analyticOrderAt f 0 ≠ ⊤ ↔ ¬∀ᶠ t in 𝓝[>] (0 : ℝ), f t = 0 := by
  simp only [Ne, analyticOrderAt_eq_top, eventuallyEq_zero_nhdsGT_iff_nhds hf]

/-- The exact leading factorization of a germ of finite order, in multiplicative form. -/
theorem exists_cofactor_of_analyticOrderAt_ne_top (hf : AnalyticAt ℝ f 0)
    (hne : analyticOrderAt f 0 ≠ ⊤) :
    ∃ c : ℝ → ℝ, AnalyticAt ℝ c 0 ∧ c 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), f t = t ^ analyticOrderNatAt f 0 * c t := by
  obtain ⟨c, hc, hc0, hfac⟩ := hf.analyticOrderAt_ne_top.mp hne
  refine ⟨c, hc, hc0, ?_⟩
  filter_upwards [hfac] with t ht
  simpa using ht

/-- A germ of order at least `n` factors through `t ^ n`, with no claim on the cofactor at `0`. -/
theorem exists_cofactor_of_natCast_le (hf : AnalyticAt ℝ f 0) {n : ℕ}
    (hn : (n : ℕ∞) ≤ analyticOrderAt f 0) :
    ∃ c : ℝ → ℝ, AnalyticAt ℝ c 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ), f t = t ^ n * c t := by
  obtain ⟨c, hc, hfac⟩ := (natCast_le_analyticOrderAt hf).mp hn
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfac] with t ht
  simpa using ht

/-- A germ presented as `t ^ n` times an analytic factor is analytic. -/
theorem analyticAt_of_eq_pow_mul {n : ℕ} {c : ℝ → ℝ} (hc : AnalyticAt ℝ c 0)
    (hfac : ∀ᶠ t in 𝓝 (0 : ℝ), f t = t ^ n * c t) : AnalyticAt ℝ f 0 :=
  ((analyticAt_id.pow n).mul hc).congr (Filter.EventuallyEq.symm hfac)

/-- A factorization through `t ^ n` is a lower bound on the order. -/
theorem le_analyticOrderAt_of_eq_pow_mul {n : ℕ} {c : ℝ → ℝ} (hc : AnalyticAt ℝ c 0)
    (hfac : ∀ᶠ t in 𝓝 (0 : ℝ), f t = t ^ n * c t) : (n : ℕ∞) ≤ analyticOrderAt f 0 := by
  refine (natCast_le_analyticOrderAt (analyticAt_of_eq_pow_mul hc hfac)).mpr ⟨c, hc, ?_⟩
  filter_upwards [hfac] with t ht
  simpa using ht

/-- A factorization through `t ^ n` with a nonvanishing cofactor computes the order exactly. -/
theorem analyticOrderAt_eq_of_eq_pow_mul {n : ℕ} {c : ℝ → ℝ} (hc : AnalyticAt ℝ c 0)
    (hc0 : c 0 ≠ 0) (hfac : ∀ᶠ t in 𝓝 (0 : ℝ), f t = t ^ n * c t) :
    analyticOrderAt f 0 = n := by
  refine (analyticAt_of_eq_pow_mul hc hfac).analyticOrderAt_eq_natCast.mpr ⟨c, hc, hc0, ?_⟩
  filter_upwards [hfac] with t ht
  simpa using ht

/-- A factorization through `t ^ n` whose cofactor *does* vanish at `0` forces the order to be
strictly larger than `n`. -/
theorem lt_analyticOrderAt_of_eq_pow_mul {n : ℕ} {c : ℝ → ℝ} (hc : AnalyticAt ℝ c 0)
    (hc0 : c 0 = 0) (hfac : ∀ᶠ t in 𝓝 (0 : ℝ), f t = t ^ n * c t) :
    (n : ℕ∞) < analyticOrderAt f 0 := by
  have hcne : analyticOrderAt c 0 ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hc, hc0⟩
  have h1 : ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt c 0 := by
    simpa using Order.one_le_iff_ne_zero.mpr hcne
  obtain ⟨d, hd, hdfac⟩ := exists_cofactor_of_natCast_le hc h1
  have hfac' : ∀ᶠ t in 𝓝 (0 : ℝ), f t = t ^ (n + 1) * d t := by
    filter_upwards [hfac, hdfac] with t ht htd
    rw [ht, htd, pow_succ]
    ring
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0 :=
    le_analyticOrderAt_of_eq_pow_mul hd hfac'
  refine lt_of_lt_of_le ?_ hle
  exact_mod_cast Nat.lt_succ_self n

/-! ### Comparing two germs -/

/-- **Order comparison, strict case.**  If `f` vanishes to strictly smaller order than `g` at
`0`, then `g t / f t → 0` as `t ↓ 0`.

No nondegeneracy hypothesis on `g` is needed: `analyticOrderAt g 0 = ⊤` (i.e. `g` is a zero germ)
is allowed and is covered by the same proof. -/
theorem tendsto_div_nhdsGT_zero_of_analyticOrderAt_lt (hf : AnalyticAt ℝ f 0)
    (hg : AnalyticAt ℝ g 0) (hlt : analyticOrderAt f 0 < analyticOrderAt g 0) :
    Tendsto (fun t => g t / f t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hftop : analyticOrderAt f 0 ≠ ⊤ := hlt.ne_top
  obtain ⟨c, hc, hc0, hcfac⟩ := exists_cofactor_of_analyticOrderAt_ne_top hf hftop
  set m := analyticOrderNatAt f 0 with hm
  have hmcast : (m : ℕ∞) = analyticOrderAt f 0 := Nat.cast_analyticOrderNatAt hftop
  have hgle : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g 0 := by
    rw [Nat.cast_add, Nat.cast_one, hmcast]
    exact (ENat.add_one_le_iff hftop).mpr hlt
  obtain ⟨d, hd, hdfac⟩ := exists_cofactor_of_natCast_le hg hgle
  have hcongr : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * d t / c t = g t / f t := by
    filter_upwards [hcfac.filter_mono nhdsWithin_le_nhds,
      hdfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hcf hdf ht
    rw [hcf, hdf, pow_succ]
    rw [show t ^ m * t * d t = t ^ m * (t * d t) by ring]
    exact (mul_div_mul_left (t * d t) (c t) (pow_ne_zero m (ne_of_gt ht))).symm
  refine Tendsto.congr' hcongr ?_
  have hlim : Tendsto (fun t : ℝ => t * d t / c t) (𝓝[>] (0 : ℝ)) (𝓝 (0 * d 0 / c 0)) :=
    ((tendsto_id.mono_right nhdsWithin_le_nhds).mul
        (hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).div
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hc0
  simpa using hlim

/-- **Order comparison, equal case.**  Two germs of the same finite order have a nonzero finite
ratio limit, namely the quotient of their leading coefficients. -/
theorem exists_ne_zero_tendsto_div_nhdsGT_of_analyticOrderAt_eq (hf : AnalyticAt ℝ f 0)
    (hg : AnalyticAt ℝ g 0) (hftop : analyticOrderAt f 0 ≠ ⊤) (hgtop : analyticOrderAt g 0 ≠ ⊤)
    (heq : analyticOrderAt f 0 = analyticOrderAt g 0) :
    ∃ r : ℝ, r ≠ 0 ∧ Tendsto (fun t => g t / f t) (𝓝[>] (0 : ℝ)) (𝓝 r) := by
  obtain ⟨c, hc, hc0, hcfac⟩ := exists_cofactor_of_analyticOrderAt_ne_top hf hftop
  obtain ⟨d, hd, hd0, hdfac⟩ := exists_cofactor_of_analyticOrderAt_ne_top hg hgtop
  have hnat : analyticOrderNatAt f 0 = analyticOrderNatAt g 0 := by
    simp only [analyticOrderNatAt, heq]
  refine ⟨d 0 / c 0, div_ne_zero hd0 hc0, ?_⟩
  have hcongr : ∀ᶠ t in 𝓝[>] (0 : ℝ), d t / c t = g t / f t := by
    filter_upwards [hcfac.filter_mono nhdsWithin_le_nhds,
      hdfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hcf hdf ht
    rw [hcf, hdf, ← hnat]
    exact (mul_div_mul_left (d t) (c t)
      (pow_ne_zero (analyticOrderNatAt f 0) (ne_of_gt ht))).symm
  refine Tendsto.congr' hcongr ?_
  exact (hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hc0

/-- **Order trichotomy for two germs.**  For two germs analytic at `0`, neither of which vanishes
identically to the right of `0`, exactly one of the three comparisons of the natural-number orders
holds, and each branch carries its ratio limit. -/
theorem analyticOrderNatAt_trichotomy (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0)
    (hfne : ¬∀ᶠ t in 𝓝[>] (0 : ℝ), f t = 0) (hgne : ¬∀ᶠ t in 𝓝[>] (0 : ℝ), g t = 0) :
    (analyticOrderNatAt f 0 < analyticOrderNatAt g 0 ∧
        Tendsto (fun t => g t / f t) (𝓝[>] (0 : ℝ)) (𝓝 0)) ∨
      (analyticOrderNatAt f 0 = analyticOrderNatAt g 0 ∧
        ∃ r : ℝ, r ≠ 0 ∧ Tendsto (fun t => g t / f t) (𝓝[>] (0 : ℝ)) (𝓝 r)) ∨
      (analyticOrderNatAt g 0 < analyticOrderNatAt f 0 ∧
        Tendsto (fun t => f t / g t) (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  have hftop : analyticOrderAt f 0 ≠ ⊤ := (analyticOrderAt_ne_top_iff_nhdsGT hf).mpr hfne
  have hgtop : analyticOrderAt g 0 ≠ ⊤ := (analyticOrderAt_ne_top_iff_nhdsGT hg).mpr hgne
  have hfcast : ((analyticOrderNatAt f 0 : ℕ) : ℕ∞) = analyticOrderAt f 0 :=
    Nat.cast_analyticOrderNatAt hftop
  have hgcast : ((analyticOrderNatAt g 0 : ℕ) : ℕ∞) = analyticOrderAt g 0 :=
    Nat.cast_analyticOrderNatAt hgtop
  rcases lt_trichotomy (analyticOrderNatAt f 0) (analyticOrderNatAt g 0) with hlt | heq | hgt
  · refine Or.inl ⟨hlt, tendsto_div_nhdsGT_zero_of_analyticOrderAt_lt hf hg ?_⟩
    rw [← hfcast, ← hgcast]
    exact_mod_cast hlt
  · refine Or.inr (Or.inl ⟨heq, ?_⟩)
    refine exists_ne_zero_tendsto_div_nhdsGT_of_analyticOrderAt_eq hf hg hftop hgtop ?_
    rw [← hfcast, ← hgcast, heq]
  · refine Or.inr (Or.inr ⟨hgt, tendsto_div_nhdsGT_zero_of_analyticOrderAt_lt hg hf ?_⟩)
    rw [← hfcast, ← hgcast]
    exact_mod_cast hgt

/-! ### The minimal order of a finite family -/

variable {ι : Type*}

/-- The least analytic order at `0` among a finite family of germs, valued in `ℕ∞`.

`ℕ∞` is unavoidable here: a member vanishing identically near `0` has order `⊤`, and there is no
natural number recording that.  Once one member is not eventually zero on the right the infimum
itself is finite; see `Math.familyAnalyticOrder_eq_order`. -/
def familyAnalyticOrder [Fintype ι] (f : ι → ℝ → ℝ) : ℕ∞ :=
  Finset.univ.inf fun i => analyticOrderAt (f i) 0

/-- The leading set of a finite family: the members realizing the least order. -/
def leadingSet [Fintype ι] (f : ι → ℝ → ℝ) : Set ι :=
  {i | analyticOrderAt (f i) 0 = familyAnalyticOrder f}

@[simp]
theorem mem_leadingSet [Fintype ι] {f : ι → ℝ → ℝ} {i : ι} :
    i ∈ leadingSet f ↔ analyticOrderAt (f i) 0 = familyAnalyticOrder f := Iff.rfl

theorem familyAnalyticOrder_le [Fintype ι] {f : ι → ℝ → ℝ} (i : ι) :
    familyAnalyticOrder f ≤ analyticOrderAt (f i) 0 :=
  Finset.inf_le (Finset.mem_univ i)

/-! ### Leading-order data for a whole family -/

/-- The simultaneous leading-order factorization of a family of germs at `0`.

Every member is divided by the *same* power `t ^ order`, which is the minimum of the members'
orders; the resulting `cofactor i` is analytic, and it is nonzero at `0` exactly for the members
that realize the minimum.  At least one member does, which is what `exists_leading` records. -/
structure LeadingOrderJet (f : ι → ℝ → ℝ) where
  /-- The common power factored out of every member; the least order in the family. -/
  order : ℕ
  /-- The analytic cofactor of member `i` after `t ^ order` has been removed. -/
  cofactor : ι → ℝ → ℝ
  /-- Every cofactor is analytic at `0`. -/
  analytic_cofactor : ∀ i, AnalyticAt ℝ (cofactor i) 0
  /-- The defining factorization, valid on a full neighbourhood of `0`. -/
  factor_eq : ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), f i t = t ^ order * cofactor i t
  /-- Some member realizes the order, i.e. its cofactor does not vanish at `0`. -/
  exists_leading : ∃ i, cofactor i 0 ≠ 0

namespace LeadingOrderJet

variable {f : ι → ℝ → ℝ}

theorem analyticAt (jet : LeadingOrderJet f) (i : ι) : AnalyticAt ℝ (f i) 0 :=
  analyticAt_of_eq_pow_mul (jet.analytic_cofactor i) (jet.factor_eq i)

theorem order_le_analyticOrderAt (jet : LeadingOrderJet f) (i : ι) :
    (jet.order : ℕ∞) ≤ analyticOrderAt (f i) 0 :=
  le_analyticOrderAt_of_eq_pow_mul (jet.analytic_cofactor i) (jet.factor_eq i)

theorem analyticOrderAt_eq_order (jet : LeadingOrderJet f) {i : ι} (hi : jet.cofactor i 0 ≠ 0) :
    analyticOrderAt (f i) 0 = jet.order :=
  analyticOrderAt_eq_of_eq_pow_mul (jet.analytic_cofactor i) hi (jet.factor_eq i)

theorem order_lt_analyticOrderAt (jet : LeadingOrderJet f) {i : ι} (hi : jet.cofactor i 0 = 0) :
    (jet.order : ℕ∞) < analyticOrderAt (f i) 0 :=
  lt_analyticOrderAt_of_eq_pow_mul (jet.analytic_cofactor i) hi (jet.factor_eq i)

theorem cofactor_ne_zero_iff (jet : LeadingOrderJet f) (i : ι) :
    jet.cofactor i 0 ≠ 0 ↔ analyticOrderAt (f i) 0 = jet.order := by
  refine ⟨jet.analyticOrderAt_eq_order, fun h hc => ?_⟩
  exact absurd h (jet.order_lt_analyticOrderAt hc).ne'

/-- The order carried by a jet is the minimum of the family's orders, so it is uniquely
determined by the family. -/
theorem familyAnalyticOrder_eq [Fintype ι] (jet : LeadingOrderJet f) :
    familyAnalyticOrder f = jet.order := by
  obtain ⟨i₀, hi₀⟩ := jet.exists_leading
  refine le_antisymm ?_ (Finset.le_inf fun i _ => jet.order_le_analyticOrderAt i)
  calc familyAnalyticOrder f ≤ analyticOrderAt (f i₀) 0 := familyAnalyticOrder_le i₀
    _ = jet.order := jet.analyticOrderAt_eq_order hi₀

/-- The leading set is exactly the support of the vector of leading coefficients. -/
theorem mem_leadingSet_iff [Fintype ι] (jet : LeadingOrderJet f) (i : ι) :
    i ∈ leadingSet f ↔ jet.cofactor i 0 ≠ 0 := by
  rw [mem_leadingSet, jet.familyAnalyticOrder_eq, ← jet.cofactor_ne_zero_iff]

theorem cofactor_eq_zero_of_notMem_leadingSet [Fintype ι] (jet : LeadingOrderJet f) {i : ι}
    (hi : i ∉ leadingSet f) : jet.cofactor i 0 = 0 := by
  by_contra hc
  exact hi ((jet.mem_leadingSet_iff i).mpr hc)

/-- **Item 2: the leading set is nonempty.** -/
theorem leadingSet_nonempty [Fintype ι] (jet : LeadingOrderJet f) : (leadingSet f).Nonempty := by
  obtain ⟨i₀, hi₀⟩ := jet.exists_leading
  exact ⟨i₀, (jet.mem_leadingSet_iff i₀).mpr hi₀⟩

/-- On the leading set the jet's order is the `ℕ`-valued analytic order of the member. -/
theorem analyticOrderNatAt_eq_order [Fintype ι] (jet : LeadingOrderJet f) {i : ι}
    (hi : i ∈ leadingSet f) : analyticOrderNatAt (f i) 0 = jet.order := by
  have h := jet.analyticOrderAt_eq_order ((jet.mem_leadingSet_iff i).mp hi)
  simp [analyticOrderNatAt, h]

/-! #### Positivity of the leading coefficients -/

/-- Nonnegativity of `f i` to the right of `0` makes the cofactor nonnegative to the right. -/
theorem cofactor_nonneg_nhdsGT (jet : LeadingOrderJet f) {i : ι}
    (hnn : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ jet.cofactor i t := by
  filter_upwards [hnn, (jet.factor_eq i).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hpos hfac ht
  rw [hfac] at hpos
  exact nonneg_of_mul_nonneg_right hpos (pow_pos ht jet.order)

/-- Nonnegativity of `f i` to the right of `0` makes the leading coefficient nonnegative. -/
theorem cofactor_zero_nonneg (jet : LeadingOrderJet f) {i : ι}
    (hnn : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) : 0 ≤ jet.cofactor i 0 :=
  ge_of_tendsto (jet.analytic_cofactor i).continuousAt.continuousWithinAt
    (jet.cofactor_nonneg_nhdsGT hnn)

/-- **Item 3.**  For a member of the leading set, nonnegativity on the right upgrades
`cofactor i 0 ≠ 0` to `0 < cofactor i 0`.

This is the step that rules out cancellation: without it the leading coefficients of the members
of the leading set could cancel in `∑ j, cofactor j 0`. -/
theorem cofactor_pos (jet : LeadingOrderJet f) {i : ι} (hnn : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t)
    (hi : jet.cofactor i 0 ≠ 0) : 0 < jet.cofactor i 0 :=
  lt_of_le_of_ne (jet.cofactor_zero_nonneg hnn) (Ne.symm hi)

/-! #### The normalized limit -/

variable [Fintype ι]

/-- The analytic total cofactor of the family. -/
theorem analyticAt_sum_cofactor (jet : LeadingOrderJet f) :
    AnalyticAt ℝ (fun t => ∑ i, jet.cofactor i t) 0 :=
  Finset.univ.analyticAt_fun_sum fun i _ => jet.analytic_cofactor i

/-- The family sum inherits the leading factorization. -/
theorem sum_factor_eq (jet : LeadingOrderJet f) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∑ i, f i t = t ^ jet.order * ∑ i, jet.cofactor i t := by
  filter_upwards [Filter.eventually_all.mpr jet.factor_eq] with t ht
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => ht i

/-- **Item 3, family form.**  Under nonnegativity, the total leading coefficient is positive.
Only the leading set contributes to it, since every other coefficient is `0`. -/
theorem sum_cofactor_zero_pos (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) : 0 < ∑ i, jet.cofactor i 0 := by
  obtain ⟨i₀, hi₀⟩ := jet.exists_leading
  refine Finset.sum_pos' (fun i _ => jet.cofactor_zero_nonneg (hnn i)) ⟨i₀, Finset.mem_univ i₀, ?_⟩
  exact jet.cofactor_pos (hnn i₀) hi₀

theorem eventually_sum_cofactor_pos (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < ∑ i, jet.cofactor i t :=
  continuousAt_const.eventually_lt jet.analyticAt_sum_cofactor.continuousAt
    (jet.sum_cofactor_zero_pos hnn)

/-- **Item 4, first half.**  The denominator is strictly positive to the right of `0`. -/
theorem eventually_sum_pos (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ i, f i t := by
  filter_upwards [(jet.sum_factor_eq).filter_mono nhdsWithin_le_nhds,
    (jet.eventually_sum_cofactor_pos hnn).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hfac hpos ht
  rw [hfac]
  exact mul_pos (pow_pos ht jet.order) hpos

/-- **Item 4.**  The normalized family converges — not merely along subsequences — to the vector
of normalized leading coefficients.  The limit vanishes off the leading set, by
`cofactor_eq_zero_of_notMem_leadingSet`, and is positive on it, by `cofactor_pos`. -/
theorem tendsto_div_sum (jet : LeadingOrderJet f) (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t)
    (i : ι) :
    Tendsto (fun t => f i t / ∑ j, f j t) (𝓝[>] (0 : ℝ))
      (𝓝 (jet.cofactor i 0 / ∑ j, jet.cofactor j 0)) := by
  have hden : (∑ j, jet.cofactor j 0) ≠ 0 := (jet.sum_cofactor_zero_pos hnn).ne'
  have hcongr : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      jet.cofactor i t / ∑ j, jet.cofactor j t = f i t / ∑ j, f j t := by
    filter_upwards [(jet.factor_eq i).filter_mono nhdsWithin_le_nhds,
      (jet.sum_factor_eq).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hfac hsum ht
    rw [hfac, hsum]
    exact (mul_div_mul_left (jet.cofactor i t) (∑ j, jet.cofactor j t)
      (pow_ne_zero jet.order (ne_of_gt ht))).symm
  refine Tendsto.congr' hcongr ?_
  exact ((jet.analytic_cofactor i).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div
    (jet.analyticAt_sum_cofactor.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hden

/-- Off the leading set, the normalized share tends to `0`. -/
theorem tendsto_div_sum_nhds_zero (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) {i : ι} (hi : i ∉ leadingSet f) :
    Tendsto (fun t => f i t / ∑ j, f j t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have := jet.tendsto_div_sum hnn i
  rwa [jet.cofactor_eq_zero_of_notMem_leadingSet hi, zero_div] at this

/-- On the leading set, the normalized share tends to a strictly positive limit. -/
theorem tendsto_div_sum_pos (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) {i : ι} (hi : i ∈ leadingSet f) :
    0 < jet.cofactor i 0 / ∑ j, jet.cofactor j 0 :=
  div_pos (jet.cofactor_pos (hnn i) ((jet.mem_leadingSet_iff i).mp hi))
    (jet.sum_cofactor_zero_pos hnn)

/-- Only the leading set contributes to the total leading coefficient, so the denominator
`∑ j, cofactor j 0` of `tendsto_div_sum` *is* the sum `∑_{j ∈ L} cofactor j 0` over the leading
set.  This is the literal form in which the normalized limit is "supported exactly on `L`". -/
theorem sum_cofactor_leadingSet (jet : LeadingOrderJet f)
    [DecidablePred fun i => i ∈ leadingSet f] :
    ∑ j ∈ Finset.univ.filter (fun i => i ∈ leadingSet f), jet.cofactor j 0 =
      ∑ j, jet.cofactor j 0 := by
  refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
  exact jet.cofactor_eq_zero_of_notMem_leadingSet (by simpa using hj)

/-- The normalized limits sum to `1`. -/
theorem sum_div_sum_cofactor (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) :
    ∑ i, jet.cofactor i 0 / ∑ j, jet.cofactor j 0 = 1 := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (jet.sum_cofactor_zero_pos hnn).ne'

/-! #### Comparison against an external scale `t ^ q` -/

/-- **Item 5, `order < q`.**  A scale strictly finer than the family's order is negligible. -/
theorem tendsto_pow_div_sum_nhds_zero (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) {q : ℕ} (hq : jet.order < q) :
    Tendsto (fun t : ℝ => t ^ q / ∑ j, f j t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hden : (∑ j, jet.cofactor j 0) ≠ 0 := (jet.sum_cofactor_zero_pos hnn).ne'
  have hcongr : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t ^ (q - jet.order) / (∑ j, jet.cofactor j t) = t ^ q / ∑ j, f j t := by
    filter_upwards [(jet.sum_factor_eq).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hsum ht
    rw [hsum, show t ^ q = t ^ jet.order * t ^ (q - jet.order) by
      rw [← pow_add, Nat.add_sub_cancel' hq.le]]
    exact (mul_div_mul_left (t ^ (q - jet.order)) (∑ j, jet.cofactor j t)
      (pow_ne_zero jet.order (ne_of_gt ht))).symm
  refine Tendsto.congr' hcongr ?_
  have hpow : Tendsto (fun t : ℝ => t ^ (q - jet.order)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t ^ (q - jet.order)) (𝓝 (0 : ℝ))
        (𝓝 ((0 : ℝ) ^ (q - jet.order))) := (continuous_pow (q - jet.order)).continuousAt.tendsto
    rw [zero_pow (by omega : q - jet.order ≠ 0)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => t ^ (q - jet.order) / ∑ j, jet.cofactor j t)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 / ∑ j, jet.cofactor j 0)) :=
    hpow.div (jet.analyticAt_sum_cofactor.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hden
  rwa [zero_div] at hlim

/-- **Item 5, `order = q`.**  At the matching scale the ratio converges to the reciprocal of the
total leading coefficient. -/
theorem tendsto_pow_div_sum_nhds_inv (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) :
    Tendsto (fun t : ℝ => t ^ jet.order / ∑ j, f j t) (𝓝[>] (0 : ℝ))
      (𝓝 (1 / ∑ j, jet.cofactor j 0)) := by
  have hden : (∑ j, jet.cofactor j 0) ≠ 0 := (jet.sum_cofactor_zero_pos hnn).ne'
  have hcongr : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      1 / (∑ j, jet.cofactor j t) = t ^ jet.order / ∑ j, f j t := by
    filter_upwards [(jet.sum_factor_eq).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hsum ht
    rw [hsum]
    simpa using (mul_div_mul_left (1 : ℝ) (∑ j, jet.cofactor j t)
      (pow_ne_zero jet.order (ne_of_gt ht))).symm
  refine Tendsto.congr' hcongr ?_
  exact tendsto_const_nhds.div
    (jet.analyticAt_sum_cofactor.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hden

/-- **Item 5, `q < order`.**  A scale strictly coarser than the family's order dominates it: the
ratio blows up.  This is where `eventually_sum_pos` is used, which is why nonnegativity is a
hypothesis of this statement too. -/
theorem tendsto_pow_div_sum_atTop (jet : LeadingOrderJet f)
    (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t) {q : ℕ} (hq : q < jet.order) :
    Tendsto (fun t : ℝ => t ^ q / ∑ j, f j t) (𝓝[>] (0 : ℝ)) atTop := by
  set u : ℝ → ℝ := fun t => t ^ (jet.order - q) * ∑ j, jet.cofactor j t with hu
  have hcongr : ∀ᶠ t in 𝓝[>] (0 : ℝ), (u t)⁻¹ = t ^ q / ∑ j, f j t := by
    filter_upwards [(jet.sum_factor_eq).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hsum ht
    rw [hsum, show t ^ jet.order * (∑ j, jet.cofactor j t) = t ^ q * u t by
      rw [hu, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hq.le]]
    simpa [one_div] using (mul_div_mul_left (1 : ℝ) (u t) (pow_ne_zero q (ne_of_gt ht))).symm
  refine Tendsto.congr' hcongr ?_
  have hupos : ∀ᶠ t in 𝓝[>] (0 : ℝ), u t ∈ Ioi (0 : ℝ) := by
    filter_upwards [(jet.eventually_sum_cofactor_pos hnn).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hpos ht
    exact mul_pos (pow_pos ht _) hpos
  have hzero : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hpow : Tendsto (fun t : ℝ => t ^ (jet.order - q)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => t ^ (jet.order - q)) (𝓝 (0 : ℝ))
          (𝓝 ((0 : ℝ) ^ (jet.order - q))) := (continuous_pow (jet.order - q)).continuousAt.tendsto
      rw [zero_pow (by omega : jet.order - q ≠ 0)] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun t : ℝ => t ^ (jet.order - q) * ∑ j, jet.cofactor j t)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 * ∑ j, jet.cofactor j 0)) :=
      hpow.mul (jet.analyticAt_sum_cofactor.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    rw [zero_mul] at hlim
    exact hlim
  exact tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hzero, hupos⟩)

end LeadingOrderJet

/-! ### Existence -/

/-- **Existence of the leading-order factorization.**  As soon as one member of a finite family of
germs analytic at `0` is not eventually zero to the right of `0`, the family admits a
simultaneous leading-order factorization.

Nonnegativity is *not* needed here; it is needed only for the positivity statements. -/
theorem exists_leadingOrderJet [Finite ι] {f : ι → ℝ → ℝ} (hf : ∀ i, AnalyticAt ℝ (f i) 0)
    (hne : ∃ i, ¬∀ᶠ t in 𝓝[>] (0 : ℝ), f i t = 0) : Nonempty (LeadingOrderJet f) := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨i₁, hi₁⟩ := hne
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset ι)
    (fun i => analyticOrderAt (f i) 0) ⟨i₁, Finset.mem_univ i₁⟩
  have hi₀top : analyticOrderAt (f i₀) 0 ≠ ⊤ := by
    intro htop
    have hle1 : analyticOrderAt (f i₀) 0 ≤ analyticOrderAt (f i₁) 0 :=
      hi₀ i₁ (Finset.mem_univ i₁)
    rw [htop, top_le_iff] at hle1
    exact hi₁ ((eventuallyEq_zero_nhdsGT_iff_nhds (hf i₁)).mpr (analyticOrderAt_eq_top.mp hle1))
  set m := analyticOrderNatAt (f i₀) 0 with hm
  have hmcast : (m : ℕ∞) = analyticOrderAt (f i₀) 0 := Nat.cast_analyticOrderNatAt hi₀top
  have hle : ∀ i, (m : ℕ∞) ≤ analyticOrderAt (f i) 0 := fun i => by
    rw [hmcast]; exact hi₀ i (Finset.mem_univ i)
  choose c hc hcfac using fun i => exists_cofactor_of_natCast_le (hf i) (hle i)
  refine ⟨{  order := m
             cofactor := c
             analytic_cofactor := hc
             factor_eq := hcfac
             exists_leading := ⟨i₀, fun hzero => ?_⟩ }⟩
  have hlt := lt_analyticOrderAt_of_eq_pow_mul (hc i₀) hzero (hcfac i₀)
  rw [hmcast] at hlt
  exact lt_irrefl _ hlt

/-- **The whole package.**  For a finite family of germs analytic at `0`, nonnegative on a right
neighbourhood of `0`, and not all eventually zero on the right, there is a least order `m` and a
vector `a` of leading coefficients such that

* `a` is nonnegative, has positive total, and is supported exactly on the members of order `m`;
* the denominator `∑ j, f j t` is eventually positive to the right of `0`;
* every normalized share `f i t / ∑ j, f j t` converges to `a i / ∑ j, a j`; and
* the external scale `t ^ q` is negligible, comparable, or dominant according as `q > m`,
  `q = m`, or `q < m`. -/
theorem exists_leadingOrder_normalization [Fintype ι] {f : ι → ℝ → ℝ}
    (hf : ∀ i, AnalyticAt ℝ (f i) 0) (hnn : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f i t)
    (hne : ∃ i, ¬∀ᶠ t in 𝓝[>] (0 : ℝ), f i t = 0) :
    ∃ (m : ℕ) (a : ι → ℝ),
      (familyAnalyticOrder f = m) ∧
      (∀ i, 0 ≤ a i) ∧
      (0 < ∑ j, a j) ∧
      (∀ i, a i ≠ 0 ↔ i ∈ leadingSet f) ∧
      (∀ i, i ∈ leadingSet f ↔ analyticOrderAt (f i) 0 = m) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ j, f j t) ∧
      (∀ i, Tendsto (fun t => f i t / ∑ j, f j t) (𝓝[>] (0 : ℝ)) (𝓝 (a i / ∑ j, a j))) ∧
      (∀ q : ℕ, m < q →
        Tendsto (fun t : ℝ => t ^ q / ∑ j, f j t) (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      Tendsto (fun t : ℝ => t ^ m / ∑ j, f j t) (𝓝[>] (0 : ℝ)) (𝓝 (1 / ∑ j, a j)) ∧
      (∀ q : ℕ, q < m → Tendsto (fun t : ℝ => t ^ q / ∑ j, f j t) (𝓝[>] (0 : ℝ)) atTop) := by
  obtain ⟨jet⟩ := exists_leadingOrderJet hf hne
  refine ⟨jet.order, fun i => jet.cofactor i 0, jet.familyAnalyticOrder_eq,
    fun i => jet.cofactor_zero_nonneg (hnn i), jet.sum_cofactor_zero_pos hnn,
    fun i => (jet.mem_leadingSet_iff i).symm, fun i => ?_,
    jet.eventually_sum_pos hnn, jet.tendsto_div_sum hnn,
    fun q hq => jet.tendsto_pow_div_sum_nhds_zero hnn hq, jet.tendsto_pow_div_sum_nhds_inv hnn,
    fun q hq => jet.tendsto_pow_div_sum_atTop hnn hq⟩
  rw [mem_leadingSet, jet.familyAnalyticOrder_eq]

end Math
