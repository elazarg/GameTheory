/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AlgebraicSelection

/-!
# Fixed analytic mixed obstructions

For finite families of global and playerwise certificate values, analyticity
freezes one maximizing ray from each family. If the global maximum eventually
dominates the playerwise maximum, their fixed-ray gap is a nonnegative
analytic germ. It is therefore either the zero germ or is bounded below by a
positive power law.

When every global ray designated as playerwise-local is bounded by the local
family, the ray carrying a positive gap is necessarily genuinely mixed.
-/

open Set Topology

namespace Math

/-- Two finite analytic families have fixed indices which simultaneously
attain their respective pointwise maxima on one common right neighborhood. -/
theorem exists_fixed_eventual_analytic_maximizers
    {G L : Type*} [Finite G] [Nonempty G] [Finite L] [Nonempty L]
    (globalValue : G → ℝ → ℝ) (localValue : L → ℝ → ℝ) {x₀ : ℝ}
    (hglobal : ∀ g, AnalyticAt ℝ (globalValue g) x₀)
    (hlocal : ∀ l, AnalyticAt ℝ (localValue l) x₀) :
    ∃ g l,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (∀ g', globalValue g' x ≤ globalValue g x) ∧
          (∀ l', localValue l' x ≤ localValue l x) := by
  obtain ⟨g, hg⟩ :=
    finite_analytic_family_eventually_fixed_maximizer globalValue hglobal
  obtain ⟨l, hl⟩ :=
    finite_analytic_family_eventually_fixed_maximizer localValue hlocal
  exact ⟨g, l, hg.and hl⟩

/-- If the maximum of a finite global analytic family eventually dominates
the maximum of a finite local analytic family, fixed maximizing rays have a
gap which is either identically zero as a right germ or has a positive
power-law lower bound. -/
theorem exists_fixed_analytic_maxGap_dichotomy
    {G L : Type*} [Finite G] [Nonempty G] [Finite L] [Nonempty L]
    (globalValue : G → ℝ → ℝ) (localValue : L → ℝ → ℝ) {x₀ : ℝ}
    (hglobal : ∀ g, AnalyticAt ℝ (globalValue g) x₀)
    (hlocal : ∀ l, AnalyticAt ℝ (localValue l) x₀)
    (hdominates :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ l,
        ∃ g, localValue l x ≤ globalValue g x) :
    ∃ g l,
      (∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (∀ g', globalValue g' x ≤ globalValue g x) ∧
          (∀ l', localValue l' x ≤ localValue l x)) ∧
      ((∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
          globalValue g x = localValue l x) ∨
        ∃ n : ℕ, ∃ c : ℝ, 0 < c ∧
          ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
            0 < globalValue g x - localValue l x ∧
              c * (x - x₀) ^ n ≤
                globalValue g x - localValue l x) := by
  obtain ⟨g, l, hmax⟩ :=
    exists_fixed_eventual_analytic_maximizers
      globalValue localValue hglobal hlocal
  let gap : ℝ → ℝ := fun x => globalValue g x - localValue l x
  have hgap_analytic : AnalyticAt ℝ gap x₀ :=
    (hglobal g).sub (hlocal l)
  have hgap_nonneg :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ gap x := by
    filter_upwards [hmax, hdominates] with x hxmax hxdom
    obtain ⟨g', hg'⟩ := hxdom l
    exact sub_nonneg.mpr (hg'.trans (hxmax.1 g'))
  refine ⟨g, l, hmax, ?_⟩
  rcases analyticAt_eventually_eq_zero_or_pos_of_eventually_nonneg
      hgap_analytic hgap_nonneg with hzero | hpos
  · left
    filter_upwards [hzero] with x hx
    exact sub_eq_zero.mp hx
  · right
    obtain ⟨n, c, hc, hpower⟩ :=
      analyticAt_eventually_const_mul_pow_le_of_eventually_pos
        hgap_analytic hpos
    exact ⟨n, c, hc, by
      filter_upwards [hpos, hpower] with x hxpos hxpower
      exact ⟨hxpos, hxpower⟩⟩

/-- In the positive-gap branch, a fixed maximizing global ray cannot be
playerwise-local if every local global ray is eventually bounded by some
member of the local family. Hence the quantitative obstruction is genuinely
mixed. -/
theorem exists_fixed_genuinelyMixed_analytic_maxGap_dichotomy
    {G L : Type*} [Finite G] [Nonempty G] [Finite L] [Nonempty L]
    (globalValue : G → ℝ → ℝ) (localValue : L → ℝ → ℝ)
    (IsLocal : G → Prop) {x₀ : ℝ}
    (hglobal : ∀ g, AnalyticAt ℝ (globalValue g) x₀)
    (hlocal : ∀ l, AnalyticAt ℝ (localValue l) x₀)
    (hdominates :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ l,
        ∃ g, localValue l x ≤ globalValue g x)
    (hlocal_bound : ∀ g, IsLocal g →
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∃ l,
        globalValue g x ≤ localValue l x) :
    ∃ g l,
      (∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (∀ g', globalValue g' x ≤ globalValue g x) ∧
          (∀ l', localValue l' x ≤ localValue l x)) ∧
      ((∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
          globalValue g x = localValue l x) ∨
        ∃ n : ℕ, ∃ c : ℝ, 0 < c ∧ ¬IsLocal g ∧
          ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
            0 < globalValue g x - localValue l x ∧
              c * (x - x₀) ^ n ≤
                globalValue g x - localValue l x) := by
  obtain ⟨g, l, hmax, hgap⟩ :=
    exists_fixed_analytic_maxGap_dichotomy
      globalValue localValue hglobal hlocal hdominates
  refine ⟨g, l, hmax, ?_⟩
  rcases hgap with hzero | ⟨n, c, hc, hpower⟩
  · exact Or.inl hzero
  · right
    have hnotlocal : ¬IsLocal g := by
      intro hgLocal
      obtain ⟨x, hxmax, hxpower, l', hglocal⟩ :=
        (hmax.and (hpower.and (hlocal_bound g hgLocal))).exists
      exact (not_lt_of_ge (hglocal.trans (hxmax.2 l')))
        (sub_pos.mp hxpower.1)
    exact ⟨n, c, hc, hnotlocal, hpower⟩

end Math
