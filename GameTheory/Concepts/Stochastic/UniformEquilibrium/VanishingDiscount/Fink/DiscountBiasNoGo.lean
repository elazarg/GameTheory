/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.AlgebraicSelection
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Real.Sqrt

/-!
# A permanent no-go boundary: unscaled tail variation does not control discount bias

This file is wired into the root `GameTheory.lean` build; it is nonetheless a standalone,
self-contained record of a boundary fact for the uniform-equilibrium program, and does not import
or edit `MertensNeymanCriterion.lean` (its abstract predicates are re-declared here, independently,
to avoid interfering with concurrent work on that file).

## The point

Converting a discounted Bellman inequality into an average-payoff (uniform-value) statement needs
multiplying by the factor `(1 - λ)/λ`, which diverges as `λ → 0`. The algebraic-selection machinery
of `Math.AlgebraicSelection` (the "F1a/F1b" bridge) shows that a value curve `v` selected by a
nonzero bivariate polynomial has vanishing **unscaled** tail variation as `λ → 0⁺`
(`Math.tailEVariation_vanishes_of_polynomial_root`). It is tempting to hope that this algebraic
control is already enough to also bound the **scaled**, discount-rescaled quantities that a
vanishing-discount argument actually needs. This file records, once and for all, that it is *not*:
there is an algebraic (indeed quadratic) value curve whose unscaled tail variation vanishes, yet
whose scaled, shift-invariant (centered) discount-bias curve has *unbounded* oscillation on every
tail interval. So the algebraic infrastructure alone cannot bridge the unscaled/scaled gap; some
extra ingredient (uniform boundedness of the derivative, or a genuinely different argument) is
needed.

## Predicates

* `IsTailVariationBounded v` — the **unscaled** tail-variation modulus, in coordinatewise
  interval-envelope form: for every `ε > 0` there is `δ > 0` such that, for every coordinate
  `s : S`, the total variation (`eVariationOn`) of `fun lam => v lam s` on `Set.Ioo 0 δ` is at
  most `ε`. (Coordinatewise rather than `S`-Pi-valued: this is the shape
  `Math.tailEVariation_vanishes_of_polynomial_root` produces per coordinate, and avoids
  Pi-metric bookkeeping that is orthogonal to the point of this file.)
* `IsDiscountBiasVariationBounded v s0` — the analogous bound on the **scaled, centered** Bellman
  drift. Since there is no transition structure here, the natural "shift-invariant" surrogate for
  the discount bias is the *centered* scaled difference
  `scaledCenteredDrift v s0 lam s := (1 - lam) / lam * (v lam s - v lam s0)`
  at a fixed reference coordinate `s0` (centering at `s0` is what makes this invariant under
  `v ↦ v + c` for a constant `c`, exactly as a genuine discount-bias quantity is). The predicate
  demands the same `ε`-`δ` interval-envelope bound on `eVariationOn` of this scaled, centered
  curve. A direct two-point (Cauchy) consequence, `IsDiscountBiasVariationBounded.pairwise_le`, is
  what the witness below actually refutes.
* `IsAlgebraicBranch v` — each coordinate `fun lam => v lam s` is, on some interval `Set.Ioo 0 ρ`,
  a continuous branch selected by a nonzero bivariate polynomial in the sense of
  `Math.bivEval` (exactly the hypothesis shape `Math.AlgebraicSelection` works with).

## The witness and the headline theorem

`vWitness : ℝ → Fin 2 → ℝ := fun lam => ![0, Real.sqrt lam]` is algebraic (coordinate `0` is the
`v = 0` branch of `P = X`; coordinate `1` is the `v² = λ` branch of `P = X² - C(X)`), has vanishing
unscaled tail variation (coordinate `0` is constant, coordinate `1` has variation `≤ √δ → 0`), but
its scaled centered drift at reference coordinate `0`,
`scaledCenteredDrift vWitness 0 lam 1 = (1 - lam) / lam * Real.sqrt lam`, is *unbounded* on every
tail interval: sending `lam → 0⁺` along the second point of a two-point comparison drives this
quantity to `+∞` (while the first point's value stays fixed), which is exactly what
`IsDiscountBiasVariationBounded.pairwise_le` forbids. The three facts are exported separately:

* `isAlgebraicBranch_vWitness`
* `isTailVariationBounded_vWitness`
* `not_isDiscountBiasVariationBounded_vWitness`

and the top theorem `not_forall_algebraicBranch_tailVariationBounded_imp_discountBias`
is immediate from these three.
-/

open Set

namespace GameTheory.DiscountBiasNoGo

/-! ## The predicates -/

/-- **Unscaled tail-variation boundedness**, coordinatewise: for every `ε > 0` there is `δ > 0`
such that, for every coordinate `s`, the total variation of `fun lam => v lam s` on `Set.Ioo 0 δ`
is at most `ε`. This is the "algebraic-selection"-facing hypothesis
(`Math.tailEVariation_vanishes_of_polynomial_root` produces exactly this, per coordinate). -/
def IsTailVariationBounded {S : Type*} (v : ℝ → S → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ s : S, eVariationOn (fun lam => v lam s) (Set.Ioo (0 : ℝ) δ) ≤ ENNReal.ofReal ε

/-- The **scaled, centered** discount-bias curve at reference coordinate `s0`: the discounted
Bellman-drift surrogate `(1 - λ)/λ · (v λ s - v λ s0)`. Centering at `s0` makes this invariant
under adding a constant to all of `v` (`v ↦ v + c` leaves `scaledCenteredDrift` unchanged), matching
the shift-invariance a genuine discount-bias quantity has. -/
noncomputable def scaledCenteredDrift {S : Type*} (v : ℝ → S → ℝ) (s0 : S) : ℝ → S → ℝ :=
  fun lam s => (1 - lam) / lam * (v lam s - v lam s0)

/-- `scaledCenteredDrift` is unchanged by adding the *same* constant `c` to every value of `v`:
the shift-invariance that motivates centering. (Adding a coordinate-dependent shift would *not*
be invariant, since it would move `v lam s` and `v lam s0` by different amounts.) -/
theorem scaledCenteredDrift_add_const {S : Type*} (v : ℝ → S → ℝ) (s0 : S) (c : ℝ)
    (lam : ℝ) (s : S) :
    scaledCenteredDrift (fun l t => v l t + c) s0 lam s = scaledCenteredDrift v s0 lam s := by
  simp only [scaledCenteredDrift]
  ring

/-- **Scaled discount-bias-variation boundedness**, coordinatewise: for every `ε > 0` there is
`δ > 0` such that, for every coordinate `s`, the total variation of the scaled centered curve
`fun lam => scaledCenteredDrift v s0 lam s` on `Set.Ioo 0 δ` is at most `ε`. This is the scaled
analogue of `IsTailVariationBounded` that a genuine vanishing-discount (Mertens–Neyman-style)
argument needs; the witness below shows algebraicity plus `IsTailVariationBounded` does *not*
imply it. -/
def IsDiscountBiasVariationBounded {S : Type*} (v : ℝ → S → ℝ) (s0 : S) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ s : S,
      eVariationOn (fun lam => scaledCenteredDrift v s0 lam s) (Set.Ioo (0 : ℝ) δ)
        ≤ ENNReal.ofReal ε

/-- The two-point (Cauchy) consequence of `IsDiscountBiasVariationBounded`, exactly mirroring
`MertensNeymanCriterion.IsTailVariationBounded.pairwise_le`: any two points of a small enough tail
interval have scaled-centered-drift values within `ε` of each other. This is the form the witness
below directly refutes. -/
theorem IsDiscountBiasVariationBounded.pairwise_le {S : Type*} {v : ℝ → S → ℝ} {s0 : S}
    (h : IsDiscountBiasVariationBounded v s0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : S, ∀ lam lam' : ℝ, lam ∈ Set.Ioo (0 : ℝ) δ →
      lam' ∈ Set.Ioo (0 : ℝ) δ →
      |scaledCenteredDrift v s0 lam s - scaledCenteredDrift v s0 lam' s| ≤ ε := by
  obtain ⟨δ, hδ, hvar⟩ := h ε hε
  refine ⟨δ, hδ, fun s lam lam' hlam hlam' => ?_⟩
  have hedist : edist (scaledCenteredDrift v s0 lam s) (scaledCenteredDrift v s0 lam' s)
      ≤ ENNReal.ofReal ε :=
    (eVariationOn.edist_le (fun l => scaledCenteredDrift v s0 l s) hlam hlam').trans (hvar s)
  rw [edist_dist] at hedist
  have hdist : dist (scaledCenteredDrift v s0 lam s) (scaledCenteredDrift v s0 lam' s) ≤ ε :=
    (ENNReal.ofReal_le_ofReal_iff hε.le).mp hedist
  rwa [Real.dist_eq] at hdist

/-- **Algebraicity**: every coordinate is, on some interval `Set.Ioo 0 ρ`, a continuous branch
selected by a nonzero bivariate polynomial — exactly `Math.AlgebraicSelection`'s hypothesis shape
(`P ≠ 0`, `ContinuousOn` on `Set.Ioo 0 ρ`, `Math.bivEval P lam (v lam s) = 0`). -/
def IsAlgebraicBranch {S : Type*} (v : ℝ → S → ℝ) : Prop :=
  ∀ s : S, ∃ (P : Polynomial (Polynomial ℝ)) (ρ : ℝ), 0 < ρ ∧ P ≠ 0 ∧
    ContinuousOn (fun lam => v lam s) (Set.Ioo (0 : ℝ) ρ) ∧
    ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, Math.bivEval P lam (v lam s) = 0

/-! ## The witness -/

/-- The witness value curve: coordinate `0` is identically `0` (the `v = 0` branch), coordinate
`1` is `Real.sqrt`. Both are algebraic, both have vanishing unscaled tail variation; but the
scaled centered drift of coordinate `1` against reference coordinate `0` is unbounded on every
tail interval. -/
noncomputable def vWitness : ℝ → Fin 2 → ℝ := fun lam => ![0, Real.sqrt lam]

@[simp] theorem vWitness_zero (lam : ℝ) : vWitness lam 0 = 0 := by simp [vWitness]

@[simp] theorem vWitness_one (lam : ℝ) : vWitness lam 1 = Real.sqrt lam := by simp [vWitness]

/-- **Fact 1: `vWitness` is algebraic.** Coordinate `0` is the `v = 0` branch of `P = X`;
coordinate `1` is the `v² = λ` branch of `P = X² - C(X)`. -/
theorem isAlgebraicBranch_vWitness : IsAlgebraicBranch vWitness := by
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · -- coordinate 0: the polynomial `P = X`, i.e. `bivEval P lam y = y`.
    refine ⟨Polynomial.X, 1, one_pos, Polynomial.X_ne_zero, ?_, ?_⟩
    · simpa using continuousOn_const
    · intro lam _
      simp only [vWitness_zero, Math.bivEval, Polynomial.eval₂_X]
  · -- coordinate 1: the polynomial `P = X² - C(X)`, i.e. `bivEval P lam y = y² - lam`.
    set P : Polynomial (Polynomial ℝ) :=
      (Polynomial.X : Polynomial (Polynomial ℝ)) ^ 2 - Polynomial.C (Polynomial.X : Polynomial ℝ)
      with hPdef
    have hPcoeff2 : P.coeff 2 = 1 := by
      simp [hPdef, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    have hPne : P ≠ 0 := by
      intro h
      rw [h] at hPcoeff2
      simp at hPcoeff2
    refine ⟨P, 1, one_pos, hPne, ?_, ?_⟩
    · simpa using Real.continuous_sqrt.continuousOn
    · intro lam hlam
      have hlam0 : 0 ≤ lam := hlam.1.le
      simp only [vWitness_one, Math.bivEval, hPdef]
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [Real.sq_sqrt hlam0]
      simp

/-- **Fact 2: `vWitness` has vanishing unscaled tail variation.** Coordinate `0` is constant
(variation `0`); coordinate `1` is `Real.sqrt`, monotone with total drop `≤ √δ` on `Set.Ioo 0 δ`,
so choosing `δ := ε ^ 2` bounds its tail variation by `ε`. -/
theorem isTailVariationBounded_vWitness : IsTailVariationBounded vWitness := by
  intro ε hε
  refine ⟨ε ^ 2, by positivity, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · have heq : (fun lam => vWitness lam 0) = fun _ : ℝ => (0 : ℝ) := by
      funext lam; simp
    rw [heq]
    have hsub : (fun _ : ℝ => (0 : ℝ)) '' Set.Ioo (0 : ℝ) (ε ^ 2) ⊆ {0} := by
      rintro y ⟨x, _hx, rfl⟩; rfl
    rw [eVariationOn.constant_on (Set.subsingleton_singleton.anti hsub)]
    exact bot_le
  · have hmono : MonotoneOn Real.sqrt (Set.Ioo (0 : ℝ) (ε ^ 2)) :=
      fun x _ y _ hxy => Real.sqrt_le_sqrt hxy
    have hkey : eVariationOn Real.sqrt (Set.Ioo (0 : ℝ) (ε ^ 2)) ≤ ENNReal.ofReal ε := by
      rw [eVariationOn.eq_biSup_inter_Icc]
      simp only [Set.mem_setOf_eq, iSup_le_iff, and_imp, Prod.forall]
      intro a b ha hb _hab
      refine le_trans (hmono.eVariationOn_le ha hb) (ENNReal.ofReal_le_ofReal ?_)
      have hbsqrt : Real.sqrt b ≤ ε := by
        have := Real.sqrt_le_sqrt hb.2.le
        rwa [Real.sqrt_sq hε.le] at this
      have hansqrt : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
      linarith
    have heq : (fun lam => vWitness lam 1) = Real.sqrt := by funext lam; simp
    rw [heq]
    exact hkey

/-- The explicit closed form of the scaled centered drift of `vWitness` at coordinate `1`,
against reference coordinate `0`. -/
theorem scaledCenteredDrift_vWitness_one (lam : ℝ) :
    scaledCenteredDrift vWitness 0 lam 1 = (1 - lam) / lam * Real.sqrt lam := by
  simp [scaledCenteredDrift]

/-- **Fact 3, the crux: `vWitness`'s scaled centered drift is unbounded on every tail interval.**
Given any putative `δ`-bound at level `ε = 1`, a two-point argument refutes it directly: fix
`lam₁ := δ / 2` (giving a fixed finite value `C`), then produce `lam₂ = t ^ 2 ∈ (0, δ)` with `t`
small enough that `(1 - lam₂) / lam₂ * √lam₂ = (1 - t ^ 2) / t ≥ |C| + 2`, so the two values differ
by more than `1`, contradicting the pairwise Cauchy bound. -/
theorem not_isDiscountBiasVariationBounded_vWitness :
    ¬ IsDiscountBiasVariationBounded vWitness 0 := by
  intro h
  obtain ⟨δ, hδ, hpair⟩ := h.pairwise_le (ε := 1) one_pos
  set lam1 : ℝ := δ / 2 with hlam1_def
  have hlam1_mem : lam1 ∈ Set.Ioo (0 : ℝ) δ := ⟨by positivity, by linarith⟩
  set C : ℝ := scaledCenteredDrift vWitness 0 lam1 1 with hC_def
  set K : ℝ := |C| + 2 with hK_def
  have hKpos : 0 < K := by positivity
  set t : ℝ := min 1 (min lam1 (min (1 / 2) (1 / (2 * K)))) with ht_def
  have ht_pos : 0 < t := by
    have h1 : (0 : ℝ) < 1 := one_pos
    have h2 : 0 < lam1 := hlam1_mem.1
    have h3 : (0 : ℝ) < 1 / 2 := by norm_num
    have h4 : 0 < 1 / (2 * K) := by positivity
    exact lt_min h1 (lt_min h2 (lt_min h3 h4))
  have ht_le1 : t ≤ 1 := min_le_left _ _
  have ht_le_lam1 : t ≤ lam1 := (min_le_right _ _).trans (min_le_left _ _)
  have ht_le_half : t ≤ 1 / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht_le_K : t ≤ 1 / (2 * K) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set lam2 : ℝ := t ^ 2 with hlam2_def
  have hlam2_pos : 0 < lam2 := by positivity
  have hlam2_le_t : lam2 ≤ t := by
    rw [hlam2_def, sq]
    exact mul_le_of_le_one_left ht_pos.le ht_le1
  have hlam2_lt_delta : lam2 < δ := by
    have : lam2 ≤ lam1 := hlam2_le_t.trans ht_le_lam1
    have hlam1lt : lam1 < δ := by rw [hlam1_def]; linarith
    linarith
  have hlam2_mem : lam2 ∈ Set.Ioo (0 : ℝ) δ := ⟨hlam2_pos, hlam2_lt_delta⟩
  have hlam2_le_half : lam2 ≤ 1 / 2 := hlam2_le_t.trans ht_le_half
  have hsqrt_lam2 : Real.sqrt lam2 = t := by
    rw [hlam2_def]; exact Real.sqrt_sq ht_pos.le
  have hC2_def : scaledCenteredDrift vWitness 0 lam2 1 = (1 - lam2) / lam2 * t := by
    rw [scaledCenteredDrift_vWitness_one, hsqrt_lam2]
  have hC2_eq : scaledCenteredDrift vWitness 0 lam2 1 = (1 - t ^ 2) / t := by
    rw [hC2_def, hlam2_def]
    have htne : t ≠ 0 := ht_pos.ne'
    field_simp
  have hKt : t * (2 * K) ≤ 1 := (le_div_iff₀ (by positivity)).mp ht_le_K
  have hKtle : K * t ≤ 1 / 2 := by nlinarith
  have hge : K ≤ scaledCenteredDrift vWitness 0 lam2 1 := by
    rw [hC2_eq, le_div_iff₀ ht_pos]
    nlinarith [sq_nonneg t]
  have hCge : scaledCenteredDrift vWitness 0 lam2 1 ≥ C + 2 := by
    have : C ≤ |C| := le_abs_self C
    linarith [hge]
  have hdiff : |scaledCenteredDrift vWitness 0 lam1 1 - scaledCenteredDrift vWitness 0 lam2 1|
      ≤ 1 := hpair 1 lam1 lam2 hlam1_mem hlam2_mem
  rw [← hC_def] at hdiff
  have : |C - scaledCenteredDrift vWitness 0 lam2 1| ≥ 2 := by
    rw [abs_sub_comm]
    rw [abs_of_nonneg (by linarith)]
    linarith
  linarith

/-- **The permanent no-go theorem.** Algebraicity plus vanishing unscaled tail variation does
*not* imply bounded scaled discount-bias variation: the witness `vWitness` is algebraic
(`isAlgebraicBranch_vWitness`) and has vanishing unscaled tail variation
(`isTailVariationBounded_vWitness`), yet its scaled discount-bias variation is unbounded
(`not_isDiscountBiasVariationBounded_vWitness`). This marks the boundary of the `Math.
AlgebraicSelection` ("F1a/F1b") algebraic bridge: it cannot, by itself, be extended to control
scaled discount-bias quantities. -/
theorem not_forall_algebraicBranch_tailVariationBounded_imp_discountBias :
    ¬ (∀ v : ℝ → Fin 2 → ℝ, IsAlgebraicBranch v → IsTailVariationBounded v →
        IsDiscountBiasVariationBounded v 0) := by
  intro h
  exact not_isDiscountBiasVariationBounded_vWitness
    (h vWitness isAlgebraicBranch_vWitness isTailVariationBounded_vWitness)

end GameTheory.DiscountBiasNoGo
