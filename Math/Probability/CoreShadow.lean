/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction.TotalVariation
import Math.ProbabilityMassFunction.Simplex
import Math.Minimax.Loomis

/-!
# Finite core-shadow alternatives

This file isolates the finite convex-geometric core of a shadow-coupling
argument.  A finite family `legal : L → PMF R` generates the legal one-step
laws by randomization.  For a controlled law `q`, exactly one of the following
can fail:

* some legal mixture is within a prescribed total-variation tolerance;
* one fixed potential `v : R → [0,1]` separates `q` from every legal mixture.

The proof is finite matrix minimax.  The row player's pure strategies are the
`{0,1}`-valued total-variation witnesses, and the column player's mixed
strategies are legal mixtures.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace Probability

variable {R L : Type*} [Fintype R] [Fintype L]

local instance boolTestFintype : Fintype (R → Bool) :=
  Fintype.ofFinite (R → Bool)

/-- The real indicator associated to a Boolean-valued function. -/
def boolPotential (a : R → Bool) : R → ℝ :=
  fun r => if a r then 1 else 0

omit [Fintype R] in
theorem boolPotential_nonneg (a : R → Bool) (r : R) :
    0 ≤ boolPotential a r := by
  by_cases h : a r = true <;> simp [boolPotential, h]

omit [Fintype R] in
theorem boolPotential_le_one (a : R → Bool) (r : R) :
    boolPotential a r ≤ 1 := by
  by_cases h : a r = true <;> simp [boolPotential, h]

/-- On a finite space, total variation is the maximum expectation gap over
Boolean-valued tests. -/
theorem pmfTV_eq_sup_boolPotential (μ ν : PMF R) :
    pmfTV μ ν =
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun a : R → Bool =>
          expect μ (boolPotential a) - expect ν (boolPotential a)) := by
  classical
  apply le_antisymm
  · let a : R → Bool := fun r =>
      decide (0 < (μ r).toReal - (ν r).toReal)
    have hpot :
        boolPotential a = pmfPositiveVariationWitness μ ν 1 := by
      funext r
      simp only [boolPotential, a, decide_eq_true_eq]
      unfold pmfPositiveVariationWitness
      split_ifs <;> rfl
    calc
      pmfTV μ ν =
          expect μ (boolPotential a) - expect ν (boolPotential a) := by
            rw [hpot, expect_sub_pmfPositiveVariationWitness]
            simp
      _ ≤ Finset.sup' Finset.univ Finset.univ_nonempty
          (fun b : R → Bool =>
            expect μ (boolPotential b) - expect ν (boolPotential b)) :=
        Finset.le_sup'
          (fun b : R → Bool =>
            expect μ (boolPotential b) - expect ν (boolPotential b))
          (Finset.mem_univ a)
  · apply Finset.sup'_le
    intro a _
    simpa using expect_sub_le_mul_pmfPositiveVariation μ ν
      (boolPotential a) (U := 1)
      (boolPotential_nonneg a) (boolPotential_le_one a)

/-- The PMF obtained by randomizing among a finite family of laws with simplex
weights. -/
def legalMixture (legal : L → PMF R) (y : stdSimplex ℝ L) : PMF R :=
  ((ProbabilityMassFunction.stdSimplexEquiv (α := L)).symm y).bind legal

omit [Fintype R] in
theorem expect_legalMixture [Finite R]
    (legal : L → PMF R) (y : stdSimplex ℝ L)
    (v : R → ℝ) :
    expect (legalMixture legal y) v =
      wsum y (fun l => expect (legal l) v) := by
  rw [legalMixture, expect_bind]
  exact ProbabilityMassFunction.expect_stdSimplexEquiv_symm_eq_wsum y _

/-- The matrix whose rows are Boolean tests and whose columns are legal laws.
Its payoff is the controlled-minus-legal expectation gap. -/
def shadowMatrix (q : PMF R) (legal : L → PMF R) :
    (R → Bool) → L → ℝ :=
  fun a l => expect q (boolPotential a) - expect (legal l) (boolPotential a)

omit [Fintype R] in
theorem wsum_shadowMatrix_eq [Finite R]
    (q : PMF R) (legal : L → PMF R)
    (y : stdSimplex ℝ L) (a : R → Bool) :
    wsum y (fun l => shadowMatrix q legal a l) =
      expect q (boolPotential a) -
        expect (legalMixture legal y) (boolPotential a) := by
  rw [expect_legalMixture]
  simp only [shadowMatrix]
  change
    (∑ l, y.val l *
      (expect q (boolPotential a) - expect (legal l) (boolPotential a))) =
      expect q (boolPotential a) -
        ∑ l, y.val l * expect (legal l) (boolPotential a)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [y.property.2]
  ring

theorem mu_aux_shadowMatrix_eq_pmfTV (q : PMF R) (legal : L → PMF R)
    (y : stdSimplex ℝ L) :
    MinimaxLoomis.mu.aux (shadowMatrix q legal) y =
      pmfTV q (legalMixture legal y) := by
  rw [MinimaxLoomis.mu.aux, pmfTV_eq_sup_boolPotential]
  apply congrArg
  funext a
  exact wsum_shadowMatrix_eq q legal y a

/-- A simplex mixture of Boolean tests is a potential taking values in
`[0,1]`. -/
def mixedPotential (x : stdSimplex ℝ (R → Bool)) : R → ℝ :=
  fun r => wsum x (fun a => boolPotential a r)

theorem mixedPotential_nonneg (x : stdSimplex ℝ (R → Bool)) (r : R) :
    0 ≤ mixedPotential x r :=
  wsum_nonneg x fun a => boolPotential_nonneg a r

theorem mixedPotential_le_one (x : stdSimplex ℝ (R → Bool)) (r : R) :
    mixedPotential x r ≤ 1 := by
  calc
    mixedPotential x r ≤ wsum x (fun _ => (1 : ℝ)) :=
      wsum_le_wsum x fun a => boolPotential_le_one a r
    _ = 1 := wsum_const x 1

theorem expect_mixedPotential (μ : PMF R)
    (x : stdSimplex ℝ (R → Bool)) :
    expect μ (mixedPotential x) =
      wsum x (fun a => expect μ (boolPotential a)) := by
  rw [expect_eq_sum]
  change
    (∑ r, (μ r).toReal * ∑ a, x.val a * boolPotential a r) =
      ∑ a, x.val a * expect μ (boolPotential a)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [expect_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

omit [Fintype L] in
theorem wsum_shadowMatrix_eq_expect_mixedPotential
    (q : PMF R) (legal : L → PMF R)
    (x : stdSimplex ℝ (R → Bool)) (l : L) :
    wsum x (fun a => shadowMatrix q legal a l) =
      expect q (mixedPotential x) -
        expect (legal l) (mixedPotential x) := by
  rw [expect_mixedPotential, expect_mixedPotential]
  simp only [shadowMatrix]
  change
    (∑ a, x.val a *
      (expect q (boolPotential a) - expect (legal l) (boolPotential a))) =
      (∑ a, x.val a * expect q (boolPotential a)) -
        ∑ a, x.val a * expect (legal l) (boolPotential a)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

omit [Fintype R] in
theorem expect_sub_legalMixture_eq_wsum [Finite R]
    (q : PMF R) (legal : L → PMF R) (y : stdSimplex ℝ L)
    (v : R → ℝ) :
    expect q v - expect (legalMixture legal y) v =
      wsum y (fun l => expect q v - expect (legal l) v) := by
  rw [expect_legalMixture]
  change
    expect q v - ∑ l, y.val l * expect (legal l) v =
      ∑ l, y.val l * (expect q v - expect (legal l) v)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, y.property.2]
  ring

/-- **Finite core-shadow alternative.**

The legal set is the convex hull of the finite family `legal`.  Either a legal
mixture is within total-variation tolerance `ε` of `q`, or a single bounded
potential separates `q` by more than `ε` from every legal mixture. -/
theorem exists_legalMixture_close_or_separator [Nonempty L]
    (q : PMF R) (legal : L → PMF R) (ε : ℝ) :
    (∃ y : stdSimplex ℝ L, pmfTV q (legalMixture legal y) ≤ ε) ∨
      ∃ v : R → ℝ,
        (∀ r, 0 ≤ v r) ∧
        (∀ r, v r ≤ 1) ∧
        ∀ y : stdSimplex ℝ L,
          ε < expect q v - expect (legalMixture legal y) v := by
  classical
  by_cases hclose :
      ∃ y : stdSimplex ℝ L, pmfTV q (legalMixture legal y) ≤ ε
  · exact Or.inl hclose
  · right
    push Not at hclose
    let A := shadowMatrix q legal
    obtain ⟨y₀, hy₀⟩ := MinimaxLoomis.exists_yy_mu0 A
    have hmu_eq :
        MinimaxLoomis.mu.aux A y₀ = MinimaxLoomis.mu0 A := by
      apply le_antisymm
      · rw [MinimaxLoomis.mu.aux]
        apply Finset.sup'_le
        intro a _
        exact hy₀ a
      · exact MinimaxLoomis.mu.aux.ge_mu0 A y₀
    have heps_mu : ε < MinimaxLoomis.mu0 A := by
      rw [← hmu_eq, mu_aux_shadowMatrix_eq_pmfTV]
      exact hclose y₀
    obtain ⟨x, hx⟩ := MinimaxLoomis.exists_xx_lam0 A
    refine ⟨mixedPotential x, mixedPotential_nonneg x,
      mixedPotential_le_one x, ?_⟩
    intro y
    rw [expect_sub_legalMixture_eq_wsum]
    have hpoint :
        ∀ l, ε <
          expect q (mixedPotential x) -
            expect (legal l) (mixedPotential x) := by
      intro l
      rw [← wsum_shadowMatrix_eq_expect_mixedPotential]
      calc
        ε < MinimaxLoomis.mu0 A := heps_mu
        _ = MinimaxLoomis.lam0 A := (Loomis.minmax_from_general A).symm
        _ ≤ wsum x (fun a => A a l) := hx l
    let gap : L → ℝ := fun l =>
      expect q (mixedPotential x) -
        expect (legal l) (mixedPotential x) - ε
    have hgap : 0 < wsum y gap := wsum_pos y fun l => by
      dsimp [gap]
      linarith [hpoint l]
    have hrewrite :
        wsum y (fun l =>
          expect q (mixedPotential x) -
            expect (legal l) (mixedPotential x)) =
          wsum y gap + ε := by
      have hterm :
          (fun l =>
            expect q (mixedPotential x) -
              expect (legal l) (mixedPotential x)) =
            fun l => gap l + ε := by
        funext l
        dsimp [gap]
        ring
      rw [hterm]
      change
        (∑ l, y.val l * (gap l + ε)) =
          (∑ l, y.val l * gap l) + ε
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, y.property.2]
      ring
    rw [hrewrite]
    linarith

/-- If one listed legal law is the baseline, the separator supplied by the
finite core-shadow alternative also has positive controlled-versus-baseline
drift. -/
theorem exists_legalMixture_close_or_separator_from_baseline [Nonempty L]
    (q p : PMF R) (legal : L → PMF R) (ε : ℝ)
    (hbaseline :
      ∃ y : stdSimplex ℝ L, legalMixture legal y = p) :
    (∃ y : stdSimplex ℝ L, pmfTV q (legalMixture legal y) ≤ ε) ∨
      ∃ v : R → ℝ,
        (∀ r, 0 ≤ v r) ∧
        (∀ r, v r ≤ 1) ∧
        (∀ y : stdSimplex ℝ L,
          ε < expect q v - expect (legalMixture legal y) v) ∧
        ε < expect q v - expect p v := by
  rcases exists_legalMixture_close_or_separator q legal ε with h | ⟨v, hv0, hv1, hvsep⟩
  · exact Or.inl h
  · right
    obtain ⟨y₀, hmix⟩ := hbaseline
    exact ⟨v, hv0, hv1, hvsep, by simpa [hmix] using hvsep y₀⟩

end Probability
end Math
