/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.CoreShadow
import Math.Probability.MaximalCoupling

/-!
# One-step core-shadow compiler

This file composes the finite legal-law alternative with the maximal
fiber-coupling construction.  Given a controlled law on a full state space,
a projection to a core state space, and finitely many legal core laws, it
produces one of two kernel-checked certificates:

* a legal mixture and a coupling whose first marginal is the controlled law,
  whose second marginal is that legal mixture, and whose projection mismatch
  is within the prescribed tolerance;
* a bounded core-observable potential which separates the projected
  controlled law from every legal mixture and has positive drift against a
  baseline whose projection is legal.

This is the exact one-step compiler needed before assembling a predictable
history-dependent shadow process.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

variable {S R L : Type*} [Finite S] [Finite R] [Fintype L]

/-- The close branch of the legal-law alternative can be compiled into an
exact coupling on the full and core state spaces. -/
theorem exists_legalMixture_coupling_or_separator [Nonempty L]
    (q : PMF S) (π : S → R) (legal : L → PMF R) (ε : ℝ) :
    (∃ (y : stdSimplex ℝ L) (ζ : PMF (S × R)),
        ζ.map Prod.fst = q ∧
        ζ.map Prod.snd = legalMixture legal y ∧
        projectionMismatchProbability π ζ ≤ ε) ∨
      ∃ v : R → ℝ,
        (∀ r, 0 ≤ v r) ∧
        (∀ r, v r ≤ 1) ∧
        ∀ y : stdSimplex ℝ L,
          ε <
            expect (q.map π) v -
              expect (legalMixture legal y) v := by
  letI := Fintype.ofFinite R
  rcases exists_legalMixture_close_or_separator (q.map π) legal ε with
    ⟨y, hy⟩ | ⟨v, hv0, hv1, hvsep⟩
  · left
    refine ⟨y, maximalFiberCoupling q π (legalMixture legal y), ?_, ?_, ?_⟩
    · exact maximalFiberCoupling_map_fst q π (legalMixture legal y)
    · exact maximalFiberCoupling_map_snd q π (legalMixture legal y)
    · rw [maximalFiberCoupling_mismatchProbability]
      exact hy
  · exact Or.inr ⟨v, hv0, hv1, hvsep⟩

/-- **Baseline-compatible one-step shadow compiler.**

If the projected baseline law belongs to the convex hull of the listed legal
laws, then either the controlled law admits an exact legal shadow coupling
within tolerance `ε`, or one bounded core potential separates it from every
legal mixture.  The same potential, pulled back along `π`, has controlled
versus baseline drift greater than `ε` on the original state space. -/
theorem exists_legalMixture_coupling_or_separator_from_baseline [Nonempty L]
    (q p : PMF S) (π : S → R) (legal : L → PMF R) (ε : ℝ)
    (hbaseline :
      ∃ y : stdSimplex ℝ L, legalMixture legal y = p.map π) :
    (∃ (y : stdSimplex ℝ L) (ζ : PMF (S × R)),
        ζ.map Prod.fst = q ∧
        ζ.map Prod.snd = legalMixture legal y ∧
        projectionMismatchProbability π ζ ≤ ε) ∨
      ∃ v : R → ℝ,
        (∀ r, 0 ≤ v r) ∧
        (∀ r, v r ≤ 1) ∧
        (∀ y : stdSimplex ℝ L,
          ε <
            expect (q.map π) v -
              expect (legalMixture legal y) v) ∧
        ε < expect (q.map π) v - expect (p.map π) v ∧
        ε < expect q (v ∘ π) - expect p (v ∘ π) := by
  letI := Fintype.ofFinite R
  rcases exists_legalMixture_close_or_separator_from_baseline
      (q.map π) (p.map π) legal ε hbaseline with
    ⟨y, hy⟩ | ⟨v, hv0, hv1, hvlegal, hvbase⟩
  · left
    refine ⟨y, maximalFiberCoupling q π (legalMixture legal y), ?_, ?_, ?_⟩
    · exact maximalFiberCoupling_map_fst q π (legalMixture legal y)
    · exact maximalFiberCoupling_map_snd q π (legalMixture legal y)
    · rw [maximalFiberCoupling_mismatchProbability]
      exact hy
  · right
    refine ⟨v, hv0, hv1, hvlegal, hvbase, ?_⟩
    simpa only [expect_map, Function.comp_def] using hvbase

end Probability
end Math
