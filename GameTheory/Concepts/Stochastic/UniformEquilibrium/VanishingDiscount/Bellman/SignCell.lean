/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Bellman.Variety
import Math.PolynomialSignCell
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Exact sign cells for the polynomial Bellman system

The polynomial Bellman presentation contains four finite constraint
families: two equality families and two nonnegativity families.  This file
packages them as one finite polynomial family and proves that membership in
the Bellman solution set depends only on its exact negative/zero/positive
sign vector.

Consequently, every closure point of the Bellman solution set is a closure
point of one complete polynomial sign cell contained in that set.  This is
the finite reduction immediately preceding analytic curve selection.

The polynomial solution variety deliberately allows an arbitrary real value
of the discount coordinate.  A vanishing-discount application must intersect
the selected cell with an explicit physical slice such as `0 < disc ∧ disc ≤ 1`
before applying curve selection.  This module supplies the algebraic sign cell,
not that domain restriction.
-/

noncomputable section

open Math.PolynomialSignCell
open Set SignType

namespace GameTheory
namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  [Fintype G.State] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- One index for each polynomial equality or inequality in the Bellman
presentation. -/
abbrev BellmanActionConstraint (G : StochasticGame ι) :=
  G.State × (Σ i : ι, G.Act i)

abbrev BellmanConstraint (G : StochasticGame ι) :=
  (G.State × ι) ⊕
    G.BellmanActionConstraint ⊕
      (G.State × ι) ⊕ G.BellmanActionConstraint

namespace BellmanConstraint

def simplexSum (s : G.State) (i : ι) : G.BellmanConstraint :=
  Sum.inl (s, i)

def simplexNonneg (s : G.State) (i : ι) (a : G.Act i) :
    G.BellmanConstraint :=
  Sum.inr (Sum.inl (s, ⟨i, a⟩))

def bellman (s : G.State) (i : ι) : G.BellmanConstraint :=
  Sum.inr (Sum.inr (Sum.inl (s, i)))

def bestResponse (s : G.State) (i : ι) (a : G.Act i) :
    G.BellmanConstraint :=
  Sum.inr (Sum.inr (Sum.inr (s, ⟨i, a⟩)))

end BellmanConstraint

/-- The polynomial belonging to a Bellman constraint index. -/
def bellmanConstraintPoly :
    G.BellmanConstraint → MvPolynomial (BellmanVar G) ℝ
  | .inl (s, i) => G.simplexSumPoly s i
  | .inr (.inl (s, ⟨i, a⟩)) => G.simplexNonnegPoly s i a
  | .inr (.inr (.inl (s, i))) => G.bellmanPoly s i
  | .inr (.inr (.inr (s, ⟨i, a⟩))) => G.bestResponsePoly s i a

/-- The allowed exact signs of one Bellman constraint.  Equality
constraints must vanish; inequality constraints may vanish or be positive. -/
def bellmanConstraintAccepts :
    G.BellmanConstraint → SignType → Prop
  | .inl _, s => s = 0
  | .inr (.inl _), s => 0 ≤ s
  | .inr (.inr (.inl _)), s => s = 0
  | .inr (.inr (.inr _)), s => 0 ≤ s

theorem bellmanConstraint_accepts_sign_iff
    (assign : BellmanVar G → ℝ) (c : G.BellmanConstraint) :
    G.bellmanConstraintAccepts c
        (SignType.sign
          (MvPolynomial.eval assign (G.bellmanConstraintPoly c))) ↔
      match c with
      | .inl (s, i) =>
          MvPolynomial.eval assign (G.simplexSumPoly s i) = 0
      | .inr (.inl (s, ⟨i, a⟩)) =>
          0 ≤ MvPolynomial.eval assign (G.simplexNonnegPoly s i a)
      | .inr (.inr (.inl (s, i))) =>
          MvPolynomial.eval assign (G.bellmanPoly s i) = 0
      | .inr (.inr (.inr (s, ⟨i, a⟩))) =>
          0 ≤ MvPolynomial.eval assign (G.bestResponsePoly s i a) := by
  rcases c with ⟨s, i⟩ | c
  · exact sign_eq_zero_iff
  rcases c with ⟨s, ⟨i, a⟩⟩ | c
  · exact sign_nonneg_iff
  rcases c with ⟨s, i⟩ | ⟨s, ⟨i, a⟩⟩
  · exact sign_eq_zero_iff
  · exact sign_nonneg_iff

/-- The direct Bellman predicate is exactly acceptance of every constraint's
sign in the combined finite polynomial family. -/
theorem isPolynomialBellmanSolution_iff_forall_constraint_sign
    (assign : BellmanVar G → ℝ) :
    G.IsPolynomialBellmanSolution assign ↔
      ∀ c : G.BellmanConstraint,
        G.bellmanConstraintAccepts c
          (polynomialSignPattern G.bellmanConstraintPoly assign c) := by
  constructor
  · rintro ⟨hsum, hnonneg, hbellman, hbest⟩ c
    rw [polynomialSignPattern,
      G.bellmanConstraint_accepts_sign_iff]
    rcases c with ⟨s, i⟩ | c
    · exact hsum s i
    rcases c with ⟨s, ⟨i, a⟩⟩ | c
    · exact hnonneg s i a
    rcases c with ⟨s, i⟩ | ⟨s, ⟨i, a⟩⟩
    · exact hbellman s i
    · exact hbest s i a
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s i
      have hc := h (BellmanConstraint.simplexSum G s i)
      have hc' :=
        (G.bellmanConstraint_accepts_sign_iff assign
          (BellmanConstraint.simplexSum G s i)).mp (by
            simpa [polynomialSignPattern] using hc)
      simpa [BellmanConstraint.simplexSum] using hc'
    · intro s i a
      have hc := h (BellmanConstraint.simplexNonneg G s i a)
      have hc' :=
        (G.bellmanConstraint_accepts_sign_iff assign
          (BellmanConstraint.simplexNonneg G s i a)).mp (by
            simpa [polynomialSignPattern] using hc)
      simpa [BellmanConstraint.simplexNonneg] using hc'
    · intro s i
      have hc := h (BellmanConstraint.bellman G s i)
      have hc' :=
        (G.bellmanConstraint_accepts_sign_iff assign
          (BellmanConstraint.bellman G s i)).mp (by
            simpa [polynomialSignPattern] using hc)
      simpa [BellmanConstraint.bellman] using hc'
    · intro s i a
      have hc := h (BellmanConstraint.bestResponse G s i a)
      have hc' :=
        (G.bellmanConstraint_accepts_sign_iff assign
          (BellmanConstraint.bestResponse G s i a)).mp (by
            simpa [polynomialSignPattern] using hc)
      simpa [BellmanConstraint.bestResponse] using hc'

/-- The set of real assignments satisfying the polynomial Bellman system. -/
def polynomialBellmanSolutionSet : Set (BellmanVar G → ℝ) :=
  {assign | G.IsPolynomialBellmanSolution assign}

/-- The polynomial Bellman solution set is closed. -/
theorem isClosed_polynomialBellmanSolutionSet :
    IsClosed G.polynomialBellmanSolutionSet := by
  have hsum : IsClosed
      {assign : BellmanVar G → ℝ |
        ∀ s i,
          MvPolynomial.eval assign (G.simplexSumPoly s i) = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun i =>
      isClosed_eq (G.simplexSumPoly s i).continuous_eval continuous_const
  have hnonneg : IsClosed
      {assign : BellmanVar G → ℝ |
        ∀ s i a,
          0 ≤ MvPolynomial.eval assign
            (G.simplexNonnegPoly s i a)} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun i =>
      isClosed_iInter fun a =>
        isClosed_le continuous_const
          (G.simplexNonnegPoly s i a).continuous_eval
  have hbellman : IsClosed
      {assign : BellmanVar G → ℝ |
        ∀ s i,
          MvPolynomial.eval assign (G.bellmanPoly s i) = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun i =>
      isClosed_eq (G.bellmanPoly s i).continuous_eval continuous_const
  have hbest : IsClosed
      {assign : BellmanVar G → ℝ |
        ∀ s i a,
          0 ≤ MvPolynomial.eval assign
            (G.bestResponsePoly s i a)} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun i =>
      isClosed_iInter fun a =>
        isClosed_le continuous_const
          (G.bestResponsePoly s i a).continuous_eval
  simpa only [polynomialBellmanSolutionSet,
    IsPolynomialBellmanSolution, setOf_and] using
    hsum.inter (hnonneg.inter (hbellman.inter hbest))

/-- Bellman-solution membership is invariant on every complete sign cell of
the combined constraint family. -/
theorem signInvariant_polynomialBellmanSolutionSet :
    SignInvariant G.bellmanConstraintPoly
      G.polynomialBellmanSolutionSet := by
  intro x y hxy
  change G.IsPolynomialBellmanSolution x ↔
    G.IsPolynomialBellmanSolution y
  rw [G.isPolynomialBellmanSolution_iff_forall_constraint_sign,
    G.isPolynomialBellmanSolution_iff_forall_constraint_sign]
  rw [hxy]

/-- Every closure point of the polynomial Bellman solution set comes from
one complete constraint sign cell contained in that solution set. -/
theorem exists_bellmanSignCell_subset_of_mem_closure
    {assign₀ : BellmanVar G → ℝ}
    (hclosure : assign₀ ∈ closure G.polynomialBellmanSolutionSet) :
    ∃ τ : SignPattern G.BellmanConstraint,
      signCell G.bellmanConstraintPoly τ ⊆
        G.polynomialBellmanSolutionSet ∧
      assign₀ ∈ closure (signCell G.bellmanConstraintPoly τ) :=
  exists_signCell_subset_of_mem_closure
    G.signInvariant_polynomialBellmanSolutionSet hclosure

end StochasticGame
end GameTheory
