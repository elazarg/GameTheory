/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.ConeSeparation
import Math.Probability

/-!
# Actual occupation flows and their separating potentials

This file uses the stochastic occupation columns

`K_i - δ_(source i)`.

In particular, a controlled transition is represented by
`Q_e - δ_(source e)`, not by the signed perturbation
`Q_e - P_(source e)`.  This records the occupation mass consumed at the
source of every transition.

For a distinguished available transition, exactly one of the following
holds:

* a nonnegative stationary occupation circulation uses that transition
  with positive mass;
* a Euclidean-unit potential has nonnegative drift under every other
  available transition and strictly positive drift under the
  distinguished transition.

The circulation is normalized to put mass one on the distinguished
transition.  This is equivalent to the unnormalized positive-mass form by
positive rescaling.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra

noncomputable section

/-- `exists_euclideanUnit_conicSeparator`, transported from coordinate
types `Fin d` and `Fin m` to arbitrary finite coordinate and generator
types. -/
theorem exists_euclideanUnit_conicSeparator_fintype
    {D J : Type*} [Fintype D] [Fintype J]
    (A : D → J → ℝ) (b : D → ℝ)
    (hnot : ¬ ∃ α : J → ℝ, (∀ j, 0 ≤ α j) ∧
      ∀ i, (∑ j, α j * A i j) = b i) :
    ∃ h : D → ℝ,
      (∑ i, h i ^ 2) = 1 ∧
      (∀ j, 0 ≤ ∑ i, h i * A i j) ∧
      (∑ i, h i * b i) < 0 := by
  let eD := Fintype.equivFin D
  let eJ := Fintype.equivFin J
  let A' : Fin (Fintype.card D) → Fin (Fintype.card J) → ℝ :=
    fun i j => A (eD.symm i) (eJ.symm j)
  let b' : Fin (Fintype.card D) → ℝ := fun i => b (eD.symm i)
  have hnot' : ¬ ∃ α : Fin (Fintype.card J) → ℝ,
      (∀ j, 0 ≤ α j) ∧
        ∀ i, (∑ j, α j * A' i j) = b' i := by
    rintro ⟨α, hα, hbalance⟩
    apply hnot
    refine ⟨fun j => α (eJ j), fun j => hα (eJ j), ?_⟩
    intro i
    have hi := hbalance (eD i)
    have hsum :
        (∑ j : J, α (eJ j) * A i j) =
          ∑ j : Fin (Fintype.card J),
            α j * A i (eJ.symm j) := by
      symm
      simpa [eJ] using
        (eJ.symm.sum_comp fun j : J => α (eJ j) * A i j)
    rw [hsum]
    simpa [A', b', eD, eJ] using hi
  obtain ⟨h, hunit, hcolumns, htarget⟩ :=
    exists_euclideanUnit_conicSeparator A' b' hnot'
  refine ⟨fun i => h (eD i), ?_, ?_, ?_⟩
  · calc
      (∑ i : D, h (eD i) ^ 2) =
          ∑ i : Fin (Fintype.card D), h i ^ 2 := by
            symm
            simpa [eD] using
              (eD.symm.sum_comp fun i : D => h (eD i) ^ 2)
      _ = 1 := hunit
  · intro j
    have hsum :
        (∑ i : D, h (eD i) * A i j) =
          ∑ i : Fin (Fintype.card D),
            h i * A (eD.symm i) j := by
      symm
      simpa [eD] using
        (eD.symm.sum_comp fun i : D => h (eD i) * A i j)
    rw [hsum]
    simpa [A', eD, eJ] using hcolumns (eJ j)
  · have hsum :
        (∑ i : D, h (eD i) * b i) =
          ∑ i : Fin (Fintype.card D), h i * b (eD.symm i) := by
      symm
      simpa [eD] using
        (eD.symm.sum_comp fun i : D => h (eD i) * b i)
    rw [hsum]
    simpa [b', eD] using htarget

end

end LinearAlgebra

namespace Probability

noncomputable section

variable {S I E : Type*}

/-- The actual occupation column of a transition kernel: arrival mass minus
one unit of mass consumed at its source. -/
def actualOccupationColumn [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (i : I) (u : S) : ℝ :=
  (kernel i u).toReal - if u = source i then 1 else 0

/-- A normalized nonnegative circulation using `i₀`.  The coefficient of
`i₀` is one and `alpha` supplies the nonnegative coefficients of all other
actual transition columns. -/
def HasNormalizedPositiveCirculation
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I) : Prop :=
  ∃ alpha : {i : I // i ≠ i₀} → ℝ,
    (∀ i, 0 ≤ alpha i) ∧
      ∀ u, column i₀ u +
        ∑ i : {i : I // i ≠ i₀}, alpha i * column i.1 u = 0

/-- An unnormalized nonnegative circulation with strictly positive mass on
`i₀`.  Coefficients of the other columns are kept in the complementary
subtype, so the source-consuming column of `i₀` cannot be duplicated. -/
def HasPositiveCirculation
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I) : Prop :=
  ∃ distinguishedMass : ℝ, 0 < distinguishedMass ∧
    ∃ mass : {i : I // i ≠ i₀} → ℝ,
      (∀ i, 0 ≤ mass i) ∧
        ∀ u, distinguishedMass * column i₀ u +
          ∑ i : {i : I // i ≠ i₀}, mass i * column i.1 u = 0

/-- Positive mass on the distinguished transition may be rescaled to one,
without changing the occupation balance or any coefficient sign. -/
theorem hasPositiveCirculation_iff_normalized
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I) :
    HasPositiveCirculation column i₀ ↔
      HasNormalizedPositiveCirculation column i₀ := by
  constructor
  · rintro ⟨distinguishedMass, hmassPos, mass, hmass, hbalance⟩
    refine ⟨fun i => mass i / distinguishedMass,
      fun i => div_nonneg (hmass i) hmassPos.le, ?_⟩
    intro u
    have hsum :
        (∑ i : {i : I // i ≠ i₀},
            mass i / distinguishedMass * column i.1 u) =
          (∑ i : {i : I // i ≠ i₀}, mass i * column i.1 u) /
            distinguishedMass := by
      simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div]
    rw [hsum]
    calc
      column i₀ u +
          (∑ i : {i : I // i ≠ i₀}, mass i * column i.1 u) /
            distinguishedMass =
          (distinguishedMass * column i₀ u +
            ∑ i : {i : I // i ≠ i₀}, mass i * column i.1 u) /
              distinguishedMass := by
                field_simp [ne_of_gt hmassPos]
      _ = 0 := by rw [hbalance u, zero_div]
  · rintro ⟨mass, hmass, hbalance⟩
    exact ⟨1, zero_lt_one, mass, hmass, by simpa using hbalance⟩

/-- A unit potential separating one column from the cone generated by all
the other columns. -/
def IsUnitStrictColumnSeparator
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I) (h : S → ℝ) : Prop :=
  (∑ u, h u ^ 2) = 1 ∧
    (∀ i : {i : I // i ≠ i₀},
      0 ≤ ∑ u, h u * column i.1 u) ∧
    0 < ∑ u, h u * column i₀ u

/-- A normalized circulation and a strict separator cannot coexist. -/
theorem normalizedPositiveCirculation_not_strictSeparator
    [Fintype S] [Fintype I] [DecidableEq I]
    {column : I → S → ℝ} {i₀ : I}
    (hcirculation : HasNormalizedPositiveCirculation column i₀) :
    ¬ ∃ h, IsUnitStrictColumnSeparator column i₀ h := by
  rintro ⟨h, -, hother, hstrict⟩
  obtain ⟨alpha, halpha, hbalance⟩ := hcirculation
  have hweightedNonneg :
      0 ≤ ∑ i : {i : I // i ≠ i₀},
        alpha i * (∑ u, h u * column i.1 u) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (halpha i) (hother i)
  have hsum :
      (∑ u, h u *
        (column i₀ u +
          ∑ i : {i : I // i ≠ i₀}, alpha i * column i.1 u)) =
        (∑ u, h u * column i₀ u) +
          ∑ i : {i : I // i ≠ i₀},
            alpha i * (∑ u, h u * column i.1 u) := by
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    calc
      (∑ u, h u *
          ∑ i : {i : I // i ≠ i₀}, alpha i * column i.1 u) =
          ∑ u, ∑ i : {i : I // i ≠ i₀},
            h u * (alpha i * column i.1 u) := by
              apply Finset.sum_congr rfl
              intro u _
              rw [Finset.mul_sum]
      _ = ∑ i : {i : I // i ≠ i₀}, ∑ u,
          h u * (alpha i * column i.1 u) := Finset.sum_comm
      _ = ∑ i : {i : I // i ≠ i₀},
          alpha i * (∑ u, h u * column i.1 u) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
  have hzero :
      (∑ u, h u *
        (column i₀ u +
          ∑ i : {i : I // i ≠ i₀}, alpha i * column i.1 u)) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    rw [hbalance u, mul_zero]
  rw [hsum] at hzero
  linarith

/-- **Actual-flow alternative.**  Exactly one of a normalized nonnegative
circulation using `i₀` and a strict unit separator exists. -/
theorem normalizedPositiveCirculation_xor_strictSeparator
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I) :
    Xor (HasNormalizedPositiveCirculation column i₀)
      (∃ h, IsUnitStrictColumnSeparator column i₀ h) := by
  classical
  by_cases hcirculation : HasNormalizedPositiveCirculation column i₀
  · exact Or.inl ⟨hcirculation,
      normalizedPositiveCirculation_not_strictSeparator hcirculation⟩
  · have hnot :
        ¬ ∃ alpha : {i : I // i ≠ i₀} → ℝ,
          (∀ i, 0 ≤ alpha i) ∧
            ∀ u, (∑ i, alpha i * column i.1 u) = -column i₀ u := by
      intro h
      apply hcirculation
      obtain ⟨alpha, halpha, hbalance⟩ := h
      refine ⟨alpha, halpha, ?_⟩
      intro u
      rw [hbalance u]
      ring
    obtain ⟨h, hunit, hother, htarget⟩ :=
      Math.LinearAlgebra.exists_euclideanUnit_conicSeparator_fintype
        (fun u (i : {i : I // i ≠ i₀}) => column i.1 u)
        (fun u => -column i₀ u) hnot
    refine Or.inr ⟨⟨h, hunit, hother, ?_⟩, hcirculation⟩
    have := htarget
    simp only [mul_neg, Finset.sum_neg_distrib] at this
    linarith

/-- Unnormalized positive-mass form of the actual-flow alternative. -/
theorem positiveCirculation_xor_strictSeparator
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I) :
    Xor (HasPositiveCirculation column i₀)
      (∃ h, IsUnitStrictColumnSeparator column i₀ h) := by
  rcases normalizedPositiveCirculation_xor_strictSeparator column i₀ with
      ⟨hcirculation, hnotSeparator⟩ | ⟨hseparator, hnotCirculation⟩
  · exact Or.inl
      ⟨(hasPositiveCirculation_iff_normalized column i₀).2 hcirculation,
        hnotSeparator⟩
  · exact Or.inr ⟨hseparator, fun hcirculation =>
      hnotCirculation
        ((hasPositiveCirculation_iff_normalized column i₀).1 hcirculation)⟩

/-- If the positive-circulation branch is impossible, every nonnegative
balanced coefficient family lies on the zero-coordinate face for the
distinguished transition. -/
theorem distinguishedMass_eq_zero_of_noPositiveCirculation
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I)
    (hno : ¬HasPositiveCirculation column i₀)
    {distinguishedMass : ℝ} {mass : {i : I // i ≠ i₀} → ℝ}
    (hdistinguishedMass : 0 ≤ distinguishedMass)
    (hmass : ∀ i, 0 ≤ mass i)
    (hbalance : ∀ u, distinguishedMass * column i₀ u +
      ∑ i : {i : I // i ≠ i₀}, mass i * column i.1 u = 0) :
    distinguishedMass = 0 := by
  rcases hdistinguishedMass.eq_or_lt with hzero | hpositive
  · exact hzero.symm
  · exact False.elim (hno
      ⟨distinguishedMass, hpositive, mass, hmass, hbalance⟩)

/-- Baseline and controlled transitions collected into one family of
actually available transitions. -/
def occupationKernel
    (baseline : S → PMF S) (controlled : E → PMF S) :
    S ⊕ E → PMF S
  | Sum.inl s => baseline s
  | Sum.inr e => controlled e

/-- Source of each baseline or controlled transition. -/
def occupationSource
    (controlledSource : E → S) : S ⊕ E → S
  | Sum.inl s => s
  | Sum.inr e => controlledSource e

/-- The standard-form occupation column family for a baseline kernel and
its available controlled transitions. -/
def stochasticOccupationColumn [DecidableEq S]
    (baseline : S → PMF S) (controlled : E → PMF S)
    (controlledSource : E → S) : S ⊕ E → S → ℝ :=
  actualOccupationColumn
    (occupationKernel baseline controlled)
    (occupationSource controlledSource)

theorem potential_pair_actualOccupationColumn
    [Fintype S] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (h : S → ℝ) (i : I) :
    (∑ u, h u * actualOccupationColumn kernel source i u) =
      expect (kernel i) h - h (source i) := by
  rw [expect_eq_sum]
  simp only [actualOccupationColumn, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hdelta :
      (∑ u, h u * if u = source i then 1 else 0) = h (source i) := by
    classical
    simp
  rw [hdelta]
  apply congrArg (fun x => x - h (source i))
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- A selected controlled transition is either used by an actual
nonnegative occupation circulation, or is detected by a bounded unit
potential.  Every baseline transition and every other controlled
transition has nonnegative potential drift; the selected transition has
strictly positive drift. -/
theorem controlledEdgeCirculation_xor_unitPotential
    [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
    (baseline : S → PMF S) (controlled : E → PMF S)
    (controlledSource : E → S) (e₀ : E) :
    Xor
      (HasPositiveCirculation
        (stochasticOccupationColumn baseline controlled controlledSource)
        (Sum.inr e₀))
      (∃ h : S → ℝ,
        (∑ u, h u ^ 2) = 1 ∧
        (∀ s, 0 ≤ expect (baseline s) h - h s) ∧
        (∀ e, e ≠ e₀ →
          0 ≤ expect (controlled e) h - h (controlledSource e)) ∧
        0 < expect (controlled e₀) h - h (controlledSource e₀)) := by
  classical
  let column :=
    stochasticOccupationColumn baseline controlled controlledSource
  rcases positiveCirculation_xor_strictSeparator
      column (Sum.inr e₀) with
      ⟨hcirculation, hnotSeparator⟩ | ⟨hseparator, hnotCirculation⟩
  · exact Or.inl ⟨hcirculation, by
      rintro ⟨h, hunit, hbaseline, hcontrolled, hstrict⟩
      apply hnotSeparator
      refine ⟨h, hunit, ?_, ?_⟩
      · rintro ⟨i, hi⟩
        rcases i with s | e
        · simpa [column, stochasticOccupationColumn, occupationKernel,
            occupationSource,
            potential_pair_actualOccupationColumn] using hbaseline s
        · have he : e ≠ e₀ := by
            intro heq
            apply hi
            simp [heq]
          simpa [column, stochasticOccupationColumn, occupationKernel,
            occupationSource,
            potential_pair_actualOccupationColumn] using hcontrolled e he
      · simpa [column, stochasticOccupationColumn, occupationKernel,
          occupationSource,
          potential_pair_actualOccupationColumn] using hstrict⟩
  · obtain ⟨h, hunit, hother, hstrict⟩ := hseparator
    refine Or.inr ⟨⟨h, hunit, ?_, ?_, ?_⟩, hnotCirculation⟩
    · intro s
      have hs := hother
        ⟨Sum.inl s, by simp⟩
      simpa [column, stochasticOccupationColumn, occupationKernel,
        occupationSource,
        potential_pair_actualOccupationColumn] using hs
    · intro e he
      have hs := hother
        ⟨Sum.inr e, by simpa using he⟩
      simpa [column, stochasticOccupationColumn, occupationKernel,
        occupationSource,
        potential_pair_actualOccupationColumn] using hs
    · simpa [column, stochasticOccupationColumn, occupationKernel,
        occupationSource,
        potential_pair_actualOccupationColumn] using hstrict

/-- Every coordinate of a Euclidean-unit potential has absolute value at
most one. -/
theorem abs_le_one_of_sum_sq_eq_one
    [Fintype S] {h : S → ℝ} (hunit : (∑ s, h s ^ 2) = 1) (s : S) :
    |h s| ≤ 1 := by
  have hsquare : h s ^ 2 ≤ ∑ u, h u ^ 2 :=
    Finset.single_le_sum (fun u _ => sq_nonneg (h u)) (Finset.mem_univ s)
  rw [hunit] at hsquare
  nlinarith [sq_nonneg (|h s| - 1), abs_nonneg (h s),
    sq_abs (h s)]

/-- The oscillation of a Euclidean-unit potential is at most two. -/
theorem sub_le_two_of_sum_sq_eq_one
    [Fintype S] {h : S → ℝ} (hunit : (∑ s, h s ^ 2) = 1)
    (s t : S) :
    h s - h t ≤ 2 := by
  have hs := abs_le_one_of_sum_sq_eq_one hunit s
  have ht := abs_le_one_of_sum_sq_eq_one hunit t
  have hs' : h s ≤ 1 := (le_abs_self (h s)).trans hs
  have ht' : -1 ≤ h t := by
    have := (neg_le_abs (h t)).trans ht
    linarith
  linarith

/-- Static count-budget ledger.  If all transition drifts are nonnegative
and the distinguished transition has drift at least `eta`, then any
nonnegative usage vector pays at least `eta` per distinguished use from
its total potential drift. -/
theorem distinguishedUse_mul_margin_le_weightedDrift
    [Fintype I]
    (drift mass : I → ℝ) (i₀ : I) {eta : ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (hdrift : ∀ i, 0 ≤ drift i)
    (hmargin : eta ≤ drift i₀) :
    mass i₀ * eta ≤ ∑ i, mass i * drift i := by
  calc
    mass i₀ * eta ≤ mass i₀ * drift i₀ :=
      mul_le_mul_of_nonneg_left hmargin (hmass i₀)
    _ ≤ ∑ i, mass i * drift i :=
      Finset.single_le_sum
        (fun i _ => mul_nonneg (hmass i) (hdrift i))
        (Finset.mem_univ i₀)

/-- Removing a forbidden transition strictly decreases the finite support
rank.  This is the well-founded rank used by standard-form occupation-face
descent. -/
theorem card_erase_lt_supportRank
    [DecidableEq I] (support : Finset I) {i₀ : I}
    (hi₀ : i₀ ∈ support) :
    (support.erase i₀).card < support.card := by
  simpa using Finset.card_erase_lt_of_mem hi₀

end

end Probability
end Math
