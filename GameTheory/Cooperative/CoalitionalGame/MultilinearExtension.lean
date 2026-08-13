/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.CoalitionalGame.Shapley
import Math.PMFProduct.CoalitionMass

/-!
# Multilinear extensions of coalitional games

The unanimity coefficients of a finite coalitional game are also the
coefficients of its multilinear extension.  This module records the exact
independent-coalition averaging identity and its discrete coordinate
derivative, together with the cardinality split into singleton, pair, and
higher-order terms.

All identities are algebraic: the coordinate vector need not lie in the unit
cube, and no sign conclusion about the coefficients or derivatives is made.
-/

noncomputable section

open scoped BigOperators

namespace Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The total exact-coalition mass of all coalitions containing `S` is the
product of the coordinates on `S`.  No interval assumption on `x` is needed. -/
theorem sum_coalitionMass_supersets (x : ι → ℝ) (S : Finset ι) :
    ∑ J ∈ (Finset.univ : Finset (Finset ι)).filter (S ⊆ ·), coalitionMass x J =
      ∏ i ∈ S, x i := by
  classical
  have hreindex :
      (Finset.univ : Finset (Finset ι)).filter (S ⊆ ·) =
        Sᶜ.powerset.image (fun K => S ∪ K) := by
    ext J
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powerset]
    constructor
    · intro hSJ
      refine ⟨J \ S, ?_, Finset.union_sdiff_of_subset hSJ⟩
      intro i hi
      rw [Finset.mem_compl]
      exact (Finset.mem_sdiff.mp hi).2
    · rintro ⟨K, hK, rfl⟩
      exact Finset.subset_union_left
  have hinj : Set.InjOn (fun K : Finset ι => S ∪ K) (Sᶜ.powerset : Set (Finset ι)) := by
    intro K hK L hL hEq
    have hKS : Disjoint S K := by
      have hK' : K ⊆ Sᶜ := Finset.mem_powerset.mp hK
      exact Finset.disjoint_left.mpr fun i hiS hiK => (Finset.mem_compl.mp (hK' hiK)) hiS
    have hLS : Disjoint S L := by
      have hL' : L ⊆ Sᶜ := Finset.mem_powerset.mp hL
      exact Finset.disjoint_left.mpr fun i hiS hiL => (Finset.mem_compl.mp (hL' hiL)) hiS
    have := congrArg (· \ S) hEq
    simpa [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hKS.symm,
      Finset.sdiff_eq_self_of_disjoint hLS.symm] using this
  rw [hreindex, Finset.sum_image (fun K hK L hL hEq => hinj hK hL hEq)]
  have hmass : ∀ K ∈ Sᶜ.powerset,
      coalitionMass x (S ∪ K) =
        (∏ i ∈ S, x i) *
          ((∏ i ∈ K, x i) * ∏ i ∈ Sᶜ \ K, (1 - x i)) := by
    intro K hK
    rw [Finset.mem_powerset] at hK
    have hdisj : Disjoint S K :=
      Finset.disjoint_left.mpr fun i hiS hiK => (Finset.mem_compl.mp (hK hiK)) hiS
    have hcompl : (S ∪ K)ᶜ = Sᶜ \ K := by
      ext i
      simp
    simp only [coalitionMass, hcompl]
    rw [Finset.prod_union hdisj]
    ring
  rw [Finset.sum_congr rfl hmass]
  rw [← Finset.mul_sum]
  have hprod := Finset.prod_add x (fun i => 1 - x i) Sᶜ
  have hone : ∏ i ∈ Sᶜ, (x i + (1 - x i)) = (1 : ℝ) := by
    convert Finset.prod_const_one
    ring
  rw [hone] at hprod
  rw [← hprod, mul_one]

end Math.PMFProduct

namespace GameTheory

open Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Multilinear evaluation of a coalitional game's unanimity coefficients. -/
def CoalGame.multilinearValue (G : CoalGame ι) (x : ι → ℝ) : ℝ :=
  ∑ S : Finset ι, G.unanimityCoeff S * ∏ i ∈ S, x i

/-- Exact-coalition averaging agrees with evaluation in unanimity/Möbius
coordinates. -/
theorem CoalGame.sum_coalitionMass_mul_value_eq_multilinearValue
    (G : CoalGame ι) (x : ι → ℝ) :
    ∑ J : Finset ι, coalitionMass x J * G.v J = G.multilinearValue x := by
  classical
  simp_rw [G.unanimity_decomposition]
  rw [show
    (∑ J : Finset ι, coalitionMass x J *
        ∑ S ∈ J.powerset, G.unanimityCoeff S) =
      ∑ S : Finset ι, G.unanimityCoeff S *
        ∑ J ∈ (Finset.univ : Finset (Finset ι)).filter (S ⊆ ·),
          coalitionMass x J from ?_]
  · simp_rw [sum_coalitionMass_supersets]
    rfl
  · rw [show
      (∑ J : Finset ι, coalitionMass x J *
          ∑ S ∈ J.powerset, G.unanimityCoeff S) =
        ∑ J : Finset ι, ∑ S ∈ J.powerset,
          coalitionMass x J * G.unanimityCoeff S by
        apply Finset.sum_congr rfl
        intro J _
        rw [Finset.mul_sum]]
    rw [show
      (∑ J : Finset ι, ∑ S ∈ J.powerset,
          coalitionMass x J * G.unanimityCoeff S) =
        ∑ S : Finset ι,
          ∑ J ∈ (Finset.univ : Finset (Finset ι)).filter (S ⊆ ·),
            coalitionMass x J * G.unanimityCoeff S from by
      apply Finset.sum_comm'
      intro J S
      simp only [Finset.mem_univ, Finset.mem_powerset, Finset.mem_filter, true_and]
      tauto]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J _
    ring

/-! ## Discrete coordinate derivatives -/

/-- Discrete coordinate derivative of the multilinear extension: coefficients
containing `who`, with that coordinate removed from their monomial. -/
def CoalGame.coordinateDerivative (G : CoalGame ι) (x : ι → ℝ) (who : ι) : ℝ :=
  ∑ S : Finset ι,
    if who ∈ S then G.unanimityCoeff S * ∏ i ∈ S.erase who, x i else 0

/-- The part of a coordinate derivative carried by coefficients of a fixed
coalition cardinality. -/
def CoalGame.coordinateDerivativeOfCard
    (G : CoalGame ι) (x : ι → ℝ) (who : ι) (card : ℕ) : ℝ :=
  ∑ S : Finset ι,
    if who ∈ S ∧ S.card = card then
      G.unanimityCoeff S * ∏ i ∈ S.erase who, x i
    else 0

/-- The higher-order part of a coordinate derivative, carried by coalitions
of cardinality at least three. -/
def CoalGame.higherOrderCoordinateDerivative
    (G : CoalGame ι) (x : ι → ℝ) (who : ι) : ℝ :=
  ∑ S : Finset ι,
    if who ∈ S ∧ 3 ≤ S.card then
      G.unanimityCoeff S * ∏ i ∈ S.erase who, x i
    else 0

/-- A coordinate derivative splits exactly into singleton, pair, and
higher-order coefficient contributions. -/
theorem CoalGame.coordinateDerivative_eq_singleton_add_pair_add_higherOrder
    (G : CoalGame ι) (x : ι → ℝ) (who : ι) :
    G.coordinateDerivative x who =
      G.coordinateDerivativeOfCard x who 1 +
        G.coordinateDerivativeOfCard x who 2 +
          G.higherOrderCoordinateDerivative x who := by
  classical
  unfold CoalGame.coordinateDerivative CoalGame.coordinateDerivativeOfCard
    CoalGame.higherOrderCoordinateDerivative
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hwho : who ∈ S
  · have hpos : 0 < S.card := Finset.card_pos.mpr ⟨who, hwho⟩
    by_cases hsingle : S.card = 1
    · simp [hwho, hsingle]
    · by_cases hpair : S.card = 2
      · simp [hwho, hpair]
      · have hhigher : 3 ≤ S.card := by omega
        simp [hwho, hsingle, hpair, hhigher]
  · simp [hwho]

/-- Switching one coordinate of the multilinear extension from zero to one
is exactly its discrete coordinate derivative. -/
theorem CoalGame.multilinearValue_update_one_sub_update_zero
    (G : CoalGame ι) (x : ι → ℝ) (who : ι) :
    G.multilinearValue (Function.update x who 1) -
        G.multilinearValue (Function.update x who 0) =
      G.coordinateDerivative x who := by
  classical
  unfold CoalGame.multilinearValue CoalGame.coordinateDerivative
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hwho : who ∈ S
  · have hprod : ∀ a : ℝ,
        (∏ i ∈ S, Function.update x who a i) =
          a * ∏ i ∈ S.erase who, x i := by
      intro a
      calc
        (∏ i ∈ S, Function.update x who a i) =
            Function.update x who a who *
              ∏ i ∈ S.erase who, Function.update x who a i :=
          (Finset.mul_prod_erase (s := S)
            (f := fun i => Function.update x who a i) (a := who) hwho).symm
        _ = a * ∏ i ∈ S.erase who, x i := by
          simp only [Function.update_self]
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          simp [Finset.ne_of_mem_erase hi]
    rw [if_pos hwho, hprod, hprod]
    ring
  · have hprod : ∀ a : ℝ,
        (∏ i ∈ S, Function.update x who a i) = ∏ i ∈ S, x i := by
      intro a
      apply Finset.prod_congr rfl
      intro i hi
      simp [ne_of_mem_of_not_mem hi hwho]
    rw [if_neg hwho, hprod, hprod]
    ring

end GameTheory
