/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.OccupationFlowAlternative

/-!
# Charged occupation-flow alternative

For a finite family of source-consuming transition columns, attach one real
charge to every available transition. Exactly one of the following holds:

* nonnegative transition masses balance and have normalized total charge one;
* a state potential dominates the charge of every transition.

This is the exact finite Farkas alternative needed before a stochastic flow
can be used as a positive incentive certificate. It does not single out one
edge and it does not reverse an unavailable transition.
-/

open Finset BigOperators

namespace Math
namespace Probability

noncomputable section

variable {S I : Type*}

/-- A nonnegative balanced transition family with total charge normalized
to one. Any balanced family with strictly positive charge can be rescaled
into this form. -/
def HasNormalizedPositiveChargedCirculation
    [Fintype S] [Fintype I]
    (column : I → S → ℝ) (charge : I → ℝ) : Prop :=
  ∃ mass : I → ℝ,
    (∀ i, 0 ≤ mass i) ∧
    (∀ s, ∑ i, mass i * column i s = 0) ∧
    ∑ i, mass i * charge i = 1

/-- A potential dominates the charge of every available transition. For an
actual occupation column `Q_i - δ_(source i)`, the right-hand side is the
one-step potential drift `Q_i h - h(source i)`. -/
def IsChargedOccupationPotential
    [Fintype S]
    (column : I → S → ℝ) (charge : I → ℝ)
    (potential : S → ℝ) : Prop :=
  ∀ i, charge i ≤ ∑ s, potential s * column i s

/-- A normalized positive charged circulation and a dominating potential
cannot coexist. -/
theorem normalizedPositiveChargedCirculation_not_potential
    [Fintype S] [Fintype I]
    {column : I → S → ℝ} {charge : I → ℝ}
    (hcirculation :
      HasNormalizedPositiveChargedCirculation column charge) :
    ¬ ∃ potential, IsChargedOccupationPotential column charge potential := by
  rintro ⟨potential, hpotential⟩
  obtain ⟨mass, hmass, hbalance, hcharge⟩ := hcirculation
  have hweighted :
      (∑ i, mass i * charge i) ≤
        ∑ i, mass i * (∑ s, potential s * column i s) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hpotential i) (hmass i)
  have hzero :
      (∑ i, mass i * (∑ s, potential s * column i s)) = 0 := by
    calc
      (∑ i, mass i * (∑ s, potential s * column i s)) =
          ∑ i, ∑ s, mass i * (potential s * column i s) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ s, ∑ i, mass i * (potential s * column i s) := by
        rw [Finset.sum_comm]
      _ = ∑ s, potential s * (∑ i, mass i * column i s) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        rw [hbalance s, mul_zero]
  rw [hcharge, hzero] at hweighted
  norm_num at hweighted

/-- **Charged occupation-flow Farkas alternative.**

Either nonnegative actual transition masses balance with positive normalized
charge, or one state potential dominates every transition's charge. The two
branches are exclusive. -/
theorem normalizedPositiveChargedCirculation_xor_potential
    [Fintype S] [Fintype I]
    (column : I → S → ℝ) (charge : I → ℝ) :
    Xor
      (HasNormalizedPositiveChargedCirculation column charge)
      (∃ potential, IsChargedOccupationPotential column charge potential) := by
  classical
  rw [xor_def]
  by_cases hcirculation :
      HasNormalizedPositiveChargedCirculation column charge
  · exact Or.inl
      ⟨hcirculation,
        normalizedPositiveChargedCirculation_not_potential hcirculation⟩
  · have hnot :
        ¬ ∃ mass : I → ℝ,
          (∀ i, 0 ≤ mass i) ∧
          ∀ coordinate : S ⊕ Unit,
            (∑ i, mass i *
              Sum.elim (column i) (fun _ => charge i) coordinate) =
                Sum.elim (fun _ : S => 0) (fun _ => 1) coordinate := by
      rintro ⟨mass, hmass, hsystem⟩
      apply hcirculation
      refine ⟨mass, hmass, ?_, ?_⟩
      · intro s
        simpa using hsystem (Sum.inl s)
      · simpa using hsystem (Sum.inr ())
    obtain ⟨separator, -, hcolumns, htarget⟩ :=
      Math.LinearAlgebra.exists_euclideanUnit_conicSeparator_fintype
        (fun coordinate i =>
          Sum.elim (column i) (fun _ => charge i) coordinate)
        (Sum.elim (fun _ : S => 0) (fun _ => 1))
        hnot
    let denominator : ℝ := -separator (Sum.inr ())
    have hdenominator : 0 < denominator := by
      simpa [denominator] using (neg_pos.mpr htarget)
    let potential : S → ℝ :=
      fun s => separator (Sum.inl s) / denominator
    have hpotential :
        IsChargedOccupationPotential column charge potential := by
      intro i
      have hcolumn := hcolumns i
      rw [Fintype.sum_sum_type] at hcolumn
      simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique] at hcolumn
      have hscaled :
          charge i ≤
            (∑ s, separator (Sum.inl s) * column i s) /
              denominator := by
        apply (le_div_iff₀ hdenominator).2
        dsimp only [denominator]
        linarith
      calc
        charge i ≤
            (∑ s, separator (Sum.inl s) * column i s) /
              denominator :=
          hscaled
        _ = ∑ s, potential s * column i s := by
          simp only [potential, div_mul_eq_mul_div]
          rw [Finset.sum_div]
    exact Or.inr
      ⟨⟨potential, hpotential⟩, fun hpositive =>
        normalizedPositiveChargedCirculation_not_potential
          hpositive ⟨potential, hpotential⟩⟩

/-- For genuine transition columns, the dual inequality is exactly a
one-step drift bound. -/
theorem isChargedOccupationPotential_actualOccupationColumn_iff
    [Fintype S] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (charge : I → ℝ) (potential : S → ℝ) :
    IsChargedOccupationPotential
        (actualOccupationColumn kernel source) charge potential ↔
      ∀ i,
        charge i ≤
          expect (kernel i) potential - potential (source i) := by
  apply forall_congr'
  intro i
  rw [potential_pair_actualOccupationColumn]

/-- Semantic form of the charged occupation alternative for a finite family
of actually available transition kernels. -/
theorem normalizedPositiveChargedCirculation_xor_driftPotential
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (charge : I → ℝ) :
    Xor
      (HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn kernel source) charge)
      (∃ potential : S → ℝ, ∀ i,
        charge i ≤
          expect (kernel i) potential - potential (source i)) := by
  have h :=
    normalizedPositiveChargedCirculation_xor_potential
      (actualOccupationColumn kernel source) charge
  rw [xor_def] at h ⊢
  rcases h with
      ⟨hcirculation, hnotPotential⟩ |
      ⟨hpotential, hnotCirculation⟩
  · exact Or.inl ⟨hcirculation, fun hsemantic =>
      hnotPotential ⟨hsemantic.choose,
        (isChargedOccupationPotential_actualOccupationColumn_iff
          kernel source charge hsemantic.choose).2
            hsemantic.choose_spec⟩⟩
  · refine Or.inr ⟨?_, hnotCirculation⟩
    obtain ⟨potential, hpotential⟩ := hpotential
    exact ⟨potential,
      (isChargedOccupationPotential_actualOccupationColumn_iff
        kernel source charge potential).1 hpotential⟩

/-- A strictly positive charged circulation rescales to the normalized
version used by the alternative. -/
theorem exists_normalizedPositiveChargedCirculation_of_pos
    [Fintype S] [Fintype I]
    {column : I → S → ℝ} {charge mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (hbalance : ∀ s, ∑ i, mass i * column i s = 0)
    (hcharge : 0 < ∑ i, mass i * charge i) :
    HasNormalizedPositiveChargedCirculation column charge := by
  let totalCharge := ∑ i, mass i * charge i
  refine ⟨fun i => mass i / totalCharge, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (hmass i) hcharge.le
  · intro s
    calc
      (∑ i, mass i / totalCharge * column i s) =
          (∑ i, mass i * column i s) / totalCharge := by
        simp only [div_mul_eq_mul_div]
        rw [Finset.sum_div]
      _ = 0 := by rw [hbalance s, zero_div]
  · calc
      (∑ i, mass i / totalCharge * charge i) =
          (∑ i, mass i * charge i) / totalCharge := by
        simp only [div_mul_eq_mul_div]
        rw [Finset.sum_div]
      _ = 1 := div_self (ne_of_gt hcharge)

/-- If finitely many owners each carry a nonnegative balanced operational
flow and their aggregate charge is positive, one owner already carries a
positive charged circulation. No cross-owner transition cancellation is
used. -/
theorem exists_owner_normalizedPositiveChargedCirculation
    {Owner : Type*} {Index : Owner → Type*}
    [Fintype Owner] [∀ owner, Fintype (Index owner)]
    [Fintype S]
    (column : ∀ owner, Index owner → S → ℝ)
    (charge mass : ∀ owner, Index owner → ℝ)
    (hmass : ∀ owner i, 0 ≤ mass owner i)
    (hbalance :
      ∀ owner s, ∑ i, mass owner i * column owner i s = 0)
    (htotal :
      0 < ∑ owner, ∑ i, mass owner i * charge owner i) :
    ∃ owner,
      HasNormalizedPositiveChargedCirculation
        (column owner) (charge owner) := by
  have hexists :
      ∃ owner, 0 < ∑ i, mass owner i * charge owner i := by
    by_contra hno
    push Not at hno
    have hsum :
        (∑ owner, ∑ i, mass owner i * charge owner i) ≤ 0 :=
      Finset.sum_nonpos fun owner _ => hno owner
    exact (not_lt_of_ge hsum) htotal
  obtain ⟨owner, howner⟩ := hexists
  exact ⟨owner,
    exists_normalizedPositiveChargedCirculation_of_pos
      (hmass owner) (hbalance owner) howner⟩

/-- A balanced finite occupation flow annihilates the weighted drift of
every state potential. -/
theorem balancedMass_weightedPotentialDrift_eq_zero
    [Fintype S] [Fintype I]
    (column : I → S → ℝ) (mass : I → ℝ)
    (hbalance : ∀ s, ∑ i, mass i * column i s = 0)
    (potential : S → ℝ) :
    ∑ i, mass i * (∑ s, potential s * column i s) = 0 := by
  calc
    (∑ i, mass i * (∑ s, potential s * column i s)) =
        ∑ i, ∑ s, mass i * (potential s * column i s) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ s, ∑ i, mass i * (potential s * column i s) := by
      rw [Finset.sum_comm]
    _ = ∑ s, potential s * (∑ i, mass i * column i s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      rw [hbalance s, mul_zero]

/-- In a normalized charged circulation, any decomposition of transition
charge into a stage term plus a potential drift has normalized weighted
stage term one. The continuation part cancels by occupation balance. -/
theorem HasNormalizedPositiveChargedCirculation.weightedStage_eq_one
    [Fintype S] [Fintype I]
    {column : I → S → ℝ} {charge : I → ℝ}
    (C : HasNormalizedPositiveChargedCirculation column charge)
    (stage : I → ℝ) (potential : S → ℝ)
    (hdecompose :
      ∀ i, charge i =
        stage i + ∑ s, potential s * column i s) :
    ∃ mass : I → ℝ,
      (∀ i, 0 ≤ mass i) ∧
      (∀ s, ∑ i, mass i * column i s = 0) ∧
      ∑ i, mass i * stage i = 1 := by
  obtain ⟨mass, hmass, hbalance, hcharge⟩ := C
  refine ⟨mass, hmass, hbalance, ?_⟩
  have hdrift :=
    balancedMass_weightedPotentialDrift_eq_zero
      column mass hbalance potential
  calc
    (∑ i, mass i * stage i) =
        (∑ i, mass i * charge i) -
          ∑ i, mass i * (∑ s, potential s * column i s) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hdecompose i]
      ring
    _ = 1 := by rw [hcharge, hdrift, sub_zero]

end

end Probability
end Math
