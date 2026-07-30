/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.FiniteDeflationIteration
import Math.Probability.AnalyticChargedPotentialEndpoint

/-!
# Analytic occupation alternatives on arbitrary finite active sets

An analytic occupation family over a fixed finite ambient index type can be
restricted to the active subtype of any `FiniteDeflationState`.  Analyticity
and the zero-coordinate-sum identity pass to this restriction.

Given an endpoint normalized positive charged circulation on the active
family, the usual analytic alternative can be rerun at that node: either an
analytic positive charged circulation persists, or a scaled potential and
its first nonzero gauge-fixed jet are produced.

The leading endpoint pairing of such a jet is nonnegative.  Deleting every
active index with strictly positive pairing preserves the endpoint
circulation by complementarity.  This supplies the circulation invariant
needed to repeat the construction at every strictly smaller active-set
rank.

The result is purely finite-dimensional and analytic.  It does not attach a
strategy or reachability interpretation to an active set.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Set
open AnalyticScaledChargedOccupationPotential

variable {S I J : Type*}

/-- Restrict a moving ambient occupation column family to one active node. -/
def activeOccupationColumn
    [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (column : ℝ → I → S → ℝ) :
    ℝ → state.ActiveIndex → S → ℝ :=
  fun t index destination => column t index.1 destination

/-- Restrict a moving ambient charge family to one active node. -/
def activeOccupationCharge
    [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (charge : ℝ → I → ℝ) :
    ℝ → state.ActiveIndex → ℝ :=
  fun t index => charge t index.1

/-- Coordinatewise analyticity is inherited by every active restriction. -/
theorem analytic_activeOccupationColumn
    [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (column : ℝ → I → S → ℝ)
    (analytic_column :
      ∀ index destination,
        AnalyticAt ℝ (fun t => column t index destination) 0) :
    ∀ index destination,
      AnalyticAt ℝ
        (fun t =>
          activeOccupationColumn state column t index destination) 0 := by
  intro index destination
  exact analytic_column index.1 destination

/-- Coordinatewise charge analyticity is inherited by every active
restriction. -/
theorem analytic_activeOccupationCharge
    [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (charge : ℝ → I → ℝ)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0) :
    ∀ index,
      AnalyticAt ℝ
        (fun t => activeOccupationCharge state charge t index) 0 := by
  intro index
  exact analytic_charge index.1

/-- The punctured zero-sum column identity is inherited by every active
restriction. -/
theorem eventually_sum_activeOccupationColumn_eq_zero
    [Fintype S] [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (column : ℝ → I → S → ℝ)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ destination, column t index destination = 0) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ index,
        ∑ destination,
          activeOccupationColumn state column
            t index destination = 0 := by
  filter_upwards [column_zero_sum] with t ht
  intro index
  exact ht index.1

/-- Normalized positive charged circulation is invariant under a finite
reindexing equivalence. -/
theorem HasNormalizedPositiveChargedCirculation.reindex
    [Fintype S] [Fintype I] [Fintype J]
    (column : I → S → ℝ) (charge : I → ℝ)
    (circulation :
      HasNormalizedPositiveChargedCirculation column charge)
    (equiv : J ≃ I) :
    HasNormalizedPositiveChargedCirculation
      (fun index => column (equiv index))
      (fun index => charge (equiv index)) := by
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one⟩ :=
    circulation
  refine ⟨fun index => mass (equiv index), ?_, ?_, ?_⟩
  · intro index
    exact mass_nonneg (equiv index)
  · intro destination
    simpa only using
      (equiv.sum_comp
        (fun index => mass index * column index destination)).trans
        (balance destination)
  · simpa only using
      (equiv.sum_comp
        (fun index => mass index * charge index)).trans
        charge_eq_one

/-- A scaled active potential packaged with its first nonzero gauge-fixed
analytic coefficient. -/
structure ActiveAnalyticPotentialJet
    [Fintype S] [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (column : ℝ → I → S → ℝ)
    (charge : ℝ → I → ℝ)
    (anchor : S) where
  scaledPotential :
    AnalyticScaledChargedOccupationPotential
      (activeOccupationColumn state column)
      (activeOccupationCharge state charge)
  gaugeFixedJet :
    GaugeFixedPotentialJet scaledPotential anchor

/-- The analytic charged-flow alternative can be rerun at an arbitrary
active-set node carrying an endpoint normalized positive circulation. -/
theorem
    activePositiveChargedCirculation_xor_nextPotentialJet
    [Fintype S] [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (column : ℝ → I → S → ℝ)
    (charge : ℝ → I → ℝ)
    (analytic_column :
      ∀ index destination,
        AnalyticAt ℝ (fun t => column t index destination) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ destination, column t index destination = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (activeOccupationColumn state column 0)
        (activeOccupationCharge state charge 0))
    (anchor : S) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation
          (activeOccupationColumn state column)
          (activeOccupationCharge state charge)))
      (Nonempty
        (ActiveAnalyticPotentialJet
          state column charge anchor)) := by
  have active_column_analytic :=
    analytic_activeOccupationColumn
      state column analytic_column
  have active_charge_analytic :=
    analytic_activeOccupationCharge
      state charge analytic_charge
  have active_zero_sum :=
    eventually_sum_activeOccupationColumn_eq_zero
      state column column_zero_sum
  rcases
      analyticPositiveChargedCirculation_xor_scaledPotential
        (activeOccupationColumn state column)
        (activeOccupationCharge state charge)
        active_column_analytic active_charge_analytic with
    analyticCirculation | scaledPotential
  · refine Or.inl ⟨analyticCirculation.1, ?_⟩
    rintro ⟨next⟩
    exact analyticCirculation.2 ⟨next.scaledPotential⟩
  · obtain ⟨nextPotential⟩ := scaledPotential.1
    obtain ⟨nextJet⟩ :=
      nextPotential.exists_gaugeFixedPotentialJet
        anchor active_charge_analytic active_zero_sum circulation
    refine Or.inr ⟨⟨{
      scaledPotential := nextPotential
      gaugeFixedJet := nextJet
    }⟩, scaledPotential.2⟩

/-- Leading endpoint pairing of one active analytic potential jet. -/
def ActiveAnalyticPotentialJet.leadingPairing
    [Fintype S] [Fintype I] [DecidableEq I]
    {state : FiniteDeflationState I}
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {anchor : S}
    (next : ActiveAnalyticPotentialJet
      state column charge anchor)
    (index : state.ActiveIndex) : ℝ :=
  ∑ destination,
    next.gaugeFixedJet.factor 0 destination *
      column 0 index.1 destination

/-- The leading active pairing is nonnegative under the endpoint
circulation invariant. -/
theorem ActiveAnalyticPotentialJet.leadingPairing_nonneg
    [Fintype S] [Fintype I] [DecidableEq I]
    {state : FiniteDeflationState I}
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {anchor : S}
    (next : ActiveAnalyticPotentialJet
      state column charge anchor)
    (analytic_column :
      ∀ index destination,
        AnalyticAt ℝ (fun t => column t index destination) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ destination, column t index destination = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (activeOccupationColumn state column 0)
        (activeOccupationCharge state charge 0))
    (index : state.ActiveIndex) :
    0 ≤ next.leadingPairing index := by
  exact next.gaugeFixedJet.leading_pair_nonneg
    (analytic_activeOccupationColumn state column analytic_column)
    (analytic_activeOccupationCharge state charge analytic_charge)
    (eventually_sum_activeOccupationColumn_eq_zero
      state column column_zero_sum)
    circulation index

/-- Restrict a supplied complementary circulation across an arbitrary
strict active-set deletion. -/
theorem deleteStrict_hasNormalizedPositiveChargedCirculation
    [Fintype S] [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (column : I → S → ℝ) (charge : I → ℝ)
    (score : state.ActiveIndex → ℝ)
    (mass : state.ActiveIndex → ℝ)
    (mass_nonneg : ∀ index, 0 ≤ mass index)
    (balance :
      ∀ destination,
        ∑ index, mass index * column index.1 destination = 0)
    (charge_eq_one :
      ∑ index, mass index * charge index.1 = 1)
    (complementary :
      ∀ index, 0 < mass index → score index = 0) :
    HasNormalizedPositiveChargedCirculation
      (fun index : (state.deleteStrict score).ActiveIndex =>
        column index.1)
      (fun index : (state.deleteStrict score).ActiveIndex =>
        charge index.1) := by
  let strictSet : Finset state.ActiveIndex :=
    state.strictActiveSet score
  let Retained :=
    {index : state.ActiveIndex // index ∉ strictSet}
  have mass_zero_of_strict :
      ∀ index, index ∈ strictSet → mass index = 0 := by
    intro index index_strict
    apply le_antisymm
    · exact le_of_not_gt fun mass_pos => by
        have score_zero := complementary index mass_pos
        have score_pos : 0 < score index :=
          (state.mem_strictActiveSet_iff score index).mp
            index_strict
        exact (ne_of_gt score_pos) score_zero
    · exact mass_nonneg index
  let retainedMass : Retained → ℝ :=
    fun index => mass index.1
  have retainedCirculation :
      HasNormalizedPositiveChargedCirculation
        (fun index : Retained => column index.1.1)
        (fun index : Retained => charge index.1.1) := by
    refine ⟨retainedMass, ?_, ?_, ?_⟩
    · intro index
      exact mass_nonneg index.1
    · intro destination
      let term : state.ActiveIndex → ℝ :=
        fun index => mass index * column index.1 destination
      let remaining : Finset state.ActiveIndex :=
        Finset.univ.filter fun index => index ∉ strictSet
      have residual_eq_full :
          (∑ index : Retained, term index.1) =
            ∑ index, term index := by
        rw [← Finset.sum_subtype
          remaining
          (fun index => by
            simp only [remaining, Finset.mem_filter,
              Finset.mem_univ, true_and])
          term]
        apply Finset.sum_subset
          (Finset.subset_univ remaining)
        intro index _ index_not_remaining
        have index_strict : index ∈ strictSet := by
          simpa only [remaining, Finset.mem_filter,
            Finset.mem_univ, true_and, not_not] using
              index_not_remaining
        change mass index * column index.1 destination = 0
        rw [mass_zero_of_strict index index_strict, zero_mul]
      change (∑ index : Retained, term index.1) = 0
      rw [residual_eq_full]
      exact balance destination
    · let term : state.ActiveIndex → ℝ :=
        fun index => mass index * charge index.1
      let remaining : Finset state.ActiveIndex :=
        Finset.univ.filter fun index => index ∉ strictSet
      have residual_eq_full :
          (∑ index : Retained, term index.1) =
            ∑ index, term index := by
        rw [← Finset.sum_subtype
          remaining
          (fun index => by
            simp only [remaining, Finset.mem_filter,
              Finset.mem_univ, true_and])
          term]
        apply Finset.sum_subset
          (Finset.subset_univ remaining)
        intro index _ index_not_remaining
        have index_strict : index ∈ strictSet := by
          simpa only [remaining, Finset.mem_filter,
            Finset.mem_univ, true_and, not_not] using
              index_not_remaining
        change mass index * charge index.1 = 0
        rw [mass_zero_of_strict index index_strict, zero_mul]
      change (∑ index : Retained, term index.1) = 1
      rw [residual_eq_full]
      exact charge_eq_one
  let equiv :
      (state.deleteStrict score).ActiveIndex ≃ Retained :=
    state.deleteStrictActiveEquivRetained score
  have reindexed :=
    HasNormalizedPositiveChargedCirculation.reindex
      (fun index : Retained => column index.1.1)
      (fun index : Retained => charge index.1.1)
      retainedCirculation equiv
  have equiv_value
      (index : (state.deleteStrict score).ActiveIndex) :
      (equiv index).1.1 = index.1 := by
    rfl
  have column_eq :
      (fun index => column (equiv index).1.1) =
        (fun index : (state.deleteStrict score).ActiveIndex =>
          column index.1) := by
    funext index destination
    rw [equiv_value]
  have charge_eq :
      (fun index => charge (equiv index).1.1) =
        (fun index : (state.deleteStrict score).ActiveIndex =>
          charge index.1) := by
    funext index
    rw [equiv_value]
  rw [column_eq, charge_eq] at reindexed
  exact reindexed

/-- Complementarity transports the endpoint circulation through deletion of
all strictly positive leading pairings. -/
theorem
    ActiveAnalyticPotentialJet.deleteStrict_hasEndpointCirculation
    [Fintype S] [Fintype I] [DecidableEq I]
    {state : FiniteDeflationState I}
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {anchor : S}
    (next : ActiveAnalyticPotentialJet
      state column charge anchor)
    (analytic_column :
      ∀ index destination,
        AnalyticAt ℝ (fun t => column t index destination) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ destination, column t index destination = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (activeOccupationColumn state column 0)
        (activeOccupationCharge state charge 0)) :
    HasNormalizedPositiveChargedCirculation
      (activeOccupationColumn
        (state.deleteStrict next.leadingPairing) column 0)
      (activeOccupationCharge
        (state.deleteStrict next.leadingPairing) charge 0) := by
  let strictSet : Finset state.ActiveIndex :=
    state.strictActiveSet next.leadingPairing
  let Retained :=
    {index : state.ActiveIndex // index ∉ strictSet}
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one, complementary⟩ :=
    next.gaugeFixedJet.exists_leading_complementary_mass
      (analytic_activeOccupationColumn state column analytic_column)
      (analytic_activeOccupationCharge state charge analytic_charge)
      (eventually_sum_activeOccupationColumn_eq_zero
        state column column_zero_sum)
      circulation
  have mass_zero_of_strict :
      ∀ index, index ∈ strictSet → mass index = 0 := by
    intro index index_strict
    apply le_antisymm
    · exact le_of_not_gt fun mass_pos => by
        have pairing_zero := complementary index mass_pos
        have pairing_pos : 0 < next.leadingPairing index := by
          exact
            (state.mem_strictActiveSet_iff
              next.leadingPairing index).mp index_strict
        exact (ne_of_gt pairing_pos) pairing_zero
    · exact mass_nonneg index
  let retainedMass : Retained → ℝ :=
    fun index => mass index.1
  have retainedCirculation :
      HasNormalizedPositiveChargedCirculation
        (fun index : Retained =>
          activeOccupationColumn state column 0 index.1)
        (fun index : Retained =>
          activeOccupationCharge state charge 0 index.1) := by
    refine ⟨retainedMass, ?_, ?_, ?_⟩
    · intro index
      exact mass_nonneg index.1
    · intro destination
      let term : state.ActiveIndex → ℝ :=
        fun index =>
          mass index *
            activeOccupationColumn state column
              0 index destination
      let remaining : Finset state.ActiveIndex :=
        Finset.univ.filter fun index => index ∉ strictSet
      have residual_eq_full :
          (∑ index : Retained, term index.1) =
            ∑ index, term index := by
        rw [← Finset.sum_subtype
          remaining
          (fun index => by
            simp only [remaining, Finset.mem_filter,
              Finset.mem_univ, true_and])
          term]
        apply Finset.sum_subset
          (Finset.subset_univ remaining)
        intro index _ index_not_remaining
        have index_strict : index ∈ strictSet := by
          simpa only [remaining, Finset.mem_filter,
            Finset.mem_univ, true_and, not_not] using
              index_not_remaining
        change
          mass index *
              activeOccupationColumn state column
                0 index destination =
            0
        rw [mass_zero_of_strict index index_strict, zero_mul]
      change
        (∑ index : Retained, term index.1) = 0
      rw [residual_eq_full]
      exact balance destination
    · let term : state.ActiveIndex → ℝ :=
        fun index =>
          mass index *
            activeOccupationCharge state charge 0 index
      let remaining : Finset state.ActiveIndex :=
        Finset.univ.filter fun index => index ∉ strictSet
      have residual_eq_full :
          (∑ index : Retained, term index.1) =
            ∑ index, term index := by
        rw [← Finset.sum_subtype
          remaining
          (fun index => by
            simp only [remaining, Finset.mem_filter,
              Finset.mem_univ, true_and])
          term]
        apply Finset.sum_subset
          (Finset.subset_univ remaining)
        intro index _ index_not_remaining
        have index_strict : index ∈ strictSet := by
          simpa only [remaining, Finset.mem_filter,
            Finset.mem_univ, true_and, not_not] using
              index_not_remaining
        change
          mass index *
              activeOccupationCharge state charge 0 index =
            0
        rw [mass_zero_of_strict index index_strict, zero_mul]
      change
        (∑ index : Retained, term index.1) = 1
      rw [residual_eq_full]
      exact charge_eq_one
  let equiv :
      (state.deleteStrict next.leadingPairing).ActiveIndex ≃
        Retained :=
    state.deleteStrictActiveEquivRetained
      next.leadingPairing
  have reindexed :=
    HasNormalizedPositiveChargedCirculation.reindex
      (fun index : Retained =>
        activeOccupationColumn state column 0 index.1)
      (fun index : Retained =>
        activeOccupationCharge state charge 0 index.1)
      retainedCirculation equiv
  have equiv_value
      (index :
        (state.deleteStrict next.leadingPairing).ActiveIndex) :
      (equiv index).1.1 = index.1 := by
    rfl
  have column_eq :
      (fun index =>
        activeOccupationColumn state column 0 (equiv index).1) =
        activeOccupationColumn
          (state.deleteStrict next.leadingPairing) column 0 := by
    funext index destination
    change
      column 0 (equiv index).1.1 destination =
        column 0 index.1 destination
    rw [equiv_value]
  have charge_eq :
      (fun index =>
        activeOccupationCharge state charge 0 (equiv index).1) =
        activeOccupationCharge
          (state.deleteStrict next.leadingPairing) charge 0 := by
    funext index
    change charge 0 (equiv index).1.1 = charge 0 index.1
    rw [equiv_value]
  rw [column_eq, charge_eq] at reindexed
  exact reindexed

/-- Finite trace of strict analytic deflations from an initial active node
to a terminal active node. -/
inductive AnalyticOccupationDeflationTrace
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : ℝ → I → S → ℝ)
    (charge : ℝ → I → ℝ)
    (anchor : S) :
    FiniteDeflationState I → FiniteDeflationState I → Type _
  | refl (state) :
      AnalyticOccupationDeflationTrace
        column charge anchor state state
  | strict
      {parent terminal : FiniteDeflationState I}
      (next : ActiveAnalyticPotentialJet
        parent column charge anchor)
      (strict_nonempty :
        ∃ index, 0 < next.leadingPairing index)
      (tail :
        AnalyticOccupationDeflationTrace column charge anchor
          (parent.deleteStrict next.leadingPairing) terminal) :
      AnalyticOccupationDeflationTrace
        column charge anchor parent terminal

namespace AnalyticOccupationDeflationTrace

/-- Every terminal active set recorded by a deflation trace is contained in
the initial active set. -/
theorem terminal_active_subset
    [Fintype S] [Fintype I] [DecidableEq I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {anchor : S}
    {initial terminal : FiniteDeflationState I}
    (trace :
      AnalyticOccupationDeflationTrace
        column charge anchor initial terminal) :
    terminal.active ⊆ initial.active := by
  induction trace with
  | refl state =>
      exact Finset.Subset.rfl
  | strict next strict_nonempty tail ih =>
      exact ih.trans Finset.sdiff_subset

end AnalyticOccupationDeflationTrace

/-- Honest terminal certificate of analytic finite deflation.  Either an
analytic charged circulation occurs, or a potential jet has zero leading
pairing on every remaining active index. -/
inductive AnalyticOccupationTerminalCertificate
    [Fintype S] [Fintype I] [DecidableEq I]
    (state : FiniteDeflationState I)
    (column : ℝ → I → S → ℝ)
    (charge : ℝ → I → ℝ)
    (anchor : S) : Type _
  | analyticCirculation
      (witness :
        AnalyticPositiveChargedCirculation
          (activeOccupationColumn state column)
          (activeOccupationCharge state charge))
  | zeroPairing
      (next :
        ActiveAnalyticPotentialJet state column charge anchor)
      (pairing_zero :
        ∀ index, next.leadingPairing index = 0)

/-- Terminal data returned by well-founded analytic deflation.  The endpoint
circulation invariant is retained explicitly at the terminal node. -/
structure AnalyticOccupationDeflationOutcome
    [Fintype S] [Fintype I] [DecidableEq I]
    (initial : FiniteDeflationState I)
    (column : ℝ → I → S → ℝ)
    (charge : ℝ → I → ℝ)
    (anchor : S) where
  terminal : FiniteDeflationState I
  trace :
    AnalyticOccupationDeflationTrace
      column charge anchor initial terminal
  endpointCirculation :
    HasNormalizedPositiveChargedCirculation
      (activeOccupationColumn terminal column 0)
      (activeOccupationCharge terminal charge 0)
  certificate :
    AnalyticOccupationTerminalCertificate
      terminal column charge anchor

/-- **Well-founded analytic finite deflation.**

Starting at any active node carrying an endpoint normalized positive
circulation, repeatedly run the analytic charged-flow alternative.  An
analytic-circulation branch terminates immediately.  A potential branch
terminates when every leading pairing is zero; otherwise complementarity
preserves the endpoint circulation on a strictly smaller active set and
well-founded recursion continues.

The returned trace is finite by the proper-subset rank and records every
strict analytic deletion. -/
theorem exists_analyticOccupationDeflationOutcome
    [Fintype S] [Fintype I] [DecidableEq I]
    (initial : FiniteDeflationState I)
    (column : ℝ → I → S → ℝ)
    (charge : ℝ → I → ℝ)
    (analytic_column :
      ∀ index destination,
        AnalyticAt ℝ (fun t => column t index destination) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ destination, column t index destination = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (activeOccupationColumn initial column 0)
        (activeOccupationCharge initial charge 0))
    (anchor : S) :
    Nonempty
      (AnalyticOccupationDeflationOutcome
        initial column charge anchor) := by
  let motive : FiniteDeflationState I → Prop :=
    fun state =>
      HasNormalizedPositiveChargedCirculation
          (activeOccupationColumn state column 0)
          (activeOccupationCharge state charge 0) →
        Nonempty
          (AnalyticOccupationDeflationOutcome
            state column charge anchor)
  have solve : ∀ state, motive state := by
    apply FiniteDeflationState.deflation_induction
    intro state recurse stateCirculation
    rcases
        activePositiveChargedCirculation_xor_nextPotentialJet
          state column charge analytic_column analytic_charge
          column_zero_sum stateCirculation anchor with
      analyticCirculation | potentialJet
    · obtain ⟨analyticWitness⟩ := analyticCirculation.1
      exact ⟨{
        terminal := state
        trace := AnalyticOccupationDeflationTrace.refl state
        endpointCirculation := stateCirculation
        certificate :=
          AnalyticOccupationTerminalCertificate.analyticCirculation
            analyticWitness
      }⟩
    · obtain ⟨next⟩ := potentialJet.1
      have pairing_nonneg :
          ∀ index, 0 ≤ next.leadingPairing index :=
        next.leadingPairing_nonneg
          analytic_column analytic_charge column_zero_sum
          stateCirculation
      by_cases strict_nonempty :
          ∃ index, 0 < next.leadingPairing index
      · let child :=
          state.deleteStrict next.leadingPairing
        have child_deflates : child.Deflates state :=
          state.deleteStrict_deflates
            next.leadingPairing strict_nonempty
        have childCirculation :
            HasNormalizedPositiveChargedCirculation
              (activeOccupationColumn child column 0)
              (activeOccupationCharge child charge 0) :=
          next.deleteStrict_hasEndpointCirculation
            analytic_column analytic_charge column_zero_sum
            stateCirculation
        obtain ⟨tailOutcome⟩ :=
          recurse child child_deflates childCirculation
        exact ⟨{
          terminal := tailOutcome.terminal
          trace := AnalyticOccupationDeflationTrace.strict
            next strict_nonempty tailOutcome.trace
          endpointCirculation :=
            tailOutcome.endpointCirculation
          certificate := tailOutcome.certificate
        }⟩
      · have pairing_zero :
            ∀ index, next.leadingPairing index = 0 := by
          intro index
          apply le_antisymm
          · exact le_of_not_gt fun pairing_pos =>
              strict_nonempty ⟨index, pairing_pos⟩
          · exact pairing_nonneg index
        exact ⟨{
          terminal := state
          trace := AnalyticOccupationDeflationTrace.refl state
          endpointCirculation := stateCirculation
          certificate :=
            AnalyticOccupationTerminalCertificate.zeroPairing
              next pairing_zero
        }⟩
  exact solve initial circulation

end Probability
end Math
