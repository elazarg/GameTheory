/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.StrictSetBudget

/-!
# Zero-drift restriction after strict player-neutral deflation

The complete strict set selected by a leading potential has uniformly
bounded expected occupation.  The residual operational family is therefore
the subtype of columns outside that set.  Every residual column has exactly
zero leading drift, and the residual finite type has strictly smaller
cardinality.

This file records the well-founded finite descent only.  It does not identify
the residual subtype with a legal recurrent child or construct its public
entry interface.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace PlayerNeutralStrictLeadingDrift

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}

/-- Operational columns remaining after deleting every column with positive
leading drift. -/
abbrev ZeroDriftIndex
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :=
  {index : germ.PlayerNeutralOccupationIndex who //
    index ∉ C.strictIndexSet}

noncomputable instance instFintypeZeroDriftIndex
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    Fintype C.ZeroDriftIndex := by
  classical
  exact Fintype.ofFinite _

/-- Kernel inherited by a residual zero-drift column. -/
def zeroDriftKernel
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (index : C.ZeroDriftIndex) : PMF G.State :=
  germ.playerNeutralOccupationKernel who index.1

/-- Source inherited by a residual zero-drift column. -/
def zeroDriftSource
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (index : C.ZeroDriftIndex) : G.State :=
  germ.playerNeutralOccupationSource who index.1

/-- Charge inherited by a residual zero-drift column. -/
def zeroDriftCharge
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (index : C.ZeroDriftIndex) : ℝ :=
  germ.playerNeutralOccupationCharge B who index.1

/-- Every retained column is complementary to the normalized leading
potential. -/
theorem zeroDriftIndex_normalizedDrift_eq_zero
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (index : C.ZeroDriftIndex) :
    expect (C.zeroDriftKernel index) C.potential -
        C.potential (C.zeroDriftSource index) =
      0 := by
  exact C.normalizedDrift_eq_zero_of_not_mem_strictIndexSet index.2

/-- Deleting the nonempty strict set strictly decreases the cardinality of
the finite operational family. -/
theorem card_zeroDriftIndex_lt
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    Fintype.card C.ZeroDriftIndex <
      Fintype.card (germ.PlayerNeutralOccupationIndex who) := by
  classical
  let strictPredicate :
      germ.PlayerNeutralOccupationIndex who → Prop :=
    fun index => index ∈ C.strictIndexSet
  letI : DecidablePred strictPredicate := Classical.decPred _
  have strict_nonempty : Nonempty {index // strictPredicate index} :=
    ⟨⟨C.index, C.index_mem_strictIndexSet⟩⟩
  have strict_card_pos :
      0 < Fintype.card {index // strictPredicate index} :=
    Fintype.card_pos_iff.mpr strict_nonempty
  have strict_card_le :
      Fintype.card {index // strictPredicate index} ≤
        Fintype.card (germ.PlayerNeutralOccupationIndex who) :=
    Fintype.card_subtype_le _
  change
    Fintype.card {index // ¬strictPredicate index} <
      Fintype.card (germ.PlayerNeutralOccupationIndex who)
  rw [Fintype.card_subtype_compl]
  omega

/-- Complementarity makes the supplied endpoint circulation live entirely
on the residual zero-drift family.  Hence strict-set deflation preserves the
normalized positive charge while strictly reducing the finite index type. -/
theorem exists_zeroDrift_normalizedPositiveChargedCirculation
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn C.zeroDriftKernel C.zeroDriftSource)
      C.zeroDriftCharge := by
  classical
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one, complementary⟩ :=
    germ.exists_playerNeutralGaugeFixedPotentialJet_complementaryMass
      B who jet circulation
  let strictPredicate :
      germ.PlayerNeutralOccupationIndex who → Prop :=
    fun index => index ∈ C.strictIndexSet
  letI : DecidablePred strictPredicate := Classical.decPred _
  have mass_zero_of_strict :
      ∀ index, strictPredicate index → mass index = 0 := by
    intro index index_strict
    apply le_antisymm
    · exact le_of_not_gt fun mass_pos => by
        have pairing_zero := complementary index mass_pos
        have drift_zero : C.normalizedDrift index = 0 := by
          rw [normalizedDrift, C.drift_eq_pairing_div index,
            pairing_zero, zero_div]
        exact
          (ne_of_gt
            ((C.mem_strictIndexSet_iff index).mp index_strict))
            drift_zero
    · exact mass_nonneg index
  let restrictedMass : C.ZeroDriftIndex → ℝ :=
    fun index => mass index.1
  refine ⟨restrictedMass, ?_, ?_, ?_⟩
  · intro index
    exact mass_nonneg index.1
  · intro destination
    let term :
        germ.PlayerNeutralOccupationIndex who → ℝ :=
      fun index =>
        mass index *
          actualOccupationColumn
            (germ.playerNeutralOccupationKernel who)
            (germ.playerNeutralOccupationSource who)
            index destination
    let remaining :
        Finset (germ.PlayerNeutralOccupationIndex who) :=
      Finset.univ.filter fun index => ¬strictPredicate index
    have residual_eq_full :
        (∑ index : C.ZeroDriftIndex, term index.1) =
        ∑ index, term index := by
      rw [← Finset.sum_subtype
        remaining
        (fun index => by
          simp only [remaining, Finset.mem_filter,
            Finset.mem_univ, true_and, strictPredicate])
        term]
      apply Finset.sum_subset (Finset.subset_univ remaining)
      intro index _ index_not_mem
      have index_strict : strictPredicate index := by
        simpa only [remaining, Finset.mem_filter,
          Finset.mem_univ, true_and, not_not] using index_not_mem
      change
        mass index *
            actualOccupationColumn
              (germ.playerNeutralOccupationKernel who)
              (germ.playerNeutralOccupationSource who)
              index destination =
          0
      rw [mass_zero_of_strict index index_strict, zero_mul]
    change
      (∑ index : C.ZeroDriftIndex,
        restrictedMass index *
          actualOccupationColumn
            C.zeroDriftKernel C.zeroDriftSource
            index destination) = 0
    rw [show
        (∑ index : C.ZeroDriftIndex,
          restrictedMass index *
            actualOccupationColumn
              C.zeroDriftKernel C.zeroDriftSource
              index destination) =
          ∑ index : C.ZeroDriftIndex,
            term index.1 by rfl]
    rw [residual_eq_full]
    exact balance destination
  · let term :
        germ.PlayerNeutralOccupationIndex who → ℝ :=
      fun index =>
        mass index *
          germ.playerNeutralOccupationCharge B who index
    let remaining :
        Finset (germ.PlayerNeutralOccupationIndex who) :=
      Finset.univ.filter fun index => ¬strictPredicate index
    have residual_eq_full :
        (∑ index : C.ZeroDriftIndex, term index.1) =
        ∑ index, term index := by
      rw [← Finset.sum_subtype
        remaining
        (fun index => by
          simp only [remaining, Finset.mem_filter,
            Finset.mem_univ, true_and, strictPredicate])
        term]
      apply Finset.sum_subset (Finset.subset_univ remaining)
      intro index _ index_not_mem
      have index_strict : strictPredicate index := by
        simpa only [remaining, Finset.mem_filter,
          Finset.mem_univ, true_and, not_not] using index_not_mem
      change
        mass index *
            germ.playerNeutralOccupationCharge B who index =
          0
      rw [mass_zero_of_strict index index_strict, zero_mul]
    change
      (∑ index : C.ZeroDriftIndex,
        restrictedMass index * C.zeroDriftCharge index) = 1
    rw [show
        (∑ index : C.ZeroDriftIndex,
          restrictedMass index * C.zeroDriftCharge index) =
          ∑ index : C.ZeroDriftIndex,
            term index.1 by rfl]
    rw [residual_eq_full]
    exact charge_eq_one

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
