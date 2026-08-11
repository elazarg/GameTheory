/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.ChargedOccupationAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMinimumTangent

/-!
# Flat stopping-law tangent circulation or active-set co-decrease

Zero-excess normalized stopping-law reset directions have coordinate sum
zero.  The finite charged-occupation alternative can therefore be applied to
the full signed debt directions, rather than merely to selected positive
recipient labels.

The dual potential can be shifted by its minimum to become nonnegative,
because constants annihilate every flat column.  If there is no entry into an
inactive debt coordinate, a potential-maximal active debtor cannot have only
nonnegative off-diagonal changes: its charged potential drift would then be
nonpositive.  Thus the dual branch exposes a co-realized decrease of another
active debt coordinate.

This is a finite tangent alternative.  Its circulation branch still requires
an integration theorem before it becomes a chronology or a semantic-state
cycle.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι Move : Type} [Fintype ι] [Fintype Move]

/-- On flat columns, the charged-occupation potential may be chosen
coordinatewise nonnegative.  The primal branch is an exact nonnegative
charged circulation of the full signed tangent vectors. -/
theorem flatDebtTangent_chargedCirculation_xor_nonnegativePotential
    [Nonempty ι]
    (column : Move → ι → ℝ) (charge : Move → ℝ)
    (hflat : ∀ move, ∑ who, column move who = 0) :
    Xor
      (HasNormalizedPositiveChargedCirculation column charge)
      (∃ potential : ι → ℝ,
        (∀ who, 0 ≤ potential who) ∧
        IsChargedOccupationPotential column charge potential) := by
  let minimum (potential : ι → ℝ) : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty potential
  have hshift : ∀ potential : ι → ℝ,
      IsChargedOccupationPotential column charge potential →
      ∃ shifted : ι → ℝ,
        (∀ who, 0 ≤ shifted who) ∧
        IsChargedOccupationPotential column charge shifted := by
    intro potential hpotential
    let shifted : ι → ℝ := fun who ↦ potential who - minimum potential
    refine ⟨shifted, ?_, ?_⟩
    · intro who
      dsimp only [shifted, minimum]
      exact sub_nonneg.mpr
        (Finset.inf'_le potential (Finset.mem_univ who))
    · intro move
      have hdrift := hpotential move
      have hsum : (∑ who, shifted who * column move who) =
          ∑ who, potential who * column move who := by
        dsimp only [shifted]
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hflat move, mul_zero,
          sub_zero]
      rw [hsum]
      exact hdrift
  have halt := normalizedPositiveChargedCirculation_xor_potential column charge
  rw [xor_def] at halt ⊢
  rcases halt with
      ⟨hcirculation, hnotPotential⟩ |
      ⟨hpotential, hnotCirculation⟩
  · refine Or.inl ⟨hcirculation, ?_⟩
    rintro ⟨potential, _hnonneg, hpotential⟩
    exact hnotPotential ⟨potential, hpotential⟩
  · obtain ⟨potential, hpotential⟩ := hpotential
    obtain ⟨shifted, hshiftedNonneg, hshifted⟩ :=
      hshift potential hpotential
    exact Or.inr
      ⟨⟨shifted, hshiftedNonneg, hshifted⟩, hnotCirculation⟩

/-- **Dual active-set consumer.**

Let one flat tangent carry strictly positive charge and satisfy the dual
potential inequality.  If its mover maximizes the potential on the active
debt support and every inactive coordinate has zero tangent, then some other
active coordinate strictly decreases.  Otherwise the positive drift would
be bounded by the maximal potential times the zero column sum. -/
theorem exists_active_coDecrease_of_flat_chargedPotential_at_max
    [DecidableEq ι]
    (active : Finset ι) (column potential : ι → ℝ)
    (mover : ι) (charge : ℝ)
    (hflat : ∑ who, column who = 0)
    (hcharge : 0 < charge)
    (hpotential : charge ≤ ∑ who, potential who * column who)
    (hmax : ∀ who ∈ active, potential who ≤ potential mover)
    (hinactive : ∀ who ∉ active, column who = 0) :
    ∃ other ∈ active.erase mover, column other < 0 := by
  by_contra hnot
  push Not at hnot
  have hterm : ∀ who ∈ (Finset.univ : Finset ι),
      potential who * column who ≤ potential mover * column who := by
    intro who _hwho
    by_cases hwhoActive : who ∈ active
    · by_cases hwhoMover : who = mover
      · subst who
        exact le_rfl
      · have hcolumnNonneg : 0 ≤ column who := by
          exact hnot who (Finset.mem_erase.mpr ⟨hwhoMover, hwhoActive⟩)
        exact mul_le_mul_of_nonneg_right
          (hmax who hwhoActive) hcolumnNonneg
    · rw [hinactive who hwhoActive, mul_zero, mul_zero]
  have hweighted : (∑ who, potential who * column who) ≤
      ∑ who, potential mover * column who :=
    Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, hflat, mul_zero] at hweighted
  linarith

/-! ## Game-facing active-set trichotomy -/

variable [DecidableEq ι]

/-- **Support entry, infinitesimal circulation, or same-column co-decrease.**

Assume a finite family of zero-excess stopping-law debt tangents has been
extracted at one common positive semantic point, one for each positive-debt
coordinate.  The mover loses exactly its positive charge, and a coordinate
which is zero at the base cannot have a negative tangent.

Then exactly the obstruction relevant to the active-set pipeline appears:

* some tangent enters a zero-debt coordinate;
* the full signed tangent columns admit a positive charged balance; or
* a nonnegative separating potential exposes one tangent which decreases
  both its potential-maximal mover and another active coordinate.

The circulation is infinitesimal.  No assertion is made that it integrates
to a literal reset cycle or chronology. -/
theorem stoppingLawFlatTangent_supportEntry_or_chargedCirculation_or_potentialCoDecrease
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    (active : Finset ι) (column : ι → ι → ℝ) (gain : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalSemanticDebtSum base)
    (hactive : ∀ who, who ∈ active ↔
      0 < quittingTerminalSemanticDebt base who)
    (hgain : ∀ mover ∈ active, 0 < gain mover)
    (hmoverLoss : ∀ mover ∈ active,
      column mover mover = -gain mover)
    (hflat : ∀ mover ∈ active, ∑ who, column mover who = 0)
    (hzeroTangent : ∀ mover ∈ active, ∀ who,
      quittingTerminalSemanticDebt base who = 0 →
        0 ≤ column mover who) :
    (∃ mover ∈ active, ∃ recipient,
        quittingTerminalSemanticDebt base recipient = 0 ∧
          0 < column mover recipient) ∨
      HasNormalizedPositiveChargedCirculation
        (fun mover : {who // who ∈ active} ↦ column mover.1)
        (fun mover : {who // who ∈ active} ↦ gain mover.1) ∨
      ∃ potential : ι → ℝ, ∃ mover ∈ active, ∃ other ∈ active.erase mover,
        (∀ who, 0 ≤ potential who) ∧
        (∀ source ∈ active,
          gain source ≤ ∑ who, potential who * column source who) ∧
        (∀ source ∈ active, potential source ≤ potential mover) ∧
        column mover mover = -gain mover ∧
        column mover other < 0 := by
  have hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt base who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hbase
  have hactiveNonempty : active.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hactive
    have hdebtZero : ∀ who, quittingTerminalSemanticDebt base who = 0 := by
      intro who
      apply le_antisymm
      · exact le_of_not_gt (by
          intro hpos
          have := (hactive who).2 hpos
          simp at this)
      · exact hdebtNonneg who
    unfold quittingTerminalSemanticDebtSum at hpositive
    simp only [hdebtZero, Finset.sum_const_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  letI : Nonempty ι := ⟨hactiveNonempty.choose⟩
  by_cases hentry : ∃ mover ∈ active, ∃ recipient,
      quittingTerminalSemanticDebt base recipient = 0 ∧
        0 < column mover recipient
  · exact Or.inl hentry
  · right
    push Not at hentry
    have hinactiveZero : ∀ mover ∈ active, ∀ who ∉ active,
        column mover who = 0 := by
      intro mover hmover who hwho
      have hdebtZero : quittingTerminalSemanticDebt base who = 0 := by
        apply le_antisymm
        · exact le_of_not_gt (fun hpos ↦ hwho ((hactive who).2 hpos))
        · exact hdebtNonneg who
      exact le_antisymm
        (hentry mover hmover who hdebtZero)
        (hzeroTangent mover hmover who hdebtZero)
    have halt := flatDebtTangent_chargedCirculation_xor_nonnegativePotential
      (fun mover : {who // who ∈ active} ↦ column mover.1)
      (fun mover : {who // who ∈ active} ↦ gain mover.1)
      (fun mover ↦ hflat mover.1 mover.2)
    rcases halt with ⟨hcirculation, _hnotPotential⟩ |
        ⟨hpotential, _hnotCirculation⟩
    · exact Or.inl hcirculation
    · right
      obtain ⟨potential, hpotentialNonneg, hpotential⟩ := hpotential
      obtain ⟨mover, hmover, hmoverMax⟩ :=
        Finset.exists_max_image active potential hactiveNonempty
      have hpotentialAll : ∀ source ∈ active,
          gain source ≤ ∑ who, potential who * column source who := by
        intro source hsource
        exact hpotential ⟨source, hsource⟩
      obtain ⟨other, hother, hotherDecrease⟩ :=
        exists_active_coDecrease_of_flat_chargedPotential_at_max
          active (column mover) potential mover (gain mover)
            (hflat mover hmover) (hgain mover hmover)
            (hpotentialAll mover hmover) hmoverMax
            (hinactiveZero mover hmover)
      exact ⟨potential, mover, hmover, other, hother,
        hpotentialNonneg, hpotentialAll, hmoverMax,
        hmoverLoss mover hmover, hotherDecrease⟩

end GameTheory
