/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumSpine
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMaxDebtFlow

/-!
# Debt-transfer regression on the minimum semantic spine

The minimum terminal-semantic inverse limit is a genuine state-matched
chronology, but it conserves every best-response-debt coordinate exactly.
Consequently its consecutive states carry no positive debt-transfer edge.

This separates two constructions which cannot be identified without a new
return argument.  Best-response resets do produce positive opposite-face
debt transfer, but their cluster points are only known to lie in the full
terminal-semantic carrier.  The minimum spine stays in the minimum-debt
fiber, where chronological debt transfer is identically zero.  Thus the
reset/incidence flow cannot be made legal merely by reading its transfer
matrix from consecutive minimum-spine states.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Debt change between consecutive states of a displayed semantic
chronology.  The source label is retained so that this has the same shape as
a reset-transfer matrix; the actual inter-state debt change depends only on
the target coordinate. -/
def quittingSemanticChronologicalDebtTransfer
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (time : ℕ) (_source target : ι) : ℝ :=
  quittingTerminalSemanticDebtChange (pair time) (pair (time + 1)) target

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinatewise conservation kills every chronological debt-transfer
entry. -/
theorem quittingSemanticChronologicalDebtTransfer_eq_zero_of_conserved
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (hconserved : ∀ time who,
      quittingTerminalSemanticDebt (pair time) who =
        quittingTerminalSemanticDebt (pair (time + 1)) who)
    (time : ℕ) (source target : ι) :
    quittingSemanticChronologicalDebtTransfer pair time source target = 0 := by
  unfold quittingSemanticChronologicalDebtTransfer
  unfold quittingTerminalSemanticDebtChange
  rw [← hconserved time target]
  exact sub_self _

/-- On a coordinate-conserving chronology, the positive-transfer support
between consecutive states is empty for every possible reset owner. -/
theorem quittingTerminalSemanticPositiveTransferSupport_consecutive_eq_empty
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (hconserved : ∀ time who,
      quittingTerminalSemanticDebt (pair time) who =
        quittingTerminalSemanticDebt (pair (time + 1)) who)
    (time : ℕ) (who : ι) :
    quittingTerminalSemanticPositiveTransferSupport
        (pair time) (pair (time + 1)) who = ∅ := by
  ext target
  constructor
  · intro htarget
    have hpositive := (Finset.mem_filter.mp htarget).2
    unfold quittingTerminalSemanticDebtChange at hpositive
    rw [← hconserved time target, sub_self] at hpositive
    exact (lt_irrefl 0 hpositive).elim
  · intro htarget
    simp at htarget

omit [DecidableEq ι] in
/-- **No positive matched flow lives on the exact minimum spine.**

If the transfer matrix is the actual debt change between consecutive
semantic states and those states conserve every debt coordinate, a matched
flow cannot cross any positive-length cutoff, regardless of the incidence
matrix.  A positive flow edge would require a positive transfer entry, while
all such entries are zero.

In particular, the coordinate-conservation conclusion of
`exists_infinite_minimumTerminalSemanticSpine` rules out using consecutive
minimum-spine debt changes as the missing provenance for the abstract
max-debt matched-flow packet. -/
theorem not_nonempty_maxDebtMatchedFlow_chronological_of_conserved
    [Nonempty ι]
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (incidence : ℕ → ι → ι → ℝ)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (hconserved : ∀ time who,
      quittingTerminalSemanticDebt (pair time) who =
        quittingTerminalSemanticDebt (pair (time + 1)) who) :
    ¬ Nonempty (QuittingFiniteMaxDebtMatchedFlow
        (fun time who => quittingTerminalSemanticDebt (pair time) who)
        (quittingSemanticChronologicalDebtTransfer pair)
        incidence cutoff) := by
  rintro ⟨packet⟩
  have hsum := packet.weight_sum 0 (Nat.zero_le cutoff)
  have hpositive : ∃ source, 0 < packet.weight 0 source := by
    by_contra hnot
    push Not at hnot
    have hzero : ∀ source, packet.weight 0 source = 0 := by
      intro source
      exact le_antisymm (hnot source) (packet.weight_nonneg 0 source)
    have hsumZero : (∑ source, packet.weight 0 source) = 0 := by
      simp [hzero]
    linarith
  obtain ⟨source, hsource⟩ := hpositive
  obtain ⟨target, _hflow, _hnext, htransfer, _hincidence⟩ :=
    packet.exists_positive_matched_successor 0 hcutoff source hsource
  rw [quittingSemanticChronologicalDebtTransfer_eq_zero_of_conserved
    pair hconserved 0 source target] at htransfer
  exact lt_irrefl 0 htransfer

end GameTheory
