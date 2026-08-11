/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPositivePartSplit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauQuantitativePassport

/-!
# Quantitative debt transfer after a best-response reset

Replacing one player along a realizing sequence by asymptotic best responses
resets that player's best-response debt.  Compactness retains a literal
terminal-semantic cluster point of the reset profiles.  At a minimum-total-
debt source, the lost coordinate is transferred to the opposite face of the
player simplex, with an exact account for any excess total debt of the reset
cluster.

This module also records the finite matched-label alternative.  Either some
opponent both receives positive transferred debt and belongs to the support
of a displayed incidence weight, or the positive-transfer support is an
exact finite separator from the incidence support.  No local regrets from
different dates are summed.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coordinate change in best-response debt between two semantic pairs. -/
def quittingTerminalSemanticDebtChange
    (source target : QuittingTerminalSemanticPair ι) (who : ι) : ℝ :=
  quittingTerminalSemanticDebt target who -
    quittingTerminalSemanticDebt source who

omit [Fintype ι] [DecidableEq ι] in
/-- Debt change is continuous in the target semantic pair. -/
theorem continuous_quittingTerminalSemanticDebtChange_right
    (source : QuittingTerminalSemanticPair ι) (who : ι) :
    Continuous (fun target : QuittingTerminalSemanticPair ι =>
      quittingTerminalSemanticDebtChange source target who) := by
  unfold quittingTerminalSemanticDebtChange
  exact (continuous_quittingTerminalSemanticDebt who).sub continuous_const

/-- **Semantic reset cluster with exact transfer account.**

The reset profiles themselves have a cluster in the attainable-semantic
carrier.  The selected debt vanishes at that cluster.  The total debt change
on the opposite face is exactly the selected source debt plus the cluster's
excess total debt.  Minimum provenance therefore gives the quantitative
transfer inequality `(Y)` from Session XIX. -/
theorem exists_terminalSemanticResetCluster_quantitative_transfer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (who : ι)
    (strategies : ℕ → (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hprofiles : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (𝓝 source))
    (hpayoff : Tendsto (fun n => quittingTerminalPayoff reward
      (Function.update (profiles n) who (strategies n)) who)
      atTop (𝓝 (source.2 who))) :
    ∃ (cluster : QuittingTerminalSemanticPair ι) (subseq : ℕ → ℕ),
      cluster ∈ quittingTerminalSemanticCarrier reward ∧
      StrictMono subseq ∧
      Tendsto (fun rank => quittingTerminalSemanticPair reward
          (Function.update (profiles (subseq rank)) who
            (strategies (subseq rank))))
        atTop (𝓝 cluster) ∧
      quittingTerminalSemanticDebt cluster who = 0 ∧
      (∑ other ∈ (Finset.univ.erase who),
          quittingTerminalSemanticDebtChange source cluster other) =
        (quittingTerminalSemanticDebtSum cluster -
            quittingTerminalSemanticDebtSum source) +
          quittingTerminalSemanticDebt source who ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ other ∈ (Finset.univ.erase who),
          quittingTerminalSemanticDebtChange source cluster other := by
  let resetPair : ℕ → QuittingTerminalSemanticPair ι := fun n =>
    quittingTerminalSemanticPair reward
      (Function.update (profiles n) who (strategies n))
  have hresetMem : ∀ n,
      resetPair n ∈ quittingTerminalSemanticCarrier reward := by
    intro n
    apply subset_closure
    exact ⟨Function.update (profiles n) who (strategies n), rfl⟩
  obtain ⟨cluster, hcluster, subseq, hsubseq, hclusterLimit⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward hM hreward).tendsto_subseq
      hresetMem
  have hresetZero : Tendsto
      (fun n => quittingTerminalSemanticDebt (resetPair n) who)
      atTop (𝓝 0) := by
    exact tendsto_terminalSemanticDebt_update_self reward profiles who
      strategies source hprofiles hpayoff
  have hresetZeroSubseq : Tendsto
      (fun rank => quittingTerminalSemanticDebt
        (resetPair (subseq rank)) who) atTop (𝓝 0) :=
    hresetZero.comp hsubseq.tendsto_atTop
  have hresetCluster : Tendsto
      (fun rank => quittingTerminalSemanticDebt
        (resetPair (subseq rank)) who)
      atTop (𝓝 (quittingTerminalSemanticDebt cluster who)) :=
    (continuous_quittingTerminalSemanticDebt who).tendsto cluster |>.comp
      hclusterLimit
  have hwhoZero : quittingTerminalSemanticDebt cluster who = 0 :=
    tendsto_nhds_unique hresetCluster hresetZeroSubseq
  have hidentity :
      (∑ other ∈ (Finset.univ.erase who),
          quittingTerminalSemanticDebtChange source cluster other) =
        (quittingTerminalSemanticDebtSum cluster -
            quittingTerminalSemanticDebtSum source) +
          quittingTerminalSemanticDebt source who := by
    unfold quittingTerminalSemanticDebtChange
    rw [Finset.sum_sub_distrib]
    have hclusterSum :
        (∑ other ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebt cluster other) =
          quittingTerminalSemanticDebtSum cluster := by
      have hsum := Finset.sum_erase_add Finset.univ
        (fun other => quittingTerminalSemanticDebt cluster other)
        (Finset.mem_univ who)
      change (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt cluster other) +
          quittingTerminalSemanticDebt cluster who =
        quittingTerminalSemanticDebtSum cluster at hsum
      rw [hwhoZero, add_zero] at hsum
      exact hsum
    have hsourceSum :
        (∑ other ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebt source other) =
          quittingTerminalSemanticDebtSum source -
            quittingTerminalSemanticDebt source who := by
      have hsum := Finset.sum_erase_add Finset.univ
        (fun other => quittingTerminalSemanticDebt source other)
        (Finset.mem_univ who)
      change (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt source other) +
          quittingTerminalSemanticDebt source who =
        quittingTerminalSemanticDebtSum source at hsum
      linarith
    rw [hclusterSum, hsourceSum]
    ring
  have htransfer : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebtChange source cluster other := by
    rw [hidentity]
    have hmin := hminimum cluster hcluster
    linarith
  refine ⟨cluster, subseq, hcluster, hsubseq, ?_, hwhoZero,
    hidentity, htransfer⟩
  change Tendsto (resetPair ∘ subseq) atTop (𝓝 cluster)
  exact hclusterLimit

/-- At least one opponent receives the average share of an aggregate debt
transfer.  The denominator is the actual number of opponents, so no ambient
player-cardinality overestimate is hidden. -/
theorem exists_opponent_average_le_debtChange
    (source target : QuittingTerminalSemanticPair ι) (who : ι)
    (hpositive : 0 < quittingTerminalSemanticDebt source who)
    (htransfer : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebtChange source target other) :
    ∃ other ∈ (Finset.univ.erase who),
      quittingTerminalSemanticDebt source who /
          ((Finset.univ.erase who).card : ℝ) ≤
        quittingTerminalSemanticDebtChange source target other := by
  let opponents : Finset ι := Finset.univ.erase who
  have hopponentsNonempty : opponents.Nonempty := by
    by_contra hempty
    have hsumZero : (∑ other ∈ opponents,
        quittingTerminalSemanticDebtChange source target other) = 0 := by
      simp only [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty]
    rw [show Finset.univ.erase who = opponents by rfl, hsumZero] at htransfer
    linarith
  by_contra hnot
  push Not at hnot
  have hstrict : ∀ other ∈ opponents,
      quittingTerminalSemanticDebtChange source target other <
        quittingTerminalSemanticDebt source who / (opponents.card : ℝ) := by
    intro other hother
    exact hnot other hother
  have hsumStrict := Finset.sum_lt_sum_of_nonempty hopponentsNonempty
    (fun other hother => hstrict other hother)
  have hcardPositive : 0 < (opponents.card : ℝ) := by
    exact_mod_cast hopponentsNonempty.card_pos
  have hconstant :
      (∑ _other ∈ opponents,
          quittingTerminalSemanticDebt source who / (opponents.card : ℝ)) =
        quittingTerminalSemanticDebt source who := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [hconstant] at hsumStrict
  have htransfer' : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ opponents,
        quittingTerminalSemanticDebtChange source target other := by
    simpa only [opponents] using htransfer
  linarith

/-- Positive support of the debt-transfer vector on the opponent face. -/
def quittingTerminalSemanticPositiveTransferSupport
    (source target : QuittingTerminalSemanticPair ι) (who : ι) : Finset ι :=
  (Finset.univ.erase who).filter fun other =>
    0 < quittingTerminalSemanticDebtChange source target other

/-- Positive support of a nonnegative incidence weight, with the resetting
player removed. -/
def quittingTerminalOpponentIncidenceSupport
    (who : ι) (incidence : ι → ℝ) : Finset ι :=
  (Finset.univ.erase who).filter fun other => 0 < incidence other

/-- Total mass of finite terminal coalitions in which a displayed opponent
of `who` participates.  A coalition may fund several opponents; only support,
not an additive allocation, is used below. -/
def quittingTerminalOpponentIncidenceMass
    (who other : ι) (mass : QuittingTerminalOutcome ι → ℝ) : ℝ :=
  ∑ terminal ∈ Finset.univ.filter
      (fun terminal => other ∈ terminal.val ∧ other ≠ who),
    mass (some terminal)

/-- Positive opponent-containing absorption supplies at least one concrete
opponent label with positive incidence in the same terminal law. -/
theorem exists_positive_opponentIncidenceMass
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hpositive : 0 < quittingTerminalOpponentContainingMass who mass) :
    ∃ other, other ≠ who ∧
      0 < quittingTerminalOpponentIncidenceMass who other mass := by
  have htermNonneg : ∀ terminal ∈
      Finset.univ.filter (fun terminal : {S : Finset ι // S.Nonempty} =>
        terminal.val ≠ {who}),
      0 ≤ mass (some terminal) := by
    intro terminal _
    exact hmass.1 (some terminal)
  obtain ⟨terminal, hterminalFilter, hterminalMass⟩ :=
    (Finset.sum_pos_iff_of_nonneg htermNonneg).mp hpositive
  have hterminalNe : terminal.val ≠ {who} :=
    (Finset.mem_filter.mp hterminalFilter).2
  have hexistsOther : ∃ other ∈ terminal.val, other ≠ who := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ other ∈ terminal.val, other = who := by
      intro other hother
      exact hnot other hother
    obtain ⟨member, hmember⟩ := terminal.property
    have hmemberEq : member = who := hall member hmember
    have hwhoMem : who ∈ terminal.val := hmemberEq ▸ hmember
    exact hterminalNe
      (Finset.eq_singleton_iff_unique_mem.mpr ⟨hwhoMem, hall⟩)
  obtain ⟨other, hotherMem, hotherNe⟩ := hexistsOther
  refine ⟨other, hotherNe, ?_⟩
  have hterminalIncidence : terminal ∈ Finset.univ.filter
      (fun candidate : {S : Finset ι // S.Nonempty} =>
        other ∈ candidate.val ∧ other ≠ who) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ terminal, hotherMem, hotherNe⟩
  have hle : mass (some terminal) ≤
      quittingTerminalOpponentIncidenceMass who other mass := by
    unfold quittingTerminalOpponentIncidenceMass
    exact Finset.single_le_sum
      (fun candidate _ => hmass.1 (some candidate)) hterminalIncidence
  exact hterminalMass.trans_le hle

/-- If the aggregate opposite-face transfer is positive, all of it can be
lower-bounded by the sum over the positive-transfer support. -/
theorem debt_le_sum_positiveTransferSupport
    (source target : QuittingTerminalSemanticPair ι) (who : ι)
    (htransfer : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebtChange source target other) :
    quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ quittingTerminalSemanticPositiveTransferSupport
          source target who,
        quittingTerminalSemanticDebtChange source target other := by
  apply htransfer.trans
  rw [quittingTerminalSemanticPositiveTransferSupport,
    Finset.sum_filter]
  apply Finset.sum_le_sum
  intro other hother
  split_ifs with hpositive
  · exact le_rfl
  · exact le_of_not_gt hpositive

/-- **Matched recipient or exact finite separator.**

The statement deliberately uses one fixed reset cluster and one fixed
incidence vector.  In the unmatched branch, the two positive supports are
literally disjoint and the whole selected debt is carried by the transfer
side of that separator.  Further progress from this branch requires a
strategic relation between the chosen best-response reset and the incidence
law; finite simplex geometry alone does not provide one. -/
theorem exists_matched_transfer_incidence_or_separator
    (source target : QuittingTerminalSemanticPair ι) (who : ι)
    (incidence : ι → ℝ)
    (htransfer : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebtChange source target other) :
    (∃ other, other ≠ who ∧
        0 < quittingTerminalSemanticDebtChange source target other ∧
        0 < incidence other) ∨
      (Disjoint
          (quittingTerminalSemanticPositiveTransferSupport source target who)
          (quittingTerminalOpponentIncidenceSupport who incidence) ∧
        quittingTerminalSemanticDebt source who ≤
          ∑ other ∈ quittingTerminalSemanticPositiveTransferSupport
              source target who,
            quittingTerminalSemanticDebtChange source target other) := by
  by_cases hmatch : ∃ other, other ≠ who ∧
      0 < quittingTerminalSemanticDebtChange source target other ∧
      0 < incidence other
  · exact Or.inl hmatch
  · right
    constructor
    · rw [Finset.disjoint_left]
      intro other htransferMem hincidenceMem
      have hother : other ≠ who := by
        exact Finset.ne_of_mem_erase
          (Finset.mem_filter.mp htransferMem).1
      have hpositiveTransfer := (Finset.mem_filter.mp htransferMem).2
      have hpositiveIncidence := (Finset.mem_filter.mp hincidenceMem).2
      exact hmatch ⟨other, hother, hpositiveTransfer, hpositiveIncidence⟩
    · exact debt_le_sum_positiveTransferSupport source target who htransfer

/-- **Concrete readout of the separator branch.**  For an incidence vector
coming from the same terminal law, an unmatched reset requires two distinct
opponents: one receives a quantitative share of transferred debt and the
other participates with positive terminal incidence.  In particular this
branch requires at least three players. -/
theorem exists_matched_transfer_incidence_or_twoOpponent_separator
    (source target : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hdebt : 0 < quittingTerminalSemanticDebt source who)
    (htransfer : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebtChange source target other)
    (hincidence : 0 < quittingTerminalOpponentContainingMass who mass) :
    (∃ other, other ≠ who ∧
        0 < quittingTerminalSemanticDebtChange source target other ∧
        0 < quittingTerminalOpponentIncidenceMass who other mass) ∨
      ∃ receiver quitter,
        receiver ≠ who ∧ quitter ≠ who ∧ receiver ≠ quitter ∧
        quittingTerminalSemanticDebt source who /
            ((Finset.univ.erase who).card : ℝ) ≤
          quittingTerminalSemanticDebtChange source target receiver ∧
        0 < quittingTerminalOpponentIncidenceMass who quitter mass ∧
        3 ≤ Fintype.card ι := by
  let incidence : ι → ℝ := fun other =>
    quittingTerminalOpponentIncidenceMass who other mass
  rcases exists_matched_transfer_incidence_or_separator
      source target who incidence htransfer with hmatch | hseparator
  · exact Or.inl hmatch
  · right
    obtain ⟨receiver, hreceiverMem, hreceiverAverage⟩ :=
      exists_opponent_average_le_debtChange source target who hdebt htransfer
    obtain ⟨quitter, hquitterNe, hquitterIncidence⟩ :=
      exists_positive_opponentIncidenceMass who mass hmass hincidence
    have hreceiverNe : receiver ≠ who :=
      Finset.ne_of_mem_erase hreceiverMem
    have hopponentsCardPos : 0 < ((Finset.univ.erase who).card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨receiver, hreceiverMem⟩)
    have haveragePos : 0 < quittingTerminalSemanticDebt source who /
        ((Finset.univ.erase who).card : ℝ) :=
      div_pos hdebt hopponentsCardPos
    have hreceiverPositive : 0 <
        quittingTerminalSemanticDebtChange source target receiver :=
      haveragePos.trans_le hreceiverAverage
    have hreceiverSupport : receiver ∈
        quittingTerminalSemanticPositiveTransferSupport source target who := by
      exact Finset.mem_filter.mpr ⟨hreceiverMem, hreceiverPositive⟩
    have hquitterSupport : quitter ∈
        quittingTerminalOpponentIncidenceSupport who incidence := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hquitterNe, Finset.mem_univ quitter⟩,
          hquitterIncidence⟩
    have hdistinct : receiver ≠ quitter := by
      intro heq
      subst quitter
      exact Finset.disjoint_left.mp hseparator.1
        hreceiverSupport hquitterSupport
    have hthree : 3 ≤ Fintype.card ι := by
      have hcard : ({who, receiver, quitter} : Finset ι).card = 3 := by
        simp [hreceiverNe.symm, hquitterNe.symm, hdistinct]
      calc
        3 = ({who, receiver, quitter} : Finset ι).card := hcard.symm
        _ ≤ Finset.univ.card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card ι := Finset.card_univ
    exact ⟨receiver, quitter, hreceiverNe, hquitterNe, hdistinct,
      hreceiverAverage, hquitterIncidence, hthree⟩

/-- With at most two players, positive same-law incidence and positive debt
transfer must meet at the unique possible opponent label. -/
theorem exists_matched_transfer_incidence_of_card_le_two
    (source target : QuittingTerminalSemanticPair ι) (who : ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hdebt : 0 < quittingTerminalSemanticDebt source who)
    (htransfer : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebtChange source target other)
    (hincidence : 0 < quittingTerminalOpponentContainingMass who mass)
    (hcard : Fintype.card ι ≤ 2) :
    ∃ other, other ≠ who ∧
      0 < quittingTerminalSemanticDebtChange source target other ∧
      0 < quittingTerminalOpponentIncidenceMass who other mass := by
  rcases exists_matched_transfer_incidence_or_twoOpponent_separator
      source target who mass hmass hdebt htransfer hincidence with
    hmatch | ⟨_receiver, _quitter, _, _, _, _, _, hthree⟩
  · exact hmatch
  · omega

/-- **Same-law reset/incidence capstone.**

At a positive minimum all-Continue plateau, choose one pure-time law which
realizes a debtor's envelope.  The very same deviated profiles have a compact
reset cluster carrying the exact opposite-face transfer account.  A
quantitative profitable atom then gives either a negative `Never` boundary,
or positive opponent incidence on that law.  In the finite branch the reset
recipient is matched to that incidence, or the same chronology supplies an
explicit two-opponent separator.

The second subsequence only extracts the semantic reset cluster; it does not
replace the terminal law or its deviated profiles. -/
theorem exists_samePureTimeLaw_resetCluster_negativeNever_or_matched_separator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward source.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (hdebt : 0 < quittingTerminalSemanticDebt source who)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ (profiles : ℕ → (quittingGame reward).BehaviorProfile)
        (quitTime : ℕ → Option ℕ)
        (mass : QuittingTerminalOutcome ι → ℝ)
        (baseSubseq : ℕ → ℕ)
        (cluster : QuittingTerminalSemanticPair ι)
        (resetSubseq : ℕ → ℕ),
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
          atTop (𝓝 source) ∧
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
      StrictMono baseSubseq ∧
      Tendsto (fun n => quittingTerminalOutcomeMass reward
          (Function.update (profiles (baseSubseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (baseSubseq n)))))
        atTop (𝓝 mass) ∧
      cluster ∈ quittingTerminalSemanticCarrier reward ∧
      StrictMono resetSubseq ∧
      Tendsto (fun rank => quittingTerminalSemanticPair reward
          (Function.update (profiles (baseSubseq (resetSubseq rank))) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (baseSubseq (resetSubseq rank))))))
        atTop (𝓝 cluster) ∧
      quittingTerminalSemanticDebt cluster who = 0 ∧
      (∑ other ∈ (Finset.univ.erase who),
          quittingTerminalSemanticDebtChange source cluster other) =
        (quittingTerminalSemanticDebtSum cluster -
            quittingTerminalSemanticDebtSum source) +
          quittingTerminalSemanticDebt source who ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ other ∈ (Finset.univ.erase who),
          quittingTerminalSemanticDebtChange source cluster other ∧
      ((quittingTerminalSemanticDebt source who /
            (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤ mass none ∧
          source.1 who < 0) ∨
        (quittingTerminalSemanticDebt source who /
              (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤
            quittingTerminalOpponentContainingMass who mass ∧
          ((∃ other, other ≠ who ∧
              0 < quittingTerminalSemanticDebtChange source cluster other ∧
              0 < quittingTerminalOpponentIncidenceMass who other mass) ∨
            ∃ receiver quitter,
              receiver ≠ who ∧ quitter ≠ who ∧ receiver ≠ quitter ∧
              quittingTerminalSemanticDebt source who /
                  ((Finset.univ.erase who).card : ℝ) ≤
                quittingTerminalSemanticDebtChange source cluster receiver ∧
              0 < quittingTerminalOpponentIncidenceMass who quitter mass ∧
              3 ≤ Fintype.card ι))) := by
  obtain ⟨profiles, quitTime, mass, baseSubseq, hprofiles, hmass,
      hbaseSubseq, hmassLimit, hmoment⟩ :=
    exists_pureTimeDeviation_terminalLaw_tendsto_semanticEnvelope
      reward source hsource who hM.le hreward
  let resetProfile : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
    Function.update (profiles (baseSubseq rank)) who
      (quittingPureTimeBehaviorStrategy reward who
        (quitTime (baseSubseq rank)))
  have hpayoff : Tendsto (fun rank =>
      quittingTerminalPayoff reward (resetProfile rank) who)
      atTop (𝓝 (source.2 who)) := by
    have hmomentLimit : Tendsto (fun rank =>
        quittingTerminalRewardMoment reward
          (quittingTerminalOutcomeMass reward (resetProfile rank)) who)
        atTop (𝓝 (quittingTerminalRewardMoment reward mass who)) :=
      ((continuous_apply who).comp
        (continuous_quittingTerminalRewardMoment reward)).tendsto mass |>.comp
          hmassLimit
    rw [hmoment] at hmomentLimit
    simpa only [quittingTerminalRewardMoment_outcomeMass] using hmomentLimit
  obtain ⟨cluster, resetSubseq, hcluster, hresetSubseq, hclusterLimit,
      hreset, hidentity, htransfer⟩ :=
    exists_terminalSemanticResetCluster_quantitative_transfer
      reward source (fun rank => profiles (baseSubseq rank)) who
      (fun rank => quittingPureTimeBehaviorStrategy reward who
        (quitTime (baseSubseq rank))) hM.le hreward hminimum
      (hprofiles.comp hbaseSubseq.tendsto_atTop) hpayoff
  obtain ⟨outcome, _hproduct, _hgain, hmassFloor, houtcome⟩ :=
    exists_terminalOutcome_quantitative_trichotomy_of_allContinuePlateau
      reward source hsource hnash who mass hM hreward hmass hmoment hdebt
  refine ⟨profiles, quitTime, mass, baseSubseq, cluster, resetSubseq,
    hprofiles, hmass, hbaseSubseq, hmassLimit, hcluster, hresetSubseq,
    ?_, hreset, hidentity, htransfer, ?_⟩
  · change Tendsto
      (fun rank => quittingTerminalSemanticPair reward
        (resetProfile (resetSubseq rank))) atTop (𝓝 cluster)
    exact hclusterLimit
  · rcases houtcome with hnever | hfinite
    · left
      rcases hnever with ⟨rfl, hnegative⟩
      exact ⟨hmassFloor, hnegative⟩
    · right
      rcases hfinite with hcontains | hexcludes
      · obtain ⟨terminal, rfl, _hwhoMem, hterminalNe, _hprofitable⟩ :=
          hcontains
        have hterminalMem : terminal ∈ Finset.univ.filter
            (fun candidate : {S : Finset ι // S.Nonempty} =>
              candidate.val ≠ {who}) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ terminal, hterminalNe⟩
        have hmassLe : mass (some terminal) ≤
            quittingTerminalOpponentContainingMass who mass := by
          unfold quittingTerminalOpponentContainingMass
          exact Finset.single_le_sum
            (fun candidate _ => hmass.1 (some candidate)) hterminalMem
        have hopponentFloor := hmassFloor.trans hmassLe
        have hopponentPositive :
            0 < quittingTerminalOpponentContainingMass who mass := by
          have hdenominator : 0 <
              (2 * M * Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
            positivity
          exact (div_pos hdebt hdenominator).trans_le hopponentFloor
        exact ⟨hopponentFloor,
          exists_matched_transfer_incidence_or_twoOpponent_separator
            source cluster who mass hmass hdebt htransfer hopponentPositive⟩
      · obtain ⟨terminal, rfl, hwhoNotMem, _hprofitable⟩ := hexcludes
        have hterminalNe : terminal.val ≠ {who} := by
          intro heq
          have : who ∈ terminal.val := by simp [heq]
          exact hwhoNotMem this
        have hterminalMem : terminal ∈ Finset.univ.filter
            (fun candidate : {S : Finset ι // S.Nonempty} =>
              candidate.val ≠ {who}) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ terminal, hterminalNe⟩
        have hmassLe : mass (some terminal) ≤
            quittingTerminalOpponentContainingMass who mass := by
          unfold quittingTerminalOpponentContainingMass
          exact Finset.single_le_sum
            (fun candidate _ => hmass.1 (some candidate)) hterminalMem
        have hopponentFloor := hmassFloor.trans hmassLe
        have hopponentPositive :
            0 < quittingTerminalOpponentContainingMass who mass := by
          have hdenominator : 0 <
              (2 * M * Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
            positivity
          exact (div_pos hdebt hdenominator).trans_le hopponentFloor
        exact ⟨hopponentFloor,
          exists_matched_transfer_incidence_or_twoOpponent_separator
            source cluster who mass hmass hdebt htransfer hopponentPositive⟩

end GameTheory
