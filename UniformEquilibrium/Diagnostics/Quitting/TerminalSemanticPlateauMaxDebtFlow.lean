/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMaxDebtConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDebtTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumAggregateSurplusConsumer
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter

/-!
# Finite max-debt face flows

A face-valued max-debt costate is a probability vector supported on the
players which maximize the current debt.  For every separable row objective,
fractional costates give no improvement: the weighted objective can be
purified to one positively weighted maximizing player.  Applied row by row,
this produces an ordinary max-debt selector with no smaller net
opponent-clock-minus-defect score.  The selector also retains the automatic
uphill switching property of the existing dynamic-costate telescope.

Fractional weights become substantive only after reset-recipient and
incidence labels are coupled across time.  The finite layered-flow packet
below retains those labels.  Every feasible unit flow contains a pure label
path whose vertices are debt maximizers and whose edges have both positive
reset transfer and positive chronological incidence.  This is a label
skeleton, not yet a legal reset/cycle path: a later consumer must show that
the selected edges come from one co-realized sequence of semantic states.
Fractional matching can improve quantitative capacity by splitting across
paths, but it cannot hide the absence of every positive matched label path.

The module does not assert that the quitting-game data always produce such a
matched flow.  It records the exact Hall-type player-subset inequality obeyed
by every flow and packages a strict violation as a cut which both excludes
the flow and selects a nonempty subset for the existing exact aggregate-
surplus theorem.  Boolean-Mobius coordinates remain available for decoding
the local coalition derivative on that selected face.  The converse
max-flow/min-cut theorem producing such a cut from flow infeasibility is not
proved here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## One max-debt face -/

/-- A probability costate supported on debt-maximizing coordinates. -/
structure QuittingDebtMaxFaceCostate (debt : ι → ℝ) where
  weight : ι → ℝ
  nonneg : ∀ who, 0 ≤ weight who
  sum_eq_one : ∑ who, weight who = 1
  maximizes_of_pos : ∀ who, 0 < weight who →
    ∀ other, debt other ≤ debt who

namespace QuittingDebtMaxFaceCostate

variable {debt : ι → ℝ}

omit [DecidableEq ι] in
/-- Every max-face costate has a positively weighted coordinate. -/
theorem exists_weight_pos (theta : QuittingDebtMaxFaceCostate debt) :
    ∃ who, 0 < theta.weight who := by
  by_contra hnot
  push Not at hnot
  have hzero : ∀ who, theta.weight who = 0 := by
    intro who
    exact le_antisymm (hnot who) (theta.nonneg who)
  have : (∑ who, theta.weight who) = 0 := by simp [hzero]
  linarith [theta.sum_eq_one]

omit [DecidableEq ι] in
/-- Linear optimization over a max-debt face has an extreme maximizing
coordinate in the positive support. -/
theorem exists_pure_ge_weightedScore
    (theta : QuittingDebtMaxFaceCostate debt) (score : ι → ℝ) :
    ∃ owner, 0 < theta.weight owner ∧
      (∀ who, debt who ≤ debt owner) ∧
      (∑ who, theta.weight who * score who) ≤ score owner := by
  let support := Finset.univ.filter fun who => 0 < theta.weight who
  have hsupportNonempty : support.Nonempty := by
    obtain ⟨who, hwho⟩ := theta.exists_weight_pos
    exact ⟨who, Finset.mem_filter.mpr ⟨Finset.mem_univ who, hwho⟩⟩
  obtain ⟨owner, hownerMem, hownerMax⟩ :=
    Finset.exists_max_image support score hsupportNonempty
  have hownerPos : 0 < theta.weight owner :=
    (Finset.mem_filter.mp hownerMem).2
  have hterm : ∀ who,
      theta.weight who * score who ≤ theta.weight who * score owner := by
    intro who
    by_cases hwho : 0 < theta.weight who
    · exact mul_le_mul_of_nonneg_left
        (hownerMax who (Finset.mem_filter.mpr
          ⟨Finset.mem_univ who, hwho⟩)) (theta.nonneg who)
    · have hzero : theta.weight who = 0 :=
        le_antisymm (le_of_not_gt hwho) (theta.nonneg who)
      simp [hzero]
  refine ⟨owner, hownerPos, theta.maximizes_of_pos owner hownerPos, ?_⟩
  calc
    (∑ who, theta.weight who * score who) ≤
        ∑ who, theta.weight who * score owner :=
      Finset.sum_le_sum fun who _ => hterm who
    _ = score owner := by
      rw [← Finset.sum_mul, theta.sum_eq_one, one_mul]

omit [DecidableEq ι] in
/-- A max-face costate evaluates the debt vector at its common maximum. -/
theorem weightedDebt_eq_of_weight_pos
    (theta : QuittingDebtMaxFaceCostate debt) (owner : ι)
    (howner : 0 < theta.weight owner) :
    (∑ who, theta.weight who * debt who) = debt owner := by
  have hdebtEq : ∀ who, 0 < theta.weight who → debt who = debt owner := by
    intro who hwho
    exact le_antisymm
      (theta.maximizes_of_pos owner howner who)
      (theta.maximizes_of_pos who hwho owner)
  calc
    (∑ who, theta.weight who * debt who) =
        ∑ who, theta.weight who * debt owner := by
      apply Finset.sum_congr rfl
      intro who _
      by_cases hwho : 0 < theta.weight who
      · rw [hdebtEq who hwho]
      · have hzero : theta.weight who = 0 :=
          le_antisymm (le_of_not_gt hwho) (theta.nonneg who)
        simp [hzero]
    _ = debt owner := by
      rw [← Finset.sum_mul, theta.sum_eq_one, one_mul]

end QuittingDebtMaxFaceCostate

/-! ## Purifying the game-facing finite clock -/

/-- The max-debt face of the actual shifted spine at one time. -/
def QuittingSpineMaxDebtFaceCostate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) :=
  QuittingDebtMaxFaceCostate fun who =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile time)) who

/-- Every finite family of fractional max-face costates can be purified
rowwise.  The selected player is still a current debt maximizer and has no
smaller value for the displayed separable score. -/
theorem exists_pureMaxDebtSelector_ge_fractionalScore
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : (time : ℕ) →
      QuittingSpineMaxDebtFaceCostate reward profile time)
    (score : ℕ → ι → ℝ) :
    ∃ owner : ℕ → ι,
      (∀ time who,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) who ≤
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time))
            (owner time)) ∧
      ∀ time,
        (∑ who, (theta time).weight who * score time who) ≤
          score time (owner time) := by
  have hchoose : ∀ time, ∃ owner,
      (∀ who,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) who ≤
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) owner) ∧
      (∑ who, (theta time).weight who * score time who) ≤ score time owner := by
    intro time
    obtain ⟨owner, _hownerPos, hmax, hscore⟩ :=
      (theta time).exists_pure_ge_weightedScore (score time)
    exact ⟨owner, hmax, hscore⟩
  choose owner howner using hchoose
  exact ⟨owner, fun time => (howner time).1, fun time => (howner time).2⟩

/-- **Fractional max-face costates do not improve the separable max-debt
clock.**  There is a pure max-debt selector whose live-mass-weighted net
opponent clock minus twice the local Nash defect dominates the fractional
score at every finite cutoff. -/
theorem exists_pureMaxDebtSelector_sum_netClock_ge_fractional
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : (time : ℕ) →
      QuittingSpineMaxDebtFaceCostate reward profile time)
    (reference : ℝ) (cutoff : ℕ) :
    ∃ owner : ℕ → ι,
      (∀ time who,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) who ≤
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time))
            (owner time)) ∧
      (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            ∑ who, (theta time).weight who *
              (reference * quittingRootOpponentAbsorptionMass
                  (quittingProfileLiveRoot reward profile time) who -
                2 * quittingRootCoordinateNashDefect reward
                  (quittingTerminalSemanticPair reward
                    (quittingAllContinueProfileSpine
                      reward profile (time + 1))).1
                  (quittingProfileLiveRoot reward profile time) who)) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            (reference * quittingRootOpponentAbsorptionMass
                (quittingProfileLiveRoot reward profile time) (owner time) -
              2 * quittingRootCoordinateNashDefect reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine
                    reward profile (time + 1))).1
                (quittingProfileLiveRoot reward profile time) (owner time)) := by
  let score : ℕ → ι → ℝ := fun time who =>
    reference * quittingRootOpponentAbsorptionMass
        (quittingProfileLiveRoot reward profile time) who -
      2 * quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).1
        (quittingProfileLiveRoot reward profile time) who
  obtain ⟨owner, howner, hscore⟩ :=
    exists_pureMaxDebtSelector_ge_fractionalScore
      reward profile theta score
  refine ⟨owner, howner, ?_⟩
  apply Finset.sum_le_sum
  intro time htime
  exact mul_le_mul_of_nonneg_left (hscore time)
    (quittingLiveMass_nonneg reward profile time)

/-! ## Layered matched flow -/

/-- A finite unit flow through max-debt labels.  A positive edge is usable
only when its recipient has both positive reset transfer and positive
chronological incidence. -/
structure QuittingFiniteMaxDebtMatchedFlow
    (debt : ℕ → ι → ℝ) (transfer incidence : ℕ → ι → ι → ℝ)
    (cutoff : ℕ) where
  weight : ℕ → ι → ℝ
  flow : ℕ → ι → ι → ℝ
  weight_nonneg : ∀ time who, 0 ≤ weight time who
  weight_sum : ∀ time, time ≤ cutoff → ∑ who, weight time who = 1
  positive_weight_maximizes : ∀ time, time ≤ cutoff → ∀ who,
    0 < weight time who → ∀ other, debt time other ≤ debt time who
  flow_nonneg : ∀ time source target, 0 ≤ flow time source target
  row_sum : ∀ time, time < cutoff → ∀ source,
    ∑ target, flow time source target = weight time source
  column_sum : ∀ time, time < cutoff → ∀ target,
    ∑ source, flow time source target = weight (time + 1) target
  matched_of_flow_pos : ∀ time, time < cutoff → ∀ source target,
    0 < flow time source target →
      0 < transfer time source target ∧ 0 < incidence time source target

namespace QuittingFiniteMaxDebtMatchedFlow

variable {debt : ℕ → ι → ℝ}
variable {transfer incidence : ℕ → ι → ι → ℝ}
variable {cutoff : ℕ}

/-- Targets which are simultaneously reachable by positive reset transfer
and positive incidence from a displayed player subset. -/
def matchedTargetSet
    (transfer incidence : ℕ → ι → ι → ℝ)
    (time : ℕ) (sources : Finset ι) : Finset ι :=
  Finset.univ.filter fun target =>
    ∃ source ∈ sources,
      0 < transfer time source target ∧
        0 < incidence time source target

omit [DecidableEq ι] in
/-- A positively weighted vertex has a positive matched outgoing edge before
the cutoff, and the edge reaches a positively weighted next vertex. -/
theorem exists_positive_matched_successor
    [Nonempty ι]
    (packet : QuittingFiniteMaxDebtMatchedFlow debt transfer incidence cutoff)
    (time : ℕ) (htime : time < cutoff) (source : ι)
    (hsource : 0 < packet.weight time source) :
    ∃ target, 0 < packet.flow time source target ∧
      0 < packet.weight (time + 1) target ∧
      0 < transfer time source target ∧
        0 < incidence time source target := by
  have hsumPositive : 0 < ∑ target, packet.flow time source target := by
    rw [packet.row_sum time htime source]
    exact hsource
  have htermNonneg : ∀ target ∈ (Finset.univ : Finset ι),
      0 ≤ packet.flow time source target :=
    fun target _ => packet.flow_nonneg time source target
  obtain ⟨target, _htargetMem, hflow⟩ :=
    (Finset.sum_pos_iff_of_nonneg htermNonneg).mp hsumPositive
  have hflowLe : packet.flow time source target ≤
      ∑ origin, packet.flow time origin target := by
    exact Finset.single_le_sum
      (fun origin _ => packet.flow_nonneg time origin target)
      (Finset.mem_univ source)
  have hnext : 0 < packet.weight (time + 1) target := by
    rw [packet.column_sum time htime target] at hflowLe
    exact hflow.trans_le hflowLe
  exact ⟨target, hflow, hnext,
    (packet.matched_of_flow_pos time htime source target hflow).1,
    (packet.matched_of_flow_pos time htime source target hflow).2⟩

omit [DecidableEq ι] in
/-- **Player-subset cut inequality.**  Any feasible matched flow sends the
weight of a source subset into its matched target neighborhood.  A violation
is therefore a quantitative finite dual certificate against the proposed
reset/incidence flow. -/
theorem sourceWeight_le_matchedTargetWeight
    (packet : QuittingFiniteMaxDebtMatchedFlow debt transfer incidence cutoff)
    (time : ℕ) (htime : time < cutoff) (sources : Finset ι) :
    (∑ source ∈ sources, packet.weight time source) ≤
      ∑ target ∈ matchedTargetSet transfer incidence time sources,
        packet.weight (time + 1) target := by
  let targets := matchedTargetSet transfer incidence time sources
  have hzeroOutside : ∀ target ∉ targets, ∀ source ∈ sources,
      packet.flow time source target = 0 := by
    intro target htarget source hsource
    apply le_antisymm
    · by_contra hnot
      have hpositive : 0 < packet.flow time source target :=
        lt_of_not_ge hnot
      have hmatched :=
        packet.matched_of_flow_pos time htime source target hpositive
      apply htarget
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ target, source, hsource, hmatched⟩
    · exact packet.flow_nonneg time source target
  have hrestrict :
      (∑ target ∈ targets,
          ∑ source ∈ sources, packet.flow time source target) =
        ∑ target,
          ∑ source ∈ sources, packet.flow time source target := by
    apply Finset.sum_subset (Finset.subset_univ targets)
    intro target _htargetMem htargetNot
    exact Finset.sum_eq_zero fun source hsource =>
      hzeroOutside target htargetNot source hsource
  have hsourceRows :
      (∑ source ∈ sources, packet.weight time source) =
        ∑ target,
          ∑ source ∈ sources, packet.flow time source target := by
    calc
      (∑ source ∈ sources, packet.weight time source) =
          ∑ source ∈ sources,
            ∑ target, packet.flow time source target := by
        apply Finset.sum_congr rfl
        intro source _
        rw [packet.row_sum time htime source]
      _ = ∑ target,
          ∑ source ∈ sources, packet.flow time source target := by
        rw [Finset.sum_comm]
  rw [← hrestrict] at hsourceRows
  rw [hsourceRows]
  apply Finset.sum_le_sum
  intro target htarget
  calc
    (∑ source ∈ sources, packet.flow time source target) ≤
        ∑ source, packet.flow time source target := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ sources)
        (fun source _ _ => packet.flow_nonneg time source target)
    _ = packet.weight (time + 1) target :=
      packet.column_sum time htime target

omit [DecidableEq ι] in
/-- A strict player-subset cut rules out every fractional matched flow, not
only pure selectors. -/
theorem not_exists_of_matchedTargetWeight_lt_sourceWeight
    (time cutoff : ℕ) (htime : time < cutoff) (sources : Finset ι)
    (weight : ℕ → ι → ℝ)
    (hcut :
      (∑ target ∈ matchedTargetSet transfer incidence time sources,
          weight (time + 1) target) <
        ∑ source ∈ sources, weight time source) :
    ¬ ∃ packet : QuittingFiniteMaxDebtMatchedFlow
        debt transfer incidence cutoff,
      packet.weight = weight := by
  rintro ⟨packet, hweight⟩
  have hhall := packet.sourceWeight_le_matchedTargetWeight
    time htime sources
  rw [hweight] at hhall
  linarith

/-- A strict Hall cut for the concrete reset-transfer/incidence relation. -/
structure QuittingFiniteMaxDebtMatchedCut
    (debt : ℕ → ι → ℝ)
    (transfer incidence : ℕ → ι → ι → ℝ)
    (weight : ℕ → ι → ℝ) (cutoff : ℕ) where
  time : ℕ
  sources : Finset ι
  time_lt : time < cutoff
  weight_nonneg : ∀ stage who, 0 ≤ weight stage who
  weight_sum_current : ∑ who, weight time who = 1
  weight_sum_next : ∑ who, weight (time + 1) who = 1
  positive_weight_maximizes : ∀ who, 0 < weight time who →
    ∀ other, debt time other ≤ debt time who
  strict :
    (∑ target ∈ matchedTargetSet transfer incidence time sources,
        weight (time + 1) target) <
      ∑ source ∈ sources, weight time source

namespace QuittingFiniteMaxDebtMatchedCut

variable {debt : ℕ → ι → ℝ}
variable {weight : ℕ → ι → ℝ}

/-- Positive deficit exposed by a strict matched-flow cut. -/
def deficit
    (cut : QuittingFiniteMaxDebtMatchedCut
      debt transfer incidence weight cutoff) : ℝ :=
  (∑ source ∈ cut.sources, weight cut.time source) -
    ∑ target ∈ matchedTargetSet transfer incidence cut.time cut.sources,
      weight (cut.time + 1) target

omit [DecidableEq ι] in
theorem deficit_pos
    (cut : QuittingFiniteMaxDebtMatchedCut
      debt transfer incidence weight cutoff) :
    0 < cut.deficit := by
  unfold deficit
  linarith [cut.strict]

omit [DecidableEq ι] in
/-- A strict cut contains a max-debt source carrying at least the average
share of the cut deficit. -/
theorem exists_maxDebtSource_deficit_div_card_le_weight
    (cut : QuittingFiniteMaxDebtMatchedCut
      debt transfer incidence weight cutoff) :
    ∃ source ∈ cut.sources,
      cut.deficit / (cut.sources.card : ℝ) ≤
          weight cut.time source ∧
        ∀ other, debt cut.time other ≤ debt cut.time source := by
  have htargetNonneg : 0 ≤
      ∑ target ∈ matchedTargetSet transfer incidence cut.time cut.sources,
        weight (cut.time + 1) target :=
    Finset.sum_nonneg fun target _ => cut.weight_nonneg _ target
  have hsourcesPositive : 0 <
      ∑ source ∈ cut.sources, weight cut.time source :=
    htargetNonneg.trans_lt cut.strict
  have hsources : cut.sources.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr fun hempty => by
      rw [hempty] at hsourcesPositive
      simp at hsourcesPositive
  have hdeficitLe : cut.deficit ≤
      ∑ source ∈ cut.sources, weight cut.time source := by
    unfold deficit
    linarith
  have hcardPositive : 0 < (cut.sources.card : ℝ) := by
    exact_mod_cast hsources.card_pos
  have havg : ∃ source ∈ cut.sources,
      cut.deficit / (cut.sources.card : ℝ) ≤
        weight cut.time source := by
    by_contra hnot
    push Not at hnot
    have hstrict : ∀ source ∈ cut.sources,
        weight cut.time source <
          cut.deficit / (cut.sources.card : ℝ) := by
      intro source hsource
      exact hnot source hsource
    have hsumStrict := Finset.sum_lt_sum_of_nonempty hsources
      (fun source hsource => hstrict source hsource)
    have hconstant :
        (∑ _source ∈ cut.sources,
            cut.deficit / (cut.sources.card : ℝ)) = cut.deficit := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [hconstant] at hsumStrict
    linarith
  obtain ⟨source, hsourceMem, hsourceWeight⟩ := havg
  have hscalePos : 0 < cut.deficit / (cut.sources.card : ℝ) :=
    div_pos cut.deficit_pos hcardPositive
  have hsourcePos : 0 < weight cut.time source :=
    hscalePos.trans_le hsourceWeight
  exact ⟨source, hsourceMem, hsourceWeight,
    cut.positive_weight_maximizes source hsourcePos⟩

omit [DecidableEq ι] in
/-- A strict cut excludes every fractional matched flow with the displayed
max-face weights. -/
theorem excludes_matchedFlow
    (cut : QuittingFiniteMaxDebtMatchedCut
      debt transfer incidence weight cutoff) :
    ¬ ∃ packet : QuittingFiniteMaxDebtMatchedFlow
        debt transfer incidence cutoff,
      packet.weight = weight :=
  not_exists_of_matchedTargetWeight_lt_sourceWeight
    cut.time cutoff cut.time_lt cut.sources weight cut.strict

/-- **Deficit-sensitive game-facing dual consumer.**

When the cut's debt vector is aligned with a positive minimum semantic pair,
one cut source is a debt maximizer and carries the average cut deficit.  If
its complementary debt is zero, it is a full-debt vertex coordinate.  If the
complementary debt is positive, one common terminal outcome carries a
strictly positive singleton surplus after multiplication by the same cut
deficit scale.  These are respectively the full-debt vertex-coordinate input
to the negative-vertex tests and the subset-surplus exit; the former still
requires the separate zero-slack test.  No arbitrary subset wrapper is used.
-/
theorem exists_maxDebtSource_vertex_or_weightedMinimumSurplus
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (cut : QuittingFiniteMaxDebtMatchedCut
      debt transfer incidence weight cutoff)
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (halign : ∀ who, debt cut.time who =
      quittingTerminalSemanticDebt pair who) :
    ∃ source ∈ cut.sources,
      cut.deficit / (cut.sources.card : ℝ) ≤
          weight cut.time source ∧
        (∀ other, quittingTerminalSemanticDebt pair other ≤
          quittingTerminalSemanticDebt pair source) ∧
        ((quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair source = 0) ∨
          ∃ outcome : QuittingTerminalOutcome ι,
            0 < cut.deficit / (cut.sources.card : ℝ) *
              (quittingTerminalSemanticDebtSum pair -
                quittingTerminalSemanticDebt pair source) ∧
            cut.deficit / (cut.sources.card : ℝ) *
                (quittingTerminalSemanticDebtSum pair -
                  quittingTerminalSemanticDebt pair source) ≤
              cut.deficit / (cut.sources.card : ℝ) *
                (quittingTerminalOutcomeReward reward outcome source -
                  reward (quittingSingletonTerminal source) source)) := by
  obtain ⟨source, hsourceMem, hsourceWeight, hsourceMax⟩ :=
    cut.exists_maxDebtSource_deficit_div_card_le_weight
  have hmax : ∀ other, quittingTerminalSemanticDebt pair other ≤
      quittingTerminalSemanticDebt pair source := by
    intro other
    simpa [halign] using hsourceMax other
  refine ⟨source, hsourceMem, hsourceWeight, hmax, ?_⟩
  let gap := quittingTerminalSemanticDebtSum pair -
    quittingTerminalSemanticDebt pair source
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hgapNonneg : 0 ≤ gap := by
    unfold gap quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun who _ => hdebtNonneg who) (Finset.mem_univ source)
      |> fun h => sub_nonneg.mpr h
  by_cases hgapZero : gap = 0
  · exact Or.inl hgapZero
  · right
    have hgapPos : 0 < gap := lt_of_le_of_ne hgapNonneg (Ne.symm hgapZero)
    have hsources : cut.sources.Nonempty := ⟨source, hsourceMem⟩
    have hcardPositive : 0 < (cut.sources.card : ℝ) := by
      exact_mod_cast hsources.card_pos
    have hscalePos : 0 < cut.deficit / (cut.sources.card : ℝ) :=
      div_pos cut.deficit_pos hcardPositive
    obtain ⟨outcome, houtcome⟩ :=
      exists_terminalOutcome_subset_singletonSurplus_ge_exactMinimumDebt
        (reward := reward) pair {source} hM hreward hpair hminimum hpositive
    have houtcome' : gap ≤
        quittingTerminalOutcomeReward reward outcome source -
          reward (quittingSingletonTerminal source) source := by
      simpa [gap] using houtcome
    exact ⟨outcome, mul_pos hscalePos hgapPos,
      mul_le_mul_of_nonneg_left houtcome' hscalePos.le⟩

end QuittingFiniteMaxDebtMatchedCut

omit [DecidableEq ι] in
/-- **Matched-flow path extraction.**  Every fractional unit flow contains a
pure path of debt-maximizing labels.  Each transition on the path is positive
both for reset transfer and for incidence.  This is the label skeleton needed
by a reset/cycle consumer; legality still requires co-realized semantic-state
provenance for the selected consecutive edges. -/
theorem exists_pure_maxDebt_matched_path
    [Nonempty ι]
    (packet : QuittingFiniteMaxDebtMatchedFlow debt transfer incidence cutoff) :
    ∃ owner : ℕ → ι,
      (∀ time, time ≤ cutoff →
        0 < packet.weight time (owner time)) ∧
      (∀ time, time ≤ cutoff → ∀ who,
        debt time who ≤ debt time (owner time)) ∧
      ∀ time, time < cutoff →
        0 < transfer time (owner time) (owner (time + 1)) ∧
        0 < incidence time (owner time) (owner (time + 1)) := by
  have hinitialSum := packet.weight_sum 0 (Nat.zero_le cutoff)
  have hinitialPositive : ∃ who, 0 < packet.weight 0 who := by
    by_contra hnot
    push Not at hnot
    have hzero : ∀ who, packet.weight 0 who = 0 := by
      intro who
      exact le_antisymm (hnot who) (packet.weight_nonneg 0 who)
    have : (∑ who, packet.weight 0 who) = 0 := by simp [hzero]
    linarith
  let initial : ι := Classical.choose hinitialPositive
  have hinitial : 0 < packet.weight 0 initial :=
    Classical.choose_spec hinitialPositive
  let next : ℕ → ι → ι := fun time source =>
    if htime : time < cutoff then
      if hsource : 0 < packet.weight time source then
        Classical.choose
          (packet.exists_positive_matched_successor time htime source hsource)
      else Classical.choice inferInstance
    else Classical.choice inferInstance
  let owner : ℕ → ι := fun time =>
    Nat.rec initial (fun step previous => next step previous) time
  have hpath : ∀ time, time ≤ cutoff →
      0 < packet.weight time (owner time) ∧
        ∀ step, step < time →
          0 < transfer step (owner step) (owner (step + 1)) ∧
          0 < incidence step (owner step) (owner (step + 1)) := by
    intro time htime
    induction time with
    | zero =>
        exact ⟨hinitial, fun step hstep => (Nat.not_lt_zero step hstep).elim⟩
    | succ time ih =>
        have htimeLt : time < cutoff := Nat.lt_of_succ_le htime
        obtain ⟨hcurrent, hedges⟩ := ih (Nat.le_of_lt htimeLt)
        have hsuccessor := packet.exists_positive_matched_successor
          time htimeLt (owner time) hcurrent
        have hnextSpec := Classical.choose_spec hsuccessor
        have hownerNext : owner (time + 1) =
            Classical.choose hsuccessor := by
          simp [owner, next, htimeLt, hcurrent]
        rw [hownerNext]
        refine ⟨hnextSpec.2.1, ?_⟩
        intro step hstep
        by_cases hlast : step = time
        · subst step
          simpa only [hownerNext] using
            (show 0 < transfer time (owner time)
                  (Classical.choose hsuccessor) ∧
                0 < incidence time (owner time)
                  (Classical.choose hsuccessor) from
              ⟨hnextSpec.2.2.1, hnextSpec.2.2.2⟩)
        · have hstepLt : step < time :=
            Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hstep) hlast
          simpa only [hownerNext] using hedges step hstepLt
  refine ⟨owner, ?_, ?_, ?_⟩
  · intro time htime
    exact (hpath time htime).1
  · intro time htime who
    exact packet.positive_weight_maximizes time htime (owner time)
      (hpath time htime).1 who
  · intro time htime
    exact (hpath (time + 1) (Nat.succ_le_of_lt htime)).2 time
      (Nat.lt_succ_self time)

end QuittingFiniteMaxDebtMatchedFlow

end GameTheory
