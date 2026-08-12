/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTangentExtraction
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSeam

/-!
# An exhaustive stopping-law frontier for a quitting counterexample regime

This module records one maintained implication from the conjecture-level
counterexample package to the current finite stopping-law residual.

Every counterexample regime has both the canonical source--dynamic-tail seam
and a positive minimum all-Continue semantic plateau.  These are retained as
simultaneous data; no identification between their limits is asserted.  A
literal sequence realizing the semantic plateau can be shifted so that
every limiting positive-debt coordinate is already positive.  Near-minimum
excess and all limiting zero-debt coordinates then vanish on that one common
sequence.  The square-root scale selector makes all of them negligible
relative to one common reset scale, so the stopping-law normalized-chord
extractor applies without an additional assumption.

The resulting finite disjunction is
`IsQuittingStoppingLawTangentPipelineAlternative`: positive total slope,
zero-debt support entry, positive charged circulation, or potential-guided
active co-decrease.  The first branch has the existing positive-slope causal
decoders.  The last three are exact residuals: this module does not claim a
chronological integration, a Bellman return, or a converse from the frontier
back to a counterexample regime.

The first missing implication is branch-specific.

* Positive total slope reaches literal terminal atoms and causal rectangle
  rows, but not a state-matched punishment/Bellman continuation.
* Zero-debt support entry is envelope/debt data; it does not yet imply
  positive co-realized mover--recipient incidence at a reached row.
* Charged circulation is an infinitesimal balance; no theorem integrates it
  to a chronological reset cycle in the semantic carrier.
* Potential-guided co-decrease retains a same-column second debtor, but does
  not yet supply a directed recipient return or metric/Bellman re-projection.

The older bare pipeline predicate is an overlapping cover because its flat
branches forget flatness and the duality decision.  The tagged predicate in
this module records the producing case splits and is disjoint: positive slope
versus flat, support entry versus no entry, and circulation versus its
separating-potential alternative.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Entry of one flat normalized reset column into a coordinate which has
zero debt at the semantic base. -/
def HasQuittingStoppingLawFlatSupportEntry
    (base : QuittingTerminalSemanticPair ι) (active : Finset ι)
    (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  let column := quittingActiveDebtTangentExtension active tangent
  ∃ mover ∈ active, ∃ recipient,
    quittingTerminalSemanticDebt base recipient = 0 ∧
      0 < column mover recipient

/-- Positive charged balance of the full signed flat reset columns. -/
def HasQuittingStoppingLawFlatChargedCirculation
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  let column := quittingActiveDebtTangentExtension active tangent
  let gain := quittingActiveDebtTangentGain active tangent
  HasNormalizedPositiveChargedCirculation
    (fun mover : {who // who ∈ active} ↦ column mover.1)
    (fun mover : {who // who ∈ active} ↦ gain mover.1)

/-- The separating-potential residual of a flat reset family, retaining the
same-column decrease of a second active debtor. -/
def HasQuittingStoppingLawFlatPotentialCoDecrease
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  let column := quittingActiveDebtTangentExtension active tangent
  let gain := quittingActiveDebtTangentGain active tangent
  ∃ potential : ι → ℝ, ∃ mover ∈ active, ∃ other ∈ active.erase mover,
    (∀ who, 0 ≤ potential who) ∧
    (∀ source ∈ active,
      gain source ≤ ∑ who, potential who * column source who) ∧
    (∀ source ∈ active, potential source ≤ potential mover) ∧
    column mover mover = -gain mover ∧
    column mover other < 0

/-- A disjointly tagged form of the current finite stopping-law frontier.

The last three branches explicitly record flatness.  Successive negations
make this a partition for the selected tangent family: positive slope versus
flat; then support entry versus no entry; then charged circulation versus its
separating-potential alternative. -/
def IsQuittingStoppingLawExhaustiveFrontierBranch
    (base : QuittingTerminalSemanticPair ι) (active : Finset ι)
    (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  (∃ mover, 0 < ∑ observer, tangent mover observer) ∨
    ((∀ mover, ∑ observer, tangent mover observer = 0) ∧
      HasQuittingStoppingLawFlatSupportEntry base active tangent) ∨
    ((∀ mover, ∑ observer, tangent mover observer = 0) ∧
      ¬ HasQuittingStoppingLawFlatSupportEntry base active tangent ∧
      HasQuittingStoppingLawFlatChargedCirculation active tangent) ∨
    ((∀ mover, ∑ observer, tangent mover observer = 0) ∧
      ¬ HasQuittingStoppingLawFlatSupportEntry base active tangent ∧
      ¬ HasQuittingStoppingLawFlatChargedCirculation active tangent ∧
      HasQuittingStoppingLawFlatPotentialCoDecrease active tangent)

omit [Nonempty ι] in
/-- Forgetting the partition tags recovers the existing stopping-law
pipeline alternative. -/
theorem IsQuittingStoppingLawExhaustiveFrontierBranch.toPipelineAlternative
    {base : QuittingTerminalSemanticPair ι} {active : Finset ι}
    {tangent : {who // who ∈ active} → ι → ℝ}
    (branch : IsQuittingStoppingLawExhaustiveFrontierBranch
      base active tangent) :
    IsQuittingStoppingLawTangentPipelineAlternative base active tangent := by
  rcases branch with hpositive | ⟨_hflat, hentry⟩ |
      ⟨_hflat, _hnoEntry, hcirculation⟩ |
      ⟨_hflat, _hnoEntry, _hnoCirculation, hpotential⟩
  · exact Or.inl hpositive
  · exact Or.inr (Or.inl hentry)
  · exact Or.inr (Or.inr (Or.inl hcirculation))
  · exact Or.inr (Or.inr (Or.inr hpotential))

/-- A provenance-preserving witness for the current exhaustive counterexample
frontier.  It retains the positive minimum plateau, one literal realizing
sequence, the common reset scale, every approximate-best-response ray, and
the common limiting normalized-chord family on which the finite alternative
is stated. -/
structure QuittingCounterexampleStoppingLawFrontier
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) where
  /-- The independently canonical optimized exact-D tail, finite source
  packet, and its summable opponent/absorption clocks. -/
  seam : QuittingCounterexampleSeamWitness regime
  base : QuittingTerminalSemanticPair ι
  profiles : ℕ → (quittingGame reward).BehaviorProfile
  active : Finset ι
  lambda : ℕ → ℝ
  lambda_pos : ∀ n, 0 < lambda n
  lambda_le_one : ∀ n, lambda n ≤ 1
  bestResponse : ∀ mover : {who // who ∈ active},
    ℕ → (quittingGame reward).BehaviorStrategy mover.1
  subseq : ℕ → ℕ
  tangent : {who // who ∈ active} → ι → ℝ
  base_mem : base ∈ quittingTerminalSemanticCarrier reward
  base_minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum base ≤
      quittingTerminalSemanticDebtSum candidate
  base_positive : 0 < quittingTerminalSemanticDebtSum base
  base_allContinue_nash : IsεQuittingRootNash reward base.1 0
    (quittingAllContinueRoot : ι → PMF Bool)
  base_allContinue_prefix :
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot base = base
  profiles_tendsto : Tendsto
    (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
    atTop (nhds base)
  active_iff : ∀ who, who ∈ active ↔
    0 < quittingTerminalSemanticDebt base who
  subseq_strictMono : StrictMono subseq
  lambda_subseq_tendsto_zero :
    Tendsto (fun rank ↦ lambda (subseq rank)) atTop (nhds 0)
  tangent_tendsto : ∀ mover observer,
    Tendsto (fun rank ↦
      quittingStoppingLawNormalizedDebtDirection reward
        (profiles (subseq rank)) mover.1
        (bestResponse mover (subseq rank)) (lambda (subseq rank))
        (lambda_pos (subseq rank)).le (lambda_le_one (subseq rank)) observer)
      atTop (nhds (tangent mover observer))
  tangent_diagonal : ∀ mover,
    tangent mover mover.1 ≤
      -quittingTerminalSemanticDebt base mover.1 / 2
  tangent_inactive_nonneg : ∀ mover observer,
    quittingTerminalSemanticDebt base observer = 0 →
      0 ≤ tangent mover observer
  tangent_sum_nonneg : ∀ mover, 0 ≤ ∑ observer, tangent mover observer
  exhaustive_branch :
    IsQuittingStoppingLawExhaustiveFrontierBranch base active tangent
  alternative :
    IsQuittingStoppingLawTangentPipelineAlternative base active tangent

/-- Every quitting counterexample regime reaches the finite stopping-law
frontier.  This is a one-way exhaustive reduction, not a characterization of
which frontier witnesses can occur. -/
theorem QuittingCounterexampleRegime.exists_stoppingLaw_exhaustiveFrontier
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    Nonempty (QuittingCounterexampleStoppingLawFrontier regime) := by
  classical
  obtain ⟨seam⟩ := regime.nonempty_seamWitness
  obtain ⟨base, hbase, hminimum, hbaseDebt, hnash, hprefix⟩ :=
    noUniformPayoff_implies_positiveMinimumSemanticPlateau regime
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  have hbasePositive : 0 < quittingTerminalSemanticDebtSum base := by
    have hnonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt base who :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) hbase
    obtain ⟨who, hwho⟩ := hbaseDebt
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_pos' (fun player _ ↦ hnonneg player)
      ⟨who, Finset.mem_univ who, hwho⟩
  obtain ⟨rawProfiles, hrawProfiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward base hbase
  let active : Finset ι := Finset.univ.filter fun who ↦
    0 < quittingTerminalSemanticDebt base who
  have hactive : ∀ who, who ∈ active ↔
      0 < quittingTerminalSemanticDebt base who := by
    intro who
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  have heventuallyActive : ∀ᶠ n in atTop, ∀ who ∈ active,
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (rawProfiles n)) who := by
    rw [eventually_all]
    intro who
    by_cases hwho : who ∈ active
    · have hcoordinate : Tendsto (fun n ↦ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (rawProfiles n)) who)
          atTop (nhds (quittingTerminalSemanticDebt base who)) := by
        exact (continuous_quittingTerminalSemanticDebt who).tendsto base |>.comp
          hrawProfiles
      filter_upwards [hcoordinate.eventually
          (Ioi_mem_nhds ((hactive who).1 hwho))] with _ hpositive
      exact fun _ ↦ hpositive
    · exact Eventually.of_forall fun _ hmem ↦ False.elim (hwho hmem)
  obtain ⟨start, hstart⟩ := eventually_atTop.1 heventuallyActive
  let profiles : ℕ → (quittingGame reward).BehaviorProfile :=
    fun n ↦ rawProfiles (n + start)
  have hprofiles : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds base) := by
    exact (tendsto_add_atTop_iff_nat start).2 hrawProfiles
  have hsourceActive : ∀ n, ∀ who ∈ active,
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who := by
    intro n who hwho
    exact hstart (n + start) (Nat.le_add_left start n) who hwho
  let epsilon : ℕ → ℝ := fun n ↦
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n)) -
      quittingTerminalSemanticDebtSum base
  have hepsilonNonneg : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact sub_nonneg.mpr (hminimum _
      (quittingTerminalSemanticPair_mem_carrier reward (profiles n)))
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    have hsum : Tendsto (fun n ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n))) atTop
        (nhds (quittingTerminalSemanticDebtSum base)) := by
      exact continuous_quittingTerminalSemanticDebtSum.tendsto base |>.comp
        hprofiles
    have hconst : Tendsto
        (fun _ : ℕ ↦ quittingTerminalSemanticDebtSum base) atTop
        (nhds (quittingTerminalSemanticDebtSum base)) := tendsto_const_nhds
    simpa only [epsilon, sub_self] using hsum.sub hconst
  let inactiveDebt : ι → ℕ → ℝ := fun who n ↦
    if quittingTerminalSemanticDebt base who = 0 then
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who
    else 0
  have hinactiveNonneg : ∀ who n, 0 ≤ inactiveDebt who n := by
    intro who n
    dsimp only [inactiveDebt]
    split_ifs
    · exact quittingTerminalDeviationDebt_nonneg reward (profiles n) who
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward)
    · exact le_rfl
  have hinactiveZero : ∀ who,
      Tendsto (inactiveDebt who) atTop (nhds 0) := by
    intro who
    dsimp only [inactiveDebt]
    by_cases hzero : quittingTerminalSemanticDebt base who = 0
    · simp only [hzero, if_pos]
      have hcoordinate : Tendsto (fun n ↦ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles n)) who)
          atTop (nhds (quittingTerminalSemanticDebt base who)) := by
        exact (continuous_quittingTerminalSemanticDebt who).tendsto base |>.comp
          hprofiles
      simpa only [hzero] using hcoordinate
    · simp only [hzero]
      exact tendsto_const_nhds
  obtain ⟨lambda, hlambdaPos, hlambdaLe, hlambdaZero,
      hepsilonRate, hinactiveRate⟩ :=
    exists_commonVanishingResetScale epsilon inactiveDebt
      hepsilonNonneg hinactiveNonneg hepsilonZero hinactiveZero
  have hnear : ∀ n, ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon n := by
    intro n candidate hcandidate
    dsimp only [epsilon]
    have hbaseLe := hminimum candidate hcandidate
    linarith
  have hinactiveRate' : ∀ who,
      quittingTerminalSemanticDebt base who = 0 →
      Tendsto (fun n ↦
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) who /
          lambda n) atTop (nhds 0) := by
    intro who hzero
    simpa only [inactiveDebt, hzero, if_pos] using hinactiveRate who
  obtain ⟨bestResponse, subseq, tangent, hsubseq, hlambdaSubseq,
      htangent, hdiagonal, htangentInactive, hsumNonneg,
      hslopeAlternative⟩ :=
    exists_commonBase_stoppingLawDebtTangentFamily
      reward base profiles active epsilon lambda
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hbase hbasePositive
      hprofiles hactive hsourceActive hnear hlambdaPos hlambdaLe hlambdaZero
      hepsilonRate hinactiveRate'
  have hfrontierBranch :
      IsQuittingStoppingLawExhaustiveFrontierBranch base active tangent := by
    rcases hslopeAlternative with hpositiveSlope | hflat
    · exact Or.inl hpositiveSlope
    · have hactiveNonempty : active.Nonempty := by
        by_contra hempty
        have hactiveEmpty : active = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hempty
        have hdebtZero : ∀ who,
            quittingTerminalSemanticDebt base who = 0 := by
          intro who
          have hnotPositive : ¬ 0 < quittingTerminalSemanticDebt base who := by
            intro hpositive
            have hmem := (hactive who).2 hpositive
            rw [hactiveEmpty] at hmem
            simp at hmem
          exact le_antisymm (le_of_not_gt hnotPositive)
            (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
              (quittingRewardBound_nonneg reward)
              (abs_reward_le_quittingRewardBound reward) hbase who)
        unfold quittingTerminalSemanticDebtSum at hbasePositive
        simp only [hdebtZero, Finset.sum_const_zero] at hbasePositive
        exact (lt_irrefl 0) hbasePositive
      let column := quittingActiveDebtTangentExtension active tangent
      let gain := quittingActiveDebtTangentGain active tangent
      have hgain : ∀ mover ∈ active, 0 < gain mover := by
        intro mover hmover
        have hdiag := hdiagonal ⟨mover, hmover⟩
        have hdebtPos := (hactive mover).1 hmover
        dsimp only [gain, quittingActiveDebtTangentGain,
          column, quittingActiveDebtTangentExtension]
        simp only [hmover, dite_true]
        linarith
      have hmoverLoss : ∀ mover ∈ active,
          column mover mover = -gain mover := by
        intro mover hmover
        dsimp only [gain, quittingActiveDebtTangentGain]
        ring
      have hcolumnFlat : ∀ mover ∈ active,
          ∑ who, column mover who = 0 := by
        intro mover hmover
        dsimp only [column, quittingActiveDebtTangentExtension]
        simp only [hmover, dite_true]
        exact hflat ⟨mover, hmover⟩
      have hzeroTangent : ∀ mover ∈ active, ∀ observer,
          quittingTerminalSemanticDebt base observer = 0 →
            0 ≤ column mover observer := by
        intro mover hmover observer hzero
        dsimp only [column, quittingActiveDebtTangentExtension]
        simp only [hmover, dite_true]
        exact htangentInactive ⟨mover, hmover⟩ observer hzero
      by_cases hentry : HasQuittingStoppingLawFlatSupportEntry
          base active tangent
      · exact Or.inr (Or.inl ⟨hflat, hentry⟩)
      · have hdebtNonneg : ∀ who,
            0 ≤ quittingTerminalSemanticDebt base who :=
          quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
            (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward) hbase
        have hinactiveZero : ∀ mover ∈ active, ∀ who ∉ active,
            column mover who = 0 := by
          intro mover hmover who hwho
          have hdebtZero : quittingTerminalSemanticDebt base who = 0 := by
            apply le_antisymm
            · exact le_of_not_gt (fun hpositive ↦
                hwho ((hactive who).2 hpositive))
            · exact hdebtNonneg who
          apply le_antisymm
          · have hnotEntry : ¬ 0 < column mover who := by
              intro hpositive
              exact hentry ⟨mover, hmover, who, hdebtZero, hpositive⟩
            exact le_of_not_gt hnotEntry
          · exact hzeroTangent mover hmover who hdebtZero
        have hduality :=
          flatDebtTangent_chargedCirculation_xor_nonnegativePotential
            (fun mover : {who // who ∈ active} ↦ column mover.1)
            (fun mover : {who // who ∈ active} ↦ gain mover.1)
            (fun mover ↦ hcolumnFlat mover.1 mover.2)
        rcases hduality with
            ⟨hcirculation, _hnotPotential⟩ |
            ⟨hpotential, hnotCirculation⟩
        · exact Or.inr (Or.inr (Or.inl
            ⟨hflat, hentry, hcirculation⟩))
        · obtain ⟨potential, hpotentialNonneg, hpotential⟩ := hpotential
          obtain ⟨mover, hmover, hmoverMax⟩ :=
            Finset.exists_max_image active potential hactiveNonempty
          have hpotentialAll : ∀ source ∈ active,
              gain source ≤ ∑ who, potential who * column source who := by
            intro source hsource
            exact hpotential ⟨source, hsource⟩
          obtain ⟨other, hother, hotherDecrease⟩ :=
            exists_active_coDecrease_of_flat_chargedPotential_at_max
              active (column mover) potential mover (gain mover)
              (hcolumnFlat mover hmover) (hgain mover hmover)
              (hpotentialAll mover hmover) hmoverMax
              (hinactiveZero mover hmover)
          have hcoDecrease :
              HasQuittingStoppingLawFlatPotentialCoDecrease
                active tangent := by
            exact ⟨potential, mover, hmover, other, hother,
              hpotentialNonneg, hpotentialAll, hmoverMax,
              hmoverLoss mover hmover, hotherDecrease⟩
          exact Or.inr (Or.inr (Or.inr
            ⟨hflat, hentry, hnotCirculation, hcoDecrease⟩))
  have halternative := hfrontierBranch.toPipelineAlternative
  exact ⟨{
    seam := seam
    base := base
    profiles := profiles
    active := active
    lambda := lambda
    lambda_pos := hlambdaPos
    lambda_le_one := hlambdaLe
    bestResponse := bestResponse
    subseq := subseq
    tangent := tangent
    base_mem := hbase
    base_minimum := hminimum
    base_positive := hbasePositive
    base_allContinue_nash := hnash
    base_allContinue_prefix := hprefix
    profiles_tendsto := hprofiles
    active_iff := hactive
    subseq_strictMono := hsubseq
    lambda_subseq_tendsto_zero := hlambdaSubseq
    tangent_tendsto := htangent
    tangent_diagonal := hdiagonal
    tangent_inactive_nonneg := htangentInactive
    tangent_sum_nonneg := hsumNonneg
    exhaustive_branch := hfrontierBranch
    alternative := halternative }⟩

/-! ## Conjecture-level frontier anchor -/

/-- The maintained stopping-law residual, bundled without choosing a
counterexample regime separately.  Refinements of the branch predicate may
change the internal frontier, while the equivalence below remains the
conjecture-level bookkeeping target. -/
def QuittingUniformExistenceFrontier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  Σ regime : QuittingCounterexampleRegime reward,
    QuittingCounterexampleStoppingLawFrontier regime

/-- Nonexistence of a uniform-equilibrium payoff is exactly inhabitation of
the maintained exhaustive stopping-law frontier. -/
theorem not_exists_uniformEquilibriumPayoff_iff_nonempty_stoppingLawFrontier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (¬ ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      Nonempty (QuittingUniformExistenceFrontier reward) := by
  constructor
  · intro hno
    let regime := quittingCounterexampleRegimeOfNoUniformPayoff reward hno
    obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
    exact ⟨⟨regime, frontier⟩⟩
  · rintro ⟨⟨regime, _frontier⟩⟩
    exact regime.not_exists_uniformEquilibriumPayoff

/-- Equivalently, the quitting-game conjecture for this reward table is the
assertion that the maintained exhaustive frontier is empty. -/
theorem exists_uniformEquilibriumPayoff_iff_no_stoppingLawFrontier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ¬ Nonempty (QuittingUniformExistenceFrontier reward) := by
  constructor
  · intro hexists hfrontier
    exact
      (not_exists_uniformEquilibriumPayoff_iff_nonempty_stoppingLawFrontier
        reward).mpr hfrontier hexists
  · intro hfrontier
    by_contra hno
    exact hfrontier
      ((not_exists_uniformEquilibriumPayoff_iff_nonempty_stoppingLawFrontier
        reward).mp hno)

end GameTheory
