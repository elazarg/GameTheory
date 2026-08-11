/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFlatTangentAlternative

/-!
# Common-base extraction of stopping-law debt tangents

A single literal near-minimizing profile sequence is used for every active
debtor.  At each index, every active debtor receives an approximate best
response and is mixed at the same scale.  The normalized debt-change matrix
is uniformly bounded, so one common subsequence extracts all player columns.

The rate hypotheses are explicit:

* near-minimality error divided by the reset scale tends to zero;
* on coordinates which vanish at the limiting base, source debt divided by
  the reset scale tends to zero.

The extracted columns have a strictly negative mover diagonal, are
nonnegative on base-inactive coordinates, and have nonnegative total slope.
Thus either one column has positive total slope, or all columns are flat and
the finite alternative in `TerminalSemanticStoppingLawFlatTangentAlternative`
applies.  No minimum-face integration or chronology is asserted.
-/

noncomputable section

namespace GameTheory

open Filter Set
open Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal profile obtained by mixing one player's complete stopping law
toward a displayed replacement strategy. -/
def quittingStoppingLawResetProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (replacement : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile who
    (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
      replacement lambda hlambda0 hlambda1)

/-- Coordinatewise debt change divided by the stopping-law reset scale. -/
def quittingStoppingLawNormalizedDebtDirection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (replacement : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (observer : ι) : ℝ :=
  quittingTerminalSemanticDebtChange
      (quittingTerminalSemanticPair reward profile)
      (quittingTerminalSemanticPair reward
        (quittingStoppingLawResetProfile reward profile who replacement
          lambda hlambda0 hlambda1)) observer / lambda

/-- **Finite common-base stopping-law tangent extraction.** -/
theorem exists_commonBase_stoppingLawDebtTangentFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (active : Finset ι) (epsilon lambda : ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hbasePositive : 0 < quittingTerminalSemanticDebtSum base)
    (hprofiles : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds base))
    (hactive : ∀ who, who ∈ active ↔
      0 < quittingTerminalSemanticDebt base who)
    (hsourceActive : ∀ n, ∀ who ∈ active,
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who)
    (hnear : ∀ n, ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon n)
    (hlambdaPos : ∀ n, 0 < lambda n)
    (hlambdaLe : ∀ n, lambda n ≤ 1)
    (herrorRate : Tendsto (fun n ↦ epsilon n / lambda n)
      atTop (nhds 0))
    (hinactiveRate : ∀ who,
      quittingTerminalSemanticDebt base who = 0 →
      Tendsto (fun n ↦
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) who /
          lambda n) atTop (nhds 0)) :
    ∃ bestResponse : ∀ mover : {who // who ∈ active},
        ℕ → (quittingGame reward).BehaviorStrategy mover.1,
      ∃ subseq : ℕ → ℕ,
      ∃ tangent : {who // who ∈ active} → ι → ℝ,
        StrictMono subseq ∧
        (∀ mover observer,
          Tendsto (fun rank ↦
            quittingStoppingLawNormalizedDebtDirection reward
              (profiles (subseq rank)) mover.1
              (bestResponse mover (subseq rank)) (lambda (subseq rank))
              (hlambdaPos (subseq rank)).le (hlambdaLe (subseq rank)) observer)
            atTop (nhds (tangent mover observer))) ∧
        (∀ mover,
          tangent mover mover.1 ≤
            -quittingTerminalSemanticDebt base mover.1 / 2) ∧
        (∀ mover observer,
          quittingTerminalSemanticDebt base observer = 0 →
            0 ≤ tangent mover observer) ∧
        (∀ mover, 0 ≤ ∑ observer, tangent mover observer) ∧
        ((∃ mover, 0 < ∑ observer, tangent mover observer) ∨
          ∀ mover, ∑ observer, tangent mover observer = 0) := by
  have hactiveNonempty : active.Nonempty := by
    by_contra hempty
    have hemptyEq : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hbaseDebtZero : ∀ who,
        quittingTerminalSemanticDebt base who = 0 := by
      intro who
      have hnotPos : ¬ 0 < quittingTerminalSemanticDebt base who := by
        intro hpos
        have := (hactive who).2 hpos
        rw [hemptyEq] at this
        simp at this
      exact le_antisymm (le_of_not_gt hnotPos)
        (quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward hM hreward hbase who)
    have hsumZero : quittingTerminalSemanticDebtSum base = 0 := by
      unfold quittingTerminalSemanticDebtSum
      simp only [hbaseDebtZero, Finset.sum_const_zero]
    rw [hsumZero] at hbasePositive
    exact (lt_irrefl 0) hbasePositive
  have hchoice : ∀ n, ∀ mover : {who // who ∈ active},
      ∃ replacement : (quittingGame reward).BehaviorStrategy mover.1,
        quittingContinuationBestResponseValue reward (profiles n) mover.1 -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward (profiles n)) mover.1 / 2 ≤
          quittingTerminalPayoff reward
            (Function.update (profiles n) mover.1 replacement) mover.1 := by
    intro n mover
    apply exists_quittingContinuation_deviation_ge_sub
      (reward := reward) (continuation := profiles n) (who := mover.1)
      (δ := quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) mover.1 / 2)
      (M := M)
    exact div_pos (hsourceActive n mover.1 mover.2) (by norm_num)
    exact hM
    exact hreward
  choose bestResponse hbestResponse using hchoice
  let direction : ℕ → {who // who ∈ active} → ι → ℝ :=
    fun n mover observer ↦
      quittingStoppingLawNormalizedDebtDirection reward (profiles n) mover.1
        (bestResponse n mover) (lambda n) (hlambdaPos n).le (hlambdaLe n)
          observer
  let directionBox : Set ({who // who ∈ active} → ι → ℝ) :=
    Set.univ.pi fun _ ↦ Set.univ.pi fun _ ↦ Set.Icc (-4 * M) (4 * M)
  have hdirectionBoxCompact : IsCompact directionBox :=
    isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hdirectionBox : ∀ n, direction n ∈ directionBox := by
    intro n
    rw [Set.mem_univ_pi]
    intro mover
    rw [Set.mem_univ_pi]
    intro observer
    have hbound := abs_quittingTerminalSemanticDebt_stoppingLawMixture_sub_le
      reward (profiles n) mover.1 observer (bestResponse n mover)
        (lambda n) (hlambdaPos n).le (hlambdaLe n) hM hreward
    dsimp only [direction, quittingStoppingLawNormalizedDebtDirection,
      quittingStoppingLawResetProfile]
    have hnormalized :
        |quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward (profiles n))
            (quittingTerminalSemanticPair reward
              (Function.update (profiles n) mover.1
                (quittingStoppingLawMixtureBehaviorStrategy reward mover.1
                  ((profiles n) mover.1) (bestResponse n mover) (lambda n)
                    (hlambdaPos n).le (hlambdaLe n)))) observer / lambda n| ≤
          4 * M := by
      rw [abs_div, abs_of_pos (hlambdaPos n), div_le_iff₀ (hlambdaPos n)]
      simpa only [quittingTerminalSemanticDebtChange, mul_assoc] using hbound
    rw [abs_le] at hnormalized
    constructor <;> nlinarith [hnormalized.1, hnormalized.2]
  obtain ⟨tangent, _htangentBox, subseq, hsubseq, htangent⟩ :=
    hdirectionBoxCompact.tendsto_subseq hdirectionBox
  have htangentCoordinate : ∀ mover observer,
      Tendsto (fun rank ↦ direction (subseq rank) mover observer)
        atTop (nhds (tangent mover observer)) := by
    intro mover observer
    exact (tendsto_pi_nhds.1 ((tendsto_pi_nhds.1 htangent) mover)) observer
  have hsourceDebt : ∀ who, Tendsto (fun n ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who)
      atTop (nhds (quittingTerminalSemanticDebt base who)) := by
    intro who
    exact (continuous_quittingTerminalSemanticDebt who).tendsto base |>.comp
      hprofiles
  have hdiagonal : ∀ mover,
      tangent mover mover.1 ≤
        -quittingTerminalSemanticDebt base mover.1 / 2 := by
    intro mover
    have hpointwise : ∀ n, direction n mover mover.1 ≤
        -quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles n)) mover.1 / 2 := by
      intro n
      let endpoint := Function.update (profiles n) mover.1
        (bestResponse n mover)
      let endpointGain := quittingTerminalPayoff reward endpoint mover.1 -
        quittingTerminalPayoff reward (profiles n) mover.1
      have hgainLower : quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) mover.1 / 2 ≤
          endpointGain := by
        dsimp only [endpointGain, endpoint, quittingTerminalSemanticDebt,
          quittingTerminalSemanticPair] at hbestResponse ⊢
        linarith [hbestResponse n mover]
      have hself := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
        reward (profiles n) mover.1 ((profiles n) mover.1)
          (bestResponse n mover) (lambda n) (hlambdaPos n).le (hlambdaLe n)
      rw [Function.update_eq_self] at hself
      have hendpointDebt : quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward endpoint) mover.1 =
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward (profiles n)) mover.1 -
            endpointGain := by
        dsimp only [endpoint, endpointGain, quittingTerminalSemanticDebt,
          quittingTerminalSemanticPair]
        rw [quittingContinuationBestResponseValue_update_self]
        ring
      have hdirectionEq : direction n mover mover.1 = -endpointGain := by
        dsimp only [direction, quittingStoppingLawNormalizedDebtDirection,
          quittingStoppingLawResetProfile, quittingTerminalSemanticDebtChange]
        apply (div_eq_iff (ne_of_gt (hlambdaPos n))).2
        rw [hself, hendpointDebt]
        ring
      rw [hdirectionEq]
      linarith
    have hleft := htangentCoordinate mover mover.1
    have hright : Tendsto (fun rank ↦
        -quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles (subseq rank))) mover.1 / 2)
        atTop (nhds (-quittingTerminalSemanticDebt base mover.1 / 2)) := by
      simpa [Function.comp_def] using
        ((hsourceDebt mover.1).neg.div_const 2).comp hsubseq.tendsto_atTop
    exact le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall fun rank ↦ hpointwise (subseq rank))
  have hinactiveNonneg : ∀ mover observer,
      quittingTerminalSemanticDebt base observer = 0 →
        0 ≤ tangent mover observer := by
    intro mover observer hzero
    have hpointwise : ∀ n,
        -quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) observer /
              lambda n ≤
          direction n mover observer := by
      intro n
      have htargetNonneg := quittingTerminalDeviationDebt_nonneg reward
        (quittingStoppingLawResetProfile reward (profiles n) mover.1
          (bestResponse n mover) (lambda n) (hlambdaPos n).le (hlambdaLe n))
        observer hM hreward
      change 0 ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStoppingLawResetProfile reward (profiles n) mover.1
            (bestResponse n mover) (lambda n) (hlambdaPos n).le
              (hlambdaLe n))) observer at htargetNonneg
      dsimp only [direction, quittingStoppingLawNormalizedDebtDirection,
        quittingTerminalSemanticDebtChange]
      exact (div_le_div_iff_of_pos_right (hlambdaPos n)).2 (by linarith)
    have hleft : Tendsto (fun rank ↦
        -quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles (subseq rank))) observer /
          lambda (subseq rank)) atTop (nhds 0) := by
      simpa [Function.comp_def, neg_div] using
        (hinactiveRate observer hzero).neg.comp hsubseq.tendsto_atTop
    have hright := htangentCoordinate mover observer
    exact le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall fun rank ↦ hpointwise (subseq rank))
  have hsumDirection : ∀ n mover,
      (∑ observer, direction n mover observer) =
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingStoppingLawResetProfile reward (profiles n) mover.1
                (bestResponse n mover) (lambda n) (hlambdaPos n).le
                  (hlambdaLe n))) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (profiles n))) / lambda n := by
    intro n mover
    dsimp only [direction, quittingStoppingLawNormalizedDebtDirection]
    rw [← Finset.sum_div]
    unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebtChange
    rw [Finset.sum_sub_distrib]
  have hsumLimit : ∀ mover,
      Tendsto (fun rank ↦ ∑ observer,
          direction (subseq rank) mover observer)
        atTop (nhds (∑ observer, tangent mover observer)) := by
    intro mover
    exact tendsto_finsetSum Finset.univ fun observer _ ↦
      htangentCoordinate mover observer
  have hsumNonneg : ∀ mover, 0 ≤ ∑ observer, tangent mover observer := by
    intro mover
    have hpointwise : ∀ n,
        -(epsilon n / lambda n) ≤ ∑ observer, direction n mover observer := by
      intro n
      rw [hsumDirection]
      have htarget := quittingTerminalSemanticPair_mem_carrier reward
        (quittingStoppingLawResetProfile reward (profiles n) mover.1
          (bestResponse n mover) (lambda n) (hlambdaPos n).le (hlambdaLe n))
      have hnearTarget := hnear n _ htarget
      calc
        -(epsilon n / lambda n) = (-epsilon n) / lambda n := by ring
        _ ≤ (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingStoppingLawResetProfile reward (profiles n) mover.1
                  (bestResponse n mover) (lambda n) (hlambdaPos n).le
                    (hlambdaLe n))) -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward (profiles n))) / lambda n :=
          (div_le_div_iff_of_pos_right (hlambdaPos n)).2 (by linarith)
    have hleft : Tendsto (fun rank ↦ -(epsilon (subseq rank) /
        lambda (subseq rank))) atTop (nhds 0) := by
      simpa [Function.comp_def] using
        herrorRate.neg.comp hsubseq.tendsto_atTop
    exact le_of_tendsto_of_tendsto hleft (hsumLimit mover)
      (Eventually.of_forall fun rank ↦ hpointwise (subseq rank))
  have hslopeAlternative :
      (∃ mover, 0 < ∑ observer, tangent mover observer) ∨
        ∀ mover, ∑ observer, tangent mover observer = 0 := by
    by_cases hpos : ∃ mover, 0 < ∑ observer, tangent mover observer
    · exact Or.inl hpos
    · right
      intro mover
      exact le_antisymm (le_of_not_gt (fun hgt ↦ hpos ⟨mover, hgt⟩))
        (hsumNonneg mover)
  refine ⟨fun mover n ↦ bestResponse n mover, subseq, tangent,
    hsubseq, ?_, hdiagonal, hinactiveNonneg, hsumNonneg,
    hslopeAlternative⟩
  intro mover observer
  exact htangentCoordinate mover observer

/-! ## Extracted-family capstone -/

/-- Extend columns indexed by the positive-debt active subtype by zero on
inactive mover labels. -/
def quittingActiveDebtTangentExtension
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ)
    (mover observer : ι) : ℝ :=
  if hmover : mover ∈ active then tangent ⟨mover, hmover⟩ observer else 0

/-- The positive mover charge of an extracted active tangent is its negative
diagonal coordinate. -/
def quittingActiveDebtTangentGain
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ)
    (mover : ι) : ℝ :=
  -quittingActiveDebtTangentExtension active tangent mover mover

/-- Final finite alternative attached to one extracted common-base tangent
family.  The first branch is a genuinely positive normalized total-debt
slope.  All remaining branches use flat columns only. -/
def IsQuittingStoppingLawTangentPipelineAlternative
    (base : QuittingTerminalSemanticPair ι) (active : Finset ι)
    (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  (∃ mover, 0 < ∑ observer, tangent mover observer) ∨
    let column := quittingActiveDebtTangentExtension active tangent
    let gain := quittingActiveDebtTangentGain active tangent
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
        column mover other < 0

/-- **Produced stopping-law tangent pipeline alternative.**

The hypotheses are the explicit common-scale conditions of
`exists_commonBase_stoppingLawDebtTangentFamily`.  The output retains one
subsequence and every literal approximate-best-response stopping-law ray.
Its limiting family is then dispatched to positive total slope, zero-debt
support entry, an infinitesimal positive charged circulation, or a
nonnegative-potential same-column co-decrease. -/
theorem exists_commonBase_stoppingLawTangent_pipelineAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (active : Finset ι) (epsilon lambda : ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hbasePositive : 0 < quittingTerminalSemanticDebtSum base)
    (hprofiles : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds base))
    (hactive : ∀ who, who ∈ active ↔
      0 < quittingTerminalSemanticDebt base who)
    (hsourceActive : ∀ n, ∀ who ∈ active,
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who)
    (hnear : ∀ n, ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon n)
    (hlambdaPos : ∀ n, 0 < lambda n)
    (hlambdaLe : ∀ n, lambda n ≤ 1)
    (herrorRate : Tendsto (fun n ↦ epsilon n / lambda n)
      atTop (nhds 0))
    (hinactiveRate : ∀ who,
      quittingTerminalSemanticDebt base who = 0 →
      Tendsto (fun n ↦
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) who /
          lambda n) atTop (nhds 0)) :
    ∃ bestResponse : ∀ mover : {who // who ∈ active},
        ℕ → (quittingGame reward).BehaviorStrategy mover.1,
      ∃ subseq : ℕ → ℕ,
      ∃ tangent : {who // who ∈ active} → ι → ℝ,
        StrictMono subseq ∧
        (∀ mover observer,
          Tendsto (fun rank ↦
            quittingStoppingLawNormalizedDebtDirection reward
              (profiles (subseq rank)) mover.1
              (bestResponse mover (subseq rank)) (lambda (subseq rank))
              (hlambdaPos (subseq rank)).le (hlambdaLe (subseq rank)) observer)
            atTop (nhds (tangent mover observer))) ∧
        IsQuittingStoppingLawTangentPipelineAlternative base active tangent := by
  obtain ⟨bestResponse, subseq, tangent, hsubseq, htangent,
      hdiagonal, hinactiveNonneg, _hsumNonneg, hslope⟩ :=
    exists_commonBase_stoppingLawDebtTangentFamily
      reward base profiles active epsilon lambda hM hreward hbase
        hbasePositive hprofiles hactive hsourceActive hnear hlambdaPos
        hlambdaLe herrorRate hinactiveRate
  refine ⟨bestResponse, subseq, tangent, hsubseq, htangent, ?_⟩
  rcases hslope with hpositiveSlope | hflat
  · exact Or.inl hpositiveSlope
  · right
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
      exact hinactiveNonneg ⟨mover, hmover⟩ observer hzero
    exact stoppingLawFlatTangent_supportEntry_or_chargedCirculation_or_potentialCoDecrease
      reward base active column gain hM hreward hbase hbasePositive hactive
        hgain hmoverLoss hcolumnFlat hzeroTangent

end GameTheory
