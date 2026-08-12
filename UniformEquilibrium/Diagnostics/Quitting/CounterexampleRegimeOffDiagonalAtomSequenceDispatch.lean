/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalSlopeFrontier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeMarkedRowProvenance

/-!
# Vanishing-error dispatch for the off-diagonal atom frontier

The fixed positive off-diagonal tangent charge can be decoded without using
a fixed approximation error.  At rank `n` the pure-time response is chosen
within `charge / (8 * (n + 1))` of the endpoint envelope.  The rectangle
still carries the fixed `charge / 4` atom bound, while the observer's debt at
the literal target endpoint tends to zero.

After passing to a fixed terminal label, the rectangle branch has exactly
three unresolved orientations: the observer is absent, the terminal is a
singleton, or the observer's terminal reward is nonpositive.  The remaining
positive-reward collision orientation feeds the existing marked-tail
consumer with no extra debt-reset hypothesis.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The vanishing error budget used by the sequence decoder. -/
def quittingStoppingLawAtomDecoderError (charge : ℝ) (rank : ℕ) : ℝ :=
  (charge / 8) / (rank + 1 : ℝ)

theorem quittingStoppingLawAtomDecoderError_pos {charge : ℝ}
    (hcharge : 0 < charge) (rank : ℕ) :
    0 < quittingStoppingLawAtomDecoderError charge rank := by
  unfold quittingStoppingLawAtomDecoderError
  positivity

theorem quittingStoppingLawAtomDecoderError_le {charge : ℝ}
    (hcharge : 0 < charge) (rank : ℕ) :
    quittingStoppingLawAtomDecoderError charge rank ≤ charge / 8 := by
  unfold quittingStoppingLawAtomDecoderError
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < rank + 1)).2
  have hrank : (0 : ℝ) ≤ rank := by positivity
  nlinarith

theorem tendsto_quittingStoppingLawAtomDecoderError (charge : ℝ) :
    Tendsto (quittingStoppingLawAtomDecoderError charge) atTop (nhds 0) := by
  have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hmul : Tendsto
      (fun rank : ℕ ↦ (charge / 8) * (1 / ((rank : ℝ) + 1)))
      atTop (nhds 0) :=
    by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ charge / 8)
          atTop (nhds (charge / 8))).mul hbase)
  convert hmul using 1
  funext rank
  unfold quittingStoppingLawAtomDecoderError
  ring

/-- One rank of the strengthened decoder.  In the cap branch, the same
pure-time response carries both the fixed rectangle atom and a quantitative
upper bound on its own endpoint debt. -/
def HasQuittingStoppingLawVanishingDebtAtomAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℝ) : Prop :=
  (∃ terminal : {S : Finset ι // S.Nonempty},
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward profile
          (Function.update profile mover target) observer (some terminal)) ∨
  ∃ quitTime : Option ℕ, ∃ terminal : {S : Finset ι // S.Nonempty},
    charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          (Function.update (Function.update profile mover (profile mover)) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          observer (some terminal) ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))) observer ≤
      error

/-- The positive-slope atom decoder with an arbitrary sufficiently small
positive approximation error. -/
theorem exists_prescribedAtom_or_pureTimeRectangleAtom_with_debtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge error : ℝ) (hlambda0 : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hcharge : 0 < charge)
    (herror : 0 < error) (herrorLe : error ≤ charge / 8)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward profile mover
      observer target charge error := by
  let endpoint := Function.update profile mover target
  let mixed := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (profile mover) target lambda hlambda0.le hlambda1)
  let sourcePair := quittingTerminalSemanticPair reward profile
  let endpointPair := quittingTerminalSemanticPair reward endpoint
  let mixedPair := quittingTerminalSemanticPair reward mixed
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1 hM hreward
  rw [Function.update_eq_self] at hchord
  change quittingTerminalSemanticDebt mixedPair observer ≤
      (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
        lambda * quittingTerminalSemanticDebt endpointPair observer at hchord
  have hendpointSlope : charge ≤
      quittingTerminalSemanticDebt endpointPair observer -
        quittingTerminalSemanticDebt sourcePair observer := by
    change lambda * charge ≤
      quittingTerminalSemanticDebt mixedPair observer -
        quittingTerminalSemanticDebt sourcePair observer at hslope
    have hscaled : lambda * charge ≤ lambda *
        (quittingTerminalSemanticDebt endpointPair observer -
          quittingTerminalSemanticDebt sourcePair observer) := by
      nlinarith
    nlinarith
  let sourceCap := quittingContinuationBestResponseValue reward profile observer
  let endpointCap := quittingContinuationBestResponseValue reward endpoint observer
  let sourcePayoff := quittingTerminalPayoff reward profile observer
  let endpointPayoff := quittingTerminalPayoff reward endpoint observer
  have hsplit : charge ≤
      (endpointCap - sourceCap) + (sourcePayoff - endpointPayoff) := by
    dsimp only [sourcePair, endpointPair, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair] at hendpointSlope
    dsimp only [sourceCap, endpointCap, sourcePayoff, endpointPayoff]
    linarith
  by_cases hpayoff : charge / 2 ≤ sourcePayoff - endpointPayoff
  · exact Or.inl (exists_absorbingTerminalPayoffDifferenceAtom reward profile
      endpoint observer (charge / 2) (by positivity) hpayoff)
  · right
    have hcap : charge / 2 < endpointCap - sourceCap := by linarith
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingContinuation_deviation_ge_sub reward endpoint observer
        (half_pos herror) hM hreward
    obtain ⟨quitTime, hquitTime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        reward endpoint observer deviation (half_pos herror)
    let pureDeviation :=
      quittingPureTimeBehaviorStrategy reward observer quitTime
    have hsourceBound :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile observer pureDeviation hM hreward
    have hpureEndpoint : endpointCap - error ≤
        quittingTerminalPayoff reward
          (Function.update endpoint observer pureDeviation) observer := by
      dsimp only [pureDeviation]
      linarith
    have hrectangle : charge / 4 ≤
        quittingTerminalPayoff reward
            (Function.update endpoint observer pureDeviation) observer -
          quittingTerminalPayoff reward
            (Function.update profile observer pureDeviation) observer := by
      dsimp only [sourceCap] at hcap hsourceBound
      linarith
    obtain ⟨terminal, hterminal⟩ :=
      exists_absorbingTerminalPayoffDifferenceAtom reward
        (Function.update endpoint observer pureDeviation)
        (Function.update profile observer pureDeviation) observer
        (charge / 4) (by positivity) hrectangle
    have hdebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update endpoint observer pureDeviation)) observer ≤ error := by
      unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
      change quittingContinuationBestResponseValue reward
          (Function.update endpoint observer pureDeviation) observer -
        quittingTerminalPayoff reward
          (Function.update endpoint observer pureDeviation) observer ≤ error
      rw [quittingContinuationBestResponseValue_update_self]
      dsimp only [endpointCap] at hpureEndpoint
      linarith
    refine ⟨quitTime, terminal, ?_, ?_⟩
    · simpa only [endpoint, pureDeviation, Function.update_eq_self] using hterminal
    · simpa only [endpoint, pureDeviation] using hdebt

/-- The strengthened decoder holds eventually on the fixed tangent column.
Unlike the older fixed-error decoder, its rectangle endpoint is an
asymptotic best response for the observer. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_fixedVanishingDebtAtomAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    ∃ (mover : {who // who ∈ frontier.active}) (observer : ι) (charge : ℝ),
      observer ≠ mover.1 ∧ 0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawVanishingDebtAtomAlternative reward
          (frontier.profiles (frontier.subseq rank)) mover.1 observer
          (frontier.bestResponse mover (frontier.subseq rank)) charge
          (quittingStoppingLawAtomDecoderError charge rank) := by
  classical
  have hactiveNonempty : frontier.active.Nonempty := by
    by_contra hempty
    have hactiveEmpty : frontier.active = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hdebtZero : ∀ who,
        quittingTerminalSemanticDebt frontier.base who = 0 := by
      intro who
      have hnotPositive :
          ¬0 < quittingTerminalSemanticDebt frontier.base who := by
        intro hpositive
        have hmem := (frontier.active_iff who).2 hpositive
        rw [hactiveEmpty] at hmem
        simp at hmem
      exact le_antisymm (le_of_not_gt hnotPositive)
        (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward)
          frontier.base_mem who)
    have hbasePositive := frontier.base_positive
    unfold quittingTerminalSemanticDebtSum at hbasePositive
    simp only [hdebtZero, Finset.sum_const_zero] at hbasePositive
    exact (lt_irrefl 0) hbasePositive
  obtain ⟨mover, hmover⟩ := hactiveNonempty
  let activeMover : {who // who ∈ frontier.active} := ⟨mover, hmover⟩
  obtain ⟨observer, hobserverNe, hpositive⟩ :=
    frontier.exists_positiveOffDiagonal hmover
  let charge := frontier.tangent activeMover observer / 2
  have hcharge : 0 < charge := div_pos hpositive (by norm_num)
  have hchargeLt : charge < frontier.tangent activeMover observer := by
    dsimp only [charge, activeMover]
    linarith
  have heventuallySlope : ∀ᶠ rank in atTop,
      charge ≤ quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover
        (frontier.bestResponse activeMover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer :=
    (frontier.tangent_tendsto activeMover observer).eventually
      (Ioi_mem_nhds hchargeLt) |>.mono fun _ hlt ↦ hlt.le
  refine ⟨activeMover, observer, charge, hobserverNe, hcharge, ?_⟩
  filter_upwards [heventuallySlope] with rank hslopeNormalized
  have hlambda := frontier.lambda_pos (frontier.subseq rank)
  have hslope : frontier.lambda (frontier.subseq rank) * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (frontier.profiles (frontier.subseq rank)) mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (frontier.profiles (frontier.subseq rank) mover)
                (frontier.bestResponse activeMover (frontier.subseq rank))
                (frontier.lambda (frontier.subseq rank)) hlambda.le
                (frontier.lambda_le_one (frontier.subseq rank))))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) observer := by
    unfold quittingStoppingLawNormalizedDebtDirection
      quittingTerminalSemanticDebtChange quittingStoppingLawResetProfile
      at hslopeNormalized
    have hscaled := (le_div_iff₀ hlambda).mp hslopeNormalized
    nlinarith
  exact exists_prescribedAtom_or_pureTimeRectangleAtom_with_debtBound
    reward (frontier.profiles (frontier.subseq rank)) mover observer
      (frontier.bestResponse activeMover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank)) charge
      (quittingStoppingLawAtomDecoderError charge rank) hlambda
      (frontier.lambda_le_one (frontier.subseq rank)) hcharge
      (quittingStoppingLawAtomDecoderError_pos hcharge rank)
      (quittingStoppingLawAtomDecoderError_le hcharge rank)
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hslope

/-! ## Fixed-label sequence extraction -/

/-- A fixed tangent column carrying prescribed-payoff atoms along a literal
strict subsequence.  The terminal label is allowed to vary; this branch has
not yet acquired a strategic sign. -/
structure QuittingStoppingLawPrescribedAtomSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  mover : {who // who ∈ frontier.active}
  observer : ι
  charge : ℝ
  observer_ne_mover : observer ≠ mover.1
  charge_pos : 0 < charge
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  terminal : {S : Finset ι // S.Nonempty}
  atom_bound : ∀ n,
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (frontier.profiles (frontier.subseq (rank n)))
          (Function.update (frontier.profiles (frontier.subseq (rank n)))
            mover.1 (frontier.bestResponse mover
              (frontier.subseq (rank n))))
          observer (some terminal)

/-- A fixed terminal rectangle along a literal strict subsequence.  Its
positive atom bound is uniform and the pure-time observer is an asymptotic
best response at the target endpoint. -/
structure QuittingStoppingLawVanishingDebtRectangleSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  mover : {who // who ∈ frontier.active}
  observer : ι
  charge : ℝ
  observer_ne_mover : observer ≠ mover.1
  charge_pos : 0 < charge
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  quitTime : ℕ → Option ℕ
  terminal : {S : Finset ι // S.Nonempty}
  atom_bound : ∀ n,
    charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (rank n))) mover.1
              (frontier.bestResponse mover (frontier.subseq (rank n))))
            observer
            (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (rank n))) mover.1
              (frontier.profiles (frontier.subseq (rank n)) mover.1))
            observer
            (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
          observer (some terminal)
  observer_debt_tendsto_zero : Tendsto (fun n ↦
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update
          (Function.update
            (frontier.profiles (frontier.subseq (rank n))) mover.1
            (frontier.bestResponse mover (frontier.subseq (rank n))))
          observer
          (quittingPureTimeBehaviorStrategy reward observer (quitTime n))))
      observer) atTop (nhds 0)

/-- **Fixed-label sequence dispatch.**  The unconditional off-diagonal
tangent column yields either prescribed atoms infinitely often or a fixed
terminal pure-time rectangle sequence whose observer debt vanishes. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
      Nonempty (QuittingStoppingLawVanishingDebtRectangleSequence frontier) := by
  classical
  obtain ⟨mover, observer, charge, hobserverNe, hcharge, halternative⟩ :=
    frontier.exists_fixedVanishingDebtAtomAlternative
  let Prescribed : ℕ → Prop := fun rank ↦
    ∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 2 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (frontier.profiles (frontier.subseq rank))
            (Function.update (frontier.profiles (frontier.subseq rank)) mover.1
              (frontier.bestResponse mover (frontier.subseq rank)))
            observer (some terminal)
  let Rectangle : ℕ → Prop := fun rank ↦
    ∃ quitTime : Option ℕ, ∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update
              (Function.update (frontier.profiles (frontier.subseq rank))
                mover.1 (frontier.bestResponse mover (frontier.subseq rank)))
              observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime))
            (Function.update
              (Function.update (frontier.profiles (frontier.subseq rank))
                mover.1 (frontier.profiles (frontier.subseq rank) mover.1))
              observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime))
            observer (some terminal) ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (Function.update (frontier.profiles (frontier.subseq rank))
                mover.1 (frontier.bestResponse mover (frontier.subseq rank)))
              observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime)))
          observer ≤ quittingStoppingLawAtomDecoderError charge rank
  have hlocal : ∀ᶠ rank in atTop, Prescribed rank ∨ Rectangle rank := by
    simpa only [Prescribed, Rectangle,
      HasQuittingStoppingLawVanishingDebtAtomAlternative] using halternative
  by_cases hprescribed : ∃ᶠ rank in atTop, Prescribed rank
  · obtain ⟨rank, hrank, hatom⟩ :=
      extraction_of_frequently_atTop hprescribed
    choose terminalAt hterminalAt using hatom
    letI : TopologicalSpace {S : Finset ι // S.Nonempty} := ⊥
    letI : DiscreteTopology {S : Finset ι // S.Nonempty} :=
      discreteTopology_bot _
    obtain ⟨terminal, terminalSubseq, hterminalSubseq,
      hterminalTendsto⟩ := CompactSpace.tendsto_subseq terminalAt
    have hterminalEventually : ∀ᶠ n in atTop,
        terminalAt (terminalSubseq n) = terminal := by
      have hsingleton : ({terminal} : Set {S : Finset ι // S.Nonempty}) ∈
          nhds terminal := by
        have hopen : IsOpen ({terminal} :
            Set {S : Finset ι // S.Nonempty}) :=
          discreteTopology_iff_isOpen_singleton.mp inferInstance terminal
        exact hopen.mem_nhds rfl
      have hmem := hterminalTendsto.eventually hsingleton
      filter_upwards [hmem] with n hn
      exact hn
    obtain ⟨labelStart, hlabelStart⟩ :=
      eventually_atTop.1 hterminalEventually
    let fixedRank : ℕ → ℕ := fun n ↦ rank (terminalSubseq (n + labelStart))
    have hfixedRank : StrictMono fixedRank := by
      intro first second hlt
      dsimp only [fixedRank]
      exact hrank (hterminalSubseq (Nat.add_lt_add_right hlt labelStart))
    have hfixedAtom : ∀ n,
        charge / 2 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward
              (frontier.profiles (frontier.subseq (fixedRank n)))
              (Function.update
                (frontier.profiles (frontier.subseq (fixedRank n))) mover.1
                (frontier.bestResponse mover
                  (frontier.subseq (fixedRank n))))
              observer (some terminal) := by
      intro n
      have h := hterminalAt (terminalSubseq (n + labelStart))
      rw [hlabelStart (n + labelStart) (Nat.le_add_left labelStart n)] at h
      simpa only [fixedRank] using h
    exact Or.inl ⟨⟨mover, observer, charge, hobserverNe, hcharge,
      fixedRank, hfixedRank, terminal, hfixedAtom⟩⟩
  · have hnotPrescribed : ∀ᶠ rank in atTop, ¬Prescribed rank :=
      Filter.not_frequently.mp hprescribed
    have hrectangle : ∀ᶠ rank in atTop, Rectangle rank := by
      filter_upwards [hlocal, hnotPrescribed] with rank hbranch hnot
      exact hbranch.resolve_left hnot
    obtain ⟨start, hstart⟩ := eventually_atTop.1 hrectangle
    have hchoice : ∀ n, Rectangle (n + start) := by
      intro n
      exact hstart (n + start) (Nat.le_add_left start n)
    choose quitTimeAt terminalAt hatomAt hdebtAt using hchoice
    letI : TopologicalSpace {S : Finset ι // S.Nonempty} := ⊥
    letI : DiscreteTopology {S : Finset ι // S.Nonempty} :=
      discreteTopology_bot _
    obtain ⟨terminal, terminalSubseq, hterminalSubseq,
      hterminalTendsto⟩ := CompactSpace.tendsto_subseq terminalAt
    have hterminalEventually : ∀ᶠ n in atTop,
        terminalAt (terminalSubseq n) = terminal := by
      have hsingleton : ({terminal} : Set {S : Finset ι // S.Nonempty}) ∈
          nhds terminal := by
        have hopen : IsOpen ({terminal} :
            Set {S : Finset ι // S.Nonempty}) :=
          discreteTopology_iff_isOpen_singleton.mp inferInstance terminal
        exact hopen.mem_nhds rfl
      have hmem := hterminalTendsto.eventually hsingleton
      filter_upwards [hmem] with n hn
      exact hn
    obtain ⟨labelStart, hlabelStart⟩ :=
      eventually_atTop.1 hterminalEventually
    let rank : ℕ → ℕ := fun n ↦ terminalSubseq (n + labelStart) + start
    let quitTime : ℕ → Option ℕ := fun n ↦
      quitTimeAt (terminalSubseq (n + labelStart))
    have hrank : StrictMono rank := by
      intro first second hlt
      dsimp only [rank]
      exact Nat.add_lt_add_right
        (hterminalSubseq (Nat.add_lt_add_right hlt labelStart)) start
    have hterminalEq : ∀ n,
        terminalAt (terminalSubseq (n + labelStart)) = terminal := by
      intro n
      exact hlabelStart (n + labelStart) (Nat.le_add_left labelStart n)
    have hatom : ∀ n,
        charge / 4 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward
              (Function.update
                (Function.update
                  (frontier.profiles (frontier.subseq (rank n))) mover.1
                  (frontier.bestResponse mover (frontier.subseq (rank n))))
                observer
                (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
              (Function.update
                (Function.update
                  (frontier.profiles (frontier.subseq (rank n))) mover.1
                  (frontier.profiles (frontier.subseq (rank n)) mover.1))
                observer
                (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
              observer (some terminal) := by
      intro n
      have h := hatomAt (terminalSubseq (n + labelStart))
      rw [hterminalEq n] at h
      simpa only [rank, quitTime] using h
    have herror : Tendsto
        (fun n ↦ quittingStoppingLawAtomDecoderError charge (rank n))
        atTop (nhds 0) :=
      (tendsto_quittingStoppingLawAtomDecoderError charge).comp
        hrank.tendsto_atTop
    have hdebt : Tendsto (fun n ↦
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (Function.update
                (frontier.profiles (frontier.subseq (rank n))) mover.1
                (frontier.bestResponse mover (frontier.subseq (rank n))))
              observer
              (quittingPureTimeBehaviorStrategy reward observer (quitTime n))))
          observer) atTop (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact quittingTerminalDeviationDebt_nonneg reward _ observer
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward)
      · intro n
        simpa only [rank, quitTime] using
          hdebtAt (terminalSubseq (n + labelStart))
      · exact herror
    exact Or.inr ⟨⟨mover, observer, charge, hobserverNe, hcharge,
      rank, hrank, quitTime, terminal, hatom, hdebt⟩⟩

/-! ## Exhaustive terminal orientation -/

/-- The three terminal orientations not consumed by the marked positive-row
theorem.  They are deliberately stated on the fixed literal terminal label. -/
def HasQuittingStoppingLawOpenRectangleOrientation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) : Prop :=
  packet.observer ∉ packet.terminal.val ∨
    packet.terminal.val.card = 1 ∨
    reward packet.terminal packet.observer ≤ 0

/-- A fixed rectangle label is either one of the three open orientations or
is precisely a positive-reward collision containing the observer. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.openOrientation_or_positiveTargetCollision
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    HasQuittingStoppingLawOpenRectangleOrientation packet ∨
      (packet.observer ∈ packet.terminal.val ∧
        1 < packet.terminal.val.card ∧
        0 < reward packet.terminal packet.observer) := by
  classical
  by_cases hobserver : packet.observer ∈ packet.terminal.val
  · by_cases hcollision : 1 < packet.terminal.val.card
    · by_cases hreward : 0 < reward packet.terminal packet.observer
      · exact Or.inr ⟨hobserver, hcollision, hreward⟩
      · exact Or.inl (Or.inr (Or.inr (le_of_not_gt hreward)))
    · have hnonempty : 0 < packet.terminal.val.card :=
        Finset.card_pos.mpr packet.terminal.property
      have hsingleton : packet.terminal.val.card = 1 := by omega
      exact Or.inl (Or.inr (Or.inl hsingleton))
  · exact Or.inl (Or.inl hobserver)

/-! ## Positive-collision consumer -/

/-- The literal target endpoint before inserting the observer's pure-time
response.  In particular, a later prefix-stack construction can target this
unchanged suffix profile. -/
def quittingStoppingLawRectangleTargetProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (frontier.profiles (frontier.subseq (packet.rank n)))
    packet.mover.1
    (frontier.bestResponse packet.mover (frontier.subseq (packet.rank n)))

/-- The named output of the marked-row consumer on the fixed literal suffix
sequence. -/
def HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (lower : ℝ) : Prop :=
  ∃ (stop : ℕ → ℕ) (cluster : QuittingTerminalSemanticPair ι)
      (subseq : ℕ → ℕ),
    cluster ∈ quittingTerminalSemanticCarrier reward ∧
    StrictMono subseq ∧
    (∀ᶠ rank in atTop,
      packet.quitTime (subseq rank) = some (stop (subseq rank))) ∧
    (∀ᶠ rank in atTop, lower ≤
      quittingStageCoalitionMass reward
        (Function.update
          (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
          packet.observer
          (quittingPureTimeBehaviorStrategy reward packet.observer
            (packet.quitTime (subseq rank))))
        (stop (subseq rank)) packet.terminal) ∧
    Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (Function.update
            (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
            packet.observer
            (quittingPureTimeBehaviorStrategy reward packet.observer
              (packet.quitTime (subseq rank))))
          (stop (subseq rank) + 1)))
      atTop (nhds cluster) ∧
    Tendsto (fun rank ↦
      let deviated := Function.update
        (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
        packet.observer
        (quittingPureTimeBehaviorStrategy reward packet.observer
          (packet.quitTime (subseq rank)))
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward deviated
            (stop (subseq rank) + 1))).1
        (quittingProfileLiveRoot reward deviated (stop (subseq rank)))
        packet.observer) atTop (nhds 0) ∧
    (quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum cluster ∨
      quittingTerminalSemanticDebtSum cluster =
          quittingTerminalSemanticDebtSum frontier.base ∧
        ∀ᶠ rank in atTop,
          lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
            ∑ other ∈ Finset.univ.erase packet.observer,
              let deviated := Function.update
                (quittingStoppingLawRectangleTargetProfile packet
                  (subseq rank)) packet.observer
                (quittingPureTimeBehaviorStrategy reward packet.observer
                  (packet.quitTime (subseq rank)))
              quittingRootCoordinateNashDefect reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward deviated
                    (stop (subseq rank) + 1))).1
                (quittingProfileLiveRoot reward deviated
                  (stop (subseq rank))) other)

/-- **Positive-collision branch closure to a named consumer.**  If the fixed
rectangle terminal contains the observer, is a collision, and pays the
observer positively, its uniform signed atom supplies persistent target mass.
Together with the vanishing endpoint debt, this is exactly the existing
marked-tail escape/other-defect alternative. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.positiveTargetCollision_markedTailDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hobserver : packet.observer ∈ packet.terminal.val)
    (hcollision : 1 < packet.terminal.val.card)
    (hrewardPositive : 0 < reward packet.terminal packet.observer) :
    HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch packet
      ((packet.charge / 4) /
        ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingRewardBound reward)) := by
  classical
  let card : ℝ := Fintype.card (QuittingTerminalOutcome ι)
  let M := quittingRewardBound reward
  let lower := (packet.charge / 4) / (card * M)
  have hcard : 0 < card := by
    dsimp only [card]
    exact_mod_cast Fintype.card_pos
  have hrewardLe : reward packet.terminal packet.observer ≤ M := by
    exact (le_abs_self _).trans
      (abs_reward_le_quittingRewardBound reward packet.terminal packet.observer)
  have hMpos : 0 < M := hrewardPositive.trans_le hrewardLe
  have hlower : 0 < lower := by
    dsimp only [lower]
    exact div_pos (div_pos packet.charge_pos (by norm_num))
      (mul_pos hcard hMpos)
  have hpersistent : ∀ᶠ n in atTop, lower ≤
      quittingTerminalOutcomeMass reward
        (Function.update
          (quittingStoppingLawRectangleTargetProfile packet n)
          packet.observer
          (quittingPureTimeBehaviorStrategy reward packet.observer
            (packet.quitTime n))) (some packet.terminal) := by
    apply Eventually.of_forall
    intro n
    let targetProfile := Function.update
      (quittingStoppingLawRectangleTargetProfile packet n) packet.observer
      (quittingPureTimeBehaviorStrategy reward packet.observer
        (packet.quitTime n))
    let sourceProfile := Function.update
      (frontier.profiles (frontier.subseq (packet.rank n))) packet.observer
      (quittingPureTimeBehaviorStrategy reward packet.observer
        (packet.quitTime n))
    let targetMass := quittingTerminalOutcomeMass reward targetProfile
      (some packet.terminal)
    let sourceMass := quittingTerminalOutcomeMass reward sourceProfile
      (some packet.terminal)
    have hbound := packet.atom_bound n
    have hsourceUpdate : Function.update
        (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
        (frontier.profiles (frontier.subseq (packet.rank n)) packet.mover.1) =
        frontier.profiles (frontier.subseq (packet.rank n)) :=
      Function.update_eq_self _ _
    rw [hsourceUpdate] at hbound
    change packet.charge / 4 ≤ card *
      ((targetMass - sourceMass) *
        reward packet.terminal packet.observer) at hbound
    have htargetNonneg : 0 ≤ targetMass :=
      (quittingTerminalOutcomeMass_mem_stdSimplex reward targetProfile).1
        (some packet.terminal)
    have hsourceNonneg : 0 ≤ sourceMass :=
      (quittingTerminalOutcomeMass_mem_stdSimplex reward sourceProfile).1
        (some packet.terminal)
    have hdiffRewardLe :
        (targetMass - sourceMass) * reward packet.terminal packet.observer ≤
          targetMass * M := by
      have hdiffLe : targetMass - sourceMass ≤ targetMass := by linarith
      have hleft := mul_le_mul_of_nonneg_right hdiffLe hrewardPositive.le
      have hright := mul_le_mul_of_nonneg_left hrewardLe htargetNonneg
      exact hleft.trans hright
    have hscaled := mul_le_mul_of_nonneg_left hdiffRewardLe hcard.le
    have htotal : packet.charge / 4 ≤ card * (targetMass * M) :=
      hbound.trans hscaled
    apply (div_le_iff₀ (mul_pos hcard hMpos)).2
    change packet.charge / 4 ≤ targetMass * (card * M)
    calc
      packet.charge / 4 ≤ card * (targetMass * M) := htotal
      _ = targetMass * (card * M) := by ring
  have hconsumer := exists_markedTailCluster_escape_or_otherNashDefect
    reward frontier.base
      (quittingStoppingLawRectangleTargetProfile packet)
      packet.observer packet.quitTime packet.terminal hobserver hlower
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) frontier.base_mem
      frontier.base_minimum frontier.base_positive hcollision
      packet.observer_debt_tendsto_zero hpersistent
  simpa only [HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch,
    lower, card, M] using hconsumer

/-- **Sequence-level strategic dispatch.**  The unconditional off-diagonal
atom frontier now has a fixed-label exhaustive output.  The positive-reward
collision orientation is consumed; precisely the three explicit rectangle
orientations above and the prescribed-payoff atom sequence remain open. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_prescribedAtomSequence_or_openRectangleOrientation_or_markedTailDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
      ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
        HasQuittingStoppingLawOpenRectangleOrientation packet ∨
          HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch packet
            ((packet.charge / 4) /
              ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
                quittingRewardBound reward)) := by
  classical
  rcases frontier.exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence
      with hprescribed | hrectangle
  · exact Or.inl hprescribed
  · obtain ⟨packet⟩ := hrectangle
    refine Or.inr ⟨packet, ?_⟩
    rcases packet.openOrientation_or_positiveTargetCollision with hopen |
      ⟨hobserver, hcollision, hreward⟩
    · exact Or.inl hopen
    · exact Or.inr
        (packet.positiveTargetCollision_markedTailDispatch hobserver hcollision
          hreward)

end GameTheory
