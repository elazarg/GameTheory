/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeExhaustiveFrontier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeCausalRegression

/-!
# Fixed positive off-diagonal atoms from the stopping-law frontier

Every counterexample stopping-law frontier has a fixed positive off-diagonal
coordinate.  Indeed, an active mover has a strictly negative diagonal tangent;
if no zero-debt coordinate receives positive tangent, inactive-coordinate
nonnegativity makes every other coordinate zero, contradicting flatness.

Thus the maintained endpoint is a literal positive off-diagonal atom
alternative.  The one-debt-owner corollary below additionally records the
positive-total-slope versus flat-support-entry dichotomy; neither theorem
manufactures co-realized terminal incidence at the recipient.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal output of the positive coordinate-slope decoder, packaged so
it can be transported along the fixed subsequence of a counterexample
frontier. -/
def HasQuittingStoppingLawDebtSlopeAtomAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge : ℝ) : Prop :=
  (∃ terminal : {S : Finset ι // S.Nonempty},
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward profile
          (Function.update profile mover target) observer (some terminal)) ∨
  ((∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update (Function.update profile mover target) observer
              (quittingPureTimeBehaviorStrategy reward observer none))
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer none))
            observer (some terminal)) ∨
    ∃ stop : ℕ, ∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update (Function.update profile mover target) observer
              (quittingPureTimeBehaviorStrategy reward observer (some stop)))
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer (some stop)))
            observer (some terminal))

/-- Every active reset column of a counterexample frontier has a strictly
positive off-diagonal coordinate.  This uses only its negative diagonal and
nonnegative total sum; none of the four tagged branch cases is needed. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_positiveOffDiagonal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    {mover : ι} (hmover : mover ∈ frontier.active) :
    ∃ observer, observer ≠ mover ∧
      0 < frontier.tangent ⟨mover, hmover⟩ observer := by
  classical
  have hdiagonal : frontier.tangent ⟨mover, hmover⟩ mover < 0 := by
    have hbound := frontier.tangent_diagonal ⟨mover, hmover⟩
    have hdebt := (frontier.active_iff mover).1 hmover
    linarith
  by_contra hnone
  push Not at hnone
  have hnonpos : ∀ observer ∈ (Finset.univ : Finset ι),
      frontier.tangent ⟨mover, hmover⟩ observer ≤ 0 := by
    intro observer _hobserver
    by_cases heq : observer = mover
    · subst observer
      exact hdiagonal.le
    · exact hnone observer heq
  have hsumNeg :
      (∑ observer, frontier.tangent ⟨mover, hmover⟩ observer) < 0 :=
    Finset.sum_neg' hnonpos
      ⟨mover, Finset.mem_univ mover, hdiagonal⟩
  exact (not_lt_of_ge (frontier.tangent_sum_nonneg ⟨mover, hmover⟩)) hsumNeg

/-- **Fixed-column atom adapter.**  One mover and one distinct observer can be
selected once on the common tangent family.  Along the already extracted
literal subsequence, their positive normalized coordinate slope eventually
feeds the existing prescribed-atom/pure-time-rectangle decoder with one
fixed positive charge. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_fixedAtomAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    ∃ (mover : {who // who ∈ frontier.active}) (observer : ι) (charge : ℝ),
      observer ≠ mover.1 ∧ 0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawDebtSlopeAtomAlternative reward
          (frontier.profiles (frontier.subseq rank)) mover.1 observer
          (frontier.bestResponse mover (frontier.subseq rank)) charge := by
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
      (Ioi_mem_nhds hchargeLt) |>.mono fun _ hlt => hlt.le
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
      quittingTerminalSemanticDebtChange quittingStoppingLawResetProfile at hslopeNormalized
    have hscaled := (le_div_iff₀ hlambda).mp hslopeNormalized
    nlinarith
  simpa only [HasQuittingStoppingLawDebtSlopeAtomAlternative] using
    (exists_prescribedAtom_or_pureTimeRectangleAtom_of_stoppingLawDebtSlope
      reward (frontier.profiles (frontier.subseq rank)) mover observer
        (frontier.bestResponse activeMover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank)) charge hlambda
        (frontier.lambda_le_one (frontier.subseq rank)) hcharge
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) hslope)

/-- **One-debt-owner frontier collapse.**  If the active positive-debt support
has cardinality at most one, charged circulation and potential co-decrease are
impossible.  The original common-base tangent family is retained unchanged. -/
/- A counterexample regime reaches a stopping-law frontier and therefore a
fixed positive off-diagonal literal atom alternative on that frontier. -/
theorem QuittingCounterexampleRegime.exists_stoppingLaw_fixedAtomAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
      ∃ (mover : {who // who ∈ frontier.active}) (observer : ι) (charge : ℝ),
        observer ≠ mover.1 ∧ 0 < charge ∧
          ∀ᶠ rank in atTop,
            HasQuittingStoppingLawDebtSlopeAtomAlternative reward
              (frontier.profiles (frontier.subseq rank)) mover.1 observer
              (frontier.bestResponse mover (frontier.subseq rank)) charge := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
  obtain ⟨mover, observer, charge, hne, hcharge, heventually⟩ :=
    frontier.exists_fixedAtomAlternative
  exact ⟨frontier, mover, observer, charge, hne, hcharge, heventually⟩

theorem QuittingCounterexampleStoppingLawFrontier.oneDebtOwner_dichotomy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hcard : frontier.active.card ≤ 1) :
    (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) ∨
      ((∀ mover, ∑ observer, frontier.tangent mover observer = 0) ∧
        HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.active frontier.tangent) := by
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
  obtain ⟨owner, howner⟩ := hactiveNonempty
  have hflatNoEntryFalse :
      ¬((∀ mover, ∑ observer, frontier.tangent mover observer = 0) ∧
        ¬HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.active frontier.tangent) := by
    rintro ⟨hflat, hnoEntry⟩
    have hownerDebt :
        0 < quittingTerminalSemanticDebt frontier.base owner :=
      (frontier.active_iff owner).1 howner
    have hdiagonal : frontier.tangent ⟨owner, howner⟩ owner < 0 := by
      have hbound := frontier.tangent_diagonal ⟨owner, howner⟩
      linarith
    have hoffDiagonal : ∀ observer, observer ≠ owner →
        frontier.tangent ⟨owner, howner⟩ observer = 0 := by
      intro observer hne
      have hinactive : observer ∉ frontier.active := by
        intro hobserver
        have heq := Finset.card_le_one.mp hcard
          owner howner observer hobserver
        exact hne heq.symm
      have hdebtNonneg :
          0 ≤ quittingTerminalSemanticDebt frontier.base observer :=
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward)
          frontier.base_mem observer
      have hdebtZero :
          quittingTerminalSemanticDebt frontier.base observer = 0 := by
        apply le_antisymm
        · exact le_of_not_gt (fun hpositive =>
            hinactive ((frontier.active_iff observer).2 hpositive))
        · exact hdebtNonneg
      have htangentNonneg :
          0 ≤ frontier.tangent ⟨owner, howner⟩ observer :=
        frontier.tangent_inactive_nonneg
          ⟨owner, howner⟩ observer hdebtZero
      have htangentNotPos :
          ¬0 < frontier.tangent ⟨owner, howner⟩ observer := by
        intro hpositive
        apply hnoEntry
        refine ⟨owner, howner, observer, hdebtZero, ?_⟩
        simpa [quittingActiveDebtTangentExtension, howner] using hpositive
      exact le_antisymm (le_of_not_gt htangentNotPos) htangentNonneg
    have hsum :
        (∑ observer, frontier.tangent ⟨owner, howner⟩ observer) =
          frontier.tangent ⟨owner, howner⟩ owner := by
      apply Finset.sum_eq_single owner
      · intro observer _ hne
        exact hoffDiagonal observer hne
      · simp
    have hzero := hflat ⟨owner, howner⟩
    rw [hsum] at hzero
    linarith
  rcases frontier.exhaustive_branch with hpositive |
      ⟨hflat, hentry⟩ |
      ⟨hflat, hnoEntry, _hcirculation⟩ |
      ⟨hflat, hnoEntry, _hnoCirculation, _hpotential⟩
  · exact Or.inl hpositive
  · exact Or.inr ⟨hflat, hentry⟩
  · exact False.elim (hflatNoEntryFalse ⟨hflat, hnoEntry⟩)
  · exact False.elim (hflatNoEntryFalse ⟨hflat, hnoEntry⟩)

end GameTheory
