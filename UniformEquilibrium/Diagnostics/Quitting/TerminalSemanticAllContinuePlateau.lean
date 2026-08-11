/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumSpine
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-!
# Finite reward obstruction on an all-Continue semantic plateau

An all-Continue minimum-semantic plateau is not an arbitrary phantom payoff.
Its prescribed vector lies in the finite reward-moment polytope and dominates
every player's own singleton reward.  A positive semantic-debt coordinate
nevertheless needs a strictly better terminal atom: either Never is strictly
better at that coordinate, or some terminal coalition other than the
player's singleton pays strictly more.

Thus the plateau branch reduces to a finite reward-table configuration.  A
vector in the convex hull of Never and the coalition reward vectors must lie
above the diagonal singleton vector while remaining strictly below another
terminal atom at every positive-debt coordinate.  The executable realizing
sequence supplied by the semantic carrier remains essential: moment
membership alone does not construct a behavior profile with that outcome
law.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A uniform upper bound on every terminal atom at one coordinate also
bounds the all-behavior terminal best-response envelope. -/
theorem quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (bound : ℝ)
    (hbound : ∀ outcome : QuittingTerminalOutcome ι,
      quittingTerminalOutcomeReward reward outcome who ≤ bound) :
    quittingContinuationBestResponseValue reward profile who ≤ bound := by
  unfold quittingContinuationBestResponseValue
  apply csSup_le
  · let candidate := quittingAlwaysContinueStrategy reward who
    exact ⟨_, ⟨candidate, rfl⟩⟩
  · rintro value ⟨deviation, rfl⟩
    let deviated := Function.update profile who deviation
    let mass := quittingTerminalOutcomeMass reward deviated
    have hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) :=
      quittingTerminalOutcomeMass_mem_stdSimplex reward deviated
    change quittingTerminalPayoff reward deviated who ≤ bound
    rw [← quittingTerminalRewardMoment_outcomeMass reward deviated]
    change (∑ outcome, mass outcome *
      quittingTerminalOutcomeReward reward outcome who) ≤ bound
    calc
      _ ≤ ∑ outcome, mass outcome * bound := by
        apply Finset.sum_le_sum
        intro outcome _
        exact mul_le_mul_of_nonneg_left (hbound outcome) (hmass.1 outcome)
      _ = (∑ outcome, mass outcome) * bound := by
        rw [Finset.sum_mul]
      _ = bound := by rw [hmass.2, one_mul]

/-- The same terminal-atom bound passes to every point of the attainable
semantic closure. -/
theorem quittingTerminalSemanticCarrier_envelope_le_of_terminalOutcomeReward_le
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (who : ι) (bound : ℝ)
    (hbound : ∀ outcome : QuittingTerminalOutcome ι,
      quittingTerminalOutcomeReward reward outcome who ≤ bound) :
    pair.2 who ≤ bound := by
  change pair ∈ {candidate : QuittingTerminalSemanticPair ι |
    candidate.2 who ≤ bound}
  apply (closure_minimal ?_ ?_) hpair
  · rintro candidate ⟨profile, rfl⟩
    exact quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
      profile who bound hbound
  · exact isClosed_le
      ((continuous_apply who).comp (continuous_snd.comp continuous_id))
      continuous_const

/-- Every semantic envelope coordinate is bounded by one terminal atom that
actually maximizes that player's finite reward table (including Never). -/
theorem exists_terminalOutcomeReward_ge_terminalSemanticEnvelope
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (who : ι) :
    ∃ outcome : QuittingTerminalOutcome ι,
      pair.2 who ≤ quittingTerminalOutcomeReward reward outcome who := by
  obtain ⟨best, _, hbest⟩ := Finset.exists_max_image Finset.univ
    (fun outcome : QuittingTerminalOutcome ι =>
      quittingTerminalOutcomeReward reward outcome who)
    Finset.univ_nonempty
  refine ⟨best,
    quittingTerminalSemanticCarrier_envelope_le_of_terminalOutcomeReward_le
      pair hpair who
        (quittingTerminalOutcomeReward reward best who) ?_⟩
  intro outcome
  exact hbest outcome (Finset.mem_univ outcome)

/-- Positive semantic debt forces a finite terminal atom strictly above the
prescribed coordinate.  Quantitatively, the atom can be chosen above the full
semantic envelope, so its advantage is at least the semantic debt.  This
statement uses the executable semantic closure, not merely membership of the
prescribed vector in the reward polytope. -/
theorem exists_terminalOutcomeReward_gt_of_positiveTerminalSemanticDebt
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who) :
    ∃ outcome : QuittingTerminalOutcome ι,
      pair.1 who < quittingTerminalOutcomeReward reward outcome who ∧
      pair.2 who ≤ quittingTerminalOutcomeReward reward outcome who := by
  obtain ⟨outcome, houtcome⟩ :=
    exists_terminalOutcomeReward_ge_terminalSemanticEnvelope pair hpair who
  refine ⟨outcome, ?_, houtcome⟩
  unfold quittingTerminalSemanticDebt at hpositive
  linarith

/-- **Finite plateau obstruction.**  At an all-Continue semantic plateau, a
positive debtor has either a profitable Never atom or a strictly better
coalition distinct from its own singleton.  Simultaneously the prescribed
vector is a finite reward moment and dominates every own-singleton reward. -/
theorem quittingTerminalSemantic_allContinuePlateau_finiteRewardObstruction
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who) :
    pair.1 ∈ quittingTerminalRewardMomentSet reward ∧
      (∀ player, reward (quittingSingletonTerminal player) player ≤
        pair.1 player) ∧
      (pair.1 who < 0 ∨
        ∃ terminal : {S : Finset ι // S.Nonempty},
          terminal.val ≠ {who} ∧ pair.1 who < reward terminal who) := by
  refine ⟨quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet
      reward pair hpair,
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward pair.1).mp hnash, ?_⟩
  obtain ⟨outcome, houtcome, henvelope⟩ :=
    exists_terminalOutcomeReward_gt_of_positiveTerminalSemanticDebt
      pair hpair who hpositive
  cases outcome with
  | none =>
      left
      simpa [quittingTerminalOutcomeReward] using houtcome
  | some terminal =>
      right
      refine ⟨terminal, ?_, ?_⟩
      · intro heq
        have hterminal : terminal = quittingSingletonTerminal who :=
          Subtype.ext heq
        have hsingleton :=
          (isZeroQuittingRootNash_allContinue_iff_singleton_le
            reward pair.1).mp hnash who
        apply (not_lt_of_ge hsingleton)
        simpa [hterminal, quittingTerminalOutcomeReward] using houtcome
      · simpa [quittingTerminalOutcomeReward] using houtcome

/-- Every all-Continue plateau retains an executable realizing sequence in
addition to its finite reward obstruction.  The sequence converges jointly
in prescribed payoff and best-response envelope; no single member is claimed
to realize the limiting pair exactly. -/
theorem exists_profiles_tendsto_allContinuePlateau_with_finiteRewardObstruction
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 pair) ∧
      pair.1 ∈ quittingTerminalRewardMomentSet reward ∧
      (∀ player, reward (quittingSingletonTerminal player) player ≤
        pair.1 player) ∧
      (pair.1 who < 0 ∨
        ∃ terminal : {S : Finset ι // S.Nonempty},
          terminal.val ≠ {who} ∧ pair.1 who < reward terminal who) := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  exact ⟨profiles, hprofiles,
    quittingTerminalSemantic_allContinuePlateau_finiteRewardObstruction
      pair hpair hnash who hpositive⟩

end GameTheory
