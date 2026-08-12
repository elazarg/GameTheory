/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion

/-!
# What a cemetery pair clock can and cannot decode

The stopping-law reset dichotomy leaves a branch in which the replacement
law has positive `Never` mass and, after deleting the reset mover and one
observer, the remaining players survive forever with positive probability.
This file records the exact strategic output available from that datum.

The pair-deleted clock is genuinely deficient: it cannot satisfy a
complete-clock hypothesis.  This is not, however, the owner-deleted clock in
the diffuse deletion theorem, and the witness contains no reward-table
insertion inequality.  Thus the cemetery datum does not select the toggle,
atomic, or deletion side.

Under a global positive terminal exploitability floor, the strongest
unconditional route is instead the reward-table dispatcher.  For the reset
mover it returns one of four possibilities: positive punishment, an incoming
singleton toggle, a strict owner toggle with its forced atomic instability,
or exact deletion preserving the same positive gap.  The cemetery witness
contributes the pair-clock obstruction, but eliminates none of these four
strategic branches.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Survival after deleting both the reset mover and one observer.  It is
ordinary mover-deleted survival after the observer is forced to Continue. -/
def quittingCemeteryPairSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) (fuel : ℕ) : ℝ :=
  quittingOpponentSurvivalWeight
    (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
    mover 0 fuel

/-- The residual information in the cemetery branch of a complete
stopping-law reset.  `pair_survival` is the finite-cutoff form of a positive
joint `Never` probability for every player outside `{mover, observer}`. -/
structure QuittingCemeteryPairClockWitness
    (roots : ℕ → ι → PMF Bool) (replacement : ℕ → PMF Bool)
    (mover observer : ι) (κ : ℝ) : Prop where
  observer_ne : observer ≠ mover
  kappa_pos : 0 < κ
  replacement_never : κ ≤ quittingHazardNeverMass replacement
  pair_survival : ∀ fuel,
    κ ≤ quittingCemeteryPairSurvivalWeight roots mover observer fuel

/-- Positive cemetery mass prevents the replacement law from having a
complete finite stopping clock. -/
theorem QuittingCemeteryPairClockWitness.replacement_not_complete
    {roots : ℕ → ι → PMF Bool} {replacement : ℕ → PMF Bool}
    {mover observer : ι} {κ : ℝ}
    (witness : QuittingCemeteryPairClockWitness
      roots replacement mover observer κ) :
    ¬ Tendsto (quittingHazardSurvival replacement) atTop (nhds 0) := by
  intro hcomplete
  have hsmall : ∀ᶠ fuel in atTop,
      quittingHazardSurvival replacement fuel < κ :=
    (tendsto_order.1 hcomplete).2 κ witness.kappa_pos
  obtain ⟨fuel, hfuel⟩ := hsmall.exists
  exact (not_lt_of_ge
    ((witness.replacement_never.trans
      (quittingHazardNeverMass_le_survival replacement fuel)))) hfuel

/-- The pair-deleted clock in a cemetery witness is deficient.  In
particular it cannot be supplied as the complete clock required by a diffuse
deletion compiler.  Notice that this statement is about deletion of two
labels; it does not assert anything about any one-player-deleted clock. -/
theorem QuittingCemeteryPairClockWitness.pairClock_not_complete
    {roots : ℕ → ι → PMF Bool} {replacement : ℕ → PMF Bool}
    {mover observer : ι} {κ : ℝ}
    (witness : QuittingCemeteryPairClockWitness
      roots replacement mover observer κ) :
    ¬ Tendsto
        (quittingCemeteryPairSurvivalWeight roots mover observer)
        atTop (nhds 0) := by
  intro hcomplete
  have hsmall : ∀ᶠ fuel in atTop,
      quittingCemeteryPairSurvivalWeight roots mover observer fuel < κ :=
    (tendsto_order.1 hcomplete).2 κ witness.kappa_pos
  obtain ⟨fuel, hfuel⟩ := hsmall.exists
  exact (not_lt_of_ge (witness.pair_survival fuel)) hfuel

/-- **Cemetery/global-floor decoder.**  A cemetery pair witness certifies two
noncomplete clocks, but supplies no reward sign capable of choosing a
strategic branch.  The positive global terminal gap nevertheless gives the
full reward-table alternative for the mover:

* its punishment value is positive;
* an outsider strictly gains by joining its singleton;
* it strictly gains by joining a nonempty opponent coalition, the associated
  pure atomic blocker balance is positive, and that pure joined row has an
  outsider deviation; or
* deleting it preserves the exact positive exploitability gap on a strictly
  smaller nonempty player type.

The proof deliberately uses the cemetery witness only for the two clock
obstructions.  Flatness and positive survival of one supplied profile do not
strengthen the reward-table dispatcher without a further gate tying that
profile to insertion or punishment inequalities. -/
theorem
    QuittingCounterexampleRegime.cemeteryPairClock_strategicDispatcher
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    (roots : ℕ → ι → PMF Bool) (replacement : ℕ → PMF Bool)
    (mover observer : ι) (κ : ℝ)
    (cemetery : QuittingCemeteryPairClockWitness
      roots replacement mover observer κ) :
    (¬ Tendsto (quittingHazardSurvival replacement) atTop (nhds 0)) ∧
      (¬ Tendsto
        (quittingCemeteryPairSurvivalWeight roots mover observer)
          atTop (nhds 0)) ∧
      (0 < quittingPunishmentValue reward mover ∨
        (∃ other, other ≠ mover ∧
          quittingSoloReward reward mover other <
            quittingSingletonCollisionReward reward mover other) ∨
        (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
          mover ∉ quitters ∧
            reward ⟨quitters, hquitters⟩ mover <
              reward
                ⟨insert mover quitters,
                  Finset.insert_nonempty mover quitters⟩ mover ∧
            0 < quittingAtomicBlockerBalance reward
              (QuittingSureSetOwnerRepair.quittingPureSetRoot
                (insert mover quitters)) mover ∧
            ∃ who, who ≠ mover ∧ ∃ deviation : PMF Bool,
              quittingRootExpectedPayoff reward 0
                  (Function.update
                    (QuittingSureSetOwnerRepair.quittingPureSetRoot
                      (insert mover quitters)) who deviation) who >
                quittingRootExpectedPayoff reward 0
                  (QuittingSureSetOwnerRepair.quittingPureSetRoot
                    (insert mover quitters)) who) ∨
        (Nonempty (QuittingDeletedPlayer mover) ∧
          HasTerminalExploitabilityGap
            (quittingDeletePlayerReward reward mover) regime.terminalGap ∧
          Fintype.card (QuittingDeletedPlayer mover) < Fintype.card ι)) := by
  refine ⟨cemetery.replacement_not_complete,
    cemetery.pairClock_not_complete, ?_⟩
  rcases regime.strictJoiner_or_soloReward_lt_punishmentValue mover with
    hincoming | hsolo
  · exact Or.inr (Or.inl hincoming)
  · by_cases hchi : quittingPunishmentValue reward mover ≤ 0
    · have hdispatch := exists_strict_owner_toggle_or_exact_playerDeletion
        reward mover regime.terminalGap_pos regime.terminalExploitability
          hsolo hchi
      have hatomic := strictToggle_or_playerDeletion_to_atomicHandoff
        reward regime.terminalGap_pos regime.terminalExploitability mover
          hdispatch
      rcases hatomic with hatomic | hdelete
      · right
        right
        left
        obtain ⟨quitters, hquitters, hmover, hstrict, houtsider⟩ := hatomic
        refine ⟨quitters, hquitters, hmover, hstrict, ?_, houtsider⟩
        rw [quittingAtomicBlockerBalance_pure_ownerToggle
          reward mover quitters hquitters hmover]
        linarith
      · exact Or.inr (Or.inr (Or.inr hdelete))
    · exact Or.inl (lt_of_not_ge hchi)

end GameTheory
