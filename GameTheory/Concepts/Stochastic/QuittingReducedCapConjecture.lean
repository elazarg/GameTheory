/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingTruncationLedgerFold
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformPayoffSelection

/-!
# The reduced form of the finite-quitting conjecture

The phase-switch machinery turns a *package* of ledger-shaped data into a
uniform-equilibrium payoff.  This file states the existence of such a package
at every tolerance as a formal target, and proves -- with no gap -- that the
target implies the finite-quitting conjecture.  Progress on the program is
exactly shrinkage of this target's hypothesis list, which is therefore
visible in diffs of the definition below.

## What the package is

`HasQuittingLedgerCapPackage reward ε` asks for a plan, a punishment plan, a
switch stage and five real caps such that

* **(L)** every player's ledger along the *plan* is at most `ledgerCap` up to
  the switch -- this is what `quittingLedgerStoppingIndex` bounds by
  construction, via `quittingLedger_lt_of_lt_quittingPunishSwitchIndex` and
  `quittingLedger_le_of_le_quittingPunishSwitchIndex`;
* **(Q)** every player's quit regret along the plan is at most
  `quitRegretCap` strictly before the switch -- supplied stage by stage by
  root endpoint `ε`-Nash through
  `quittingLedgerQuitRegret_le_of_isεQuittingRootEndpointNash`;
* **(R)** every player's opponent-survival weight through the switch is at
  most `reach`;
* **(P)** the punishment plan caps every player's unilateral continuation
  payoff by `punishCap who + punishError`;
* **(A)** the assembled error, `(L) + (Q) + reach·(5·bound)` from the plan
  phase plus `reach·(max (punishCap + punishError) 0 + bound)` from the
  punishment phase, is at most `ε`.

Clauses (L), (Q) and (R) are exactly the hypotheses of
`quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`;
clause (P) is hypothesis (b) of
`quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le`, and clause (R)
doubles as its hypothesis (c).  Nothing else is asked for.

## Which clauses are open, and how far

**(R) is the Case-1 residual.**  In Simon's Case 2, where the switch stage is
achieved by the punished player's planned-survival clock,
`quittingOpponentSurvivalWeight_le_of_target_plannedSurvivalStoppingIndex`
supplies (R) for every player other than the punished one.  For the punished
player itself, and in Case 1 -- the switch achieved by a ledger clock -- (R)
is the rank-one crossing-probability estimate, whose abstract layer exists
(the one-sided decision-variation maximal inequality) but whose excursion
instantiation does not.  (R) is a clause of the package precisely so that
this is visible.

**(P) is currently dischargeable only at ceiling-IR targets.**  The landed
attainment result, `hpunish_quittingAllContinueRoots_of_ceilingIR`, discharges
(P) with the all-continue punishment whenever the target dominates
`max 0 (reward (quittingSingletonTerminal who) who)`.  Targets between the
true punishment level and that ceiling need the punishment-attainment lower
bound, which is open.  The clause is nevertheless stated abstractly here: the
assembly consumes only the inequality, so scoping the package to the
all-continue punishment would make it strictly stronger than needed.

## Scope

This is a reduction, not a proof.  The conjecture itself remains
`quittingGame_exists_uniformEquilibriumPayoff` in `QuittingConjecture.lean`;
what is added here is a second, quantitative open declaration standing
between the machinery and that conjecture, together with a gap-free
implication from it.

## Open declarations

This file contains one `sorry`, deliberately, in
`quittingGame_hasQuittingLedgerCapPackage`.  Everything else in it, in
particular the implication
`quittingGame_exists_uniformEquilibriumPayoff_of_hasQuittingLedgerCapPackage`,
is proved.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The per-tolerance input package for the assembled phase-switch cap.**
A plan, a punishment plan, a switch stage and the five caps the assembly
consumes: the plan's ledger up to the switch, the plan's quit regret before
it, the opponent-survival reach at it, the punishment cap, and the arithmetic
clause tying the assembled error to `ε`.

Every clause is consumed verbatim by
`quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_of_plan_ledger_le`;
see the module docstring for which of them are currently dischargeable and
where. -/
def HasQuittingLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  ∃ (plan punish : ℕ → ι → PMF Bool) (switch : ℕ)
      (ledgerCap quitRegretCap reach punishError : ℝ) (punishCap : ι → ℝ),
    0 ≤ quitRegretCap ∧
    (∀ (who : ι) (index : ℕ), index ≤ switch →
      quittingLedger reward plan who index ≤ ledgerCap) ∧
    (∀ (who : ι) (stage : ℕ), stage < switch →
      quittingLedgerQuitRegret reward plan who stage ≤ quitRegretCap) ∧
    (∀ who : ι, quittingOpponentSurvivalWeight plan who 0 switch ≤ reach) ∧
    (∀ (who : ι) (g : ℕ → PMF Bool),
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap who + punishError) ∧
    (∀ who : ι,
      (ledgerCap + quitRegretCap + reach * (5 * quittingRewardBound reward)) +
        reach * (max (punishCap who + punishError) 0 + quittingRewardBound reward) ≤ ε)

/-- **The package yields a terminal `ε`-Nash profile.**  The phase-switch
profile it names is terminal `ε`-Nash: the fold turns clauses (L), (Q), (R)
into the plan-phase hypothesis, clause (P) is hypothesis (b), clause (R) is
hypothesis (c), and clause (A) is the arithmetic. -/
theorem exists_isεAsymptoticNash_of_hasQuittingLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage : HasQuittingLedgerCapPackage reward ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  obtain ⟨plan, punish, switch, ledgerCap, quitRegretCap, reach, punishError, punishCap,
    hquitRegretCap, hledger, hregret, hreach, hpunish, herror⟩ := hpackage
  refine ⟨quittingPhaseSwitchProfile reward plan punish switch, ?_⟩
  refine isεAsymptoticNash_quittingPhaseSwitchProfile reward plan punish switch
    (planError := ledgerCap + quitRegretCap + reach * (5 * quittingRewardBound reward))
    (survivalCap := reach) (bound := quittingRewardBound reward)
    (quittingRewardBound_nonneg reward) (abs_reward_le_quittingRewardBound reward)
    (fun who g => ?_) hpunish hreach herror
  exact quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le
    reward plan who switch (quittingRewardBound_nonneg reward) hquitRegretCap
    (abs_reward_le_quittingRewardBound reward) (hledger who) (hregret who) (hreach who) g

/-- **The reduced statement implies the finite-quitting conjecture.**  A
weight admitting a package at every positive tolerance has a uniform
equilibrium payoff -- the conclusion of
`quittingGame_exists_uniformEquilibriumPayoff`.

This is the measurable residual of the program: no `sorry` is used here, so
every future weakening of `HasQuittingLedgerCapPackage` transports to the
conjecture for free. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_hasQuittingLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpackage : ∀ ε : ℝ, 0 < ε → HasQuittingLedgerCapPackage reward ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors reward
    fun ε hε =>
      exists_isεAsymptoticNash_of_hasQuittingLedgerCapPackage reward (hpackage ε hε)

/-- **The reduced conjecture.**

Every finite quitting weight admits, at every positive tolerance, a
ledger-shaped input package for the assembled phase-switch cap.

`HEADLINE` -- an *intentional open declaration*, and the quantitative residual
the quitting program is now reduced to: by
`quittingGame_exists_uniformEquilibriumPayoff_of_hasQuittingLedgerCapPackage`
it implies `quittingGame_exists_uniformEquilibriumPayoff`, with no gap.

Read the `sorry` as *not proved here*.  What separates it from a theorem is
listed clause by clause in the module docstring; the two live obstructions
are the Case-1 reach estimate (clause (R)) and punishment attainment below
the solo-clipped ceiling (clause (P)). -/
theorem quittingGame_hasQuittingLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) (hε : 0 < ε) :
    HasQuittingLedgerCapPackage reward ε := by
  sorry

end GameTheory
