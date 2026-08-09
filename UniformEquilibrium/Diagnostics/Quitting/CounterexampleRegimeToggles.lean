/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Membership-toggle instability under a quitting counterexample regime

Fix a finite quitting game with reward table `r`, extended by `r(∅) = 0` for
nonabsorption, and a counterexample regime: a positive terminal gap by which
every behavioral profile admits a unilateral terminal improvement.  This
module records the quantitative instability that the gap forces on the
finitely many pure sure-exit profiles and on all stationary profiles.

For every coalition `S`, the profile in which exactly the members of `S`
quit at every live history pays `r(S)`, and every unilateral behavior
deviation is worth at most the better of the deviator's two membership
toggles — joining the exit set or leaving it.  Applying the regime's gap to
this profile therefore produces, at every `S`, a player who gains at least
the gap by toggling its own membership.  Splitting on membership gives the
leave-or-join form: some member gains at least the gap by staying behind, or
some outsider gains at least the gap by joining.  In particular no sure exit
set exists, at any coalition including the empty and the grand one.

Reading the toggle at distinguished coalitions yields concrete finite
rejection tests.  At `S = ∅` the only nontrivial toggle is a solo exit, so
some player's solo reward is at least the gap.  At a singleton `S = {owner}`
whose owner's solo reward exceeds `-gap`, the owner's own toggles are ruled
out and some distinct opponent gains at least the gap by colliding with the
owner's exit; combining the two coalitions shows the game has at least two
players.  At `S = univ` there is no outsider, so some player gains at least
the gap by letting the others leave without it.  Finally, since every
unilateral deviation from a stationary profile is capped by the deviator's
selected stationary cap, every stationary root has a player whose cap
exceeds its realized payoff by at least the gap.

All statements are finite, table-level inequalities, intended as search-facing
rejection tests: a candidate reward table on which any one of them fails
cannot carry a counterexample regime.

## Reference

Quitting games and their uniform equilibria are those of Solan and Vieille,
*Quitting games*, Israel J. Math. 119 (2001).  The statements here are
original to this development.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [Fintype ι] [DecidableEq ι] in
/-- A singleton's set reward is the owner's solo reward, read at any
player. -/
theorem quittingSetReward_singleton_eq_soloReward (owner who : ι) :
    quittingSetReward reward ({owner} : Finset ι) who =
      quittingSoloReward reward owner who := by
  simp [quittingSetReward, quittingSoloReward]

namespace QuittingCounterexampleRegime

/-- **No profile is Nash below the gap.**  Under a counterexample regime, no
behavioral profile whatsoever is a terminal `ε`-equilibrium for any tolerance
`ε` smaller than the regime's terminal gap. -/
theorem not_isεAsymptoticNash_of_lt_terminalGap
    (regime : QuittingCounterexampleRegime reward)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε : ℝ} (hε : ε < regime.terminalGap) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  intro hnash
  obtain ⟨who, dev, hgain⟩ := regime.terminalExploitability profile
  have hupper := hnash who dev
  linarith

/-- **The uniform toggle instability.**  At every coalition `S`, some player
gains at least the terminal gap over `r(S)` by toggling its own membership
in `S`: the better of joining and leaving beats the on-path reward by the
gap. -/
theorem exists_toggle_gain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    ∃ who, quittingSetReward reward S who + regime.terminalGap ≤
      max (quittingSetReward reward (insert who S) who)
        (quittingSetReward reward (S.erase who) who) := by
  obtain ⟨who, dev, hgain⟩ := regime.terminalExploitability
    (quittingStationaryProfile reward (quittingPureSetRoot S))
  refine ⟨who, ?_⟩
  rw [quittingTerminalPayoff_pureSetRoot] at hgain
  exact hgain.trans
    (quittingTerminalPayoff_update_pureSetRoot_le reward S who dev)

/-- **The leave-or-join dichotomy.**  At every coalition `S`, either some
member gains at least the terminal gap by staying behind while the rest of
`S` exits, or some outsider gains at least the terminal gap by joining the
exit.  The trivial toggle at each player is eliminated by positivity of the
gap. -/
theorem exists_leave_or_join_gain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    (∃ member ∈ S,
        quittingSetReward reward S member + regime.terminalGap ≤
          quittingSetReward reward (S.erase member) member) ∨
      ∃ outsider ∉ S,
        quittingSetReward reward S outsider + regime.terminalGap ≤
          quittingSetReward reward (insert outsider S) outsider := by
  obtain ⟨who, hwho⟩ := regime.exists_toggle_gain S
  by_cases hmem : who ∈ S
  · refine Or.inl ⟨who, hmem, ?_⟩
    rw [Finset.insert_eq_self.mpr hmem] at hwho
    rcases le_max_iff.mp hwho with hstay | hleave
    · linarith [regime.terminalGap_pos]
    · exact hleave
  · refine Or.inr ⟨who, hmem, ?_⟩
    rw [Finset.erase_eq_of_notMem hmem] at hwho
    rcases le_max_iff.mp hwho with hjoin | hstay
    · exact hjoin
    · linarith [regime.terminalGap_pos]

/-- **No sure exit set survives.**  Under a counterexample regime, no
coalition — empty, proper, or grand — passes the sure-exit-set test. -/
theorem not_isQuittingSureExitSet
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    ¬ IsQuittingSureExitSet reward S := by
  intro h
  obtain ⟨who, hwho⟩ := regime.exists_toggle_gain S
  have hmax := (isQuittingSureExitSet_iff_forall_max reward S).mp h who
  linarith [regime.terminalGap_pos]

/-- **A profitable solo exit exists.**  Reading the toggle at the empty
coalition: some player's solo reward is at least the terminal gap. -/
theorem exists_terminalGap_le_soloReward
    (regime : QuittingCounterexampleRegime reward) :
    ∃ who, regime.terminalGap ≤ quittingSoloReward reward who who := by
  obtain ⟨who, hwho⟩ := regime.exists_toggle_gain (∅ : Finset ι)
  rw [Finset.insert_empty, Finset.erase_empty, quittingSetReward_empty,
    zero_add, quittingSetReward_singleton_eq_soloReward] at hwho
  rcases le_max_iff.mp hwho with hgain | hzero
  · exact ⟨who, hgain⟩
  · exact absurd hzero (not_le.mpr regime.terminalGap_pos)

/-- A counterexample regime forces at least one player. -/
theorem nonempty_players
    (regime : QuittingCounterexampleRegime reward) : Nonempty ι := by
  obtain ⟨who, -⟩ := regime.exists_terminalGap_le_soloReward
  exact ⟨who⟩

/-- **A collision gain at every viable singleton.**  If an owner's solo
reward exceeds the negated terminal gap — in particular whenever it is
nonnegative — then the owner's own toggles at `{owner}` are ruled out, and
some distinct opponent gains at least the gap by joining the owner's exit. -/
theorem exists_collision_gain
    (regime : QuittingCounterexampleRegime reward) {owner : ι}
    (howner : -regime.terminalGap < quittingSoloReward reward owner owner) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other + regime.terminalGap ≤
        quittingSingletonCollisionReward reward owner other := by
  obtain ⟨who, hwho⟩ := regime.exists_toggle_gain ({owner} : Finset ι)
  by_cases hne : who = owner
  · exfalso
    rw [hne, Finset.insert_eq_self.mpr (Finset.mem_singleton_self owner),
      Finset.erase_singleton, quittingSetReward_empty,
      quittingSetReward_singleton_eq_soloReward] at hwho
    rcases le_max_iff.mp hwho with hstay | hleave
    · linarith [regime.terminalGap_pos]
    · linarith
  · refine ⟨who, hne, ?_⟩
    rw [Finset.erase_eq_of_notMem
        (show who ∉ ({owner} : Finset ι) by simpa using hne),
      quittingSetReward_insert_singleton,
      quittingSetReward_singleton_eq_soloReward] at hwho
    rcases le_max_iff.mp hwho with hjoin | hstay
    · exact hjoin
    · linarith [regime.terminalGap_pos]

/-- **At least two players.**  The empty-coalition toggle produces an owner
with a profitable solo exit, whose singleton coalition then produces a
distinct colliding opponent. -/
theorem one_lt_card
    (regime : QuittingCounterexampleRegime reward) :
    1 < Fintype.card ι := by
  obtain ⟨owner, howner⟩ := regime.exists_terminalGap_le_soloReward
  have howner' : -regime.terminalGap <
      quittingSoloReward reward owner owner := by
    linarith [regime.terminalGap_pos]
  obtain ⟨other, hne, -⟩ := regime.exists_collision_gain howner'
  exact Fintype.one_lt_card_iff.mpr ⟨other, owner, hne⟩

/-- **The grand exit leaks.**  At the grand coalition there is no outsider,
so some player gains at least the terminal gap by staying behind while all
the others exit. -/
theorem exists_grandExit_leave_gain
    (regime : QuittingCounterexampleRegime reward) :
    ∃ who, quittingSetReward reward (Finset.univ : Finset ι) who +
        regime.terminalGap ≤
      quittingSetReward reward (Finset.univ.erase who) who := by
  obtain ⟨who, hwho⟩ := regime.exists_toggle_gain (Finset.univ : Finset ι)
  refine ⟨who, ?_⟩
  rw [Finset.insert_eq_self.mpr (Finset.mem_univ who)] at hwho
  rcases le_max_iff.mp hwho with hstay | hleave
  · linarith [regime.terminalGap_pos]
  · exact hleave

/-- **Every stationary profile is cap-exploitable.**  At every stationary
root, some player's selected stationary cap exceeds that player's realized
terminal payoff by at least the terminal gap.  This is the toggle instability
extended from pure sure-exit roots to arbitrary stationary rows. -/
theorem exists_stationaryCap_gain
    (regime : QuittingCounterexampleRegime reward) (root : ι → PMF Bool) :
    ∃ who, quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who + regime.terminalGap ≤
      quittingStationaryUnilateralCap reward root who := by
  obtain ⟨who, dev, hgain⟩ := regime.terminalExploitability
    (quittingStationaryProfile reward root)
  exact ⟨who, hgain.trans
    (quittingTerminalPayoff_update_stationary_le_cap reward root who dev)⟩

end QuittingCounterexampleRegime

end GameTheory
