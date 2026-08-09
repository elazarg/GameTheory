/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles

/-!
# Finite instability ceilings and pure-toggle potential games

Membership toggles give a completely finite obstruction carried by every
quitting counterexample.  This module packages the exact toggle, its best
gain at a coalition, and the minimum best gain over the coalition cube.  The
counterexample terminal margin lies below that computable table invariant.

The analogous stationary ceiling is stated as an infimum, not as an attained
minimum: the selected stationary cap has a singular all-Continue boundary.

Finally, any scalar ordinal potential that strictly increases along every
profitable membership toggle yields a maximizing sure-exit coalition and
hence a uniform-equilibrium payoff.  A counterexample therefore cannot have
the finite improvement property on its pure coalition cube.
-/

noncomputable section

namespace GameTheory

open Set
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Toggle one player's membership in an exit coalition. -/
def quittingToggleCoalition (S : Finset ι) (who : ι) : Finset ι :=
  if who ∈ S then S.erase who else insert who S

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem quittingToggleCoalition_of_mem
    {S : Finset ι} {who : ι} (hwho : who ∈ S) :
    quittingToggleCoalition S who = S.erase who := by
  simp [quittingToggleCoalition, hwho]

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem quittingToggleCoalition_of_notMem
    {S : Finset ι} {who : ι} (hwho : who ∉ S) :
    quittingToggleCoalition S who = insert who S := by
  simp [quittingToggleCoalition, hwho]

omit [Fintype ι] [Nonempty ι] in
/-- A membership toggle always changes the coalition. -/
theorem quittingToggleCoalition_ne (S : Finset ι) (who : ι) :
    quittingToggleCoalition S who ≠ S := by
  by_cases hwho : who ∈ S
  · rw [quittingToggleCoalition_of_mem hwho]
    exact Finset.erase_ne_self.mpr hwho
  · rw [quittingToggleCoalition_of_notMem hwho]
    exact Finset.insert_ne_self.mpr hwho

/-- Payoff improvement from toggling `who` at `S`. -/
def quittingPureToggleGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) : ℝ :=
  quittingSetReward reward (quittingToggleCoalition S who) who -
    quittingSetReward reward S who

/-- Best pure membership-toggle gain at one coalition. -/
def quittingPureToggleExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (quittingPureToggleGain reward S)

/-- Minimum best pure-toggle gain over the finite coalition cube. -/
def quittingPureToggleCeiling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (quittingPureToggleExploitability reward)

namespace QuittingCounterexampleRegime

omit [Nonempty ι] in
/-- The terminal gap is realized by an exact membership toggle at every
coalition. -/
theorem exists_exactToggle_gain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    ∃ who, quittingSetReward reward S who + regime.terminalGap ≤
      quittingSetReward reward (quittingToggleCoalition S who) who := by
  rcases regime.exists_leave_or_join_gain S with hleave | hjoin
  · obtain ⟨who, hmem, hgain⟩ := hleave
    exact ⟨who, by simpa [quittingToggleCoalition_of_mem hmem] using hgain⟩
  · obtain ⟨who, hnot, hgain⟩ := hjoin
    exact ⟨who, by simpa [quittingToggleCoalition_of_notMem hnot] using hgain⟩

/-- Pointwise pure-toggle exploitability dominates the regime margin. -/
theorem terminalGap_le_pureToggleExploitability
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    regime.terminalGap ≤ quittingPureToggleExploitability reward S := by
  obtain ⟨who, hgain⟩ := regime.exists_exactToggle_gain S
  unfold quittingPureToggleExploitability quittingPureToggleGain
  exact (by linarith : regime.terminalGap ≤
      quittingSetReward reward (quittingToggleCoalition S who) who -
        quittingSetReward reward S who) |>.trans
    (Finset.le_sup' (quittingPureToggleGain reward S)
      (Finset.mem_univ who))

/-- **Computable pure-toggle ceiling.**  Every counterexample terminal margin
is below the minimum, over all coalitions, of their best membership-toggle
gain. -/
theorem terminalGap_le_pureToggleCeiling
    (regime : QuittingCounterexampleRegime reward) :
    regime.terminalGap ≤ quittingPureToggleCeiling reward := by
  unfold quittingPureToggleCeiling
  rw [Finset.le_inf'_iff]
  exact fun S _ => regime.terminalGap_le_pureToggleExploitability S

/-! ## A finite closed improvement orbit -/

/-- A chosen player witnessing the exact toggle gain at a coalition. -/
noncomputable def improvingTogglePlayer
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) : ι :=
  Classical.choose (regime.exists_exactToggle_gain S)

/-- The chosen outgoing neighbor in the coalition improvement graph. -/
noncomputable def improvingToggleNext
    (regime : QuittingCounterexampleRegime reward)
    (S : Finset ι) : Finset ι :=
  quittingToggleCoalition S (regime.improvingTogglePlayer S)

omit [Nonempty ι] in
theorem improvingToggleNext_gain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    quittingSetReward reward S (regime.improvingTogglePlayer S) +
        regime.terminalGap ≤
      quittingSetReward reward (regime.improvingToggleNext S)
        (regime.improvingTogglePlayer S) := by
  exact Classical.choose_spec (regime.exists_exactToggle_gain S)

omit [Nonempty ι] in
theorem improvingToggleNext_ne
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    regime.improvingToggleNext S ≠ S :=
  quittingToggleCoalition_ne S (regime.improvingTogglePlayer S)

omit [Nonempty ι] in
/-- The chosen finite improvement graph has a closed directed walk whose
length is a positive multiple of four.  Every edge carries a payoff gain of
at least the terminal margin, though the gaining player may change from edge
to edge.  This is a finite recurrence witness, not a telescoping payoff
contradiction. -/
theorem exists_closedImprovementWalk_multiple_four
    (regime : QuittingCounterexampleRegime reward) :
    ∃ start stop : ℕ, start < stop ∧ 4 ∣ stop - start ∧
      let next := regime.improvingToggleNext
      (next^[start]) ∅ = (next^[stop]) ∅ ∧
      ∀ time,
        quittingSetReward reward ((next^[time]) ∅)
              (regime.improvingTogglePlayer ((next^[time]) ∅)) +
            regime.terminalGap ≤
          quittingSetReward reward ((next^[time + 1]) ∅)
            (regime.improvingTogglePlayer ((next^[time]) ∅)) := by
  let next := regime.improvingToggleNext
  obtain ⟨first, second, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun block : ℕ => (next^[4 * block]) (∅ : Finset ι))
  have hedge : ∀ time,
      quittingSetReward reward ((next^[time]) ∅)
            (regime.improvingTogglePlayer ((next^[time]) ∅)) +
          regime.terminalGap ≤
        quittingSetReward reward ((next^[time + 1]) ∅)
          (regime.improvingTogglePlayer ((next^[time]) ∅)) := by
    intro time
    have hgain := regime.improvingToggleNext_gain ((next^[time]) ∅)
    change quittingSetReward reward ((next^[time]) ∅)
            (regime.improvingTogglePlayer ((next^[time]) ∅)) +
          regime.terminalGap ≤
        quittingSetReward reward (next ((next^[time]) ∅))
          (regime.improvingTogglePlayer ((next^[time]) ∅)) at hgain
    simpa only [Function.iterate_succ_apply'] using hgain
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨4 * first, 4 * second, by omega, ?_, heq, hedge⟩
    exact ⟨second - first, by omega⟩
  · refine ⟨4 * second, 4 * first, by omega, ?_, heq.symm, hedge⟩
    exact ⟨first - second, by omega⟩

end QuittingCounterexampleRegime

/-! ## Stationary infimum ceiling -/

/-- Best selected-cap gain at a stationary quitting root. -/
def quittingStationaryCapExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who =>
    quittingStationaryUnilateralCap reward root who -
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who

/-- Infimum stationary selected-cap exploitability.  No attainment is built
into this definition. -/
def quittingStationaryCapCeiling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  sInf (Set.range (quittingStationaryCapExploitability reward))

namespace QuittingCounterexampleRegime

theorem terminalGap_le_stationaryCapExploitability
    (regime : QuittingCounterexampleRegime reward)
    (root : ι → PMF Bool) :
    regime.terminalGap ≤ quittingStationaryCapExploitability reward root := by
  obtain ⟨who, hgain⟩ := regime.exists_stationaryCap_gain root
  unfold quittingStationaryCapExploitability
  exact (by linarith : regime.terminalGap ≤
      quittingStationaryUnilateralCap reward root who -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who) |>.trans
    (Finset.le_sup'
      (fun who => quittingStationaryUnilateralCap reward root who -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who)
      (Finset.mem_univ who))

/-- **Stationary-cap infimum ceiling.**  The regime margin lies below the
infimum of stationary selected-cap exploitability. -/
theorem terminalGap_le_stationaryCapCeiling
    (regime : QuittingCounterexampleRegime reward) :
    regime.terminalGap ≤ quittingStationaryCapCeiling reward := by
  unfold quittingStationaryCapCeiling
  have hnonempty :
      (Set.range (quittingStationaryCapExploitability reward)).Nonempty :=
    ⟨quittingStationaryCapExploitability reward
        quittingAllContinueRoot,
      ⟨quittingAllContinueRoot, rfl⟩⟩
  have hbounded :
      BddBelow (Set.range (quittingStationaryCapExploitability reward)) :=
    ⟨regime.terminalGap, by
      rintro _ ⟨root, rfl⟩
      exact regime.terminalGap_le_stationaryCapExploitability root⟩
  rw [le_csInf_iff hbounded hnonempty]
  rintro _ ⟨root, rfl⟩
  exact regime.terminalGap_le_stationaryCapExploitability root

end QuittingCounterexampleRegime

/-! ## Ordinal-potential sufficient condition -/

/-- A natural-valued ordinal potential for pure coalition membership
toggles.  Only the sign of each strict payoff improvement is required. -/
def HasQuittingToggleOrdinalPotential
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ potential : Finset ι → ℕ,
    ∀ S who,
      quittingSetReward reward S who <
          quittingSetReward reward (quittingToggleCoalition S who) who →
        potential S < potential (quittingToggleCoalition S who)

omit [Fintype ι] [Nonempty ι] in
/-- A pure toggle ordinal potential produces a maximizing sure-exit
coalition. -/
theorem exists_sureExitSet_of_toggleOrdinalPotential
    [Finite ι]
    (hpotential : HasQuittingToggleOrdinalPotential reward) :
    ∃ S, IsQuittingSureExitSet reward S := by
  letI := Fintype.ofFinite ι
  obtain ⟨potential, hpotential⟩ := hpotential
  obtain ⟨S, -, hS⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty potential
  have hmax : ∀ T : Finset ι, potential T ≤ potential S := by
    intro T
    rw [← hS]
    exact Finset.le_sup' potential (Finset.mem_univ T)
  refine ⟨S, (isQuittingSureExitSet_iff_forall_max reward S).2 fun who => ?_⟩
  have htoggle : quittingSetReward reward
      (quittingToggleCoalition S who) who ≤ quittingSetReward reward S who := by
    by_contra hnot
    have himprove : quittingSetReward reward S who <
        quittingSetReward reward (quittingToggleCoalition S who) who :=
      lt_of_not_ge hnot
    exact (not_lt_of_ge (hmax _)) (hpotential S who himprove)
  by_cases hmem : who ∈ S
  · rw [quittingToggleCoalition_of_mem hmem] at htoggle
    rw [Finset.insert_eq_self.mpr hmem]
    exact max_le le_rfl htoggle
  · rw [quittingToggleCoalition_of_notMem hmem] at htoggle
    rw [Finset.erase_eq_of_notMem hmem]
    exact max_le htoggle le_rfl

omit [Nonempty ι] in
/-- Every quitting table with a pure membership-toggle ordinal potential has
a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_toggleOrdinalPotential
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpotential : HasQuittingToggleOrdinalPotential reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨S, hS⟩ := exists_sureExitSet_of_toggleOrdinalPotential hpotential
  exact ⟨quittingSetReward reward S,
    isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hS⟩

end GameTheory
