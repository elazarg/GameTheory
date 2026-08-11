/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFiniteInstability

/-!
# A strict toggle orbit in every quitting counterexample

The counterexample margin gives every pure quitter coalition a profitable
one-player membership toggle.  Choosing one such toggle at every vertex and
iterating on the finite coalition cube produces a closed strict-improvement
walk.  Starting from the empty coalition, its first edge is a profitable solo
exit and its second edge enters a genuine collision coalition.

This is the strongest cycle supplied by finiteness alone.  It is a legal
cycle in the *static membership-toggle graph*, but not a chronology of the
quitting game: every nonempty vertex is already an absorbing action profile,
and the construction provides neither Bellman-compatible continuation
values nor a renewable punishment state.  In particular it does not turn a
recurrence of player labels into a semantic reset cycle.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- Every coalition has a player whose literal membership toggle realizes at
least the counterexample margin. -/
theorem exists_strictToggle_gain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    ∃ who, quittingSetReward reward S who + regime.terminalGap ≤
      quittingSetReward reward (quittingToggleCoalition S who) who := by
  rcases regime.exists_leave_or_join_gain S with
    ⟨member, hmember, hgain⟩ | ⟨outsider, houtsider, hgain⟩
  · exact ⟨member, by
      rw [quittingToggleCoalition_of_mem hmember]
      exact hgain⟩
  · exact ⟨outsider, by
      rw [quittingToggleCoalition_of_notMem houtsider]
      exact hgain⟩

/-- A deterministic profitable toggle player, chosen only to expose the
finite orbit. -/
noncomputable def strictTogglePlayer
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) : ι :=
  Classical.choose (regime.exists_strictToggle_gain S)

/-- The coalition reached by the chosen strict membership toggle. -/
noncomputable def strictToggleSuccessor
    (regime : QuittingCounterexampleRegime reward)
    (S : Finset ι) : Finset ι :=
  quittingToggleCoalition S (regime.strictTogglePlayer S)

/-- The chosen edge realizes at least the uniform counterexample margin. -/
theorem strictToggleSuccessor_gain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    quittingSetReward reward S (regime.strictTogglePlayer S) +
        regime.terminalGap ≤
      quittingSetReward reward (regime.strictToggleSuccessor S)
        (regime.strictTogglePlayer S) := by
  exact Classical.choose_spec (regime.exists_strictToggle_gain S)

/-- Every chosen toggle edge is a strict payoff improvement. -/
theorem strictToggleSuccessor_strictGain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    quittingSetReward reward S (regime.strictTogglePlayer S) <
      quittingSetReward reward (regime.strictToggleSuccessor S)
        (regime.strictTogglePlayer S) := by
  linarith [regime.strictToggleSuccessor_gain S, regime.terminalGap_pos]

/-- Every chosen edge changes exactly one coalition membership and hence is
not a self-loop. -/
theorem strictToggleSuccessor_ne
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    regime.strictToggleSuccessor S ≠ S := by
  exact quittingToggleCoalition_ne S (regime.strictTogglePlayer S)

/-- The first selected edge from Never is a singleton exit. -/
theorem strictToggleSuccessor_empty_eq_singleton
    (regime : QuittingCounterexampleRegime reward) :
    regime.strictToggleSuccessor (∅ : Finset ι) =
      {regime.strictTogglePlayer (∅ : Finset ι)} := by
  rw [strictToggleSuccessor,
    quittingToggleCoalition_of_notMem (by simp)]
  rfl

/-- The second selected edge from Never cannot undo the first player's solo
exit: the two margin inequalities would contradict positivity.  It therefore
adds a distinct player and enters a two-player collision coalition. -/
theorem strictToggleSuccessor_singleton_is_pair
    (regime : QuittingCounterexampleRegime reward) :
    let owner := regime.strictTogglePlayer (∅ : Finset ι)
    let singleton := regime.strictToggleSuccessor (∅ : Finset ι)
    let other := regime.strictTogglePlayer singleton
    other ≠ owner ∧
      regime.strictToggleSuccessor singleton = {owner, other} := by
  let owner := regime.strictTogglePlayer (∅ : Finset ι)
  let singleton := regime.strictToggleSuccessor (∅ : Finset ι)
  let other := regime.strictTogglePlayer singleton
  change other ≠ owner ∧
    regime.strictToggleSuccessor singleton = {owner, other}
  have hsingleton : singleton = {owner} := by
    exact regime.strictToggleSuccessor_empty_eq_singleton
  have hfirst := regime.strictToggleSuccessor_gain (∅ : Finset ι)
  have hsecond := regime.strictToggleSuccessor_gain singleton
  change quittingSetReward reward ∅ owner + regime.terminalGap ≤
    quittingSetReward reward singleton owner at hfirst
  change quittingSetReward reward singleton other + regime.terminalGap ≤
    quittingSetReward reward (regime.strictToggleSuccessor singleton) other
      at hsecond
  have hotherNe : other ≠ owner := by
    intro heq
    have hotherMem : other ∈ singleton := by
      rw [hsingleton, heq]
      simp
    have hback : regime.strictToggleSuccessor singleton = ∅ := by
      rw [strictToggleSuccessor,
        quittingToggleCoalition_of_mem hotherMem, hsingleton, heq]
      simp
    rw [heq, hback, quittingSetReward_empty] at hsecond
    rw [quittingSetReward_empty] at hfirst
    linarith [regime.terminalGap_pos]
  refine ⟨hotherNe, ?_⟩
  have hotherNotMem : other ∉ singleton := by
    rw [hsingleton]
    simpa using hotherNe
  rw [strictToggleSuccessor,
    quittingToggleCoalition_of_notMem hotherNotMem, hsingleton]
  ext player
  simp [or_comm]

/-- **Finite strict-toggle orbit.**

From any coalition, the chosen strict membership-toggle dynamics contains a
closed nontrivial walk.  Every displayed edge changes one player's action and
strictly improves that player's one-stage payoff by at least the same
counterexample margin. -/
theorem exists_strictToggleClosedOrbit_from
    (regime : QuittingCounterexampleRegime reward) (seed : Finset ι) :
    ∃ start stop : ℕ, start < stop ∧
      let successor := regime.strictToggleSuccessor
      (successor^[start]) seed = (successor^[stop]) seed ∧
      ∀ time,
        successor ((successor^[time]) seed) ≠ (successor^[time]) seed ∧
        quittingSetReward reward ((successor^[time]) seed)
              (regime.strictTogglePlayer ((successor^[time]) seed)) +
            regime.terminalGap ≤
          quittingSetReward reward (successor ((successor^[time]) seed))
            (regime.strictTogglePlayer ((successor^[time]) seed)) := by
  let successor := regime.strictToggleSuccessor
  obtain ⟨first, second, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun time : ℕ => (successor^[time]) seed)
  have hedge : ∀ time,
      successor ((successor^[time]) seed) ≠ (successor^[time]) seed ∧
      quittingSetReward reward ((successor^[time]) seed)
            (regime.strictTogglePlayer ((successor^[time]) seed)) +
          regime.terminalGap ≤
        quittingSetReward reward (successor ((successor^[time]) seed))
          (regime.strictTogglePlayer ((successor^[time]) seed)) := by
    intro time
    exact ⟨regime.strictToggleSuccessor_ne _,
      regime.strictToggleSuccessor_gain _⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨first, second, hlt, heq, hedge⟩
  · exact ⟨second, first, hgt, heq.symm, hedge⟩

/-- Starting the strict orbit at Never exposes a solo edge followed by a
collision edge before finite recurrence closes the static toggle walk. -/
theorem exists_strictToggleClosedOrbit_from_empty_with_collision_entry
    (regime : QuittingCounterexampleRegime reward) :
    let owner := regime.strictTogglePlayer (∅ : Finset ι)
    let singleton := regime.strictToggleSuccessor (∅ : Finset ι)
    let other := regime.strictTogglePlayer singleton
    singleton = {owner} ∧ other ≠ owner ∧
      regime.strictToggleSuccessor singleton = {owner, other} ∧
      ∃ start stop : ℕ, start < stop ∧
        let successor := regime.strictToggleSuccessor
        (successor^[start]) (∅ : Finset ι) =
          (successor^[stop]) ∅ ∧
        ∀ time,
          successor ((successor^[time]) (∅ : Finset ι)) ≠
              (successor^[time]) ∅ ∧
          quittingSetReward reward ((successor^[time]) ∅)
                (regime.strictTogglePlayer ((successor^[time]) ∅)) +
              regime.terminalGap ≤
            quittingSetReward reward
              (successor ((successor^[time]) ∅))
              (regime.strictTogglePlayer ((successor^[time]) ∅)) := by
  dsimp only
  refine ⟨regime.strictToggleSuccessor_empty_eq_singleton,
    (regime.strictToggleSuccessor_singleton_is_pair).1,
    (regime.strictToggleSuccessor_singleton_is_pair).2, ?_⟩
  exact regime.exists_strictToggleClosedOrbit_from ∅

end QuittingCounterexampleRegime

end GameTheory
