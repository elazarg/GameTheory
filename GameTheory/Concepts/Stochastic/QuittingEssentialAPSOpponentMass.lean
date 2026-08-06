/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSUniformWindowMass

/-!
# Opponent mass forced by bounded essential-APS paths

A total absorption-mass lower bound is not by itself a playerwise survival
bound: in an arbitrary owner-labelled path all mass could be assigned to one
owner.  Along an active Flesch path this concentration is impossible.

Fix a player `who` and inspect the payoff coordinate of `successor who`.
Whenever `who` owns the current edge, activity at the next vertex turns the
singleton arc equation into a strictly positive displacement of that fixed
coordinate.  Every edge owned by somebody else can compensate by at most
`2 * bound` times its mass.  Boundedness of the two endpoint values therefore
gives

`gap * ownMass ≤ 2 * bound + 2 * bound * opponentMass`.

Combining this inequality with a lower bound on total mass yields a positive
lower bound on the mass contributed by opponents of every player once enough
windows are concatenated.  This is the missing deterministic bridge from the
compact APS `nu`-lemma to opponent-survival contraction.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [DecidableEq ι]

/-- Total absorption mass in the half-open window `[start, start + fuel)`. -/
def quittingEssentialAPSWindowMass
    (mass : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel, mass (start + offset)

/-- Mass in a window carried by edges owned by `who`. -/
def quittingEssentialAPSOwnerWindowMass
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι)
    (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    if owner (start + offset) = who then mass (start + offset) else 0

/-- Mass in a window carried by opponents of `who`. -/
def quittingEssentialAPSOpponentWindowMass
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι)
    (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    if owner (start + offset) = who then 0 else mass (start + offset)

@[simp] theorem quittingEssentialAPSWindowMass_zero
    (mass : ℕ → ℝ) (start : ℕ) :
    quittingEssentialAPSWindowMass mass start 0 = 0 := by
  simp [quittingEssentialAPSWindowMass]

@[simp] theorem quittingEssentialAPSOwnerWindowMass_zero
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι) (start : ℕ) :
    quittingEssentialAPSOwnerWindowMass owner mass who start 0 = 0 := by
  simp [quittingEssentialAPSOwnerWindowMass]

@[simp] theorem quittingEssentialAPSOpponentWindowMass_zero
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι) (start : ℕ) :
    quittingEssentialAPSOpponentWindowMass owner mass who start 0 = 0 := by
  simp [quittingEssentialAPSOpponentWindowMass]

/-- Appending the final stage to a total-mass window. -/
theorem quittingEssentialAPSWindowMass_succ
    (mass : ℕ → ℝ) (start fuel : ℕ) :
    quittingEssentialAPSWindowMass mass start (fuel + 1) =
      quittingEssentialAPSWindowMass mass start fuel + mass (start + fuel) := by
  simp [quittingEssentialAPSWindowMass]

/-- Appending the final stage to an owner-mass window. -/
theorem quittingEssentialAPSOwnerWindowMass_succ
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι)
    (start fuel : ℕ) :
    quittingEssentialAPSOwnerWindowMass owner mass who start (fuel + 1) =
      quittingEssentialAPSOwnerWindowMass owner mass who start fuel +
        if owner (start + fuel) = who then mass (start + fuel) else 0 := by
  simp [quittingEssentialAPSOwnerWindowMass]

/-- Appending the final stage to an opponent-mass window. -/
theorem quittingEssentialAPSOpponentWindowMass_succ
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι)
    (start fuel : ℕ) :
    quittingEssentialAPSOpponentWindowMass owner mass who start (fuel + 1) =
      quittingEssentialAPSOpponentWindowMass owner mass who start fuel +
        if owner (start + fuel) = who then 0 else mass (start + fuel) := by
  simp [quittingEssentialAPSOpponentWindowMass]

/-- Owner mass plus opponent mass is total mass. -/
theorem quittingEssentialAPSOwnerWindowMass_add_opponentWindowMass
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι)
    (start fuel : ℕ) :
    quittingEssentialAPSOwnerWindowMass owner mass who start fuel +
        quittingEssentialAPSOpponentWindowMass owner mass who start fuel =
      quittingEssentialAPSWindowMass mass start fuel := by
  unfold quittingEssentialAPSOwnerWindowMass
    quittingEssentialAPSOpponentWindowMass quittingEssentialAPSWindowMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro offset _
  by_cases howner : owner (start + offset) = who <;> simp [howner]

/-- Total mass splits over two consecutive windows. -/
theorem quittingEssentialAPSWindowMass_add
    (mass : ℕ → ℝ) (start first second : ℕ) :
    quittingEssentialAPSWindowMass mass start (first + second) =
      quittingEssentialAPSWindowMass mass start first +
        quittingEssentialAPSWindowMass mass (start + first) second := by
  simp [quittingEssentialAPSWindowMass, Finset.sum_range_add,
    Nat.add_assoc]

/-- Repeating a uniform window lower bound gives a linear lower bound over a
concatenation of windows. -/
theorem mul_le_quittingEssentialAPSWindowMass_mul
    (mass : ℕ → ℝ) {window : ℕ} {nu : ℝ}
    (hwindow : ∀ start,
      nu ≤ quittingEssentialAPSWindowMass mass start window) :
    ∀ (blocks start : ℕ),
      (blocks : ℝ) * nu ≤
        quittingEssentialAPSWindowMass mass start (blocks * window) := by
  intro blocks
  induction blocks with
  | zero =>
      intro start
      simp
  | succ blocks ih =>
      intro start
      rw [Nat.succ_mul, quittingEssentialAPSWindowMass_add]
      calc
        (↑(blocks + 1) : ℝ) * nu =
            (blocks : ℝ) * nu + nu := by
          push_cast
          ring
        _ ≤ quittingEssentialAPSWindowMass mass start (blocks * window) +
            quittingEssentialAPSWindowMass mass
              (start + blocks * window) window :=
          add_le_add (ih start) (hwindow (start + blocks * window))

/-- At an edge owned by `who`, activity at the successor vertex turns the arc
identity into a positive displacement of the successor coordinate. -/
theorem gap_mul_mass_le_quittingEssentialAPS_step_of_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (owner : ℕ → ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {gap : ℝ}
    (hmass : ∀ time, 0 ≤ mass time)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time))
    (hgap : ∀ player,
      gap ≤ quittingSoloReward reward player (successor player) -
        quittingSoloReward reward (successor player) (successor player))
    (time : ℕ) (who : ι) (howner : owner time = who) :
    gap * mass time ≤
      value time (successor who) - value (time + 1) (successor who) := by
  have harcWho := congrFun (harc time) (successor who)
  rw [howner] at harcWho
  simp only [quittingSingletonArcPayoff] at harcWho
  have hnextActive := hactive (time + 1)
  rw [hownerNext time, howner] at hnextActive
  calc
    gap * mass time ≤ mass time *
        (quittingSoloReward reward who (successor who) -
          quittingSoloReward reward (successor who) (successor who)) := by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hgap who) (hmass time)
    _ = value time (successor who) -
        value (time + 1) (successor who) := by
      rw [harcWho, hnextActive]
      ring

/-- An edge not owned by `who` can offset the chosen successor coordinate by
at most `2 * bound` times that edge's mass. -/
theorem quittingEssentialAPS_step_add_mass_bound_nonneg_of_not_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (owner : ℕ → ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {bound : ℝ}
    (hmass : ∀ time, 0 ≤ mass time)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (time : ℕ) (who : ι) :
    0 ≤ value time (successor who) - value (time + 1) (successor who) +
      (2 * bound) * mass time := by
  have hstep := abs_quittingSingletonArc_step_le_mass_mul_bound
    (hmass time) (harc time) (successor who)
      (hrootBound time (successor who))
      (hvalueBound (time + 1) (successor who))
  have hlower :
      -(mass time * (2 * bound)) ≤
        value time (successor who) - value (time + 1) (successor who) := by
    calc
      -(mass time * (2 * bound)) ≤
          -|value time (successor who) -
            value (time + 1) (successor who)| := neg_le_neg hstep
      _ ≤ value time (successor who) -
          value (time + 1) (successor who) := neg_abs_le _
  nlinarith

/-- **Bounded successor-coordinate drift.**  Own-owner mass creates at least
`gap` units of displacement per unit mass.  Opponent mass can cancel at most
`2 * bound` units per unit mass. -/
theorem gap_mul_quittingEssentialAPSOwnerWindowMass_le_endpoint_add_opponentMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (owner : ℕ → ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {gap bound : ℝ}
    (hmass : ∀ time, 0 ≤ mass time)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time))
    (hgap : ∀ player,
      gap ≤ quittingSoloReward reward player (successor player) -
        quittingSoloReward reward (successor player) (successor player))
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    ∀ start fuel who,
      gap * quittingEssentialAPSOwnerWindowMass owner mass who start fuel ≤
        value start (successor who) -
          value (start + fuel) (successor who) +
        (2 * bound) *
          quittingEssentialAPSOpponentWindowMass owner mass who start fuel := by
  intro start fuel
  induction fuel with
  | zero =>
      intro who
      simp
  | succ fuel ih =>
      intro who
      rw [quittingEssentialAPSOwnerWindowMass_succ,
        quittingEssentialAPSOpponentWindowMass_succ]
      have htime : start + (fuel + 1) = start + fuel + 1 := by omega
      rw [htime]
      by_cases howner : owner (start + fuel) = who
      · simp only [if_pos howner, add_zero]
        have hstep :=
          gap_mul_mass_le_quittingEssentialAPS_step_of_owner
            reward successor owner mass value hmass harc hactive
              hownerNext hgap (start + fuel) who howner
        calc
          gap *
              (quittingEssentialAPSOwnerWindowMass owner mass who start fuel +
                mass (start + fuel)) =
            gap * quittingEssentialAPSOwnerWindowMass owner mass who start fuel +
              gap * mass (start + fuel) := by ring
          _ ≤ (value start (successor who) -
                value (start + fuel) (successor who) +
                (2 * bound) *
                  quittingEssentialAPSOpponentWindowMass owner mass who
                    start fuel) +
              (value (start + fuel) (successor who) -
                value (start + fuel + 1) (successor who)) :=
            add_le_add (ih who) hstep
          _ = value start (successor who) -
                value (start + fuel + 1) (successor who) +
              (2 * bound) *
                quittingEssentialAPSOpponentWindowMass owner mass who
                  start fuel := by ring
      · simp only [if_neg howner, add_zero]
        have hstep :=
          quittingEssentialAPS_step_add_mass_bound_nonneg_of_not_owner
            reward successor owner mass value hmass harc hrootBound
              hvalueBound (start + fuel) who
        calc
          gap * quittingEssentialAPSOwnerWindowMass owner mass who start fuel ≤
            value start (successor who) -
                value (start + fuel) (successor who) +
              (2 * bound) *
                quittingEssentialAPSOpponentWindowMass owner mass who
                  start fuel := ih who
          _ ≤ (value start (successor who) -
                value (start + fuel) (successor who) +
                (2 * bound) *
                  quittingEssentialAPSOpponentWindowMass owner mass who
                    start fuel) +
              (value (start + fuel) (successor who) -
                  value (start + fuel + 1) (successor who) +
                (2 * bound) * mass (start + fuel)) :=
            le_add_of_nonneg_right hstep
          _ = value start (successor who) -
                value (start + fuel + 1) (successor who) +
              (2 * bound) *
                (quittingEssentialAPSOpponentWindowMass owner mass who
                  start fuel + mass (start + fuel)) := by ring

/-- Endpoint boundedness removes the remaining telescoping term. -/
theorem gap_mul_quittingEssentialAPSOwnerWindowMass_le_bound_add_opponentMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (owner : ℕ → ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {gap bound : ℝ}
    (hmass : ∀ time, 0 ≤ mass time)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time))
    (hgap : ∀ player,
      gap ≤ quittingSoloReward reward player (successor player) -
        quittingSoloReward reward (successor player) (successor player))
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (start fuel : ℕ) (who : ι) :
    gap * quittingEssentialAPSOwnerWindowMass owner mass who start fuel ≤
      2 * bound + (2 * bound) *
        quittingEssentialAPSOpponentWindowMass owner mass who start fuel := by
  have hdrift :=
    gap_mul_quittingEssentialAPSOwnerWindowMass_le_endpoint_add_opponentMass
      reward successor owner mass value hmass harc hactive hownerNext hgap
        hrootBound hvalueBound start fuel who
  have hendpoint :
      value start (successor who) - value (start + fuel) (successor who) ≤
        2 * bound := by
    calc
      value start (successor who) - value (start + fuel) (successor who) ≤
          |value start (successor who) -
            value (start + fuel) (successor who)| := le_abs_self _
      _ ≤ |value start (successor who)| +
          |value (start + fuel) (successor who)| := abs_sub _ _
      _ ≤ bound + bound :=
        add_le_add (hvalueBound start (successor who))
          (hvalueBound (start + fuel) (successor who))
      _ = 2 * bound := by ring
  linarith

/-- A total-mass lower bound forces an explicit opponent-mass lower bound. -/
theorem div_le_quittingEssentialAPSOpponentWindowMass_of_windowMass_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (owner : ℕ → ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {gap bound totalFloor : ℝ}
    (hgapPos : 0 < gap) (hbound : 0 ≤ bound)
    (hmass : ∀ time, 0 ≤ mass time)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time))
    (hgap : ∀ player,
      gap ≤ quittingSoloReward reward player (successor player) -
        quittingSoloReward reward (successor player) (successor player))
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (start fuel : ℕ) (who : ι)
    (htotal : totalFloor ≤ quittingEssentialAPSWindowMass mass start fuel) :
    (gap * totalFloor - 2 * bound) / (gap + 2 * bound) ≤
      quittingEssentialAPSOpponentWindowMass owner mass who start fuel := by
  have hown :=
    gap_mul_quittingEssentialAPSOwnerWindowMass_le_bound_add_opponentMass
      reward successor owner mass value hmass harc hactive hownerNext hgap
        hrootBound hvalueBound start fuel who
  have hsplit :=
    quittingEssentialAPSOwnerWindowMass_add_opponentWindowMass
      owner mass who start fuel
  have hdenom : 0 < gap + 2 * bound := by positivity
  apply (div_le_iff₀ hdenom).2
  nlinarith

end GameTheory
