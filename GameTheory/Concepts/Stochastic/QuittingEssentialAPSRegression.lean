/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPS

/-!
# Regression guards for the essential APS operator

The undiscounted operator admits degenerate `mass = 0` decompositions. Hence a
viable active-face point can be invariant without describing any absorption.
This file records the mechanism in a table-independent form: if a singleton
set `{value}` self-generates and the owner's singleton vector is not `value`,
every self-loop decomposition has mass exactly zero.

This is the formal regression behind the warning that invariant sets are not,
without an absorption-progress hypothesis, executable singleton-flow paths.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- A nontrivial point cannot satisfy a positive-mass affine self-loop. -/
theorem quittingEssentialAPSMass_eq_zero_of_selfArc
    {mass : ℝ} {root value : Payoff ι}
    (hself : value = quittingSingletonArcPayoff mass root value)
    (hne : root ≠ value) :
    mass = 0 := by
  by_contra hmass
  apply hne
  funext who
  have hwho := congrFun hself who
  simp only [quittingSingletonArcPayoff] at hwho
  have hfactor : mass * (root who - value who) = 0 := by
    calc
      mass * (root who - value who) =
          mass * root who + (1 - mass) * value who - value who := by
        ring
      _ = value who - value who := by
        rw [← hwho]
      _ = 0 := sub_self _
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hmass)

/-- **Zero-mass false-fixed-point mechanism.** The point survives the prefix
operator, but every decomposition which keeps the continuation in the
singleton set `{value}` uses absorption mass zero. -/
theorem quittingEssentialAPS_zeroMassFixedPoint_regression
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (value : Payoff ι)
    (hviable : QuittingEssentialAPSViable reward value)
    (hactive : value owner = quittingSoloReward reward owner owner)
    (hne : quittingSoloReward reward owner ≠ value) :
    value ∈ quittingEssentialAPSPrefix reward owner
        ({value} : Set (Payoff ι)) ∧
      ∀ mass next,
        next ∈ ({value} : Set (Payoff ι)) →
        value = quittingSingletonArcPayoff mass
          (quittingSoloReward reward owner) next →
        mass = 0 := by
  constructor
  · exact mem_quittingEssentialAPSPrefix_of_zero reward owner
      hviable (by simp) hactive
  · intro mass next hnext hself
    have hnextEq : next = value := by simpa using hnext
    subst next
    exact quittingEssentialAPSMass_eq_zero_of_selfArc hself hne

end GameTheory
