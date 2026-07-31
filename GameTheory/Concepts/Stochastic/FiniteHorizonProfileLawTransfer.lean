/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FullHorizonPublicHistoryEnvelope

/-!
# Finite-horizon profile-law transfer

A terminal payoff at horizon `fuel` depends only on behavior at stages
strictly before `fuel`.  This file records that elementary but important
interface.  Two profiles which agree at every public history before the
horizon induce the same history laws through the horizon, including after
the same unilateral behavior deviation.

The final theorem also identifies the prescribed full-history envelope at
the root with the terminal-payoff expectation for an arbitrary behavior
profile.  Neither result uses equilibrium or a special stopping rule.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- Two behavior profiles agree at every public history strictly before a
fixed terminal horizon. -/
def ProfilesAgreeBefore
    (left right : G.BehaviorProfile) (fuel : ℕ) : Prop :=
  ∀ who time (history : G.Hist time), time < fuel →
    left who time history = right who time history

namespace ProfilesAgreeBefore

variable {left right : G.BehaviorProfile} {fuel : ℕ}

theorem refl (profile : G.BehaviorProfile) (fuel : ℕ) :
    ProfilesAgreeBefore profile profile fuel :=
  fun _ _ _ _ => rfl

theorem symm
    (hagree : ProfilesAgreeBefore left right fuel) :
    ProfilesAgreeBefore right left fuel :=
  fun who time history time_lt =>
    (hagree who time history time_lt).symm

theorem trans {third : G.BehaviorProfile}
    (hleft : ProfilesAgreeBefore left right fuel)
    (hright : ProfilesAgreeBefore right third fuel) :
    ProfilesAgreeBefore left third fuel :=
  fun who time history time_lt =>
    (hleft who time history time_lt).trans
      (hright who time history time_lt)

theorem update [DecidableEq ι]
    (hagree : ProfilesAgreeBefore left right fuel)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    ProfilesAgreeBefore
      (Function.update left who deviation)
      (Function.update right who deviation) fuel := by
  intro player time history time_lt
  by_cases same : player = who
  · subst player
    simp
  · simp only [Function.update_of_ne same]
    exact hagree player time history time_lt

end ProfilesAgreeBefore

/-- Agreement before `fuel` gives agreement of the current joint-action law
at every earlier public history. -/
theorem stageActionDist_eq_of_profilesAgreeBefore
    [Fintype ι]
    {left right : G.BehaviorProfile} {fuel time : ℕ}
    (hagree : ProfilesAgreeBefore left right fuel)
    (history : G.Hist time) (time_lt : time < fuel) :
    G.stageActionDist left history =
      G.stageActionDist right history := by
  unfold stageActionDist
  congr 1
  funext who
  exact hagree who time history time_lt

/-- Profiles agreeing before `fuel` induce the same public-history law at
every time through `fuel`. -/
theorem histDist_eq_of_profilesAgreeBefore
    [Fintype ι]
    {left right : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
    (hagree : ProfilesAgreeBefore left right fuel) :
    ∀ time, time ≤ fuel →
      G.histDist left initial time =
        G.histDist right initial time := by
  intro time time_le
  induction time with
  | zero =>
      rfl
  | succ time ih =>
      have time_lt : time < fuel := by omega
      rw [G.histDist_succ, G.histDist_succ, ih (Nat.le_of_lt time_lt)]
      apply bind_congr_on_support
      intro history _
      rw [
        G.stageActionDist_eq_of_profilesAgreeBefore
          hagree history time_lt
      ]

/-- Every finite terminal-payoff expectation is invariant under agreement
before the terminal horizon. -/
theorem expect_terminal_eq_of_profilesAgreeBefore
    [Fintype ι] [Finite G.State]
    {left right : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
    (hagree : ProfilesAgreeBefore left right fuel)
    (terminal : G.Hist fuel → ℝ) :
    expect (G.histDist left initial fuel) terminal =
      expect (G.histDist right initial fuel) terminal := by
  rw [
    G.histDist_eq_of_profilesAgreeBefore
      hagree fuel (le_refl fuel)
  ]

namespace FiniteFullHistoryControlledStoppingModel

variable
    [Fintype ι] [DecidableEq ι]
    [Finite G.State]
    [∀ who, Finite (G.Act who)]
    {fuel : ℕ}

/-- For an arbitrary profile, the prescribed full-history envelope at the
root equals the expectation of its terminal obstacle. -/
theorem expect_obstacle_eq_prescribedPotential
    (profile : G.BehaviorProfile)
    (obstacle : G.Hist fuel → Payoff ι)
    (initial : G.State) (who : ι) :
    expect (G.histDist profile initial fuel)
        (fun history => obstacle history who) =
      (G.finiteFullHistoryControlledStoppingModel
        profile obstacle).prescribedPotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial) := by
  let potential :=
    prescribedHistoryPotential profile obstacle who
  have expected_eq_root :
      ∀ time, time ≤ fuel →
        G.expectedHistoryValue profile initial potential time =
          potential 0 (G.emptyHist initial) := by
    intro time time_le
    induction time with
    | zero =>
        simp [expectedHistoryValue]
    | succ time ih =>
        have time_lt : time < fuel := by omega
        rw [G.expectedHistoryValue_succ]
        calc
          expect (G.histDist profile initial time)
              (fun history =>
                G.historyContinuationEU
                  profile potential history) =
            expect (G.histDist profile initial time)
              (potential time) := by
                apply congrArg
                funext history
                exact
                  prescribedHistoryPotential_harmonic
                    profile obstacle who history time_lt
          _ = potential 0 (G.emptyHist initial) :=
            ih (Nat.le_of_lt time_lt)
  calc
    expect (G.histDist profile initial fuel)
        (fun history => obstacle history who) =
      G.expectedHistoryValue profile initial potential fuel := by
        unfold expectedHistoryValue
        apply congrArg
        funext history
        exact
          (prescribedHistoryPotential_at_horizon
            profile obstacle who history).symm
    _ = potential 0 (G.emptyHist initial) :=
      expected_eq_root fuel (le_refl fuel)
    _ =
      (G.finiteFullHistoryControlledStoppingModel
        profile obstacle).prescribedPotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial) := by
            rfl

end FiniteFullHistoryControlledStoppingModel

end StochasticGame
end GameTheory
