/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFirstStageAdapter

/-!
# The unique live history and live mass in a quitting game

Before absorption a quitting game has one public history: every past state was
live and every past joint action was all-continue.  This file exposes that
history and the probability of reaching it.  These are the elementary
stopping-process coordinates used by the terminal-to-uniform bridge.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The unique length-`time` history whose current state is still live. -/
def quittingLiveHist
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) : (quittingGame reward).Hist time :=
  (fun _ => (none, quittingAllContinueAction), none)

omit [DecidableEq ι] in
@[simp] theorem quittingLiveHist_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingLiveHist reward 0 = (quittingGame reward).emptyHist none := by
  apply Prod.ext
  · funext index
    exact Fin.elim0 index
  · rfl

omit [DecidableEq ι] in
@[simp] theorem quittingLiveHist_snd
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (time : ℕ) :
    (quittingLiveHist reward time).2 = none :=
  rfl

omit [DecidableEq ι] in
/-- Snoc-ing one more all-continue live stage gives the next live history. -/
theorem quittingLiveHist_snoc
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (time : ℕ) :
    ((Fin.snoc (quittingLiveHist reward time).1
        (none, quittingAllContinueAction), none) :
      (quittingGame reward).Hist (time + 1)) =
      quittingLiveHist reward (time + 1) := by
  apply Prod.ext
  · funext index
    refine Fin.lastCases ?_ (fun earlier => ?_) index
    · simp [quittingLiveHist]
    · simp [quittingLiveHist]
  · rfl

omit [DecidableEq ι] in
/-- Any supported history whose current state is live is the canonical
all-continue history. -/
theorem eq_quittingLiveHist_of_mem_support_histDist_of_snd_eq_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∀ {time : ℕ} (history : (quittingGame reward).Hist time),
      history ∈ ((quittingGame reward).histDist profile none time).support →
      history.2 = none →
      history = quittingLiveHist reward time := by
  classical
  intro time
  induction time with
  | zero =>
      intro history hs _
      simpa using (PMF.mem_support_pure_iff _ _).mp hs
  | succ time ih =>
      intro history hs hlive
      rw [(quittingGame reward).mem_support_histDist_succ] at hs
      obtain ⟨previous, hprevious, action, haction,
        next, hnext, rfl⟩ := hs
      change (ι → Bool) at action
      have hnextNone : next = none := hlive
      subst next
      have hpreviousNone : previous.2 = none := by
        cases hstate : previous.2 with
        | none => rfl
        | some S =>
            exfalso
            have htransition :
                (quittingGame reward).transition previous.2 action =
                  PMF.pure (some S) := by
              rw [hstate]
              rfl
            rw [htransition] at hnext
            change (none : Option {S : Finset ι // S.Nonempty}) ∈
              (PMF.pure (some S) :
                PMF (Option {S : Finset ι // S.Nonempty})).support at hnext
            have himpossible :=
              (PMF.mem_support_pure_iff (some S)
                (none : Option {S : Finset ι // S.Nonempty})).mp hnext
            simp at himpossible
      have hpreviousEq := ih previous hprevious hpreviousNone
      have hnoQuit : ¬(quittingQuitters action).Nonempty := by
        rw [hpreviousNone] at hnext
        by_contra hquit
        rw [quittingGame_transition_none,
          dif_pos (by simpa [quittingQuitters] using hquit)] at hnext
        simp at hnext
      have hactionEq :=
        eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
          action hnoQuit
      subst previous
      subst action
      exact quittingLiveHist_snoc reward time

/-- Probability that play is still live after `time` completed stages. -/
def quittingLiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) : ℝ :=
  (((quittingGame reward).histDist profile none time)
    (quittingLiveHist reward time)).toReal

omit [DecidableEq ι] in
@[simp] theorem quittingLiveMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingLiveMass reward profile 0 = 1 := by
  simp [quittingLiveMass]

omit [DecidableEq ι] in
theorem quittingLiveMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    0 ≤ quittingLiveMass reward profile time :=
  ENNReal.toReal_nonneg

end GameTheory
