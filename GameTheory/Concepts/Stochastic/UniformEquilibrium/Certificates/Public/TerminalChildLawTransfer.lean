/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.TerminalChildDispatcher

/-!
# Law transfer for terminal child dispatch

Canonical terminal-child dispatch changes only malformed suffix histories.
Histories generated from an initial state always genuinely start at that
state.  Consequently, behavior profiles that agree on all genuine histories
induce identical history laws, stage-payoff expectations, and history-value
expectations, including after the same unilateral deviation.

The final lemmas apply this principle to `canonicalTerminalChildProfile`.
They show that raw child potentials and accounts may be reused unchanged at
the expectation level.  Pointwise `PublicPhaseSuffixInterface` equalities for
global potential and account extensions remain separate gluing data.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- One-step extension preserves the initial state of a genuine history. -/
theorem Hist.StartsAt.snoc {initial : G.State} {length : ℕ}
    {history : G.Hist length} (hstart : history.StartsAt initial)
    (action : G.JointAct) (next : G.State) :
    Hist.StartsAt initial
      ((Fin.snoc history.1 (history.2, action), next) :
        G.Hist (length + 1)) := by
  cases length with
  | zero =>
      let records : Fin 1 → G.State × G.JointAct :=
        Fin.snoc history.1 (history.2, action)
      change (records 0).1 = initial
      change history.2 = initial at hstart
      simpa [records, Fin.snoc_zero] using hstart
  | succ length =>
      simpa [Hist.StartsAt] using hstart

/-- Every history in an induced history law genuinely starts at the supplied
initial state. -/
theorem startsAt_of_mem_support_histDist [Fintype ι]
    (profile : G.BehaviorProfile) (initial : G.State) (length : ℕ)
    (history : G.Hist length)
    (hsupport : history ∈ (G.histDist profile initial length).support) :
    history.StartsAt initial := by
  induction length with
  | zero =>
      have history_eq : history = G.emptyHist initial := by
        simpa only [G.histDist_zero, PMF.support_pure,
          Set.mem_singleton_iff] using hsupport
      subst history
      exact Hist.startsAt_empty (G := G) initial
  | succ length ih =>
      rw [G.mem_support_histDist_succ] at hsupport
      obtain ⟨previous, hprevious, action, _haction, next, _hnext,
        rfl⟩ := hsupport
      exact (ih previous hprevious).snoc action next

/-- Two behavior profiles agree on every history genuinely rooted at one
initial state. -/
def ProfilesAgreeOnStartsAt (left right : G.BehaviorProfile)
    (initial : G.State) : Prop :=
  ∀ who length (history : G.Hist length), history.StartsAt initial →
    left who length history = right who length history

namespace ProfilesAgreeOnStartsAt

variable {left right : G.BehaviorProfile} {initial : G.State}

theorem refl (profile : G.BehaviorProfile) (initial : G.State) :
    ProfilesAgreeOnStartsAt profile profile initial :=
  fun _ _ _ _ => rfl

theorem symm
    (hagree : ProfilesAgreeOnStartsAt left right initial) :
    ProfilesAgreeOnStartsAt right left initial :=
  fun who length history hstart =>
    (hagree who length history hstart).symm

theorem trans {third : G.BehaviorProfile}
    (hleft : ProfilesAgreeOnStartsAt left right initial)
    (hright : ProfilesAgreeOnStartsAt right third initial) :
    ProfilesAgreeOnStartsAt left third initial :=
  fun who length history hstart =>
    (hleft who length history hstart).trans
      (hright who length history hstart)

theorem update [DecidableEq ι]
    (hagree : ProfilesAgreeOnStartsAt left right initial)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    ProfilesAgreeOnStartsAt
      (Function.update left who deviation)
      (Function.update right who deviation) initial := by
  intro player length history hstart
  by_cases hplayer : player = who
  · subst player
    simp
  · simp only [Function.update_of_ne hplayer]
    exact hagree player length history hstart

end ProfilesAgreeOnStartsAt

/-- Agreement on genuine histories gives agreement of current joint-action
laws at every genuine history. -/
theorem stageActionDist_eq_of_profilesAgreeOnStartsAt [Fintype ι]
    {left right : G.BehaviorProfile} {initial : G.State}
    (hagree : ProfilesAgreeOnStartsAt left right initial)
    {length : ℕ} {history : G.Hist length}
    (hstart : history.StartsAt initial) :
    G.stageActionDist left history =
      G.stageActionDist right history := by
  unfold stageActionDist
  congr 1
  funext who
  exact hagree who length history hstart

/-- Agreement on genuine histories induces exactly the same finite history
law from the common initial state. -/
theorem histDist_eq_of_profilesAgreeOnStartsAt [Fintype ι]
    {left right : G.BehaviorProfile} {initial : G.State}
    (hagree : ProfilesAgreeOnStartsAt left right initial) :
    ∀ length, G.histDist left initial length =
      G.histDist right initial length := by
  intro length
  induction length with
  | zero =>
      rfl
  | succ length ih =>
      rw [G.histDist_succ, G.histDist_succ, ih]
      apply bind_congr_on_support
      intro history hsupport
      have hstart :=
        G.startsAt_of_mem_support_histDist right initial length
          history hsupport
      rw [G.stageActionDist_eq_of_profilesAgreeOnStartsAt hagree hstart]

/-- The same history potential has the same expectation under profiles that
agree on genuine histories. -/
theorem expectedHistoryValue_eq_of_profilesAgreeOnStartsAt [Fintype ι]
    {left right : G.BehaviorProfile} {initial : G.State}
    (hagree : ProfilesAgreeOnStartsAt left right initial)
    (potential : G.HistoryPotential) (length : ℕ) :
    G.expectedHistoryValue left initial potential length =
      G.expectedHistoryValue right initial potential length := by
  unfold expectedHistoryValue
  rw [G.histDist_eq_of_profilesAgreeOnStartsAt hagree length]

/-- Potentials that agree on genuine histories also have equal expectations
under profiles with the same genuine-history behavior. -/
theorem expectedHistoryValue_eq_of_profilesAndPotentialsAgreeOnStartsAt
    [Fintype ι] {left right : G.BehaviorProfile} {initial : G.State}
    (hprofile : ProfilesAgreeOnStartsAt left right initial)
    (leftPotential rightPotential : G.HistoryPotential)
    (hpotential : ∀ length (history : G.Hist length),
      history.StartsAt initial →
        leftPotential length history = rightPotential length history)
    (length : ℕ) :
    G.expectedHistoryValue left initial leftPotential length =
      G.expectedHistoryValue right initial rightPotential length := by
  unfold expectedHistoryValue
  rw [G.histDist_eq_of_profilesAgreeOnStartsAt hprofile length]
  apply expect_congr_on_support
  intro history hsupport
  exact hpotential length history
    (G.startsAt_of_mem_support_histDist right initial length
      history hsupport)

/-- Expected stage payoffs are unchanged by modifications outside genuine
histories. -/
theorem expectedStagePayoff_eq_of_profilesAgreeOnStartsAt [Fintype ι]
    {left right : G.BehaviorProfile} {initial : G.State}
    (hagree : ProfilesAgreeOnStartsAt left right initial)
    (length : ℕ) (who : ι) :
    G.expectedStagePayoff left initial length who =
      G.expectedStagePayoff right initial length who := by
  unfold expectedStagePayoff
  rw [G.histDist_eq_of_profilesAgreeOnStartsAt hagree length]
  apply expect_congr_on_support
  intro history hsupport
  have hstart :=
    G.startsAt_of_mem_support_histDist right initial length
      history hsupport
  unfold stageEUAt
  rw [G.stageActionDist_eq_of_profilesAgreeOnStartsAt hagree hstart]

/-- Canonical child completion and the supplied raw child agree on every
genuine child history. -/
theorem profilesAgreeOnStartsAt_canonicalTerminalChildProfile
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) :
    ProfilesAgreeOnStartsAt
      (G.canonicalTerminalChildProfile fuel selection child base)
      (child base) base.2 := by
  intro who length history hstart
  exact G.canonicalTerminalChildProfile_apply_of_startsAt
    fuel selection child base who history hstart

/-- Canonical off-path completion preserves the raw child's history law. -/
theorem histDist_canonicalTerminalChildProfile
    [Fintype ι] (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (length : ℕ) :
    G.histDist
        (G.canonicalTerminalChildProfile fuel selection child base)
        base.2 length =
      G.histDist (child base) base.2 length :=
  G.histDist_eq_of_profilesAgreeOnStartsAt
    (G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base) length

/-- Canonical off-path completion preserves every raw child history-potential
expectation. -/
theorem expectedHistoryValue_canonicalTerminalChildProfile
    [Fintype ι] (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (potential : G.HistoryPotential)
    (length : ℕ) :
    G.expectedHistoryValue
        (G.canonicalTerminalChildProfile fuel selection child base)
        base.2 potential length =
      G.expectedHistoryValue (child base) base.2 potential length :=
  G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
    (G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base) potential length

/-- If a global/rebased potential is not literally the raw child potential,
agreement on genuine child histories is exactly enough for expectation-level
transfer. -/
theorem expectedHistoryValue_canonicalTerminalChildProfile_of_potentialsAgree
    [Fintype ι] (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel)
    (canonicalPotential rawPotential : G.HistoryPotential)
    (hpotential : ∀ length (history : G.Hist length),
      history.StartsAt base.2 →
        canonicalPotential length history =
          rawPotential length history)
    (length : ℕ) :
    G.expectedHistoryValue
        (G.canonicalTerminalChildProfile fuel selection child base)
        base.2 canonicalPotential length =
      G.expectedHistoryValue (child base) base.2 rawPotential length :=
  G.expectedHistoryValue_eq_of_profilesAndPotentialsAgreeOnStartsAt
    (G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base)
    canonicalPotential rawPotential hpotential length

/-- Canonical off-path completion preserves expected stage payoffs. -/
theorem expectedStagePayoff_canonicalTerminalChildProfile
    [Fintype ι] (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (length : ℕ) (who : ι) :
    G.expectedStagePayoff
        (G.canonicalTerminalChildProfile fuel selection child base)
        base.2 length who =
      G.expectedStagePayoff (child base) base.2 length who :=
  G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
    (G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base) length who

/-- The same unilateral deviation induces the same child history law before
and after canonical off-path completion. -/
theorem histDist_update_canonicalTerminalChildProfile
    [Fintype ι] [DecidableEq ι]
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (who : ι)
    (deviation : G.BehaviorStrategy who) (length : ℕ) :
    G.histDist
        (Function.update
          (G.canonicalTerminalChildProfile fuel selection child base)
          who deviation)
        base.2 length =
      G.histDist (Function.update (child base) who deviation)
        base.2 length :=
  G.histDist_eq_of_profilesAgreeOnStartsAt
    ((G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base).update who deviation) length

/-- Deviation-account expectations are unchanged by canonical off-path
completion. -/
theorem expectedHistoryValue_update_canonicalTerminalChildProfile
    [Fintype ι] [DecidableEq ι]
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (who : ι)
    (deviation : G.BehaviorStrategy who)
    (potential : G.HistoryPotential) (length : ℕ) :
    G.expectedHistoryValue
        (Function.update
          (G.canonicalTerminalChildProfile fuel selection child base)
          who deviation)
        base.2 potential length =
      G.expectedHistoryValue
        (Function.update (child base) who deviation)
        base.2 potential length :=
  G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
    ((G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base).update who deviation)
    potential length

/-- The deviation-account version of genuine-history potential transfer. -/
theorem
    expectedHistoryValue_update_canonicalTerminalChildProfile_of_potentialsAgree
    [Fintype ι] [DecidableEq ι]
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (who : ι)
    (deviation : G.BehaviorStrategy who)
    (canonicalPotential rawPotential : G.HistoryPotential)
    (hpotential : ∀ length (history : G.Hist length),
      history.StartsAt base.2 →
        canonicalPotential length history =
          rawPotential length history)
    (length : ℕ) :
    G.expectedHistoryValue
        (Function.update
          (G.canonicalTerminalChildProfile fuel selection child base)
          who deviation)
        base.2 canonicalPotential length =
      G.expectedHistoryValue
        (Function.update (child base) who deviation)
        base.2 rawPotential length :=
  G.expectedHistoryValue_eq_of_profilesAndPotentialsAgreeOnStartsAt
    ((G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base).update who deviation)
    canonicalPotential rawPotential hpotential length

/-- Deviation-stage payoff expectations are unchanged by canonical off-path
completion. -/
theorem expectedStagePayoff_update_canonicalTerminalChildProfile
    [Fintype ι] [DecidableEq ι]
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (who : ι)
    (deviation : G.BehaviorStrategy who) (length : ℕ) :
    G.expectedStagePayoff
        (Function.update
          (G.canonicalTerminalChildProfile fuel selection child base)
          who deviation)
        base.2 length who =
      G.expectedStagePayoff
        (Function.update (child base) who deviation)
        base.2 length who :=
  G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
    ((G.profilesAgreeOnStartsAt_canonicalTerminalChildProfile
      fuel selection child base).update who deviation)
    length who

end StochasticGame
end GameTheory
