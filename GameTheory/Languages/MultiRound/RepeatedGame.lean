/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Repeated.Discounted

/-!
# Infinite Repeated Games

An infinite repeated game plays the same stage game at every natural-numbered
period.  Players observe the public history of past action profiles and choose
the next stage-game action.

This file is an action/payoff presentation adapter over
`GameTheory.Concepts.Repeated`: it turns the presentation below into a stage
`KernelGame`, then reuses its histories, repeated play, discounting, and
equilibrium results. Finite protocol syntax lives in `MultiRoundGame`, whose
`rounds : List Round` is a separate compiled-language representation.

## Main definitions

* `RepeatedGame` — an infinite repeated game with observable stage actions
* `RepeatedGame.play` — the generated stream of action profiles
* `RepeatedGame.discountedPayoff` — normalized discounted payoff
* `RepeatedGame.discountedKernelGame` — strategic-form kernel game induced by a
  fixed discount factor

## Main results

* `RepeatedGame.discountedPayoff_constStrategy` — constant play has the stage
  payoff for `0 ≤ δ < 1`
* `RepeatedGame.constStrategy_isDiscountedNash` — repeating a stage Nash action
  profile is Nash in the discounted repeated game, under bounded stage payoffs
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Math.Probability

/-- An infinite repeated game with public observation of past action profiles. -/
structure RepeatedGame (ι : Type) where
  /-- Per-player action set in the stage game. -/
  Act : ι → Type
  /-- Stage-game utility given a joint action profile. -/
  stageUtil : (∀ i, Act i) → ι → ℝ

namespace RepeatedGame

variable {ι : Type}

/-- The one-shot stage game underlying the repeated-game presentation. -/
noncomputable abbrev stageKernelGame (R : RepeatedGame ι) : KernelGame ι :=
  KernelGame.ofEU R.Act R.stageUtil

/-- History before period `t`: the public sequence of past action profiles. -/
abbrev History (R : RepeatedGame ι) (t : ℕ) : Type :=
  R.stageKernelGame.ProfileHistory t

/-- A strategy chooses an action after every finite public action history. -/
abbrev Strategy (R : RepeatedGame ι) (i : ι) : Type :=
  R.stageKernelGame.RepeatedStrategy i

/-- A repeated-game strategy profile. -/
abbrev RProfile (R : RepeatedGame ι) : Type :=
  R.stageKernelGame.RepeatedProfile

/-- Payoff of a single round given a joint action. -/
def roundPayoff (R : RepeatedGame ι) (a : ∀ i, R.Act i) (who : ι) : ℝ :=
  R.stageUtil a who

/-- Generate the action profile stream using the generic repeated-play API. -/
abbrev play (R : RepeatedGame ι) (σ : R.RProfile) :
    (t : ℕ) → (∀ i, R.Act i) :=
  R.stageKernelGame.repeatedPlay σ

/-- Constant repeated play of a fixed stage action profile. -/
abbrev constStrategy (R : RepeatedGame ι) (a : ∀ i, R.Act i) : R.RProfile :=
  R.stageKernelGame.stationaryRepeatedProfile a

/-- Normalized discounted payoff in the infinite repeated game.

The definition is total for all real `δ`; the payoff interpretation and lemmas
below use the explicit side conditions `0 ≤ δ` and `δ < 1`. -/
abbrev discountedPayoff (R : RepeatedGame ι) (δ : ℝ)
    (σ : R.RProfile) (who : ι) : ℝ :=
  R.stageKernelGame.discountedAveragePayoff δ σ who

/-- The strategic-form kernel game induced by a fixed discounted repeated game. -/
noncomputable abbrev discountedKernelGame
    (R : RepeatedGame ι) (δ : ℝ) : KernelGame ι :=
  R.stageKernelGame.discountedRepeatedKernelGame δ

@[simp] theorem play_constStrategy
    (R : RepeatedGame ι) (a : ∀ i, R.Act i) (t : ℕ) :
    R.play (R.constStrategy a) t = a := by
  exact R.stageKernelGame.repeatedPlay_stationaryRepeatedProfile a t

/-- If one player deviates from constant play, every realized period profile is
the constant action profile with only that player's current action updated. -/
theorem play_update_constStrategy
    (R : RepeatedGame ι) [DecidableEq ι] (a : ∀ i, R.Act i)
    (who : ι) (dev : R.Strategy who) (t : ℕ) :
    R.play (Function.update (R.constStrategy a) who dev) t =
      Function.update a who
        (dev t (fun k => R.play (Function.update (R.constStrategy a) who dev) k)) := by
  exact R.stageKernelGame.repeatedPlay_update_stationaryRepeatedProfile a who dev t

/-- Discounted stage utilities are summable when stage utilities are uniformly
bounded and `δ ∈ [0,1)`. -/
theorem summable_discounted_stageUtil_of_abs_bound
    (R : RepeatedGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : R.RProfile} (who : ι)
    (hbd : ∀ a : ∀ i, R.Act i, |R.stageUtil a who| ≤ C) :
    Summable fun t : ℕ => δ ^ t * R.stageUtil (R.play σ t) who := by
  have hbd' : ∀ ρ : R.stageKernelGame.Profile,
      |R.stageKernelGame.eu ρ who| ≤ C := by
    intro ρ
    simpa only [KernelGame.eu_ofEU] using hbd ρ
  simpa only [KernelGame.eu_ofEU] using
    (R.stageKernelGame.summable_discounted_stageEU_of_abs_bound
      hδ0 hδ1 who hbd' (σ := σ))

/-- Pointwise dominance of all stage payoffs implies dominance of normalized
discounted payoffs. -/
theorem discountedPayoff_le_of_forall_stageUtil_le
    (R : RepeatedGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ τ : R.RProfile} (who : ι)
    (hbd : ∀ a : ∀ i, R.Act i, |R.stageUtil a who| ≤ C)
    (hle : ∀ t : ℕ,
      R.stageUtil (R.play σ t) who ≤ R.stageUtil (R.play τ t) who) :
    R.discountedPayoff δ σ who ≤ R.discountedPayoff δ τ who := by
  have hbd' : ∀ ρ : R.stageKernelGame.Profile,
      |R.stageKernelGame.eu ρ who| ≤ C := by
    intro ρ
    simpa only [KernelGame.eu_ofEU] using hbd ρ
  have hle' : ∀ t : ℕ,
      R.stageKernelGame.eu (R.play σ t) who ≤
        R.stageKernelGame.eu (R.play τ t) who := by
    intro t
    simpa only [KernelGame.eu_ofEU] using hle t
  exact R.stageKernelGame.discountedAveragePayoff_le_of_forall_stageEU_le
    hδ0 hδ1 who hbd' hle'

/-- Normalized discounted payoff of constant repeated play is the stage payoff,
for discount factors in `[0, 1)`. -/
theorem discountedPayoff_constStrategy
    (R : RepeatedGame ι) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (a : ∀ i, R.Act i) (who : ι) :
    R.discountedPayoff δ (R.constStrategy a) who = R.stageUtil a who := by
  simpa only [KernelGame.eu_ofEU] using
    (R.stageKernelGame.discountedAveragePayoff_stationaryRepeatedProfile
      hδ0 hδ1 a who)

/-- If `a` is a stage-game Nash action profile, then constant repetition of `a`
is Nash in the discounted repeated game induced by any `δ ∈ [0,1)`, assuming
bounded stage payoffs for each player. -/
theorem constStrategy_isDiscountedNash
    (R : RepeatedGame ι) [DecidableEq ι]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (a : ∀ i, R.Act i)
    (hstage : ∀ (who : ι) (a' : R.Act who),
      R.stageUtil a who ≥ R.stageUtil (Function.update a who a') who)
    (hbd : ∀ who, ∃ C : ℝ,
      ∀ a : ∀ i, R.Act i, |R.stageUtil a who| ≤ C) :
    (R.discountedKernelGame δ).IsNash (R.constStrategy a) := by
  intro who dev
  obtain ⟨C, hC⟩ := hbd who
  simp only [KernelGame.discountedRepeatedKernelGame_eu]
  rw [ge_iff_le]
  exact R.discountedPayoff_le_of_forall_stageUtil_le
    (σ := Function.update (R.constStrategy a) who dev)
    (τ := R.constStrategy a) hδ0 hδ1 who hC (fun t => by
      rw [R.play_update_constStrategy a who dev t]
      rw [R.play_constStrategy a t]
      exact hstage who _)

end RepeatedGame

end GameTheory
