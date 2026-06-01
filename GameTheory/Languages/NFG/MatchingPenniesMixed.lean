/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.BinaryMixed
import GameTheory.Concepts.ConstantSumCorrelated
import GameTheory.Languages.NFG.Examples
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.NormNum

/-!
# Mixed Matching Pennies

This file instantiates the language-independent binary mixed-game calculus for
the normal-form matching-pennies example.  The exact half/half mixed Nash theorem
is proved in `GameTheory.Concepts.BinaryMixed` for any matching-pennies-like
two-player `KernelGame` with Boolean player/action labels; this file only
supplies the `heads`/`tails` labels and the four semantic payoff equations.
-/

open scoped BigOperators
open Math.Probability

namespace NFG

noncomputable section

open MPAction

private instance : Nonempty MPAction := ⟨heads⟩

private instance matchingPenniesOutcomeFintype :
    Fintype matchingPennies.toKernelGame.Outcome := by
  change Fintype (∀ _ : Bool, MPAction)
  infer_instance

private instance matchingPenniesOutcomeFinite :
    Finite matchingPennies.toKernelGame.Outcome :=
  @Fintype.finite matchingPennies.toKernelGame.Outcome matchingPenniesOutcomeFintype

private instance matchingPenniesStrategyNonempty :
    ∀ i : Bool, Nonempty (matchingPennies.toKernelGame.Strategy i) :=
  fun _ => ⟨heads⟩

private instance matchingPenniesStrategyFintype :
    ∀ i : Bool, Fintype (matchingPennies.toKernelGame.Strategy i) :=
  fun _ => by
    change Fintype MPAction
    infer_instance

/-- The binary action labels for the compiled matching-pennies kernel game:
`true` is heads and `false` is tails. -/
private def matchingPenniesLabels :
    GameTheory.KernelGame.BinaryActionLabels matchingPennies.toKernelGame where
  player := Equiv.refl Bool
  toBool := fun _ =>
    { toFun := fun
        | heads => true
        | tails => false
      invFun := fun
        | true => heads
        | false => tails
      left_inv := by
        intro a
        cases a <;> rfl
      right_inv := by
        intro b
        cases b <;> rfl }

/-- Matching pennies satisfies the language-independent semantic payoff pattern
for matching-pennies-like binary kernel games. -/
private def matchingPennies_matchingPenniesLike :
    matchingPennies.toKernelGame.MatchingPenniesLike matchingPenniesLabels where
  scale := 1
  scale_pos := by norm_num
  eu_true := by
    intro a b
    cases a <;> cases b <;>
      simp [GameTheory.KernelGame.BinaryActionLabels.profile,
        GameTheory.KernelGame.BinaryActionLabels.action,
        GameTheory.KernelGame.BinaryActionLabels.playerOf, matchingPenniesLabels,
        GameTheory.KernelGame.eu, NFGGame.toKernelGame, matchingPennies,
        Math.Probability.expect_pure]
  eu_false := by
    intro a b
    cases a <;> cases b <;>
      simp [GameTheory.KernelGame.BinaryActionLabels.profile,
        GameTheory.KernelGame.BinaryActionLabels.action,
        GameTheory.KernelGame.BinaryActionLabels.playerOf, matchingPenniesLabels,
        GameTheory.KernelGame.eu, NFGGame.toKernelGame, matchingPennies,
        Math.Probability.expect_pure]

/-- The fair mixed profile for matching pennies. -/
def matchingPenniesFairMixed : MixedProfile (fun _ : Bool => MPAction) :=
  fun _ => PMF.uniformOfFintype MPAction

/-- Matching pennies is balanced at the uniform mixed profile: every pure
deviation has zero gain when both players are uniform. -/
theorem matchingPennies_uniform_mixed_balanced :
    matchingPennies.toKernelGame.IsUniformMixedBalanced :=
  GameTheory.KernelGame.MatchingPenniesLike.uniformMixed_balanced
    matchingPennies_matchingPenniesLike

/-- In the mixed matching-pennies game, Nash equilibrium is exactly the profile
where both players assign probability `1 / 2` to heads. -/
theorem matchingPennies_mixed_nash_iff_half (σ : MixedProfile (fun _ : Bool => MPAction)) :
    IsNashMixed matchingPennies σ ↔
      (σ true heads).toReal = (1 / 2 : ℝ) ∧
        (σ false heads).toReal = (1 / 2 : ℝ) := by
  change matchingPennies.toKernelGame.mixedExtension.IsNash σ ↔
    (σ true heads).toReal = (1 / 2 : ℝ) ∧
      (σ false heads).toReal = (1 / 2 : ℝ)
  simpa [GameTheory.KernelGame.BinaryActionLabels.probTrue,
    GameTheory.KernelGame.BinaryActionLabels.action,
    GameTheory.KernelGame.BinaryActionLabels.playerOf, matchingPenniesLabels] using
      GameTheory.KernelGame.MatchingPenniesLike.mixed_nash_iff_half
        matchingPennies_matchingPenniesLike σ

/-- The fair mixed profile is a mixed Nash equilibrium of matching pennies. -/
theorem matchingPennies_fair_mixed_nash :
    IsNashMixed matchingPennies matchingPenniesFairMixed := by
  rw [matchingPennies_mixed_nash_iff_half]
  constructor
  · change ((PMF.uniformOfFintype MPAction) heads).toReal = (1 / 2 : ℝ)
    rw [PMF.uniformOfFintype_apply]
    have hcard : Fintype.card MPAction = 2 := by rfl
    rw [hcard]
    norm_num
  · change ((PMF.uniformOfFintype MPAction) heads).toReal = (1 / 2 : ℝ)
    rw [PMF.uniformOfFintype_apply]
    have hcard : Fintype.card MPAction = 2 := by rfl
    rw [hcard]
    norm_num

private theorem matchingPenniesLabels_uniform_eq_fair :
    matchingPenniesLabels.uniformMixedProfile = matchingPenniesFairMixed := by
  funext i
  apply PMF.ext
  intro a
  simp only [matchingPenniesFairMixed]
  change (PMF.uniformOfFintype (matchingPennies.toKernelGame.Strategy i)) a =
    (PMF.uniformOfFintype MPAction) a
  rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  have hcard_left : Fintype.card (matchingPennies.toKernelGame.Strategy i) = 2 := by
    change Fintype.card MPAction = 2
    rfl
  have hcard_right : Fintype.card MPAction = 2 := by
    rfl
  rw [hcard_left, hcard_right]

/-- The fair mixed Nash distribution is a correlated equilibrium of matching pennies. -/
theorem matchingPennies_fair_correlated_eq :
    matchingPennies.toKernelGame.IsCorrelatedEq
      (Math.PMFProduct.pmfPi matchingPenniesFairMixed) := by
  exact matchingPennies.toKernelGame.mixed_nash_isCorrelatedEq
    matchingPenniesFairMixed matchingPennies_fair_mixed_nash

/-- Any correlated equilibrium of matching pennies is the independent uniform
mixed Nash distribution. -/
theorem matchingPennies_correlated_eq_unique
    {μ : PMF (GameTheory.KernelGame.Profile matchingPennies.toKernelGame)}
    (hCE : matchingPennies.toKernelGame.IsCorrelatedEq μ) :
    μ = Math.PMFProduct.pmfPi matchingPenniesFairMixed := by
  have h :=
    GameTheory.KernelGame.MatchingPenniesLike.correlated_eq_unique
      matchingPennies_matchingPenniesLike hCE
  simpa [matchingPenniesLabels_uniform_eq_fair] using h

/-- Matching pennies has a unique correlated equilibrium: the independent
uniform mixed Nash distribution. -/
theorem matchingPennies_correlated_eq_iff
    (μ : PMF (GameTheory.KernelGame.Profile matchingPennies.toKernelGame)) :
    matchingPennies.toKernelGame.IsCorrelatedEq μ ↔
      μ = Math.PMFProduct.pmfPi matchingPenniesFairMixed := by
  constructor
  · exact matchingPennies_correlated_eq_unique
  · intro hμ
    rw [hμ]
    exact matchingPennies_fair_correlated_eq

end

end NFG
