/-
# Guarded one-step stochastic utility

The normalized Bellman return integrates the actual next-state law. This
operation has no finite-state or bounded-value premise; its caller supplies
the integration certificate needed at the selected state and joint action.
-/

import GameTheory.Stochastic.Basic
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Stochastic.Game

open GameTheory.Math.Probability

universe uι us ua

variable {ι : Type uι} (G : Game.{uι, us, ua} ι)

/-- A state-dependent mixed action profile. -/
abbrev StationaryMixedProfile : Type _ :=
  G.State → ∀ player, PMF (G.Action player)

/-- Actions are played once, and the resulting state is recorded with them. -/
abbrev oneStepSignature : GameSignature ι where
  Strategy := G.Action
  Outcome := (∀ player, G.Action player) × G.State

/-- The actual one-step stochastic form at `state`. -/
abbrev oneStepForm (state : G.State) : GameForm ι where
  sig := G.oneStepSignature
  play joint := (G.transition state joint).map (fun next => (joint, next))

/-- Realized normalized utility at one stochastic step. -/
def oneStepUtility (β : ℝ) (value : G.State → ι → ℝ)
    (state : G.State) (outcome : G.oneStepSignature.Outcome)
    (who : ι) : ℝ :=
  (1 - β) * G.stageUtility state outcome.1 who +
    β * value outcome.2 who

/-- The actual stochastic auxiliary game at one state. -/
abbrev discountedAuxGame (β : ℝ)
    (value : G.State → ι → ℝ) (state : G.State) : UtilityGame ι where
  form := G.oneStepForm state
  utility := G.oneStepUtility β value state

/-- Stationary mixed Nash and Bellman equality. Only actual incumbent and
unilateral-deviation laws need be integrable. -/
def IsDiscountedStationaryBellmanEq [Fintype ι] [DecidableEq ι]
    (β : ℝ) (profile : G.StationaryMixedProfile)
    (value : G.State → ι → ℝ) : Prop :=
  (∀ state,
    IsNash (G.discountedAuxGame β value state).form.mixed
      (euPreference (G.discountedAuxGame β value state).utility)
      (profile state)) ∧
  ∀ state who,
    ∃ hintegrable : UtilityIntegrable
        (G.discountedAuxGame β value state).utility who
        ((G.discountedAuxGame β value state).form.mixed.play
          (profile state)),
      expectedUtility (G.discountedAuxGame β value state).utility who
        ((G.discountedAuxGame β value state).form.mixed.play
          (profile state)) hintegrable = value state who

/-- One normalized stage return under the actual stochastic transition law. -/
def normalizedOneStepUtility (β : ℝ) (value : G.State → ℝ)
    (state : G.State) (joint : ∀ player, G.Action player) (who : ι)
    (hintegrable : PayoffIntegrable (G.transition state joint)
      value) : ℝ :=
  (1 - β) * G.stageUtility state joint who +
    β * expect (G.transition state joint) value hintegrable

/-- An actual transition guard supplies pure one-step utility integration. -/
theorem oneStepUtility_pure_integrable (β : ℝ)
    (value : G.State → ι → ℝ) (state : G.State)
    (joint : ∀ player, G.Action player) (who : ι)
    (hintegrable : PayoffIntegrable (G.transition state joint)
      (fun next => value next who)) :
    UtilityIntegrable (G.oneStepUtility β value state) who
      ((G.oneStepForm state).play joint) := by
  apply (payoffIntegrable_map_iff (fun next => (joint, next))
    (G.transition state joint) _).mpr
  exact payoffIntegrable_add
    (payoffIntegrable_constant (G.transition state joint)
      ((1 - β) * G.stageUtility state joint who))
    (payoffIntegrable_const_mul hintegrable)

/-- The scalar Bellman formula is exactly the expectation of the actual
one-step realized utility, with only the selected transition integrated. -/
theorem oneStepUtility_pure_expected (β : ℝ)
    (value : G.State → ι → ℝ) (state : G.State)
    (joint : ∀ player, G.Action player) (who : ι)
    (hintegrable : PayoffIntegrable (G.transition state joint)
      (fun next => value next who))
    (hstep : UtilityIntegrable (G.oneStepUtility β value state) who
      ((G.oneStepForm state).play joint)) :
    expectedUtility (G.oneStepUtility β value state) who
        ((G.oneStepForm state).play joint) hstep =
      G.normalizedOneStepUtility β (fun next => value next who)
        state joint who hintegrable := by
  rw [expectedUtility_map]
  let hconst := payoffIntegrable_constant (G.transition state joint)
    ((1 - β) * G.stageUtility state joint who)
  let hmul := payoffIntegrable_const_mul (c := β) hintegrable
  calc
    expect (G.transition state joint)
        (fun next => G.oneStepUtility β value state (joint, next) who) _ =
      expect (G.transition state joint)
        (fun next => (1 - β) * G.stageUtility state joint who +
          β * value next who) (payoffIntegrable_add hconst hmul) := rfl
    _ = expect (G.transition state joint)
          (fun _ => (1 - β) * G.stageUtility state joint who) hconst +
        expect (G.transition state joint)
          (fun next => β * value next who) hmul := expect_add hconst hmul
    _ = G.normalizedOneStepUtility β (fun next => value next who)
        state joint who hintegrable := by
      rw [expect_constant, expect_const_mul]
      rfl

end GameTheory.Stochastic.Game
