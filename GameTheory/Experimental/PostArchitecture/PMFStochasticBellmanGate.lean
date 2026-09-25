/-
EXP-138: the stationary Bellman predicate uses actual one-step laws on
infinite states. An unrelated pure joint action has divergent continuation
utility, while each unilateral deviation from the all-false profile remains
on a point-mass transition.
-/

import GameTheory.Stochastic.OneStep
import GameTheory.Experimental.PostArchitecture.PMFStaticGate

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.PMFStochasticBellmanGate

open GameTheory GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration

abbrev Player := Fin 2

abbrev game : Stochastic.Game Player where
  State := ℕ
  Action _ := Bool
  transition state joint :=
    if joint 0 && joint 1 then geometric else PMF.pure state
  stageUtility state _ _ := exploding state

def value (state : ℕ) (_who : Player) : ℝ := exploding state

private theorem stageUtility_eq (state : ℕ)
    (joint : Player → Bool) (who : Player) :
    game.stageUtility state joint who = exploding state := rfl

def allFalse : game.StationaryMixedProfile :=
  fun _ _ => PMF.pure false

abbrev deviated (state : ℕ) (who : Player) (replacement : PMF Bool) :
    Player → PMF Bool :=
  Profile.update (sig := game.oneStepSignature.mixed)
    (allFalse state) who replacement

def trueFalse : game.StationaryMixedProfile :=
  fun _ who => PMF.pure (who == 0)

def allTrueJoint : Player → Bool := fun _ => true

def allTrueLaw : PMF ((∀ _ : Player, Bool) × ℕ) :=
  geometric.map (fun next => (allTrueJoint, next))

theorem allTrueLaw_eq_oneStep :
    allTrueLaw = (game.oneStepForm (0 : ℕ)).play allTrueJoint := rfl

private theorem update_false_joint_not_both (who : Player)
    (choice : Bool) :
    !(Profile.update (sig := game.oneStepSignature)
        (fun _ : Player => false) who choice 0 &&
      Profile.update (sig := game.oneStepSignature)
        (fun _ : Player => false) who choice 1) := by
  fin_cases who <;> cases choice <;> decide

private theorem deviation_joint_not_both (state : ℕ) (who : Player)
    (replacement : PMF Bool) (joint : Player → Bool)
    (hjoint : joint ∈ (independentProduct
      (deviated state who replacement)).support) :
    !(joint 0 && joint 1) := by
  have hcoord := (independentProduct_support_iff
    (deviated state who replacement) joint).mp hjoint
  fin_cases who
  · have hfalse : joint 1 = false := by
      have h := hcoord 1
      simp [deviated, allFalse, Profile.update_of_ne] at h
      exact h
    simp [hfalse]
  · have hfalse : joint 0 = false := by
      have h := hcoord 0
      simp [deviated, allFalse, Profile.update_of_ne] at h
      exact h
    simp [hfalse]

private theorem deviation_law (state : ℕ) (who : Player)
    (replacement : PMF Bool) :
    (game.oneStepForm state).mixed.play
      (deviated state who replacement) =
      (independentProduct
        (deviated state who replacement)).map
          (fun joint => (joint, state)) := by
  let p := independentProduct
    (deviated state who replacement)
  calc
    (game.oneStepForm state).mixed.play
        (deviated state who replacement) =
      p.bind (fun joint => (game.oneStepForm state).play joint) := rfl
    _ = p.bind (fun joint => PMF.pure (joint, state)) := by
      apply bind_congr_on_support p
      intro joint hjoint
      have hnot := deviation_joint_not_both state who replacement joint hjoint
      have hcond : ¬(joint 0 = true ∧ joint 1 = true) := by
        intro ⟨h0, h1⟩
        simp [h0, h1] at hnot
      simp [game, Stochastic.Game.oneStepForm, hcond]
      exact PMF.pure_map (f := fun next : ℕ => (joint, next)) state
    _ = p.map (fun joint => (joint, state)) := PMF.bind_pure_comp _ _

set_option maxHeartbeats 1000000 in
private theorem deviation_value (state : ℕ) (who : Player)
    (replacement : PMF Bool) :
    ∃ h : UtilityIntegrable
        (game.discountedAuxGame (1 / 2) value state).utility who
        ((game.discountedAuxGame (1 / 2) value state).form.mixed.play
          (deviated state who replacement)),
      expectedUtility (game.discountedAuxGame (1 / 2) value state).utility who
          ((game.discountedAuxGame (1 / 2) value state).form.mixed.play
            (deviated state who replacement)) h = value state who := by
  let p := independentProduct (deviated state who replacement)
  let c := exploding state
  have hconst : PayoffIntegrable p (fun _ => c) :=
    payoffIntegrable_constant p c
  have hsource : PayoffIntegrable p
      (fun joint => game.oneStepUtility (1 / 2) value state
        (joint, state) who) := by
    convert hconst using 1
    funext joint
    simp [c, Stochastic.Game.oneStepUtility, value]
    ring
  have hmap : UtilityIntegrable
      (game.discountedAuxGame (1 / 2) value state).utility who
      (p.map (fun joint => (joint, state))) :=
    (payoffIntegrable_map_iff (fun joint => (joint, state)) p _).mpr hsource
  have h : UtilityIntegrable
      (game.discountedAuxGame (1 / 2) value state).utility who
      ((game.discountedAuxGame (1 / 2) value state).form.mixed.play
        (deviated state who replacement)) := by
    rw [deviation_law]
    exact hmap
  refine ⟨h, ?_⟩
  calc
    expectedUtility (game.discountedAuxGame (1 / 2) value state).utility who
        ((game.discountedAuxGame (1 / 2) value state).form.mixed.play
          (deviated state who replacement)) h =
      expectedUtility (game.discountedAuxGame (1 / 2) value state).utility who
        (p.map (fun joint => (joint, state))) hmap := by
      exact expectedUtility_congr_law _ _ (deviation_law state who replacement) h hmap
    _ = expect p (fun joint => game.oneStepUtility (1 / 2) value state
        (joint, state) who) hsource := expectedUtility_map _ _ _ _ hmap
    _ = expect p (fun _ => c) hconst := by
      apply expect_congr_on_support (hf := hsource) (hg := hconst)
      intro joint _
      simp [c, Stochastic.Game.oneStepUtility, value]
      ring
    _ = value state who := by
      rw [expect_constant]
      rfl

private theorem deviated_self (state : ℕ) (who : Player) :
    deviated state who (PMF.pure false) = allFalse state := by
  simpa only [deviated, allFalse] using
    Profile.update_eq_self (sig := game.oneStepSignature.mixed)
      (allFalse state) who

set_option maxHeartbeats 1000000 in
theorem allFalse_bellman :
    game.IsDiscountedStationaryBellmanEq (1 / 2) allFalse value := by
  constructor
  · intro state
    apply (isNash_iff
      (F := (game.discountedAuxGame (1 / 2) value state).form.mixed)
      (weaklyPrefers := euPreference
        (game.discountedAuxGame (1 / 2) value state).utility)
      (allFalse state)).2
    intro who replacement
    obtain ⟨hbase, hbase_value⟩ :=
      deviation_value state who (PMF.pure false)
    obtain ⟨hdeviation, hdeviation_value⟩ :=
      deviation_value state who replacement
    simp only [deviated_self] at hbase hbase_value
    refine ⟨hbase, hdeviation, ?_⟩
    rw [hbase_value, hdeviation_value]
  · intro state who
    obtain ⟨hbase, hbase_value⟩ :=
      deviation_value state who (PMF.pure false)
    simp only [deviated_self] at hbase hbase_value
    exact ⟨hbase, hbase_value⟩

set_option maxHeartbeats 1000000 in
theorem unrelated_transition_not_integrable :
    ¬ PayoffIntegrable allTrueLaw (fun outcome =>
      (1 - (1 / 2 : ℝ)) * exploding 0 +
        (1 / 2 : ℝ) * exploding outcome.2) := by
  intro hstep
  have hsource : PayoffIntegrable geometric (fun next =>
      (1 - (1 / 2 : ℝ)) * exploding 0 + (1 / 2 : ℝ) * exploding next) := by
    dsimp only [allTrueLaw] at hstep
    exact (payoffIntegrable_map_iff
      (fun next : ℕ => (allTrueJoint, next)) geometric _).mp hstep
  have hscaled : PayoffIntegrable geometric
      (fun next => (1 / 2 : ℝ) * exploding next) := by
    have hconst := payoffIntegrable_constant geometric
      ((1 - (1 / 2 : ℝ)) * exploding 0)
    convert payoffIntegrable_sub hsource hconst using 1
    funext next
    ring
  have hexplode : PayoffIntegrable geometric exploding := by
    convert payoffIntegrable_const_mul (c := (2 : ℝ)) hscaled using 1
    funext next
    ring
  exact PMFStaticGate.explodingUtility_not_integrable hexplode

set_option maxHeartbeats 1000000 in
theorem unrelated_oneStep_not_integrable :
    ∀ who : Player, ¬ UtilityIntegrable
      (game.discountedAuxGame (1 / 2) value (0 : ℕ)).utility who
      ((game.discountedAuxGame (1 / 2) value (0 : ℕ)).form.play
        allTrueJoint) := by
  intro who h
  have h' : PayoffIntegrable ((game.oneStepForm (0 : ℕ)).play allTrueJoint)
      (fun outcome => (1 - (1 / 2 : ℝ)) * exploding 0 +
        (1 / 2 : ℝ) * exploding outcome.2) := by
    convert h using 1
    funext outcome
    rfl
  apply unrelated_transition_not_integrable
  rwa [allTrueLaw_eq_oneStep]

set_option maxHeartbeats 1000000 in
theorem trueFalse_not_bellman :
    ¬ game.IsDiscountedStationaryBellmanEq (1 / 2) trueFalse value := by
  intro hbellman
  have hprofile : Profile.update (trueFalse (0 : ℕ)) (1 : Player)
      (PMF.pure true) =
      (game.oneStepForm (0 : ℕ)).purify allTrueJoint := by
    funext who
    fin_cases who <;> rfl
  have hdeviation := (hbellman.1 (0 : ℕ)).deviationIntegrable
    (1 : Player) (PMF.pure true)
  have hlaw :
      (game.discountedAuxGame (1 / 2) value (0 : ℕ)).form.mixed.play
        (Profile.update (trueFalse (0 : ℕ)) (1 : Player) (PMF.pure true)) =
      (game.discountedAuxGame (1 / 2) value (0 : ℕ)).form.play allTrueJoint := by
    rw [hprofile]
    exact (game.oneStepForm (0 : ℕ)).mixed_play_purify allTrueJoint
  exact unrelated_oneStep_not_integrable 1
    (payoffIntegrable_congr_law hlaw hdeviation)

end GameTheory.Experimental.PostArchitecture.PMFStochasticBellmanGate
