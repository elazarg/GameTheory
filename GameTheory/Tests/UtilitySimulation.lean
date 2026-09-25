/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MixtureUtilitySimulation
import GameTheory.Tests.MixtureSimulation

/-! # Utility-simulation regressions for a genuine mixed deviation -/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn.Tests

open GameTheory.Math.Probability

def booleanUtility (value : Bool) (_player : Unit) : ℝ :=
  if value then 2 else 0

private theorem booleanUtility_bound (value : Bool) :
    |booleanUtility value ()| ≤ 2 := by
  cases value <;> norm_num [booleanUtility]

private theorem observed_integrable {Outcome : Type*} (law : PMF Outcome)
    (observe : Outcome → Bool) :
    UtilityIntegrable (fun outcome (_ : Unit) => booleanUtility (observe outcome) ())
      () law := by
  apply payoffIntegrable_of_bounded law _ (C := 2)
  intro outcome
  exact booleanUtility_bound (observe outcome)

def firstUtility : UtilitySimulation source middle
    (fun outcome player => booleanUtility (sourceObserve outcome) player)
    (fun outcome player => booleanUtility (middleObserve outcome) player)
    (singletonGroups Unit) :=
  first.toUtilitySimulation booleanUtility (fun _ _ => trivial) (by
    intro profile who replacement
    cases who
    exact observed_integrable _ middleObserve)

def secondUtility : UtilitySimulation middle target
    (fun outcome player => booleanUtility (middleObserve outcome) player)
    (fun outcome player => booleanUtility (targetObserve outcome) player)
    (singletonGroups Unit) :=
  second.toUtilitySimulation booleanUtility (fun _ _ => trivial) (by
    intro profile who replacement
    cases who
    exact observed_integrable _ targetObserve)

def layeredUtility : UtilitySimulation source target
    (fun outcome player => booleanUtility (sourceObserve outcome) player)
    (fun outcome player => booleanUtility (targetObserve outcome) player)
    (singletonGroups Unit) :=
  firstUtility.trans secondUtility

private theorem source_value (profile : Profile source.sig) (replacement : Bool)
    (h : UtilityIntegrable
      (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
      (source.play (Profile.update profile () replacement))) :
    expectedUtility (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
      (source.play (Profile.update profile () replacement)) h =
        booleanUtility replacement () := by
  cases replacement <;>
    simp [source, sourceObserve, expectedUtility_pure, booleanUtility,
      Profile.update_same]

private theorem coin_value (h : PayoffIntegrable coin (fun bit => booleanUtility bit ())) :
    expect coin (fun bit => booleanUtility bit ()) h = 1 := by
  rw [expect_eq_sum]
  simp [coin, PMF.uniformOfFintype_apply, booleanUtility]

private theorem target_value (profile : Profile target.sig) (replacement : Fin 3)
    (h : UtilityIntegrable
      (fun outcome player => booleanUtility (targetObserve outcome) player) ()
      (target.play (Profile.update profile () replacement))) :
    expectedUtility (fun outcome player => booleanUtility (targetObserve outcome) player) ()
      (target.play (Profile.update profile () replacement)) h =
        if replacement = 0 then 0 else if replacement = 1 then 2 else 1 := by
  fin_cases replacement
  · simp [target, targetObserve, booleanUtility, Profile.update_same,
      expectedUtility_pure]
  · simp [target, targetObserve, booleanUtility, Profile.update_same,
      expectedUtility_pure]
  · have hmap : UtilityIntegrable
        (fun outcome player => booleanUtility (targetObserve outcome) player) ()
        (coin.map TargetOutcome.published) := by
      simpa [target, Profile.update_same] using h
    have hcoin : PayoffIntegrable coin (fun bit => booleanUtility bit ()) := by
      exact payoffIntegrable_of_finite coin _
    have hlaw : (coin.map TargetOutcome.published).map targetObserve =
        coin.map id := by
      have hf : targetObserve ∘ TargetOutcome.published = id := by
        funext bit
        rfl
      rw [PMF.map_comp, hf]
    have heq : expectedUtility
        (fun outcome player => booleanUtility (targetObserve outcome) player) ()
        (coin.map TargetOutcome.published) hmap =
          expect coin (fun bit => booleanUtility bit ()) hcoin := by
      exact expect_observed_law_eq (coin.map TargetOutcome.published) coin
        targetObserve id (fun bit => booleanUtility bit ()) hlaw hmap hcoin
    simpa [target, Profile.update_same] using heq.trans (coin_value hcoin)

/-- The mean-one target deviation forces the uniform certificate to select
the source action worth two. -/
example :
    ∃ alternative : source.sig.Strategy (), alternative = true ∧
      ∀ hsource : UtilityIntegrable
          (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
          (source.play (Profile.update (fun _ => false) () alternative)),
        ∃ htarget : UtilityIntegrable
            (fun outcome player => booleanUtility (targetObserve outcome) player) ()
            (target.play (Profile.update
              (layeredUtility.compileProfile (fun _ => false)) () (2 : Fin 3))),
          expectedUtility
              (fun outcome player => booleanUtility (targetObserve outcome) player) ()
              (target.play (Profile.update
                (layeredUtility.compileProfile (fun _ => false)) () (2 : Fin 3))) htarget ≤
            expectedUtility
              (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
              (source.play (Profile.update (fun _ => false) () alternative)) hsource := by
  obtain ⟨alternative, bound⟩ :=
    layeredUtility.unilateral_bound subset_rfl (fun _ => false) () (2 : Fin 3)
  refine ⟨alternative, ?_, bound⟩
  cases alternative with
  | false =>
      have hs := observed_integrable
        (source.play (Profile.update (fun _ => false) () false)) sourceObserve
      obtain ⟨ht, hle⟩ := bound hs
      rw [target_value _ 2 ht, source_value _ false hs] at hle
      norm_num [booleanUtility] at hle
  | true => rfl

/-- Error two transfers from the false source profile. -/
example : IsεNash target
    (fun outcome player => booleanUtility (targetObserve outcome) player) 2
    (layeredUtility.compileProfile (fun _ => false)) := by
  apply (layeredUtility.isεNash_compileProfile_iff 2 (fun _ => false)).mpr
  rw [isεNash_iff]
  intro who alternative
  cases who
  let hbase := observed_integrable (source.play (fun _ => false)) sourceObserve
  let hdev := observed_integrable
    (source.play (Profile.update (fun _ => false) () alternative)) sourceObserve
  refine ⟨hbase, hdev, ?_⟩
  rw [source_value _ alternative hdev]
  have hbaseValue : expectedUtility
      (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
      (source.play (fun _ => false)) hbase = 0 := by
    simp [sourceObserve, booleanUtility, expectedUtility_pure]
  rw [hbaseValue]
  cases alternative <;> norm_num [booleanUtility]

/-- The source action worth two dominates against every source profile. -/
theorem compiled_dominant_isBestResponse :
    IsBestResponse target
      (euPreference fun outcome player => booleanUtility (targetObserve outcome) player) ()
      (layeredUtility.compileProfile (fun _ => false))
      (layeredUtility.compileStrategy () true) := by
  refine layeredUtility.isBestResponse_compileStrategy_of_isDominant subset_rfl () true ?_
    (fun _ => false)
  intro alternative profile
  have hbase : UtilityIntegrable
      (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
      (source.play (Profile.update profile () true)) := observed_integrable _ sourceObserve
  have hdev : UtilityIntegrable
      (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
      (source.play (Profile.update profile () alternative)) :=
    observed_integrable _ sourceObserve
  refine ⟨hbase, hdev, ?_⟩
  rw [source_value profile alternative hdev, source_value profile true hbase]
  cases alternative <;> norm_num [booleanUtility]

/-- The mixed target deviation has value one, strictly below the compiled
source action worth two. -/
example :
    expectedUtility (fun outcome player => booleanUtility (targetObserve outcome) player) ()
        (target.play (Profile.update (layeredUtility.compileProfile (fun _ => false)) ()
          (2 : Fin 3))) (observed_integrable _ targetObserve) = 1 ∧
      expectedUtility (fun outcome player => booleanUtility (targetObserve outcome) player) ()
        (target.play (Profile.update (layeredUtility.compileProfile (fun _ => false)) ()
          (layeredUtility.compileStrategy () true)))
          (observed_integrable _ targetObserve) = 2 := by
  constructor
  · exact target_value _ 2 _
  · have hcompile : layeredUtility.compileStrategy () true = (1 : Fin 3) := rfl
    simpa [hcompile] using target_value
      (layeredUtility.compileProfile (fun _ => false)) 1
      (observed_integrable _ targetObserve)

end GameTheory.GameForm.MixtureSimulationOn.Tests
