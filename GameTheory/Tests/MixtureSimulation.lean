/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MixtureSimulationComposition
import GameTheory.Core.MixedSimulation
import GameTheory.Core.MixedSimulation

/-! # Regression tests for mixture simulation and composition -/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn.Tests

open GameTheory.Math.Probability

def coin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

inductive SourceOutcome where | observed (value : Bool)
inductive MiddleOutcome where | visible (value : Bool)
inductive TargetOutcome where | published (value : Bool)

abbrev sourceSignature : GameSignature Unit where
  Strategy _ := Bool
  Outcome := SourceOutcome

abbrev middleSignature : GameSignature Unit where
  Strategy _ := Fin 3
  Outcome := MiddleOutcome

abbrev targetSignature : GameSignature Unit where
  Strategy _ := Fin 3
  Outcome := TargetOutcome

abbrev source : GameForm Unit where
  sig := sourceSignature
  play profile := FinDist.pure (.observed (profile ()))

abbrev middle : GameForm Unit where
  sig := middleSignature
  play profile :=
    if profile () = 0 then FinDist.pure (.visible false)
    else if profile () = 1 then FinDist.pure (.visible true)
    else coin.map .visible

abbrev target : GameForm Unit where
  sig := targetSignature
  play profile :=
    if profile () = 0 then FinDist.pure (.published false)
    else if profile () = 1 then FinDist.pure (.published true)
    else coin.map .published

def sourceObserve : SourceOutcome → Bool := fun | .observed value => value
def middleObserve : MiddleOutcome → Bool := fun | .visible value => value
def targetObserve : TargetOutcome → Bool := fun | .published value => value

/-- The native mixed extension admits every finite-support mixed deviation,
while the pure maximizing profile remains canonical Nash. -/
theorem native_mixed_embedding_isNash :
    IsεNash source.mixed (fun outcome _ => if sourceObserve outcome then 1 else 0) 0
      (source.purify (fun _ => true)) := by
  rw [source.isεNash_purify_iff, isεNash_iff]
  intro who replacement
  cases who
  cases replacement <;> norm_num [source, sourceObserve, expectedUtility]

def first : MixtureSimulationOn source middle sourceObserve middleObserve (fun _ _ => True) where
  compileStrategy _ strategy := if strategy then 1 else 0
  honest_law profile := by cases h : profile () <;> simp [source, middle, sourceObserve,
    middleObserve, h]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    cases who
    fin_cases replacement
    · exact ⟨FinDist.pure false, by simp [source, middle, sourceObserve, middleObserve]⟩
    · exact ⟨FinDist.pure true, by simp [source, middle, sourceObserve, middleObserve]⟩
    · exact ⟨coin, by
        simp only [Fin.reduceFinMk, Profile.update_same, Fin.isValue, Fin.reduceEq,
          ↓reduceIte, FinDist.map_comp, FinDist.map_pure]
        rw [show middleObserve ∘ MiddleOutcome.visible = id from rfl, FinDist.map_id]
        simp only [sourceObserve, FinDist.bind_pure]⟩

def second : MixtureSimulationOn middle target middleObserve targetObserve (fun _ _ => True) where
  compileStrategy _ strategy := strategy
  honest_law profile := by
    simp only [middle, target]
    split_ifs <;> simp only [FinDist.map_pure, FinDist.map_comp, Function.comp_def,
      middleObserve, targetObserve]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    cases who
    refine ⟨FinDist.pure replacement, ?_⟩
    simp only [middle, target, FinDist.pure_bind, Profile.update_same]
    split_ifs <;> simp only [FinDist.map_pure, FinDist.map_comp, Function.comp_def,
      middleObserve, targetObserve]

def composed : MixtureSimulationOn source target sourceObserve targetObserve (fun _ _ => True) :=
  first.trans second (fun _ _ => trivial)

/-- The extra target strategy has a genuinely mixed observation law, so it
cannot be represented by selecting either pure source strategy. -/
theorem mixed_target_not_single_source :
    (target.play (fun _ => (2 : Fin 3))).map targetObserve ≠
        (source.play (fun _ => false)).map sourceObserve ∧
      (target.play (fun _ => (2 : Fin 3))).map targetObserve ≠
        (source.play (fun _ => true)).map sourceObserve := by
  have htarget : (target.play (fun _ => (2 : Fin 3))).map targetObserve = coin := by
    rw [show target.play (fun _ => (2 : Fin 3)) = coin.map TargetOutcome.published from rfl,
      FinDist.map_comp, show targetObserve ∘ TargetOutcome.published = id from rfl,
      FinDist.map_id]
  constructor <;> intro h
  · rw [htarget] at h
    simp only [FinDist.map_pure, sourceObserve] at h
    have := congrArg (fun law => law.prob true) h
    norm_num [coin, FinDist.prob_mix, FinDist.prob_pure_eq_ite] at this
  · rw [htarget] at h
    simp only [FinDist.map_pure, sourceObserve] at h
    have := congrArg (fun law => law.prob false) h
    norm_num [coin, FinDist.prob_mix, FinDist.prob_pure_eq_ite] at this

/-- Composition expands the third game's mixed deviation into the source
mixture rather than strengthening it to one source strategy. -/
example : ∃ alternatives : FinDist (source.sig.Strategy ()),
    (target.play (Profile.update (composed.compileProfile (fun _ => false)) () (2 : Fin 3))).map
        targetObserve =
      alternatives.bind fun alternative =>
        (source.play (Profile.update (fun _ => false) () alternative)).map sourceObserve :=
  composed.deviation_mixture (fun _ => false) () 2 trivial

/-- The left edge need only admit the embedded pure middle strategies. -/
def firstRestricted :
    MixtureSimulationOn source middle sourceObserve middleObserve (fun _ s => s ≠ 2) where
  compileStrategy := first.compileStrategy
  honest_law := first.honest_law
  compiled_considered who strategy := by
    cases who
    cases strategy <;> decide
  deviation_mixture profile who replacement _ :=
    first.deviation_mixture profile who replacement trivial

/-- Even the target's mixed strategy composes through the restricted left edge:
its witness uses only the two considered pure middle strategies. -/
def composedRestricted :
    MixtureSimulationOn source target sourceObserve targetObserve (fun _ _ => True) :=
  firstRestricted.transOn second fun profile who replacement _ => by
    cases who
    obtain ⟨alternatives, hlaw⟩ := first.deviation_mixture profile () replacement trivial
    refine ⟨alternatives.map (first.compileStrategy ()), ?_, ?_⟩
    · rw [FinDist.bind_map]
      have htarget :
          (target.play (Profile.update
            (second.compileProfile (firstRestricted.compileProfile profile)) () replacement)).map
              targetObserve =
          (middle.play (Profile.update
            (fun player => first.compileStrategy player (profile player)) () replacement)).map
              middleObserve := by
        simp only [target, middle, Profile.update_same]
        split_ifs <;> simp only [FinDist.map_pure, FinDist.map_comp, Function.comp_def,
          middleObserve, targetObserve]
      rw [htarget, hlaw]
      apply FinDist.bind_congr
      intro alternative _
      rw [show firstRestricted.compileProfile profile = first.compileProfile profile from rfl]
      rw [first.compileProfile_update]
      exact (first.honest_law (Profile.update profile () alternative)).symm
    · intro alternative halternative
      rw [FinDist.support_map] at halternative
      obtain ⟨pureAlternative, _, rfl⟩ := halternative
      exact firstRestricted.compiled_considered () pureAlternative

example : ∃ alternatives : FinDist Bool,
    (target.play (Profile.update (composedRestricted.compileProfile (fun _ => false)) () 2)).map
        targetObserve =
      alternatives.bind fun alternative =>
        (source.play (Profile.update (fun _ => false) () alternative)).map sourceObserve :=
  composedRestricted.deviation_mixture (fun _ => false) () 2 trivial

namespace MissingCoverage

abbrev constantSource : GameForm Unit where
  sig := { Strategy := fun _ => Unit, Outcome := Bool }
  play _ := FinDist.pure false

abbrev revealed : GameForm Unit where
  sig := { Strategy := fun _ => Bool, Outcome := Bool }
  play profile := FinDist.pure (profile ())

def left : MixtureSimulationOn constantSource revealed id id (fun _ s => s = false) where
  compileStrategy _ _ := false
  honest_law _ := rfl
  compiled_considered _ _ := rfl
  deviation_mixture profile who replacement hreplacement := by
    cases who
    subst replacement
    exact ⟨FinDist.pure (), by simp⟩

def right : MixtureSimulationOn revealed revealed id id (fun _ _ => True) where
  compileStrategy _ strategy := strategy
  honest_law _ := rfl
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ :=
    ⟨FinDist.pure replacement, by simp⟩

/-- Two individually valid restricted edges do not suffice for composition:
the right edge can introduce an outcome unavailable to the source. -/
theorem no_total_composite :
    ¬ Nonempty (MixtureSimulationOn constantSource revealed id id (fun _ _ => True)) := by
  rintro ⟨simulation⟩
  obtain ⟨alternatives, hlaw⟩ :=
    simulation.deviation_mixture (fun _ => ()) () true trivial
  simp only [revealed, constantSource, Profile.update_same, FinDist.map_id,
    FinDist.bind_const] at hlaw
  have hprob := congrArg (fun law => law.prob true) hlaw
  norm_num [FinDist.prob_pure_eq_ite] at hprob

/-- Reflection remains available without a total mixture certificate. -/
example (utility : Bool → Unit → ℝ) (ε : ℝ)
    (htarget : IsεNash revealed utility ε (fun _ => false)) :
    IsεNash constantSource utility ε (fun _ => ()) :=
  isεNash_of_honest_law (source := constantSource) (target := revealed)
    (fun _ _ => false) (fun _ => rfl)
    (sourceObserve := id) (targetObserve := id) utility ε (fun _ => ()) htarget

end MissingCoverage

end GameTheory.GameForm.MixtureSimulationOn.Tests
