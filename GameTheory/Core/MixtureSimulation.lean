/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.Approximate

/-! # Game-form simulation by finite mixtures of unilateral deviations -/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uι us uo us' uo' uv

section DirectTransfer

variable {Player : Type uι} [DecidableEq Player]
variable {source : GameForm.{uι, us, uo} Player} {target : GameForm.{uι, us', uo'} Player}
variable {Observation : Type uv} {sourceObserve : source.sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}

/-- Honest observed laws alone reflect approximate Nash. No representation of
target deviations, or restriction on them, is required in this direction. -/
theorem isεNash_of_honest_law
    (compile : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honest_law : ∀ profile,
      (target.play (Profile.map compile profile)).map targetObserve =
        (source.play profile).map sourceObserve)
    (value : Observation → Player → ℝ) (ε : ℝ) (profile : Profile source.sig)
    (htarget : IsεNash target (fun outcome who => value (targetObserve outcome) who) ε
      (Profile.map compile profile)) :
    IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile := by
  have hexpect (players : Profile source.sig) (who : Player) :
      (target.play (Profile.map compile players)).expect
          (fun outcome => value (targetObserve outcome) who) =
        (source.play players).expect (fun outcome => value (sourceObserve outcome) who) := by
    simpa only [FinDist.expect_map] using
      congrArg (fun law => law.expect (fun observation => value observation who))
        (honest_law players)
  rw [GameTheory.isεNash_iff] at htarget ⊢
  intro who replacement
  have h := htarget who (compile who replacement)
  dsimp only [expectedUtility] at h
  rw [← Profile.map_update, hexpect, hexpect] at h
  exact h

/-- The exact-Nash specialization of honest-law-only reflection. -/
theorem isNash_of_honest_law
    (compile : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honest_law : ∀ profile,
      (target.play (Profile.map compile profile)).map targetObserve =
        (source.play profile).map sourceObserve)
    (value : Observation → Player → ℝ) (profile : Profile source.sig)
    (htarget : IsNash target (euPreference fun outcome who => value (targetObserve outcome) who)
      (Profile.map compile profile)) :
    IsNash source (euPreference fun outcome who => value (sourceObserve outcome) who) profile := by
  rw [GameTheory.isNash_iff_isεNash_zero] at htarget ⊢
  exact isεNash_of_honest_law compile honest_law value 0 profile htarget

/-- Profile-local finite-mixture coverage preserves every considered deviation
bound. Only this profile's honest law is needed; compilation need not cover a
considered target strategy in this direction. -/
theorem considered_deviations_of_isεNash_of_mixtures
    (profile : Profile source.sig) (targetProfile : Profile target.sig)
    (Considered : (who : Player) → target.sig.Strategy who → Prop)
    (honest_law : (target.play targetProfile).map targetObserve =
      (source.play profile).map sourceObserve)
    (deviation_mixture : ∀ who replacement, Considered who replacement →
      ∃ alternatives : FinDist (source.sig.Strategy who),
        (target.play (Profile.update targetProfile who replacement)).map targetObserve =
          alternatives.bind fun alternative =>
            (source.play (Profile.update profile who alternative)).map sourceObserve)
    (value : Observation → Player → ℝ) (ε : ℝ)
    (hsource : IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile) :
    ∀ who replacement, Considered who replacement →
      (target.play (Profile.update targetProfile who replacement)).expect
          (fun outcome => value (targetObserve outcome) who) ≤
        (target.play targetProfile).expect
          (fun outcome => value (targetObserve outcome) who) + ε := by
  rw [GameTheory.isεNash_iff] at hsource
  intro who replacement hconsidered
  obtain ⟨alternatives, hlaw⟩ := deviation_mixture who replacement hconsidered
  have hdev := congrArg (fun law => law.expect (fun observation => value observation who)) hlaw
  have hhonest :=
    congrArg (fun law => law.expect (fun observation => value observation who)) honest_law
  simp only [FinDist.expect_map, FinDist.expect_bind] at hdev hhonest
  rw [hdev, hhonest]
  exact FinDist.expect_le_of_forall _ _ _ fun alternative _ => hsource who alternative

end DirectTransfer

/-- Exact common-observation laws, with each target deviation represented by
a finite mixture of legal unilateral source deviations. -/
structure MixtureSimulationOn {Player : Type uι} [DecidableEq Player]
    (source : GameForm.{uι, us, uo} Player) (target : GameForm.{uι, us', uo'} Player)
    {Observation : Type uv} (sourceObserve : source.sig.Outcome → Observation)
    (targetObserve : target.sig.Outcome → Observation)
    (Considered : (who : Player) → target.sig.Strategy who → Prop) where
  compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who
  honest_law : ∀ profile,
    (target.play (fun who => compileStrategy who (profile who))).map targetObserve =
      (source.play profile).map sourceObserve
  compiled_considered : ∀ who strategy, Considered who (compileStrategy who strategy)
  deviation_mixture : ∀ profile who replacement, Considered who replacement →
    ∃ alternatives : FinDist (source.sig.Strategy who),
      (target.play (Profile.update (fun player => compileStrategy player (profile player))
        who replacement)).map targetObserve =
      alternatives.bind fun alternative =>
        (source.play (Profile.update profile who alternative)).map sourceObserve

namespace MixtureSimulationOn

variable {Player : Type uι} [DecidableEq Player]
variable {source : GameForm.{uι, us, uo} Player} {target : GameForm.{uι, us', uo'} Player}
variable {Observation : Type uv} {sourceObserve : source.sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}
variable (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)

def compileProfile (profile : Profile source.sig) : Profile target.sig :=
  Profile.map simulation.compileStrategy profile

@[simp] theorem compileProfile_apply (profile : Profile source.sig) (who : Player) :
    simulation.compileProfile profile who = simulation.compileStrategy who (profile who) := rfl

theorem compileProfile_update (profile : Profile source.sig) (who : Player)
    (replacement : source.sig.Strategy who) :
    Profile.update (simulation.compileProfile profile) who
        (simulation.compileStrategy who replacement) =
      simulation.compileProfile (Profile.update profile who replacement) := by
  exact (Profile.map_update simulation.compileStrategy profile who replacement).symm

/-- Read an edge through a coarser observation. Both sides must be read the same
way, which is what keeps the certificate meaningful: the edge still equates
laws, now of what the new reading sees. This is how two edges are brought to a
common observation before composing. -/
def reobserve {Observation' : Type*} (f : Observation → Observation')
    (sourceObserve' : source.sig.Outcome → Observation')
    (targetObserve' : target.sig.Outcome → Observation')
    (hsource : ∀ outcome, sourceObserve' outcome = f (sourceObserve outcome))
    (htarget : ∀ outcome, targetObserve' outcome = f (targetObserve outcome)) :
    MixtureSimulationOn source target sourceObserve' targetObserve' Considered where
  compileStrategy := simulation.compileStrategy
  honest_law profile := by
    have hs : sourceObserve' = f ∘ sourceObserve := funext hsource
    have ht : targetObserve' = f ∘ targetObserve := funext htarget
    rw [hs, ht, ← FinDist.map_comp, ← FinDist.map_comp, simulation.honest_law profile]
  compiled_considered := simulation.compiled_considered
  deviation_mixture profile who replacement hconsidered := by
    obtain ⟨alternatives, hlaw⟩ :=
      simulation.deviation_mixture profile who replacement hconsidered
    refine ⟨alternatives, ?_⟩
    have hs : sourceObserve' = f ∘ sourceObserve := funext hsource
    have ht : targetObserve' = f ∘ targetObserve := funext htarget
    rw [hs, ht, ← FinDist.map_comp, hlaw, FinDist.map_bind]
    exact FinDist.bind_congr fun alternative _ => FinDist.map_comp _ _ _

/-- Replace the target's reading by one that agrees with it on every play. The
hypothesis is about laws, not about outcomes: a reading that differs where the
game never goes is still the same edge. -/
def reobserveTarget (targetObserve' : target.sig.Outcome → Observation)
    (agree : ∀ players : Profile target.sig,
      (target.play players).map targetObserve' = (target.play players).map targetObserve) :
    MixtureSimulationOn source target sourceObserve targetObserve' Considered where
  compileStrategy := simulation.compileStrategy
  honest_law profile := by
    rw [agree]
    exact simulation.honest_law profile
  compiled_considered := simulation.compiled_considered
  deviation_mixture profile who replacement hconsidered := by
    obtain ⟨alternatives, hlaw⟩ :=
      simulation.deviation_mixture profile who replacement hconsidered
    refine ⟨alternatives, ?_⟩
    rw [agree]
    exact hlaw

theorem expect_compile (profile : Profile source.sig) (value : Observation → ℝ) :
    (target.play (simulation.compileProfile profile)).expect
        (fun outcome => value (targetObserve outcome)) =
      (source.play profile).expect (fun outcome => value (sourceObserve outcome)) := by
  unfold compileProfile Profile.map
  have hlaw := congrArg (fun law => law.expect value) (simulation.honest_law profile)
  simpa only [FinDist.expect_map] using hlaw

theorem guarantee (profile : Profile source.sig) (who : Player)
    (value : Observation → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : source.sig.Strategy who,
      bound ≤ (source.play (Profile.update profile who alternative)).expect
        (value ∘ sourceObserve))
    (replacement : target.sig.Strategy who) (hconsidered : Considered who replacement) :
    bound ≤ (target.play
      (Profile.update (simulation.compileProfile profile) who replacement)).expect
        (value ∘ targetObserve) := by
  obtain ⟨alternatives, hlaw⟩ :=
    simulation.deviation_mixture profile who replacement hconsidered
  have hexpect := congrArg (fun law => law.expect value) hlaw
  simp only [FinDist.expect_map, FinDist.expect_bind] at hexpect
  unfold compileProfile Profile.map
  dsimp only [Function.comp_def]
  rw [hexpect]
  calc
    bound = alternatives.expect (fun _ => bound) := (FinDist.expect_const _ _).symm
    _ ≤ _ := FinDist.expect_mono fun alternative _ => by
      simpa only [Function.comp_def] using hbound alternative

theorem considered_deviations_iff_isεNash (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig) :
    (∀ who replacement, Considered who replacement →
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
          (fun outcome => value (targetObserve outcome) who) ≤
        (target.play (simulation.compileProfile profile)).expect
          (fun outcome => value (targetObserve outcome) who) + ε) ↔
      IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile := by
  rw [GameTheory.isεNash_iff]
  constructor
  · intro h who alternative
    have hdev := h who (simulation.compileStrategy who alternative)
      (simulation.compiled_considered who alternative)
    rw [simulation.compileProfile_update] at hdev
    rw [
      simulation.expect_compile (Profile.update profile who alternative)
        (fun observation => value observation who),
      simulation.expect_compile profile (fun observation => value observation who)] at hdev
    exact hdev
  · intro h
    exact considered_deviations_of_isεNash_of_mixtures profile
      (simulation.compileProfile profile) Considered (simulation.honest_law profile)
      (simulation.deviation_mixture profile) value ε ((GameTheory.isεNash_iff _ _).2 h)

theorem isεNash_compileProfile_iff (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsεNash target (fun outcome who => value (targetObserve outcome) who) ε
        (simulation.compileProfile profile) ↔
      IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile := by
  rw [← simulation.considered_deviations_iff_isεNash value ε profile]
  rw [GameTheory.isεNash_iff]
  constructor
  · intro h who replacement _
    exact h who replacement
  · intro h who replacement
    exact h who replacement (hall who replacement)

theorem isNash_compileProfile_iff (value : Observation → Player → ℝ)
    (profile : Profile source.sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsNash target (euPreference fun outcome who => value (targetObserve outcome) who)
        (simulation.compileProfile profile) ↔
      IsNash source (euPreference fun outcome who => value (sourceObserve outcome) who)
        profile := by
  simpa only [GameTheory.isNash_iff_isεNash_zero] using
    simulation.isεNash_compileProfile_iff value 0 profile hall

end MixtureSimulationOn
end GameTheory.GameForm
