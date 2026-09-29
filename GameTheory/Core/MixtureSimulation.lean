/- Copyright (c) 2026 GameTheory contributors. All rights reserved. -/

import GameTheory.Core.Approximate

/-! # Game-form simulation by PMF mixtures of unilateral deviations -/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uι us uo us' uo' uv

section DirectTransfer

variable {Player : Type uι} [DecidableEq Player]
variable {source : GameForm.{uι, us, uo} Player}
variable {target : GameForm.{uι, us', uo'} Player}
variable {Observation : Type uv}
variable {sourceObserve : source.sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}

private theorem isεNash_of_compiled_deviations
    (compile : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honest_law : ∀ profile,
      (target.play (Profile.map compile profile)).map targetObserve =
        (source.play profile).map sourceObserve)
    (value : Observation → Player → ℝ) (ε : ℝ) (profile : Profile source.sig)
    (hcompiled : ∀ who (replacement : source.sig.Strategy who),
      euPreferenceWithin ε (fun outcome player => value (targetObserve outcome) player) who
        (target.play (Profile.map compile profile))
        (target.play (Profile.update (Profile.map compile profile) who
          (compile who replacement)))) :
    IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile := by
  have hexpectation : ∀ (players : Profile source.sig) who,
      UtilityHasExpectation (fun outcome player => value (targetObserve outcome) player) who
          (target.play (Profile.map compile players)) ↔
        UtilityHasExpectation (fun outcome player => value (sourceObserve outcome) player) who
          (source.play players) := fun players who =>
    hasExpectation_observed_law_iff _ _ targetObserve sourceObserve
      (fun observation => value observation who) (honest_law players)
  have hvalue : ∀ (players : Profile source.sig) who,
      extendedExpectedUtility (fun outcome player => value (targetObserve outcome) player) who
          (target.play (Profile.map compile players)) =
        extendedExpectedUtility (fun outcome player => value (sourceObserve outcome) player) who
          (source.play players) := fun players who =>
    extendedExpect_observed_law_eq _ _ targetObserve sourceObserve
      (fun observation => value observation who) (honest_law players)
  rw [GameTheory.isεNash_iff]
  intro who replacement
  obtain ⟨htbase, htdev, hle⟩ := hcompiled who replacement
  rw [← Profile.map_update compile profile who replacement] at htdev hle
  rw [hvalue, hvalue] at hle
  exact ⟨(hexpectation _ _).1 htbase, (hexpectation _ _).1 htdev, hle⟩

/-- Honest observed-law equality reflects approximate Nash; no target
strategy representation is needed in this direction. -/
theorem isεNash_of_honest_law
    (compile : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honest_law : ∀ profile,
      (target.play (Profile.map compile profile)).map targetObserve =
        (source.play profile).map sourceObserve)
    (value : Observation → Player → ℝ) (ε : ℝ) (profile : Profile source.sig)
    (htarget : IsεNash target (fun outcome who => value (targetObserve outcome) who) ε
      (Profile.map compile profile)) :
    IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile := by
  apply isεNash_of_compiled_deviations compile honest_law value ε profile
  intro who replacement
  exact (GameTheory.isεNash_iff _ _).mp htarget who (compile who replacement)

/-- Exact Nash is the zero-slack specialization of honest-law reflection. -/
theorem isNash_of_honest_law
    (compile : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honest_law : ∀ profile,
      (target.play (Profile.map compile profile)).map targetObserve =
        (source.play profile).map sourceObserve)
    (value : Observation → Player → ℝ) (profile : Profile source.sig)
    (htarget : IsNash target (euPreference fun outcome who => value (targetObserve outcome) who)
      (Profile.map compile profile)) :
    IsNash source (euPreference fun outcome who => value (sourceObserve outcome) who)
      profile := by
  rw [GameTheory.isNash_iff_isεNash_zero] at htarget ⊢
  exact isεNash_of_honest_law compile honest_law value 0 profile htarget

/-- An arbitrary PMF mixture of source deviations preserves each considered
deviation comparison when its actual target law has an expected utility. -/
theorem considered_deviations_of_isεNash_of_mixtures
    (profile : Profile source.sig) (targetProfile : Profile target.sig)
    (Considered : (who : Player) → target.sig.Strategy who → Prop)
    (honest_law : (target.play targetProfile).map targetObserve =
      (source.play profile).map sourceObserve)
    (deviation_mixture : ∀ who replacement, Considered who replacement →
      ∃ alternatives : PMF (source.sig.Strategy who),
        (target.play (Profile.update targetProfile who replacement)).map targetObserve =
          alternatives.bind fun alternative =>
            (source.play (Profile.update profile who alternative)).map sourceObserve)
    (value : Observation → Player → ℝ) (ε : ℝ)
    (hdev : ∀ who replacement, Considered who replacement →
      UtilityHasExpectation (fun outcome player => value (targetObserve outcome) player) who
        (target.play (Profile.update targetProfile who replacement)))
    (hsource : IsεNash source
      (fun outcome who => value (sourceObserve outcome) who) ε profile) :
    ∀ who replacement, Considered who replacement →
      euPreferenceWithin ε (fun outcome player => value (targetObserve outcome) player) who
        (target.play targetProfile)
        (target.play (Profile.update targetProfile who replacement)) := by
  rw [GameTheory.isεNash_iff] at hsource
  intro who replacement hconsidered
  obtain ⟨alternatives, hlaw⟩ := deviation_mixture who replacement hconsidered
  obtain ⟨hsbase, _, _⟩ := hsource who (profile who)
  have hbase : extendedExpectedUtility
      (fun outcome player => value (targetObserve outcome) player) who
      (target.play targetProfile) =
        extendedExpectedUtility (fun outcome player => value (sourceObserve outcome) player)
          who (source.play profile) :=
    extendedExpect_observed_law_eq _ _ targetObserve sourceObserve
      (fun observation => value observation who) honest_law
  have hdevValue : extendedExpectedUtility
      (fun outcome player => value (targetObserve outcome) player) who
      (target.play (Profile.update targetProfile who replacement)) =
        extendedExpect (alternatives.bind fun alternative =>
            (source.play (Profile.update profile who alternative)).map sourceObserve)
          (fun observation => value observation who) := by
    rw [← hlaw]
    exact (extendedExpect_map targetObserve _ (fun observation => value observation who)).symm
  refine ⟨(hasExpectation_observed_law_iff _ _ targetObserve sourceObserve
      (fun observation => value observation who) honest_law).2 hsbase,
    hdev who replacement hconsidered, ?_⟩
  rw [hdevValue, hbase]
  exact extendedExpect_bind_le fun alternative _ =>
    (extendedExpect_map sourceObserve _ _).trans_le (hsource who alternative).2.2

end DirectTransfer

/-- Exact common-observation laws. Each considered target deviation is an
ordinary PMF mixture of legal unilateral source deviations. -/
structure MixtureSimulationOn {Player : Type uι} [DecidableEq Player]
    (source : GameForm.{uι, us, uo} Player) (target : GameForm.{uι, us', uo'} Player)
    {Observation : Type uv} (sourceObserve : source.sig.Outcome → Observation)
    (targetObserve : target.sig.Outcome → Observation)
    (Considered : (who : Player) → target.sig.Strategy who → Prop) where
  /-- Compile each player's source strategy into its target strategy. -/
  compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who
  honest_law : ∀ profile,
    (target.play (Profile.map compileStrategy profile)).map targetObserve =
      (source.play profile).map sourceObserve
  compiled_considered : ∀ who strategy, Considered who (compileStrategy who strategy)
  deviation_mixture : ∀ profile who replacement, Considered who replacement →
    ∃ alternatives : PMF (source.sig.Strategy who),
      (target.play (Profile.update (Profile.map compileStrategy profile)
        who replacement)).map targetObserve =
      alternatives.bind fun alternative =>
        (source.play (Profile.update profile who alternative)).map sourceObserve

namespace MixtureSimulationOn

variable {Player : Type uι} [DecidableEq Player]
variable {source : GameForm.{uι, us, uo} Player}
variable {target : GameForm.{uι, us', uo'} Player}
variable {Observation : Type uv}
variable {sourceObserve : source.sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}
variable (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)

/-- Compile every coordinate of a source strategy profile. -/
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

/-- Reobserve both sides through one further reading. -/
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
    rw [hs, ht, ← PMF.map_comp, ← PMF.map_comp, simulation.honest_law profile]
  compiled_considered := simulation.compiled_considered
  deviation_mixture profile who replacement hconsidered := by
    obtain ⟨alternatives, hlaw⟩ :=
      simulation.deviation_mixture profile who replacement hconsidered
    refine ⟨alternatives, ?_⟩
    have hs : sourceObserve' = f ∘ sourceObserve := funext hsource
    have ht : targetObserve' = f ∘ targetObserve := funext htarget
    rw [hs, ht, ← PMF.map_comp, hlaw, PMF.map_bind]
    congr 1
    funext alternative
    exact PMF.map_comp _ _ _

/-- Replace a target reading by one with the same law on every play. -/
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

/-- Honest observed laws preserve integrability and guarded values. -/
theorem integrable_compile_iff (profile : Profile source.sig)
    (value : Observation → ℝ) :
    PayoffIntegrable (target.play (simulation.compileProfile profile))
        (value ∘ targetObserve) ↔
      PayoffIntegrable (source.play profile) (value ∘ sourceObserve) :=
  payoffIntegrable_observed_law_iff _ _ targetObserve sourceObserve value
    (simulation.honest_law profile)

theorem expect_compile (profile : Profile source.sig) (value : Observation → ℝ) :
    expect (target.play (simulation.compileProfile profile))
        (value ∘ targetObserve) =
      expect (source.play profile) (value ∘ sourceObserve) :=
  expect_observed_law_eq _ _ targetObserve sourceObserve value
    (simulation.honest_law profile)

/-- A lower bound on every source deviation transfers to a considered target
mixture once that actual target deviation is integrable. -/
theorem guarantee (profile : Profile source.sig) (who : Player)
    (value : Observation → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : source.sig.Strategy who,
      PayoffIntegrable
          (source.play (Profile.update profile who alternative))
          (value ∘ sourceObserve) →
        bound ≤ expect (source.play (Profile.update profile who alternative))
          (value ∘ sourceObserve))
    (replacement : target.sig.Strategy who) (hconsidered : Considered who replacement)
    (htarget : PayoffIntegrable
      (target.play (Profile.update (simulation.compileProfile profile) who replacement))
      (value ∘ targetObserve)) :
    bound ≤ expect
      (target.play (Profile.update (simulation.compileProfile profile) who replacement))
      (value ∘ targetObserve) := by
  let kernel : source.sig.Strategy who → PMF Observation := fun alternative =>
    (source.play (Profile.update profile who alternative)).map sourceObserve
  obtain ⟨alternatives, hlaw⟩ :=
    simulation.deviation_mixture profile who replacement hconsidered
  have htobs : PayoffIntegrable
      ((target.play (Profile.update
        (simulation.compileProfile profile) who replacement)).map targetObserve)
      value := (payoffIntegrable_map_iff targetObserve _ value).mpr htarget
  have hbind : PayoffIntegrable (alternatives.bind kernel) value := by
    rw [← hlaw]
    exact htobs
  have hmean : bound ≤ expect (alternatives.bind kernel) value := by
    apply expect_bind_ge_constant_on_support alternatives kernel value bound hbind
    intro alternative ha
    have hcond := payoffIntegrable_bind_conditional_on_support
      alternatives kernel value hbind alternative ha
    have hsource : PayoffIntegrable
        (source.play (Profile.update profile who alternative))
        (value ∘ sourceObserve) :=
      (payoffIntegrable_map_iff sourceObserve _ value).mp hcond
    exact (hbound alternative hsource).trans_eq
      (expect_map sourceObserve _ value).symm
  calc
    bound ≤ expect (alternatives.bind kernel) value := hmean
    _ = expect ((target.play (Profile.update
        (simulation.compileProfile profile) who replacement)).map targetObserve)
        value := (expect_congr_law hlaw value).symm
    _ = expect (target.play (Profile.update
        (simulation.compileProfile profile) who replacement))
        (value ∘ targetObserve) :=
      expect_map targetObserve _ value

/-- The considered target comparisons are equivalent to source approximate
Nash together with an expected utility for every actual considered target
deviation. -/
theorem considered_deviations_iff_isεNash
    (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig) :
    (∀ who replacement, Considered who replacement →
      euPreferenceWithin ε
        (fun outcome player => value (targetObserve outcome) player) who
        (target.play (simulation.compileProfile profile))
        (target.play (Profile.update (simulation.compileProfile profile) who replacement))) ↔
      IsεNash source (fun outcome player => value (sourceObserve outcome) player) ε profile ∧
        ∀ who replacement, Considered who replacement →
          UtilityHasExpectation
            (fun outcome player => value (targetObserve outcome) player) who
            (target.play (Profile.update
              (simulation.compileProfile profile) who replacement)) := by
  constructor
  · intro h
    constructor
    · apply isεNash_of_compiled_deviations simulation.compileStrategy
        simulation.honest_law value ε profile
      intro who replacement
      exact h who (simulation.compileStrategy who replacement)
        (simulation.compiled_considered who replacement)
    · intro who replacement hconsidered
      obtain ⟨_, hdev, _⟩ := h who replacement hconsidered
      exact hdev
  · rintro ⟨hsource, hdev⟩ who replacement hconsidered
    exact considered_deviations_of_isεNash_of_mixtures profile
      (simulation.compileProfile profile) Considered (simulation.honest_law profile)
      (simulation.deviation_mixture profile) value ε hdev hsource
      who replacement hconsidered

/-- Total consideration yields an exact iff. The additional conjunct is the
expected utility each actual target deviation law must have. -/
theorem isεNash_compileProfile_iff (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsεNash target (fun outcome who => value (targetObserve outcome) who) ε
        (simulation.compileProfile profile) ↔
      IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile ∧
        ∀ who replacement,
          UtilityHasExpectation
            (fun outcome player => value (targetObserve outcome) player) who
            (target.play (Profile.update
              (simulation.compileProfile profile) who replacement)) := by
  constructor
  · intro htarget
    have h := (simulation.considered_deviations_iff_isεNash value ε profile).mp
      (fun who replacement _ =>
        (GameTheory.isεNash_iff _ _).mp htarget who replacement)
    exact ⟨h.1, fun who replacement => h.2 who replacement (hall who replacement)⟩
  · intro h
    have hconsidered :=
      (simulation.considered_deviations_iff_isεNash value ε profile).mpr
        ⟨h.1, fun who replacement _ => h.2 who replacement⟩
    apply (GameTheory.isεNash_iff _ _).mpr
    intro who replacement
    exact hconsidered who replacement (hall who replacement)

theorem isNash_compileProfile_iff (value : Observation → Player → ℝ)
    (profile : Profile source.sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsNash target (euPreference fun outcome who => value (targetObserve outcome) who)
        (simulation.compileProfile profile) ↔
      IsNash source (euPreference fun outcome who => value (sourceObserve outcome) who)
        profile ∧
        ∀ who replacement,
          UtilityHasExpectation
            (fun outcome player => value (targetObserve outcome) player) who
            (target.play (Profile.update
              (simulation.compileProfile profile) who replacement)) := by
  simpa only [GameTheory.isNash_iff_isεNash_zero] using
    simulation.isεNash_compileProfile_iff value 0 profile hall

end MixtureSimulationOn
end GameTheory.GameForm
