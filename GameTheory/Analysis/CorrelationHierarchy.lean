/-
# Correlated and coarse correlated equilibrium as preservation targets

Correlated equilibrium refines coarse correlated equilibrium, but the gap is
not one of reachability. A coarse deviation is committed before the
recommendation is seen, so its comparison is the sum, over recommendations, of
the correlated comparisons that switch that recommendation; no probability
condition on the device turns such a sum back into its summands. Only a
point-mass device removes the aggregation: then Nash, coarse correlated, and
correlated equilibrium coincide.

Two standard game forms realize the separations of the preservation
properties. In the *mediated extension* a player chooses a response to its own
private recommendation; its Nash comparisons at the obedient profile are the
correlated comparisons of the device, so compiling a device into its mediated
extension preserves correlated equilibrium but preserves coarse correlated
equilibrium only when the two already coincide. In the *commitment form* a
player either obeys or commits to an action before the draw; its Nash
comparisons are the coarse comparisons, so compiling it back into the device
preserves coarse correlated equilibrium but preserves correlated equilibrium
only when the two already coincide.
-/

import GameTheory.Analysis.IncentiveHierarchy

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uv

variable {ι : Type uι} [DecidableEq ι] {Observation : Type uv}

namespace GameForm

variable (F : GameForm.{uι, us, uo} ι)

/-! ## Point-mass devices -/

/-- At a point-mass device a recommendation-dependent deviation is the
constant deviation to its response to the recommended strategy. -/
theorem equilibriumComparison_recommendation_pure (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) (who : ι)
    (respond : F.sig.Strategy who → F.sig.Strategy who) :
    equilibriumComparison F (PMF.pure profile) (DeviationScheme.recommendation F.sig) observe
        who respond =
      equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
        observe who (respond (profile who)) := by
  simp [equilibriumComparison, PMF.pure_map]

/-- **No aggregation without correlation.** At a point-mass device the
correlated comparisons imply the coarse ones and conversely, for every
utility. -/
theorem implies_recommendation_pure (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies
        (equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
          observe)
        (equilibriumComparison F (PMF.pure profile) (DeviationScheme.recommendation F.sig)
          observe) ∧
      IncentiveComparison.Implies
        (equilibriumComparison F (PMF.pure profile) (DeviationScheme.recommendation F.sig)
          observe)
        (equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
          observe) := by
  refine ⟨fun utility holds who respond => ?_, fun utility holds who replacement => ?_⟩
  · exact (IncentiveComparison.holds_iff_of_eq
      (F.equilibriumComparison_recommendation_pure profile observe who respond) _).2 (holds who _)
  · exact (IncentiveComparison.holds_iff_of_eq
      (F.equilibriumComparison_recommendation_pure profile observe who fun _ => replacement)
        _).1 (holds who _)

/-- Correlated comparisons always imply coarse ones: a coarse deviation is the
correlated deviation that ignores the recommendation. -/
theorem implies_unilateralConstant (device : PMF (Profile F.sig))
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies
      (equilibriumComparison F device (DeviationScheme.recommendation F.sig) observe)
      (equilibriumComparison F device (DeviationScheme.unilateralConstant F.sig) observe) := by
  intro utility holds who replacement
  have hsame : equilibriumComparison F device (DeviationScheme.recommendation F.sig) observe
      who (fun _ => replacement) =
      equilibriumComparison F device (DeviationScheme.unilateralConstant F.sig) observe
        who replacement := by
    simp only [equilibriumComparison]
    rfl
  exact (IncentiveComparison.holds_iff_of_eq hsame _).1 (holds who _)

/-! ## Randomized deviations -/

/-- A randomized deviation's law is the mixture, over its draws, of the constant
deviations' laws. -/
theorem outcomeLaw_unilateralRandomized (statusQuo : PMF (Profile F.sig)) (who : ι)
    (replacement : PMF (F.sig.Strategy who)) :
    F.outcomeLaw ((DeviationScheme.unilateralRandomized F.sig).apply statusQuo who
        replacement) =
      replacement.bind fun strategy => F.outcomeLaw
        ((DeviationScheme.unilateralConstant F.sig).apply statusQuo who strategy) := by
  simp only [DeviationScheme.unilateralRandomized_apply,
    DeviationScheme.unilateralConstant_apply, GameForm.outcomeLaw, PMF.bind_bind,
    PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- **Randomized deviations add nothing.** Against any status quo, constant and
randomized unilateral deviations give families that imply each other for every
utility: a randomized comparison is a mixture of constant ones. -/
theorem implies_unilateralRandomized_iff [Finite Observation] (statusQuo : PMF (Profile F.sig))
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies
        (equilibriumComparison F statusQuo (DeviationScheme.unilateralConstant F.sig) observe)
        (equilibriumComparison F statusQuo (DeviationScheme.unilateralRandomized F.sig) observe) ∧
      IncentiveComparison.Implies
        (equilibriumComparison F statusQuo (DeviationScheme.unilateralRandomized F.sig) observe)
        (equilibriumComparison F statusQuo (DeviationScheme.unilateralConstant F.sig) observe) := by
  refine ⟨fun utility holds who replacement => ?_, fun utility holds who replacement => ?_⟩
  · have halternative : (equilibriumComparison F statusQuo
        (DeviationScheme.unilateralRandomized F.sig) observe who replacement).alternative =
        replacement.bind fun strategy => (equilibriumComparison F statusQuo
          (DeviationScheme.unilateralConstant F.sig) observe who strategy).alternative := by
      exact (congrArg (PMF.map observe)
        (F.outcomeLaw_unilateralRandomized statusQuo who replacement)).trans (PMF.map_bind _ _ _)
    change euPreference _ () _ _
    refine ⟨hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _),
      hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _), ?_⟩
    rw [halternative]
    exact extendedExpect_bind_le fun strategy _ => (holds who strategy).2.2
  · have hsame : equilibriumComparison F statusQuo (DeviationScheme.unilateralRandomized F.sig)
        observe who (PMF.pure replacement) =
        equilibriumComparison F statusQuo (DeviationScheme.unilateralConstant F.sig) observe
          who replacement := by
      unfold equilibriumComparison
      exact congrArg (fun law => IncentiveComparison.mk ((F.outcomeLaw statusQuo).map observe)
        ((F.outcomeLaw law).map observe))
          ((DeviationScheme.constantToRandomized F.sig).apply_eq statusQuo who replacement)
    exact (IncentiveComparison.holds_iff_of_eq hsame _).1 (holds who _)

/-! ## The mixed extension -/

section Mixed

variable [Fintype ι]

/-- In the mixed extension a mixed deviation's comparison is the mixture of the
pure deviations' comparisons, so pure deviations imply mixed ones for every
utility. -/
theorem implies_mixed_of_pure [Finite Observation] (profile : Profile F.sig.mixed)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies
      (fun who (strategy : F.sig.Strategy who) =>
        equilibriumComparison F.mixed (PMF.pure profile)
          (DeviationScheme.unilateralConstant _) observe who (PMF.pure strategy))
      (equilibriumComparison F.mixed (PMF.pure profile)
        (DeviationScheme.unilateralConstant _) observe) := by
  intro utility holds who replacement
  have hstatus (mixed : PMF (F.sig.Strategy who)) :
      (DeviationScheme.unilateralConstant F.mixed.sig).apply (PMF.pure profile) who mixed =
        PMF.pure (Profile.update profile who mixed) :=
    (DeviationScheme.unilateralConstant_apply _ _ _ _).trans (PMF.pure_map _ _)
  have halternative : (equilibriumComparison F.mixed (PMF.pure profile)
      (DeviationScheme.unilateralConstant _) observe who replacement).alternative =
      replacement.bind fun strategy => (equilibriumComparison F.mixed (PMF.pure profile)
        (DeviationScheme.unilateralConstant _) observe who (PMF.pure strategy)).alternative := by
    change (F.mixed.outcomeLaw _).map observe = _
    simp only [equilibriumComparison]
    rw [hstatus replacement, GameForm.outcomeLaw, PMF.pure_bind,
      GameForm.mixed_play_update F profile who replacement]
    refine (PMF.map_bind _ _ _).trans (congrArg _ (funext fun strategy => ?_))
    rw [hstatus (PMF.pure strategy), GameForm.outcomeLaw, PMF.pure_bind]
  change euPreference _ () _ _
  refine ⟨hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _),
    hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _), ?_⟩
  rw [halternative]
  exact extendedExpect_bind_le fun strategy _ => (holds who strategy).2.2

/-- At a profile of point masses, the mixed extension's pure-deviation
comparisons are the original game's Nash comparisons. -/
theorem equilibriumComparison_mixed_pure (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) (who : ι) (strategy : F.sig.Strategy who) :
    equilibriumComparison F.mixed (PMF.pure fun player => PMF.pure (profile player))
        (DeviationScheme.unilateralConstant _) observe who (PMF.pure strategy) =
      equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
        observe who strategy := by
  have hupdate : (Profile.update (sig := F.mixed.sig) (fun player => PMF.pure (profile player))
      who (PMF.pure strategy)) =
        fun player => PMF.pure (Profile.update profile who strategy player) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Profile.update_of_ne _ _ hplayer]
  simp only [equilibriumComparison, DeviationScheme.unilateralConstant_apply, PMF.pure_map,
    GameForm.outcomeLaw, PMF.pure_bind]
  simp only [independentProduct_pure, PMF.pure_bind]
  congr 2
  exact (congrArg (fun law => (independentProduct law).bind F.play) hupdate).trans
    (by rw [independentProduct_pure, PMF.pure_bind])

/-- **Pure and mixed Nash are one family.** At a pure profile, the original
game's Nash family and the mixed extension's Nash family imply each other for
every utility. -/
theorem implies_mixed_iff [Finite Observation] (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies
        (equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
          observe)
        (equilibriumComparison F.mixed (PMF.pure fun player => PMF.pure (profile player))
          (DeviationScheme.unilateralConstant _) observe) ∧
      IncentiveComparison.Implies
        (equilibriumComparison F.mixed (PMF.pure fun player => PMF.pure (profile player))
          (DeviationScheme.unilateralConstant _) observe)
        (equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
          observe) := by
  have hsame (utility : Observation → ι → ℝ) (who : ι) (strategy : F.sig.Strategy who) :=
    IncentiveComparison.holds_iff_of_eq
      (F.equilibriumComparison_mixed_pure profile observe who strategy) (utility · who)
  refine ⟨fun utility holds => F.implies_mixed_of_pure _ observe utility
      fun who strategy => (hsame utility who strategy).2 (holds who strategy),
    fun utility holds who strategy => (hsame utility who strategy).1 (holds who _)⟩

end Mixed

/-! ## The mediated extension -/

/-- The mediated extension: the device draws a recommendation profile and each
player applies its own response to its own recommendation. -/
@[reducible]
def mediated (device : PMF (Profile F.sig)) : GameForm ι where
  sig := { Strategy := fun who => F.sig.Strategy who → F.sig.Strategy who
           Outcome := F.sig.Outcome }
  play responses := device.bind fun recommended => F.play fun who => responses who
    (recommended who)

/-- Every player obeys its recommendation. -/
def obedient (device : PMF (Profile F.sig)) : Profile (F.mediated device).sig :=
  fun _ => id

/-- The mediated extension's Nash comparisons at the obedient profile are the
device's correlated comparisons. -/
theorem equilibriumComparison_mediated (device : PMF (Profile F.sig))
    (observe : F.sig.Outcome → Observation) (who : ι)
    (respond : F.sig.Strategy who → F.sig.Strategy who) :
    equilibriumComparison (F.mediated device) (PMF.pure (F.obedient device))
        (DeviationScheme.unilateralConstant _) observe who respond =
      equilibriumComparison F device (DeviationScheme.recommendation F.sig) observe
        who respond := by
  have hresponse (recommended : Profile F.sig) :
      (fun player => Profile.update (F.obedient device) who respond player
          (recommended player)) =
        Profile.update recommended who (respond (recommended who)) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Profile.update_of_ne _ _ hplayer, obedient]
  simp only [equilibriumComparison, DeviationScheme.unilateralConstant_apply,
    DeviationScheme.recommendation_apply, PMF.pure_map, GameForm.outcomeLaw, PMF.pure_bind,
    PMF.bind_map, Function.comp_def, hresponse]
  rfl

/-- **Obedience in the mediated extension is correlated equilibrium**, for any
preference. -/
theorem isNash_mediated_obedient_iff (weaklyPrefers : WeakPreference ι F.sig.Outcome)
    (device : PMF (Profile F.sig)) :
    IsNash (F.mediated device) weaklyPrefers (F.obedient device) ↔
      IsCorrelatedEq F weaklyPrefers device := by
  rw [isNash_iff, isCorrelatedEq_iff]
  refine forall_congr' fun who => forall_congr' fun respond => ?_
  have hresponse (recommended : Profile F.sig) :
      (fun player => Profile.update (F.obedient device) who respond player
          (recommended player)) =
        Profile.update recommended who (respond (recommended who)) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Profile.update_of_ne _ _ hplayer, GameForm.obedient]
  have hhonest : (F.mediated device).play (F.obedient device) = F.outcomeLaw device := rfl
  have hdeviation : (F.mediated device).play (Profile.update (F.obedient device) who respond) =
      device.bind fun recommended =>
        F.play (Profile.update recommended who (respond (recommended who))) := by
    simp only [GameForm.mediated, hresponse]
  rw [hhonest, hdeviation]

/-- **Descent through the mediated extension.** Compiling a device into its
mediated extension preserves correlated equilibrium for every utility, and
preserves coarse correlated equilibrium exactly when coarse correlated
equilibrium already implies correlated equilibrium at the device. -/
theorem mediated_preservation (device : PMF (Profile F.sig))
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies
        (equilibriumComparison F device (DeviationScheme.recommendation F.sig) observe)
        (equilibriumComparison (F.mediated device) (PMF.pure (F.obedient device))
          (DeviationScheme.recommendation _) observe) ∧
      (IncentiveComparison.Implies
          (equilibriumComparison F device (DeviationScheme.unilateralConstant F.sig) observe)
          (equilibriumComparison (F.mediated device) (PMF.pure (F.obedient device))
            (DeviationScheme.unilateralConstant _) observe) ↔
        IncentiveComparison.Implies
          (equilibriumComparison F device (DeviationScheme.unilateralConstant F.sig) observe)
          (equilibriumComparison F device (DeviationScheme.recommendation F.sig) observe)) := by
  have hnash (utility : Observation → ι → ℝ) (who : ι)
      (respond : F.sig.Strategy who → F.sig.Strategy who) :
      (equilibriumComparison (F.mediated device) (PMF.pure (F.obedient device))
          (DeviationScheme.unilateralConstant _) observe who respond).Holds (utility · who) ↔
        (equilibriumComparison F device (DeviationScheme.recommendation F.sig) observe who
          respond).Holds (utility · who) :=
    IncentiveComparison.holds_iff_of_eq (F.equilibriumComparison_mediated device observe who
      respond) _
  refine ⟨?_, ⟨fun himplies utility holds who respond => (hnash utility who respond).1
      (himplies utility holds who respond),
    fun himplies utility holds who respond => (hnash utility who respond).2
      (himplies utility holds who respond)⟩⟩
  refine IncentiveComparison.Implies.trans ?_
    ((F.mediated device).implies_recommendation_pure (F.obedient device) observe).1
  intro utility holds who respond
  exact (hnash utility who respond).2 (holds who respond)

/-! ## The commitment form -/

/-- The commitment form: each player obeys (`none`) or commits to a strategy
before the device draws. -/
@[reducible]
def commitment (device : PMF (Profile F.sig)) : GameForm ι where
  sig := { Strategy := fun who => Option (F.sig.Strategy who)
           Outcome := F.sig.Outcome }
  play commitments := device.bind fun recommended => F.play fun who =>
    (commitments who).getD (recommended who)

/-- The commitment form's Nash comparisons at universal obedience are the
coarse comparisons of the device, together with trivial comparisons for
choosing to obey. -/
theorem equilibriumComparison_commitment_some (device : PMF (Profile F.sig))
    (observe : F.sig.Outcome → Observation) (who : ι) (replacement : F.sig.Strategy who) :
    equilibriumComparison (F.commitment device) (PMF.pure fun _ => none)
        (DeviationScheme.unilateralConstant _) observe who (some replacement) =
      equilibriumComparison F device (DeviationScheme.unilateralConstant F.sig) observe
        who replacement := by
  have hcommit (recommended : Profile F.sig) :
      (fun player => (Profile.update (sig := (F.commitment device).sig) (fun _ => none) who
          (some replacement) player).getD (recommended player)) =
        Profile.update recommended who replacement := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Profile.update_of_ne _ _ hplayer]
  simp only [equilibriumComparison, DeviationScheme.unilateralConstant_apply, PMF.pure_map,
    GameForm.outcomeLaw, PMF.pure_bind, PMF.bind_map, Function.comp_def, hcommit]
  simp

theorem equilibriumComparison_commitment_none_holds (device : PMF (Profile F.sig))
    (observe : F.sig.Outcome → Observation) (who : ι) (utility : Observation → ℝ)
    [Finite Observation] :
    (equilibriumComparison (F.commitment device) (PMF.pure fun _ => none)
        (DeviationScheme.unilateralConstant _) observe who none).Holds utility := by
  let _ : Fintype Observation := Fintype.ofFinite _
  rw [IncentiveComparison.holds_iff]
  simp [equilibriumComparison]

/-- **Ascent from the commitment form.** Compiling the commitment form at
universal obedience into the device preserves coarse correlated equilibrium for
every utility, and preserves correlated equilibrium exactly when coarse
correlated equilibrium already implies correlated equilibrium at the
device. -/
theorem commitment_preservation [Finite Observation] (device : PMF (Profile F.sig))
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies
        (equilibriumComparison (F.commitment device) (PMF.pure fun _ => none)
          (DeviationScheme.unilateralConstant _) observe)
        (equilibriumComparison F device (DeviationScheme.unilateralConstant F.sig) observe) ∧
      (IncentiveComparison.Implies
          (equilibriumComparison (F.commitment device) (PMF.pure fun _ => none)
            (DeviationScheme.recommendation _) observe)
          (equilibriumComparison F device (DeviationScheme.recommendation F.sig) observe) ↔
        IncentiveComparison.Implies
          (equilibriumComparison F device (DeviationScheme.unilateralConstant F.sig) observe)
          (equilibriumComparison F device (DeviationScheme.recommendation F.sig) observe)) := by
  let _ : Fintype Observation := Fintype.ofFinite _
  have hcoarse (utility : Observation → ι → ℝ) :
      (∀ who replacement, (equilibriumComparison (F.commitment device)
          (PMF.pure fun _ => none) (DeviationScheme.unilateralConstant _) observe who
            replacement).Holds (utility · who)) ↔
        ∀ who replacement, (equilibriumComparison F device
          (DeviationScheme.unilateralConstant F.sig) observe who replacement).Holds
            (utility · who) := by
    constructor
    · intro holds who replacement
      exact (IncentiveComparison.holds_iff_of_eq
        (F.equilibriumComparison_commitment_some device observe who replacement) _).1
          (holds who (some replacement))
    · intro holds who choice
      cases choice with
      | none => exact F.equilibriumComparison_commitment_none_holds device observe who _
      | some replacement =>
          exact (IncentiveComparison.holds_iff_of_eq
            (F.equilibriumComparison_commitment_some device observe who replacement) _).2
              (holds who replacement)
  have hpure := (F.commitment device).implies_recommendation_pure (fun _ => none) observe
  refine ⟨fun utility holds => (hcoarse utility).1 holds, ⟨fun himplies utility holds => ?_,
    fun himplies utility holds => ?_⟩⟩
  · exact himplies utility (hpure.1 utility ((hcoarse utility).2 holds))
  · exact himplies utility ((hcoarse utility).1 (hpure.2 utility holds))

end GameForm

end GameTheory
