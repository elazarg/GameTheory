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
    [Fintype Observation] :
    (equilibriumComparison (F.commitment device) (PMF.pure fun _ => none)
        (DeviationScheme.unilateralConstant _) observe who none).Holds utility := by
  rw [IncentiveComparison.holds_iff]
  simp [equilibriumComparison]

/-- **Ascent from the commitment form.** Compiling the commitment form at
universal obedience into the device preserves coarse correlated equilibrium for
every utility, and preserves correlated equilibrium exactly when coarse
correlated equilibrium already implies correlated equilibrium at the
device. -/
theorem commitment_preservation [Fintype Observation] (device : PMF (Profile F.sig))
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
