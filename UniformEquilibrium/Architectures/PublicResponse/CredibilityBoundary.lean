/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Adaptive.PotentialSystem
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.PublicActionFrequencyResponse

/-!
# The credibility boundary for observable public responses

An action-frequency response provides public statistical evidence about a
unilateral change of behavior.  It does not imply that the prescribed target
is incentive compatible.

The first theorem below exposes a necessary consequence of an adaptive
potential certificate: every unilateral deviation is capped, at every
certified horizon, by the target plus twice the certificate error.  The
one-state example then strengthens the existing out-of-range-target
counterexample.  Its target is feasible and is attained exactly by a public
stationary profile, while a bounded centered action-frequency detector has
strict positive drift under a pure response.  Nevertheless, no adaptive
potential certificate exists at error `1 / 4`, because that same response is
a profitable unilateral deviation.

Thus the remaining interface is specifically strategic credibility, not
observability, target feasibility, or statistical power.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.PMFProduct Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- A single adaptive potential certificate already gives the deviation cap
used by its verifier: at every certified horizon, a unilateral deviation
earns at most the target plus twice the certificate error. -/
theorem finiteAveragePayoff_update_le_target_add_two_error_of_certificate
    [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {s₀ : G.State} {v : Payoff ι} {error : ℝ}
    (certificate : G.IsAdaptivePotentialCertificateAt s₀ v error)
    (owner : ι) (deviation : G.BehaviorStrategy owner) :
    ∃ profile : G.BehaviorProfile, ∃ horizon : ℕ, 2 ≤ horizon ∧
      ∀ total, horizon ≤ total →
        G.finiteAveragePayoff s₀ total
            (Function.update profile owner deviation)
            owner ≤
          v owner + 2 * error := by
  obtain ⟨profile, horizon, lowerPotential, upperPotential,
      deviationPotential, lowerCharge, upperCharge, deviationCharge,
      horizon_ge_two, lower_initial, upper_initial, deviation_initial,
      lower_submartingale, lower_stage, upper_supermartingale,
      upper_stage, deviation_supermartingale, deviation_stage,
      lower_charge_cesaro, upper_charge_cesaro,
      deviation_charge_cesaro⟩ := certificate
  refine ⟨profile, horizon, horizon_ge_two, ?_⟩
  intro total htotal
  have htotal_pos : 0 < total := by omega
  have hbound :=
    G.finiteAveragePayoff_le_of_expectedHistoryValue_supermartingale_ge
      (Function.update profile owner deviation) s₀ owner
      (deviationPotential owner)
      (deviationCharge owner deviation)
      (deviation_supermartingale owner deviation)
      (deviation_stage owner deviation)
      htotal_pos
  rw [G.expectedHistoryValue_zero] at hbound
  have hinitial := deviation_initial owner
  have hcharge :=
    deviation_charge_cesaro owner deviation total htotal
  rw [abs_le] at hinitial
  linarith

namespace CredibleResponseNoAutomaticCertificate

open ActionDetectorNoAutomaticCloser

/-- The feasible target zero.  It is attained by always playing `false`. -/
def feasibleTarget : Payoff Player := fun _ => 0

/-- The stationary behavior which attains `feasibleTarget` exactly. -/
def obeyProfile : game.BehaviorProfile :=
  game.stationaryBehaviorProfile fun _ => PMF.pure false

/-- The publicly observable pure response which always plays `true`. -/
def pureTrueDeviation : game.BehaviorStrategy () :=
  fun _ _ => PMF.pure true

/-- The target is not merely in the payoff range: one public stationary
profile attains it at every positive finite horizon. -/
theorem finiteAveragePayoff_obeyProfile_eq_feasibleTarget
    (total : ℕ) (_htotal : 0 < total) :
    game.finiteAveragePayoff () total obeyProfile () =
      feasibleTarget () := by
  have habsorbing : game.IsAbsorbingState () := by
    intro action
    simp [game]
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hstage (time : ℕ) :
      game.expectedStagePayoff obeyProfile () time () = 0 := by
    change
      game.expectedStagePayoff
          (game.stationaryBehaviorProfile
            (fun _ : Player => PMF.pure false))
          () time () =
        0
    rw [game.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
      habsorbing]
    change
      expect
          (pmfPi (fun _ : Player => PMF.pure false))
          (fun action => if action () then 1 else 0) =
        0
    rw [pmfPi_pure, expect_pure]
    simp
  simp_rw [hstage]
  simp [feasibleTarget]

/-- Updating any candidate profile by the response overwrites the unique
player's behavior, so its stage payoff is one at every date. -/
theorem expectedStagePayoff_update_pureTrueDeviation_eq_one
    (profile : game.BehaviorProfile) (time : ℕ) :
    game.expectedStagePayoff
        (Function.update profile () pureTrueDeviation) () time () = 1 := by
  have hprofile :
      Function.update profile () pureTrueDeviation =
        game.stationaryBehaviorProfile
          (fun _ : Player => PMF.pure true) := by
    funext owner stage history
    have howner : owner = () := Subsingleton.elim _ _
    subst owner
    simp [pureTrueDeviation, StochasticGame.stationaryBehaviorProfile]
  rw [hprofile]
  have habsorbing : game.IsAbsorbingState () := by
    intro action
    simp [game]
  rw [game.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
    habsorbing]
  change
    expect
        (pmfPi (fun _ : Player => PMF.pure true))
        (fun action => if action () then 1 else 0) =
      1
  rw [pmfPi_pure, expect_pure]
  simp

/-- The pure response earns average payoff one against every candidate
profile at every positive horizon. -/
theorem finiteAveragePayoff_update_pureTrueDeviation_eq_one
    (profile : game.BehaviorProfile)
    (total : ℕ) (htotal : 0 < total) :
    game.finiteAveragePayoff () total
        (Function.update profile () pureTrueDeviation) () = 1 := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp_rw [expectedStagePayoff_update_pureTrueDeviation_eq_one]
  simp [htotal.ne']

/-- The feasible target admits no adaptive certificate at error `1 / 4`.
The obstruction is credibility: the public response is a unilateral
deviation with payoff one, whereas a certificate would cap it at one half. -/
theorem not_isAdaptivePotentialCertificateAt_feasibleTarget :
    ¬game.IsAdaptivePotentialCertificateAt
      () feasibleTarget (1 / 4 : ℝ) := by
  intro certificate
  obtain ⟨profile, horizon, lowerPotential, upperPotential,
      deviationPotential, lowerCharge, upperCharge, deviationCharge,
      horizon_ge_two, lower_initial, upper_initial, deviation_initial,
      lower_submartingale, lower_stage, upper_supermartingale,
      upper_stage, deviation_supermartingale, deviation_stage,
      lower_charge_cesaro, upper_charge_cesaro,
      deviation_charge_cesaro⟩ := certificate
  have htotal_pos : 0 < horizon := by omega
  have hbound :=
    game.finiteAveragePayoff_le_of_expectedHistoryValue_supermartingale_ge
      (Function.update profile () pureTrueDeviation) () ()
      (deviationPotential ())
      (deviationCharge () pureTrueDeviation)
      (deviation_supermartingale () pureTrueDeviation)
      (deviation_stage () pureTrueDeviation)
      htotal_pos
  rw [game.expectedHistoryValue_zero] at hbound
  have hinitial := deviation_initial ()
  have hcharge :=
    deviation_charge_cesaro () pureTrueDeviation horizon le_rfl
  rw [finiteAveragePayoff_update_pureTrueDeviation_eq_one
    profile horizon htotal_pos] at hbound
  simp only [feasibleTarget] at hinitial
  rw [abs_le] at hinitial
  norm_num at hinitial hcharge ⊢
  linarith

/-- Exact strengthened no-go result.  All of the response-side data hold:

* the target is attained by a public stationary profile at every horizon;
* the action-frequency score is centered under prescribed mixing;
* it has strict positive drift under the pure response;

yet no adaptive potential certificate exists. -/
theorem feasible_target_and_detector_but_no_automatic_adaptiveCloser :
    (∀ total, 0 < total →
        game.finiteAveragePayoff () total obeyProfile () =
          feasibleTarget ()) ∧
      (expect (pmfPi prescribedProfile)
          (game.publicActionFrequencyScore
            () (prescribedProfile ()) true) = 0 ∧
        0 <
          expect (pmfPi comparisonProfile)
            (game.publicActionFrequencyScore
              () (prescribedProfile ()) true)) ∧
      ¬game.IsAdaptivePotentialCertificateAt
        () feasibleTarget (1 / 4 : ℝ) := by
  exact ⟨finiteAveragePayoff_obeyProfile_eq_feasibleTarget,
    centered_and_positive_action_detector,
    not_isAdaptivePotentialCertificateAt_feasibleTarget⟩

end CredibleResponseNoAutomaticCertificate

end StochasticGame
end GameTheory
