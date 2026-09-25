/-
EXP-133 follow-up: infinite public signals and unbounded integrable outcomes.
The first signal selects a permanent Boolean action, so continuation values
are not constant. The monitored Bellman theorem uses its general PMF guards.
-/

import GameTheory.Repeated.MonitoringDiscounted
import GameTheory.Experimental.PostArchitecture.PMFRepeatedGate

noncomputable section

namespace GameTheory.Experimental.PMFMonitoringGate

open GameTheory GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration
open GameTheory.Experimental.PMFStaticGate

@[reducible]
def form : GameForm Unit where
  sig := { Strategy := fun _ => Bool, Outcome := ℕ × ℕ }
  play profile := geometric.map fun noise => (if profile () then 1 else 0, noise)

@[reducible]
def game : UtilityGame Unit where
  form := form
  utility outcome _ := (outcome.1 : ℝ) + ((outcome.2 : ℝ) + 1)

theorem stage_integrable : game.form.HasIntegrableUtility game.utility := by
  intro who profile
  exact PMFRepeatedGate.stage_integrable who
    (fun _ => if profile () then 1 else 0)

theorem stage_law_infinite_support (profile : Profile game.form.sig) :
    (game.form.play profile).support.Infinite :=
  PMFRepeatedGate.stage_law_infinite_support
    (fun _ => if profile () then 1 else 0)

/-- Even on each individual stage law's support, realized utility is unbounded. -/
theorem stage_utility_unbounded (profile : Profile game.form.sig) (bound : ℝ) :
    ∃ outcome ∈ (game.form.play profile).support, bound < game.utility outcome () := by
  obtain ⟨noise, hnoise⟩ := exists_nat_gt bound
  refine ⟨(if profile () then 1 else 0, noise), ?_, ?_⟩
  · rw [PMF.mem_support_map_iff]
    exact ⟨noise, (geometric_positive noise).ne', rfl⟩
  · have hnonneg : (0 : ℝ) ≤ ((if profile () then 1 else 0 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith

def noiseMean : ℝ :=
  expect geometric (fun noise => (noise : ℝ) + 1) linearUtility_integrable_geometric

theorem stagePayoff_eq (profile : Profile game.form.sig) :
    game.stagePayoff profile () (stage_integrable () profile) =
      (if profile () then (1 : ℝ) else 0) + noiseMean := by
  have hconst := payoffIntegrable_constant geometric
    ((if profile () then 1 else 0 : ℕ) : ℝ)
  have hlinear := linearUtility_integrable_geometric
  have hmap := expectedUtility_map game.utility ()
    (fun noise : ℕ => (if profile () then 1 else 0, noise)) geometric
    (stage_integrable () profile)
  have hadd := expect_add hconst hlinear
  rw [expect_constant] at hadd
  simpa [game, form, UtilityGame.stagePayoff, expectedUtility, linearUtility,
    noiseMean] using hmap.trans hadd

theorem stage_bound (profile : Profile game.form.sig) :
    |game.stagePayoff profile () (stage_integrable () profile)| ≤ 1 + |noiseMean| := by
  rw [stagePayoff_eq]
  calc
    |(if profile () then (1 : ℝ) else 0) + noiseMean| ≤
        |if profile () then (1 : ℝ) else 0| + |noiseMean| := abs_add_le _ _
    _ ≤ 1 + |noiseMean| := by split_ifs <;> norm_num

@[reducible]
def monitoring : game.PublicMonitoring where
  Signal := ℕ
  signalLaw _ := geometric

theorem signals_infinite_support (profile : Profile game.form.sig) :
    (monitoring.signalLaw profile).support.Infinite := by
  rw [show monitoring.signalLaw profile = geometric from rfl, geometric_support]
  exact Set.infinite_univ

/-- Choose false initially, then keep the action selected by the first signal. -/
def responding : monitoring.MonitoredProfile := fun _ t =>
  match t with
  | 0 => fun _ => false
  | _ + 1 => fun history => decide (Even (history 0))

theorem afterSignal_responding (signal : ℕ) :
    monitoring.afterSignal responding signal =
      monitoring.stationaryMonitoredProfile (fun _ => decide (Even signal)) := by
  funext who t history
  simp [UtilityGame.PublicMonitoring.afterSignal, responding,
    UtilityGame.PublicMonitoring.stationaryMonitoredProfile]

theorem monitored_integrable (profile : monitoring.MonitoredProfile) (t : ℕ) :
    monitoring.MonitoredStageIntegrable profile t () :=
  monitoring.monitoredStageIntegrable_of_expected_bound
    profile t () stage_integrable stage_bound

abbrev discountedValue (profile : monitoring.MonitoredProfile) : ℝ :=
  monitoring.discountedPayoffOfBounded
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    stage_integrable profile () stage_bound

theorem discounted_afterSignal (signal : ℕ) :
    discountedValue (monitoring.afterSignal responding signal) =
      (if Even signal then (1 : ℝ) else 0) + noiseMean := by
  rw [afterSignal_responding]
  unfold discountedValue UtilityGame.PublicMonitoring.discountedPayoffOfBounded
  rw [monitoring.discountedPayoff_stationaryMonitoredProfile
    (by norm_num) (by norm_num) _ () (stage_integrable () _)]
  simp [stagePayoff_eq]

/-- The Bellman continuation integrand is nonconstant on supported signals. -/
theorem continuation_values_differ :
    discountedValue (monitoring.afterSignal responding 0) ≠
      discountedValue (monitoring.afterSignal responding 1) := by
  rw [discounted_afterSignal, discounted_afterSignal]
  norm_num

theorem continuation_integrable :
    PayoffIntegrable geometric
      (fun signal => discountedValue (monitoring.afterSignal responding signal)) :=
  monitoring.discountedAfterSignal_integrable_of_expected_bound
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    stage_integrable responding () stage_bound

/-- The first-signal Bellman identity uses the actual infinite signal law. -/
theorem bellman :
    discountedValue responding =
      (1 / 2 : ℝ) * noiseMean + (1 / 2 : ℝ) *
        expect geometric
          (fun signal => discountedValue (monitoring.afterSignal responding signal))
          continuation_integrable := by
  have h := monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    stage_integrable responding () stage_bound
  norm_num [stagePayoff_eq, responding, discountedValue] at h
  exact h

end GameTheory.Experimental.PMFMonitoringGate
