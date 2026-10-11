import GameTheory.Analysis.EnforcementSynthesis
import GameTheory.Math.Probability.ExpectationMixture
import GameTheory.Analysis.ObservableEnforcement
import GameTheory.Analysis.IncentiveSimulation
noncomputable section
namespace GameTheory.Tests.Enforcement
open GameTheory GameTheory.Enforcement GameTheory.Math.Probability

private def base (outcome : Bool) : ℝ := if outcome then 3 else 0
private def deviation : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)
private def comparison : IncentiveComparison Bool := ⟨PMF.pure false, deviation⟩

private theorem gain_bound :
    expect comparison.alternative base - expect comparison.prescribed base ≤ (3 / 2 : ℝ) := by
  change expect deviation base - expect (PMF.pure false) base ≤ _
  rw [deviation, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)]
  norm_num [expect_pure, base]

private theorem collection_bound : (1 / 2 : ℝ) ≤
    (comparison.alternative.toOuterMeasure {true}).toReal -
      (comparison.prescribed.toOuterMeasure {true}).toReal := by
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton]
  change (1 / 2 : ℝ) ≤ (deviation true).toReal - (PMF.pure false true).toReal
  rw [deviation, mix_apply_toReal]
  norm_num [PMF.pure_apply]

/-- A computed penalty deters a genuinely randomized, partially detected deviation. -/
theorem synthesized_penalty_deters : comparison.Holds (penalizedPayoff base {true} 3) := by
  have inferred : Math.ScalarInequalities.infer ({false} : Finset Bool)
      (fun _ => 3 / 2) (fun _ => 1 / 2) = some 3 := by
    norm_num [Math.ScalarInequalities.infer, Math.ScalarInequalities.candidate]
  exact inferred_deposit_holds ({false} : Finset Bool) (fun _ => 3 / 2) (fun _ => 1 / 2)
    inferred (fun _ => comparison) base {true}
    (fun _ _ => payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)
    (fun _ _ => by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using gain_bound)
    (fun _ _ => by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using collection_bound)
      (Finset.mem_singleton_self _)

/-- Charging every outcome cancels between plans, so no amount deters positive gain. -/
theorem inevitable_charge_does_not_deter (penalty : ℝ) :
    ¬ (IncentiveComparison.mk (PMF.pure false) (PMF.pure true)).Holds
      (penalizedPayoff base Set.univ penalty) := by
  exact not_holds_of_equal_collection
    (IncentiveComparison.mk (PMF.pure false) (PMF.pure true)) base Set.univ penalty
    (payoffIntegrable_pure false base) (payoffIntegrable_pure true base)
    (by simp) (by norm_num [expect_pure, base])

/-- Admitting every possible observation makes sound deterrence impossible for a profitable
  deviation. -/
theorem no_sound_deterrent_with_full_admission :
    ¬ ∃ alarm : Bool → PMF Bool, ∃ penalty : ℝ, 0 ≤ penalty ∧
      (∀ observation ∈ (Set.univ : Set Bool), ((alarm observation) true).toReal = 0) ∧
      (IncentiveComparison.mk (PMF.pure false) (PMF.pure true)).Holds
        (monitoredPayoff base id alarm penalty) := by
  intro deters
  have detected := (exists_sound_deterrent_iff
    (IncentiveComparison.mk (PMF.pure false) (PMF.pure true)) base id Set.univ
    (fun _ _ => Set.mem_univ _) (payoffIntegrable_pure false base) (payoffIntegrable_pure true base)
    (by norm_num [expect_pure, base])).mp deters
  simp at detected

/-- Mixtures over infinite indices preserve actual deterrence comparisons. -/
theorem infinite_mixture_preserves_deterrence (weights : PMF ℕ)
    (comparisons : ℕ → IncentiveComparison Bool)
    (deters : ∀ index ∈ weights.support, (comparisons index).Holds (penalizedPayoff base {true}
      3)) :
    (IncentiveComparison.mk (weights.bind fun index => (comparisons index).prescribed)
      (weights.bind fun index => (comparisons index).alternative)).Holds (penalizedPayoff base
        {true} 3) :=
  IncentiveComparison.holds_bind weights comparisons _
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _) deters

end GameTheory.Tests.Enforcement
