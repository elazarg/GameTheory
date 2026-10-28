module

/-
# Proper equilibrium

A proper equilibrium is the limit of full-support epsilon-proper profiles
with epsilon tending to zero. The relative error condition uses the canonical
mixed extension and actual expected-utility comparisons; no second play law or
equilibrium-of-a-law predicate is introduced.
-/

public import GameTheory.Core.Proper
public import GameTheory.Analysis.TremblingHand
public import GameTheory.Math.Probability.FiniteOptimality

@[expose] public section

noncomputable section

namespace GameTheory.GameForm

open Filter GameTheory.Math.Probability

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : GameForm ι)

/-- A pointwise limit of epsilon-proper profiles as the positive error ratio
tends to zero. -/
def IsProper (utility : F.sig.Outcome → ι → ℝ)
    (profile : Profile F.sig.mixed) : Prop :=
  ∃ (epsilon : ℕ → ℝ) (approximating : ℕ → Profile F.sig.mixed),
    (∀ n, F.IsεProper utility (epsilon n) (approximating n)) ∧
      Tendsto epsilon atTop (nhds 0) ∧
        Analysis.MixedProfileConvergesPointwise approximating profile

private def properLower (utility : F.sig.Outcome → ι → ℝ) (epsilon : ℝ)
    (profile : Profile F.sig.mixed) : F.Perturbation := by
  classical
  exact fun who action =>
    if ∃ better, expectedUtility utility who
        (F.mixed.play (Profile.update profile who (PMF.pure action))) <
      expectedUtility utility who
        (F.mixed.play (Profile.update profile who (PMF.pure better))) then
      (profile who action).toReal
    else min epsilon 1 * (profile who action).toReal

private theorem properLower_positive {utility : F.sig.Outcome → ι → ℝ}
    {epsilon : ℝ} {profile : Profile F.sig.mixed}
    (proper : F.IsεProper utility epsilon profile) :
    (F.properLower utility epsilon profile).Positive := by
  intro who action
  have massPositive : 0 < (profile who action).toReal :=
    pmf_toReal_pos_iff.mpr (proper.2.1 who action)
  unfold properLower
  split
  · exact massPositive
  · exact mul_pos (lt_min proper.1 zero_lt_one) massPositive

private theorem properLower_respects (utility : F.sig.Outcome → ι → ℝ)
    (epsilon : ℝ) (profile : Profile F.sig.mixed) :
    F.RespectsPerturbation (F.properLower utility epsilon profile) profile := by
  intro who action
  unfold properLower
  split
  · exact le_rfl
  · exact mul_le_of_le_one_left ENNReal.toReal_nonneg (min_le_right epsilon 1)

private theorem properLower_le {utility : F.sig.Outcome → ι → ℝ}
    {epsilon : ℝ} {profile : Profile F.sig.mixed}
    (proper : F.IsεProper utility epsilon profile) (who : ι) (action : F.sig.Strategy who) :
    F.properLower utility epsilon profile who action ≤ epsilon := by
  unfold properLower
  split
  · next inferior =>
      obtain ⟨better, strictlyBetter⟩ := inferior
      exact (proper.2.2.2 who action better strictlyBetter).trans
        (mul_le_of_le_one_right proper.1.le (pmf_toReal_apply_le_one _ _))
  · simpa only [mul_one] using mul_le_mul (min_le_left epsilon 1)
      (pmf_toReal_apply_le_one (profile who) action) ENNReal.toReal_nonneg proper.1.le

private theorem isPerturbedEq_properLower [∀ who, Fintype (F.sig.Strategy who)]
    {utility : F.sig.Outcome → ι → ℝ} (integrable : F.HasIntegrableUtility utility)
    {epsilon : ℝ} {profile : Profile F.sig.mixed} :
    F.IsPerturbedEq (euPreference utility) (F.properLower utility epsilon profile) profile := by
  classical
  have mixedIntegrable := integrable.mixed_of_finite (F := F)
  rw [F.isPerturbedEq_iff]
  refine ⟨F.properLower_respects utility epsilon profile, ?_⟩
  intro who replacement respects
  apply (euPreference_iff utility who _ _ (mixedIntegrable who _)
    (mixedIntegrable who _)).mpr
  rw [expectedUtility_mixed_eq_expect F utility profile who (mixedIntegrable who _),
    expectedUtility_mixed_eq_expect F utility
      (Profile.update profile who replacement) who (mixedIntegrable who _)]
  simp only [Profile.update_same, Profile.update_idem]
  apply expect_le_of_suboptimal_mass_le
  intro action inferior
  have bound := respects action
  unfold properLower at bound
  split at bound
  · exact bound
  · next notInferior => exact False.elim (notInferior inferior)

/-- Proper equilibrium refines trembling-hand perfection under the existing
finite-strategy and actual pure-play integration assumptions. -/
theorem IsProper.isTremblingHandPerfect [∀ who, Finite (F.sig.Strategy who)]
    {utility : F.sig.Outcome → ι → ℝ} {profile : Profile F.sig.mixed}
    (proper : F.IsProper utility profile) (integrable : F.HasIntegrableUtility utility) :
    F.IsTremblingHandPerfect (euPreference utility) profile := by
  classical
  let : ∀ who, Fintype (F.sig.Strategy who) := fun _ => Fintype.ofFinite _
  obtain ⟨epsilon, approximating, proper, vanishes, converges⟩ := proper
  refine ⟨fun n => F.properLower utility (epsilon n) (approximating n), approximating,
    fun n => ⟨F.properLower_positive (proper n),
      F.isPerturbedEq_properLower integrable⟩, ?_, converges⟩
  intro who action
  apply squeeze_zero (fun n => (F.properLower_positive (proper n) who action).le)
    (fun n => F.properLower_le (proper n) who action) vanishes

/-- Every proper equilibrium is canonical mixed Nash. -/
theorem IsProper.isNash [∀ who, Finite (F.sig.Strategy who)]
    {utility : F.sig.Outcome → ι → ℝ} {profile : Profile F.sig.mixed}
    (proper : F.IsProper utility profile) (integrable : F.HasIntegrableUtility utility) :
    IsNash F.mixed (euPreference utility) profile :=
  (proper.isTremblingHandPerfect F integrable).isNash F integrable

/-- A full-support mixed Nash equilibrium is proper. Actual incumbent-law
integrability suffices: full support transports it to each pure deviation,
and indifference makes every relative error condition vacuous. -/
theorem _root_.GameTheory.IsNash.isProper_of_fullSupport
    {utility : F.sig.Outcome → ι → ℝ} {profile : Profile F.sig.mixed}
    (nash : IsNash F.mixed (euPreference utility) profile)
    (full : ∀ who, FullSupport (profile who))
    (integrable : ∀ who, UtilityIntegrable utility who (F.mixed.play profile)) :
    F.IsProper utility profile := by
  let epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < epsilon n :=
    one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))
  have vanishes : Tendsto epsilon atTop (nhds 0) := by
    have limit := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert limit using 1
    funext n
    simp only [epsilon, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have pureIntegrable (who : ι) (action : F.sig.Strategy who) :
      UtilityIntegrable utility who
        (F.mixed.play (Profile.update profile who (PMF.pure action))) := by
    let laws := fun a => F.mixed.play (Profile.update profile who (PMF.pure a))
    have mixed : UtilityIntegrable utility who ((profile who).bind laws) := by
      rw [← mixed_play_update_self F profile who]
      exact integrable who
    exact payoffIntegrable_bind_conditional_on_support (profile who) laws
      (fun outcome => utility outcome who) mixed action (full who action)
  refine ⟨epsilon, fun _ => profile, ?_, vanishes,
    Analysis.mixedProfileConvergesPointwise_const profile⟩
  intro n
  refine ⟨positive n, full, pureIntegrable, ?_⟩
  intro who worse better inferior
  rw [nash.expectedUtility_eq_of_mem_support who (integrable who) (full who worse),
    nash.expectedUtility_eq_of_mem_support who (integrable who) (full who better)] at inferior
  exact False.elim (lt_irrefl _ inferior)

end GameTheory.GameForm
