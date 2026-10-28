module

/-
# Interim optimality and truthful Bayesian Nash equilibrium

For independent type laws, the canonical Bayesian payoff of each whole-plan
deviation is the expectation of its fixed-opponents interim payoff. Optimality
at supported own types therefore gives truthful Bayesian Nash equilibrium.
No incentive condition is imposed at null types by this equilibrium bridge.
-/

public import GameTheory.Mechanism.SingleParameter.Independent

@[expose] public section

noncomputable section

namespace GameTheory.Mechanism.SingleParameterMechanism

open GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] [DecidableEq Player]
variable (M : SingleParameterMechanism Player)

/-- Optimal averaged utility at every supported own type implies canonical
truthful Bayesian Nash equilibrium. The guards concern the actual report
slices and whole-plan deviations, and do not restrict support to be finite. -/
theorem isNash_truthful_of_averageOpponents (laws : Player → PMF ℝ)
    (hq : ∀ who r, PayoffIntegrable (independentProduct laws)
      (fun others => M.allocation (Profile.update others who r) who))
    (hp : ∀ who r, PayoffIntegrable (independentProduct laws)
      (fun others => M.payment (Profile.update others who r) who))
    (hdev : ∀ who (d : ℝ → ℝ), PayoffIntegrable (independentProduct laws)
      (fun types => M.utility (Profile.update types who (d (types who))) who (types who)))
    (hIC : ∀ who, ∀ t ∈ (laws who).support, ∀ r,
      (M.averageOpponents (independentProduct laws)).utility (fun _ => r) who t ≤
        (M.averageOpponents (independentProduct laws)).utility (fun _ => t) who t) :
    let BM := M.toQuasiLinearMechanism.toBayesianMechanism
    let B := BM.toBayesianGame (independentProduct laws)
    IsNash B.toForm (euPreference B.utility) (BM.truthfulPlan (independentProduct laws)) := by
  let μ := independentProduct laws
  let BM := M.toQuasiLinearMechanism.toBayesianMechanism
  let B := BM.toBayesianGame μ
  change IsNash B.toForm (euPreference B.utility) (BM.truthfulPlan μ)
  have hpayoff (who : Player) (d : ℝ → ℝ) :
      B.planPayoff who (Profile.update (BM.truthfulPlan μ) who d) =
        (fun types => M.utility (Profile.update types who (d (types who))) who (types who)) := by
    funext types
    change BM.utility types (BM.choose ((BM.toBayesianGame μ).actionsOf
      (Profile.update (BM.truthfulPlan μ) who d) types)) who = _
    rw [BM.actionsOf_update_truthfulPlan]
    rfl
  have htruth (who : Player) : B.planPayoff who (BM.truthfulPlan μ) =
      (fun types => M.utility types who (types who)) := by
    funext types
    rfl
  have hbase (who : Player) :
      PayoffIntegrable μ (fun types => M.utility types who (types who)) := by
    simpa only [id_eq, Profile.update_eq_self] using hdev who id
  have havg (who : Player) (r t : ℝ) :
      (M.averageOpponents μ).utility (fun _ => r) who t =
        expect μ (fun others => M.utility (Profile.update others who r) who t) := by
    simpa only [Profile.update_eq_self] using
      M.averageOpponents_utility μ who (fun _ => r) r t (hq who r) (hp who r)
  rw [isNash_iff]
  intro who d
  have htruthInt : UtilityIntegrable B.utility who (B.toForm.play (BM.truthfulPlan μ)) := by
    rw [B.planPayoff_integrable_iff, htruth]
    exact hbase who
  have hdevInt : UtilityIntegrable B.utility who
      (B.toForm.play (Profile.update (BM.truthfulPlan μ) who d)) := by
    rw [B.planPayoff_integrable_iff, hpayoff]
    exact hdev who d
  refine (euPreference_iff _ _ _ _ htruthInt hdevInt).mpr ?_
  rw [B.expectedUtility_eq_prior who _, B.expectedUtility_eq_prior who _,
    hpayoff who d, htruth who]
  have hd := expect_independentPrior laws who _ (hdev who d)
  have ht := expect_independentPrior laws who _ (hbase who)
  simp only [Profile.update_same, Profile.update_idem] at hd ht
  rw [hd, ht]
  have hdi := integrable_independentPrior_conditional laws who _ (hdev who d)
  have hti := integrable_independentPrior_conditional laws who _ (hbase who)
  simp only [Profile.update_same, Profile.update_idem] at hdi hti
  apply expect_mono _ hdi hti
  intro t hs
  rw [← havg who (d t) t, ← havg who t t]
  exact hIC who t hs (d t)

end GameTheory.Mechanism.SingleParameterMechanism
