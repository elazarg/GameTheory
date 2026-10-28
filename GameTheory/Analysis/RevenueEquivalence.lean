module

/-
# Interim payment identities and realized revenue equivalence

Interval-wide expected-utility optimality determines interim payments from
interim allocation and lowest-type utility. Independent type laws connect
these scalar identities to actual expected total receipts. Optimality at
prior-null types is an explicit hypothesis, not a consequence of Bayesian
Nash equilibrium. Every realized receipt used by the tower is integrable.
-/

public import GameTheory.Analysis.SingleParameter
public import GameTheory.Mechanism.SingleParameter.Independent

@[expose] public section

noncomputable section

namespace GameTheory.Mechanism.SingleParameterMechanism

open GameTheory.Math.Probability
open scoped BigOperators

variable {Player : Type*} [DecidableEq Player]
variable (M : SingleParameterMechanism Player)

private theorem averageOpponents_optimal_on
    (μ : PMF (SingleParameterReportProfile Player)) (who : Player)
    (reports : SingleParameterReportProfile Player) {a b : ℝ}
    (hint : ∀ r ∈ Set.Icc a b,
      PayoffIntegrable μ (fun others => M.allocation (Profile.update others who r) who) ∧
        PayoffIntegrable μ (fun others => M.payment (Profile.update others who r) who))
    (hIC : ∀ t ∈ Set.Icc a b,
      IsMaxOn (fun r => expect μ (fun others =>
        M.utility (Profile.update others who r) who t)) (Set.Icc a b) t) :
    ∀ t ∈ Set.Icc a b, IsMaxOn
      (fun r => (M.averageOpponents μ).utility (Profile.update reports who r) who t)
      (Set.Icc a b) t := by
  intro t ht r hr
  change (M.averageOpponents μ).utility (Profile.update reports who r) who t ≤
    (M.averageOpponents μ).utility (Profile.update reports who t) who t
  rw [M.averageOpponents_utility μ who reports r t (hint r hr).1 (hint r hr).2,
    M.averageOpponents_utility μ who reports t t (hint t ht).1 (hint t ht).2]
  exact hIC t ht hr

/-- Interval-wide interim incentive constraints give the payment envelope,
including every declared null type. Opponents' law is fixed across true types. -/
theorem interim_payment_identity (μ : PMF (SingleParameterReportProfile Player))
    (who : Player) (reports : SingleParameterReportProfile Player) {a b : ℝ}
    (hint : ∀ r ∈ Set.Icc a b,
      PayoffIntegrable μ (fun others => M.allocation (Profile.update others who r) who) ∧
        PayoffIntegrable μ (fun others => M.payment (Profile.update others who r) who))
    (hIC : ∀ t ∈ Set.Icc a b,
      IsMaxOn (fun r => expect μ (fun others =>
        M.utility (Profile.update others who r) who t)) (Set.Icc a b) t)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    (M.averageOpponents μ).payment (Profile.update reports who t) who =
      t * OwnAllocation (M.averageOpponents μ).allocation who reports t -
        (M.averageOpponents μ).utility (Profile.update reports who a) who a -
        ∫ s in a..t, OwnAllocation (M.averageOpponents μ).allocation who reports s :=
  (M.averageOpponents μ).payment_identity_on who reports
    (M.averageOpponents_optimal_on μ who reports hint hIC) ht

section Independent

variable [Fintype Player]

/-- Actual expected payment equals the marginal expectation of interim
payment. Only integrability of the actual joint payment is needed. -/
theorem expected_payment_eq_interim (laws : Player → PMF ℝ) (who : Player)
    (reports : SingleParameterReportProfile Player)
    (hp : PayoffIntegrable (independentProduct laws) (fun types => M.payment types who)) :
    expect (independentProduct laws) (fun types => M.payment types who) =
      expect (laws who) (fun t =>
        (M.averageOpponents (independentProduct laws)).payment
          (Profile.update reports who t) who) := by
  simpa only [averageOpponents, Profile.update_same] using
    expect_independentPrior laws who (fun types => M.payment types who) hp

/-- Realized total receipts integrate to the sum of expected interim payments. -/
theorem expected_revenue_eq_interim (laws : Player → PMF ℝ)
    (reports : SingleParameterReportProfile Player)
    (hp : ∀ who, PayoffIntegrable (independentProduct laws) (fun types => M.payment types who)) :
    expect (independentProduct laws) (fun types => ∑ who, M.payment types who) =
      ∑ who, expect (laws who) (fun t =>
        (M.averageOpponents (independentProduct laws)).payment
          (Profile.update reports who t) who) := by
  rw [expect_sum _ _ hp]
  apply Finset.sum_congr rfl
  intro who _
  exact M.expected_payment_eq_interim laws who reports (hp who)

/-- Equal interim allocations and lowest-type utilities imply equal expected
realized receipts. IC holds throughout each declared interval, including null
types; actual joint payments are integrable. No efficiency assumption is used. -/
theorem revenue_equivalence (N : SingleParameterMechanism Player) (laws : Player → PMF ℝ)
    (a b : Player → ℝ) (hsupport : ∀ who, (laws who).support ⊆ Set.Icc (a who) (b who))
    (hintM : ∀ who, ∀ r ∈ Set.Icc (a who) (b who),
      PayoffIntegrable (independentProduct laws)
        (fun others => M.allocation (Profile.update others who r) who) ∧
      PayoffIntegrable (independentProduct laws)
        (fun others => M.payment (Profile.update others who r) who))
    (hintN : ∀ who, ∀ r ∈ Set.Icc (a who) (b who),
      PayoffIntegrable (independentProduct laws)
        (fun others => N.allocation (Profile.update others who r) who) ∧
      PayoffIntegrable (independentProduct laws)
        (fun others => N.payment (Profile.update others who r) who))
    (hICM : ∀ who, ∀ t ∈ Set.Icc (a who) (b who),
      IsMaxOn (fun r => expect (independentProduct laws) (fun others =>
        M.utility (Profile.update others who r) who t)) (Set.Icc (a who) (b who)) t)
    (hICN : ∀ who, ∀ t ∈ Set.Icc (a who) (b who),
      IsMaxOn (fun r => expect (independentProduct laws) (fun others =>
        N.utility (Profile.update others who r) who t)) (Set.Icc (a who) (b who)) t)
    (hq : ∀ who, ∀ t ∈ Set.Icc (a who) (b who),
      (M.averageOpponents (independentProduct laws)).allocation (fun _ => t) who =
        (N.averageOpponents (independentProduct laws)).allocation (fun _ => t) who)
    (hbase : ∀ who,
      (M.averageOpponents (independentProduct laws)).utility (fun _ => a who) who (a who) =
        (N.averageOpponents (independentProduct laws)).utility (fun _ => a who) who (a who))
    (hpM : ∀ who, PayoffIntegrable (independentProduct laws) (fun types => M.payment types who))
    (hpN : ∀ who, PayoffIntegrable (independentProduct laws) (fun types => N.payment types who)) :
    expect (independentProduct laws) (fun types => ∑ who, M.payment types who) =
      expect (independentProduct laws) (fun types => ∑ who, N.payment types who) := by
  let reports : SingleParameterReportProfile Player := fun _ => 0
  rw [M.expected_revenue_eq_interim laws reports hpM,
    N.expected_revenue_eq_interim laws reports hpN]
  apply Finset.sum_congr rfl
  intro who _
  apply expect_congr_on_support
  intro t ht
  apply (M.averageOpponents (independentProduct laws)).payment_unique_on who reports
    (M.averageOpponents_optimal_on _ who reports (hintM who) (hICM who))
    (N.averageOpponents_optimal_on _ who reports (hintN who) (hICN who))
    _ _ (hsupport who ht)
  · intro r hr
    simpa only [OwnAllocation, averageOpponents, Profile.update_same] using hq who r hr
  · simpa only [utility, averageOpponents, Profile.update_same] using hbase who

end Independent

end GameTheory.Mechanism.SingleParameterMechanism
