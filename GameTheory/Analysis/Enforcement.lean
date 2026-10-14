module

/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

public import GameTheory.Analysis.IncentiveCone
public import GameTheory.Math.Probability.EventPenalty
public import GameTheory.Math.ScalarInequalitiesCorrectness

@[expose] public section

/-! # Incentives under event penalties

A comparison's penalty effect is its additional collection probability, not
the deviating probability alone. The exact regret identity and guarded
comparison criterion apply to arbitrary laws with integrable base utilities.
For a finite comparison family, eventual deterrence is exactly nonnegative
additional collection and no positive gain at unchanged collection. Rare
departures can share a finite penalty when gain and detection scale together;
pointwise positive detection alone need not give a uniform penalty.
-/

noncomputable section
namespace GameTheory.Enforcement
open GameTheory.Math.Probability
variable {Outcome Index : Type*}

/-- The probability difference, rather than detection alone, is what matters
when the comparison plan may also incur a sanction. -/
theorem regret_eq (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) (penalty : ℝ)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base) :
    expect comparison.alternative (penalizedPayoff base sanction penalty) -
        expect comparison.prescribed (penalizedPayoff base sanction penalty) =
      (expect comparison.alternative base - expect comparison.prescribed base) -
        ((comparison.alternative.toOuterMeasure sanction).toReal -
          (comparison.prescribed.toOuterMeasure sanction).toReal) * penalty := by
  rw [expect_penalizedPayoff _ _ _ _ alternativeIntegrable,
    expect_penalizedPayoff _ _ _ _ prescribedIntegrable]
  ring

/-- Conditional detection and bounded gain give a quantitative deterrence certificate. -/
theorem regret_le (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) {penalty gain probability : ℝ}
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : expect comparison.alternative base - expect comparison.prescribed base ≤ gain)
    (detection : probability ≤ (comparison.alternative.toOuterMeasure sanction).toReal)
    (no_sanction : (comparison.prescribed.toOuterMeasure sanction).toReal = 0) :
    expect comparison.alternative (penalizedPayoff base sanction penalty) -
        expect comparison.prescribed (penalizedPayoff base sanction penalty) ≤
      gain - probability * penalty := by
  rw [regret_eq _ _ _ _ prescribedIntegrable alternativeIntegrable, no_sanction, sub_zero]
  exact sub_le_sub gain_bound (mul_le_mul_of_nonneg_right detection penalty_nonneg)

theorem holds_of_sanction (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) {penalty gain probability : ℝ}
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : expect comparison.alternative base - expect comparison.prescribed base ≤ gain)
    (detection : probability ≤ (comparison.alternative.toOuterMeasure sanction).toReal)
    (no_sanction : (comparison.prescribed.toOuterMeasure sanction).toReal = 0)
    (sufficient : gain ≤ probability * penalty) :
    comparison.Holds (penalizedPayoff base sanction penalty) := by
  have bound := regret_le comparison base sanction prescribedIntegrable alternativeIntegrable
    penalty_nonneg gain_bound detection no_sanction
  exact (IncentiveComparison.holds_iff_of_integrable comparison
    (penalizedPayoff base sanction penalty)
    (payoffIntegrable_penalizedPayoff prescribedIntegrable sanction penalty)
    (payoffIntegrable_penalizedPayoff alternativeIntegrable sanction penalty)).mpr
      (sub_nonpos.mp (bound.trans (sub_nonpos.mpr sufficient)))

theorem strictly_prefers_of_sanction (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) {penalty gain probability : ℝ}
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : expect comparison.alternative base - expect comparison.prescribed base ≤ gain)
    (detection : probability ≤ (comparison.alternative.toOuterMeasure sanction).toReal)
    (no_sanction : (comparison.prescribed.toOuterMeasure sanction).toReal = 0)
    (sufficient : gain < probability * penalty) :
    expect comparison.alternative (penalizedPayoff base sanction penalty) <
      expect comparison.prescribed (penalizedPayoff base sanction penalty) := by
  have bound := regret_le comparison base sanction prescribedIntegrable alternativeIntegrable
    penalty_nonneg gain_bound detection no_sanction
  exact sub_neg.mp (bound.trans_lt (sub_neg.mpr sufficient))

/-- A fixed utility sanction cannot deter every positive rescaling of a
profitable base utility. The sanction term is held fixed: this is not a claim
about rescaling the entire utility function, including its value for money. -/
theorem exists_rescaling_defeating_sanction (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (profitable : expect comparison.prescribed base < expect comparison.alternative base) :
    ∃ scale : ℝ, 0 < scale ∧
      expect comparison.prescribed
          (penalizedPayoff (fun outcome => scale * base outcome) sanction penalty) <
        expect comparison.alternative
          (penalizedPayoff (fun outcome => scale * base outcome) sanction penalty) := by
  let advantage := expect comparison.alternative base - expect comparison.prescribed base
  let charge :=
    ((comparison.alternative.toOuterMeasure sanction).toReal -
      (comparison.prescribed.toOuterMeasure sanction).toReal) * penalty
  have advantage_pos : 0 < advantage := sub_pos.mpr profitable
  let scale := (|charge| + 1) / advantage
  have scale_pos : 0 < scale := div_pos (by positivity) advantage_pos
  refine ⟨scale, scale_pos, sub_pos.mp ?_⟩
  rw [regret_eq _ _ _ _ (payoffIntegrable_const_mul prescribedIntegrable)
      (payoffIntegrable_const_mul alternativeIntegrable), expect_const_mul, expect_const_mul,
    ← mul_sub]
  change 0 < scale * advantage - charge
  dsimp only [scale]
  rw [div_mul_cancel₀ _ advantage_pos.ne']
  linarith [le_abs_self charge]

/-- The utility gain is offset precisely by the increase in collection risk. -/
theorem holds_iff_incremental_sanction (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base) :
    comparison.Holds (penalizedPayoff base sanction penalty) ↔
      expect comparison.alternative base - expect comparison.prescribed base ≤
        ((comparison.alternative.toOuterMeasure sanction).toReal -
          (comparison.prescribed.toOuterMeasure sanction).toReal) * penalty := by
  have regret := regret_eq comparison base sanction penalty prescribedIntegrable
    alternativeIntegrable
  constructor
  · intro holds
    have compared := (IncentiveComparison.holds_iff_of_integrable _ _
      (payoffIntegrable_penalizedPayoff prescribedIntegrable sanction penalty)
      (payoffIntegrable_penalizedPayoff alternativeIntegrable sanction penalty)).mp holds
    change expect comparison.alternative _ ≤ expect comparison.prescribed _ at compared
    rw [← sub_nonpos, regret] at compared
    exact sub_nonpos.mp compared
  · intro bound
    refine (IncentiveComparison.holds_iff_of_integrable _ _
      (payoffIntegrable_penalizedPayoff prescribedIntegrable sanction penalty)
      (payoffIntegrable_penalizedPayoff alternativeIntegrable sanction penalty)).mpr ?_
    rw [← sub_nonpos, regret]
    exact sub_nonpos.mpr bound

/-- Every sufficiently large penalty deters a finite table exactly when collection
never decreases and unchanged collection has no profitable deviation. The ambient
comparison carrier need not be finite. -/
theorem exists_uniform_sanction_iff (rows : Finset Index)
    (comparisons : Index → IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome)
    (prescribedIntegrable : ∀ index ∈ rows, PayoffIntegrable (comparisons index).prescribed base)
    (alternativeIntegrable : ∀ index ∈ rows, PayoffIntegrable (comparisons index).alternative
      base) :
    (∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ penalty, cutoff ≤ penalty → ∀ index ∈ rows,
      (comparisons index).Holds (penalizedPayoff base sanction penalty)) ↔
    ∀ index ∈ rows,
      0 ≤ ((comparisons index).alternative.toOuterMeasure sanction).toReal -
        ((comparisons index).prescribed.toOuterMeasure sanction).toReal ∧
      (((comparisons index).alternative.toOuterMeasure sanction).toReal =
          ((comparisons index).prescribed.toOuterMeasure sanction).toReal →
        (comparisons index).Holds base) := by
  let gain (index : Index) :=
    expect (comparisons index).alternative base - expect (comparisons index).prescribed base
  let increment (index : Index) :=
    ((comparisons index).alternative.toOuterMeasure sanction).toReal -
      ((comparisons index).prescribed.toOuterMeasure sanction).toReal
  constructor
  · rintro ⟨cutoff, nonnegative, deters⟩
    have condition := (Math.ScalarInequalities.exists_eventually_feasible_iff rows gain
      increment).mp
      ⟨cutoff, nonnegative, fun penalty large index member =>
        (holds_iff_incremental_sanction _ _ _ _ (prescribedIntegrable index member)
          (alternativeIntegrable index member)).mp (deters penalty large index member)⟩
    intro index member
    refine ⟨(condition index member).1, fun equal => ?_⟩
    apply (IncentiveComparison.holds_iff_of_integrable _ _
      (prescribedIntegrable index member) (alternativeIntegrable index member)).mpr
    exact sub_nonpos.mp ((condition index member).2 (sub_eq_zero.mpr equal))
  · intro condition
    have scalarCondition : ∀ index ∈ rows, 0 ≤ increment index ∧
        (increment index = 0 → gain index ≤ 0) := by
      intro index member
      refine ⟨(condition index member).1, fun zero => ?_⟩
      exact sub_nonpos.mpr ((IncentiveComparison.holds_iff_of_integrable _ _
        (prescribedIntegrable index member) (alternativeIntegrable index member)).mp
          ((condition index member).2 (sub_eq_zero.mp zero)))
    obtain ⟨cutoff, nonnegative, feasible⟩ :=
      (Math.ScalarInequalities.exists_eventually_feasible_iff rows gain increment).mpr
        scalarCondition
    exact ⟨cutoff, nonnegative, fun penalty large index member =>
      (holds_iff_incremental_sanction _ _ _ _ (prescribedIntegrable index member)
        (alternativeIntegrable index member)).mpr (feasible penalty large index member)⟩

/-- A sanction cannot repair a profitable comparison with unchanged risk,
regardless of its magnitude. This includes a binary charge already certain. -/
theorem not_holds_of_equal_collection (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (equal : (comparison.alternative.toOuterMeasure sanction).toReal =
      (comparison.prescribed.toOuterMeasure sanction).toReal)
    (profitable : expect comparison.prescribed base < expect comparison.alternative base) :
    ¬ comparison.Holds (penalizedPayoff base sanction penalty) := by
  rw [holds_iff_incremental_sanction _ _ _ _ prescribedIntegrable alternativeIntegrable, equal,
    sub_self, zero_mul]
  exact not_le.mpr (sub_pos.mpr profitable)

/-- A first-departure comparison scales both its possible gain and its added
collection risk by the probability of departing. Thus arbitrarily rare mixed
departures do not require unbounded fines when detection is conditional on the
departure. The probabilistic coupling establishing these two bounds is external. -/
theorem holds_of_departure_bound (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (departure gain detection penalty : ℝ)
    (departure_nonnegative : 0 ≤ departure) (penalty_nonnegative : 0 ≤ penalty)
    (gain_bound : expect comparison.alternative base - expect comparison.prescribed base ≤
      departure * gain)
    (collection_bound : departure * detection ≤
      (comparison.alternative.toOuterMeasure sanction).toReal -
        (comparison.prescribed.toOuterMeasure sanction).toReal)
    (sufficient : gain ≤ detection * penalty) :
    comparison.Holds (penalizedPayoff base sanction penalty) := by
  rw [holds_iff_incremental_sanction _ _ _ _ prescribedIntegrable alternativeIntegrable]
  calc
    _ ≤ departure * gain := gain_bound
    _ ≤ departure * (detection * penalty) :=
      mul_le_mul_of_nonneg_left sufficient departure_nonnegative
    _ = (departure * detection) * penalty := (mul_assoc ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right collection_bound penalty_nonnegative

/-- Pointwise positive detection in an infinite family does not supply one
finite uniform fine: these tests have unit gain and detection tending to zero. -/
theorem no_uniform_sanction_for_vanishing_detection :
    ¬ ∃ penalty : ℝ, ∀ index : ℕ, (1 : ℝ) ≤ (1 / (index + 1 : ℝ)) * penalty := by
  rintro ⟨penalty, deters⟩
  obtain ⟨index, larger⟩ := exists_nat_gt penalty
  have positive : (0 : ℝ) < index + 1 := by positivity
  have bound := deters index
  rw [one_div_mul_eq_div, le_div_iff₀ positive, one_mul] at bound
  linarith

end GameTheory.Enforcement
