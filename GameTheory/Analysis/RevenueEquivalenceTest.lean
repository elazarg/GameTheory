module

/-
Independent two-player mechanisms with equal interim allocations and payments
but different realized receipts. One mechanism is Bayesian truthful and fails
dominant-strategy truthfulness.
-/

public import GameTheory.Analysis.RevenueEquivalence
public import GameTheory.Mechanism.SingleParameter.Bayesian
public import GameTheory.Math.Probability.ExpectationMixture

@[expose] public section

noncomputable section

namespace GameTheory.Tests.RevenueEquivalence

open Mechanism Mechanism.SingleParameterMechanism Math.Probability
open scoped BigOperators

def twoPoint : PMF ℝ := mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure 0) (PMF.pure 2)

def laws (_ : Bool) : PMF ℝ := twoPoint

@[reducible]
def prior : PMF (SingleParameterReportProfile Bool) := independentProduct laws

@[reducible]
def quadratic : SingleParameterMechanism Bool where
  allocation reports who := reports who
  payment reports who := (reports who) ^ 2 / 2

@[reducible]
def scaled : SingleParameterMechanism Bool where
  allocation reports who := reports who * (2 * reports (!who) - 1)
  payment reports who := ((reports who) ^ 2 / 2) * (2 * reports (!who) - 1)

private theorem twoPoint_support {t : ℝ} (ht : t ∈ twoPoint.support) : t = 0 ∨ t = 2 := by
  by_contra hn
  push Not at hn
  have hz : twoPoint t = 0 := by
    simp [twoPoint, mix_apply, PMF.pure_apply, hn.1, hn.2]
  exact ht hz

private theorem prior_support_finite : prior.support.Finite := by
  apply (Set.finite_range (fun bits : Bool → Bool =>
    (fun who => if bits who then (2 : ℝ) else 0))).subset
  intro types ht
  refine ⟨fun who => decide (types who = 2), ?_⟩
  funext who
  have hs := twoPoint_support ((independentProduct_support_iff laws types).mp ht who)
  rcases hs with h | h <;> simp [h]

private theorem integrable (f : SingleParameterReportProfile Bool → ℝ) :
    PayoffIntegrable prior f := payoffIntegrable_of_finite_support prior f prior_support_finite

private theorem expect_twoPoint (f : ℝ → ℝ) :
    expect twoPoint f = (f 0 + f 2) / 2 := by
  rw [twoPoint, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)]
  simp only [expect_pure]
  ring

private theorem expect_coordinate (who : Bool) (f : ℝ → ℝ) :
    expect prior (fun types => f (types who)) = (f 0 + f 2) / 2 := by
  have h := expect_map (fun types : SingleParameterReportProfile Bool => types who) prior f
  rw [prior, independentProduct_map_eval] at h
  exact h.symm.trans (expect_twoPoint f)

private theorem quadratic_average_allocation (reports : SingleParameterReportProfile Bool)
    (who : Bool) : (quadratic.averageOpponents prior).allocation reports who = reports who := by
  simp only [averageOpponents, Profile.update_same, expect_constant]

private theorem quadratic_average_payment (reports : SingleParameterReportProfile Bool)
    (who : Bool) :
    (quadratic.averageOpponents prior).payment reports who = (reports who) ^ 2 / 2 := by
  simp only [averageOpponents, Profile.update_same, expect_constant]

private theorem scaled_average_allocation (reports : SingleParameterReportProfile Bool)
    (who : Bool) : (scaled.averageOpponents prior).allocation reports who = reports who := by
  have hne : (!who) ≠ who := by cases who <;> decide
  change expect prior (fun others =>
    Profile.update others who (reports who) who *
      (2 * Profile.update others who (reports who) (!who) - 1)) = reports who
  simp only [Profile.update_same,
    Profile.update_of_ne (sig := singleParameterSignature Bool) _ _ hne]
  rw [expect_coordinate (!who) (fun x => reports who * (2 * x - 1))]
  ring

private theorem scaled_average_payment (reports : SingleParameterReportProfile Bool)
    (who : Bool) :
    (scaled.averageOpponents prior).payment reports who = (reports who) ^ 2 / 2 := by
  have hne : (!who) ≠ who := by cases who <;> decide
  change expect prior (fun others =>
    (Profile.update others who (reports who) who ^ 2 / 2) *
      (2 * Profile.update others who (reports who) (!who) - 1)) = (reports who) ^ 2 / 2
  simp only [Profile.update_same,
    Profile.update_of_ne (sig := singleParameterSignature Bool) _ _ hne]
  rw [expect_coordinate (!who) (fun x => ((reports who) ^ 2 / 2) * (2 * x - 1))]
  ring

private theorem quadratic_expected_utility (who : Bool) (r t : ℝ) :
    expect prior (fun others => quadratic.utility (Profile.update others who r) who t) =
      t * r - r ^ 2 / 2 := by
  calc
    _ = (quadratic.averageOpponents prior).utility
        (Profile.update (fun _ => 0) who r) who t :=
      (quadratic.averageOpponents_utility prior who (fun _ => 0) r t
        (integrable _) (integrable _)).symm
    _ = _ := by
      simp only [utility, quadratic_average_allocation, quadratic_average_payment,
        Profile.update_same]

private theorem scaled_expected_utility (who : Bool) (r t : ℝ) :
    expect prior (fun others => scaled.utility (Profile.update others who r) who t) =
      t * r - r ^ 2 / 2 := by
  calc
    _ = (scaled.averageOpponents prior).utility
        (Profile.update (fun _ => 0) who r) who t :=
      (scaled.averageOpponents_utility prior who (fun _ => 0) r t
        (integrable _) (integrable _)).symm
    _ = _ := by
      simp only [utility, scaled_average_allocation, scaled_average_payment,
        Profile.update_same]

theorem realized_receipts_differ :
    (∑ who : Bool, quadratic.payment (fun _ => 2) who) = 4 ∧
      (∑ who : Bool, scaled.payment (fun _ => 2) who) = 12 := by
  norm_num [Fintype.sum_bool]

theorem scaled_not_isDSIC : ¬scaled.IsDSIC := by
  intro h
  have hi := (scaled.isDSIC_iff.mp h) false (fun _ => 0) 1
  norm_num [utility, Profile.update_same,
    Profile.update_of_ne (sig := singleParameterSignature Bool) _ _
      (by decide : true ≠ false)] at hi

theorem expected_receipts_equal :
    expect prior (fun types => ∑ who : Bool, quadratic.payment types who) =
      expect prior (fun types => ∑ who : Bool, scaled.payment types who) := by
  apply quadratic.revenue_equivalence scaled laws (fun _ => 0) (fun _ => 2)
  · intro who t ht
    rcases twoPoint_support ht with rfl | rfl <;> norm_num
  · intro who r _
    exact ⟨integrable _, integrable _⟩
  · intro who r _
    exact ⟨integrable _, integrable _⟩
  · intro who t _ r _
    change expect _ _ ≤ expect _ _
    rw [quadratic_expected_utility, quadratic_expected_utility]
    nlinarith [sq_nonneg (r - t)]
  · intro who t _ r _
    change expect _ _ ≤ expect _ _
    rw [scaled_expected_utility, scaled_expected_utility]
    nlinarith [sq_nonneg (r - t)]
  · intro who t _
    rw [quadratic_average_allocation, scaled_average_allocation]
  · intro who
    simp only [utility, quadratic_average_allocation, quadratic_average_payment,
      scaled_average_allocation, scaled_average_payment]
  · intro who
    exact integrable _
  · intro who
    exact integrable _

theorem expected_receipts_value :
    expect prior (fun types => ∑ who : Bool, quadratic.payment types who) = 2 ∧
      expect prior (fun types => ∑ who : Bool, scaled.payment types who) = 2 := by
  have hq : expect prior (fun types => ∑ who : Bool, quadratic.payment types who) = 2 := by
    rw [expect_sum _ _ (fun who => integrable _)]
    have hp (who : Bool) : expect prior (fun types => quadratic.payment types who) = 1 := by
      change expect prior (fun types => (types who) ^ 2 / 2) = 1
      rw [expect_coordinate who (fun x => x ^ 2 / 2)]
      norm_num
    simp_rw [hp]
    norm_num
  exact ⟨hq, expected_receipts_equal.symm.trans hq⟩

theorem scaled_truthful_BNE :
    let BM := scaled.toQuasiLinearMechanism.toBayesianMechanism
    let B := BM.toBayesianGame prior
    IsNash B.toForm (euPreference B.utility) (BM.truthfulPlan prior) := by
  apply scaled.isNash_truthful_of_averageOpponents laws
  · intro who r
    exact integrable _
  · intro who r
    exact integrable _
  · intro who d
    exact integrable _
  · intro who t _ r
    simp only [utility, scaled_average_allocation, scaled_average_payment]
    nlinarith [sq_nonneg (r - t)]

end GameTheory.Tests.RevenueEquivalence
