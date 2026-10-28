module

/-
Null types and varying conditional beliefs delimit interim envelope claims.
Truthful Bayesian Nash equilibrium only constrains supported own types;
an envelope over an interval needs incentive comparisons throughout it.
With correlated types, actual conditional beliefs may vary with the true
type even when reporting incentives are satisfied everywhere.
-/

public import GameTheory.Analysis.SingleParameter
public import GameTheory.Mechanism.SingleParameter.Bayesian
public import GameTheory.Math.Probability.Conditioning

@[expose] public section

noncomputable section

namespace GameTheory.Tests.RevenueBoundary

open Mechanism Mechanism.SingleParameterMechanism Math.Probability Set

@[reducible]
def nullMechanism : SingleParameterMechanism Unit where
  allocation _ _ := 0
  payment reports _ := (reports ()) ^ 2

def nullLaws : Unit → PMF ℝ := fun _ => PMF.pure 0

private theorem nullPrior_eq_pure :
    independentProduct nullLaws = PMF.pure (fun _ : Unit => (0 : ℝ)) :=
  independentProduct_pure _

/-- Truthful reporting is a canonical BNE because only true type zero occurs. -/
theorem null_truthful_isNash :
    let BM := nullMechanism.toQuasiLinearMechanism.toBayesianMechanism
    let B := BM.toBayesianGame (independentProduct nullLaws)
    IsNash B.toForm (euPreference B.utility)
      (BM.truthfulPlan (independentProduct nullLaws)) := by
  apply nullMechanism.isNash_truthful_of_averageOpponents nullLaws
  · intro who r
    rw [nullPrior_eq_pure]
    exact payoffIntegrable_pure _ _
  · intro who r
    rw [nullPrior_eq_pure]
    exact payoffIntegrable_pure _ _
  · intro who d
    rw [nullPrior_eq_pure]
    exact payoffIntegrable_pure _ _
  · intro who t ht r
    have ht0 : t = 0 := by simpa [nullLaws, PMF.mem_support_pure_iff] using ht
    subst t
    cases who
    simp only [utility, averageOpponents, nullPrior_eq_pure, expect_pure,
      Profile.update_same, mul_zero, zero_sub, zero_pow (by decide : 2 ≠ 0), neg_zero]
    exact neg_nonpos.mpr (sq_nonneg r)

theorem type_one_is_null : (1 : ℝ) ∉ (nullLaws ()).support := by
  norm_num [nullLaws, PMF.mem_support_pure_iff]

/-- BNE at the point-mass prior does not imply interval-wide interim IC. -/
theorem null_interval_optimality_fails :
    ¬ IsMaxOn (fun r =>
      (nullMechanism.averageOpponents (independentProduct nullLaws)).utility
        (fun _ => r) () 1) (Icc (0 : ℝ) 1) 1 := by
  intro h
  have hbad := (isMaxOn_iff.mp h) 0 (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  norm_num [utility, averageOpponents, nullPrior_eq_pure, expect_pure,
    Profile.update_same] at hbad

/-- The unsupported type's charge is not determined by the zero allocation
and the supported type's baseline charge. -/
theorem null_payment_envelope_fails :
    let A := nullMechanism.averageOpponents (independentProduct nullLaws)
    A.payment (fun _ => 1) () ≠ A.payment (fun _ => 0) () +
      A.allocation (fun _ => 1) () - ∫ s in (0 : ℝ)..1, A.allocation (fun _ => s) () := by
  norm_num [averageOpponents, nullPrior_eq_pure, expect_pure, Profile.update_same]

@[reducible]
def correlatedMechanism : SingleParameterMechanism Bool where
  allocation _ _ := 0
  payment reports who := -reports (!who)

/-- A conditional-belief extension that will agree with the actual prior at
both supported own types. No assertion about null-type conditioning is made. -/
def correlatedBeliefs (t : ℝ) : PMF (SingleParameterReportProfile Bool) :=
  PMF.pure (fun _ => t)

def correlatedPrior : PMF (SingleParameterReportProfile Bool) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (fun _ => 0)) (PMF.pure (fun _ => 1))

private theorem correlatedPrior_support {types : SingleParameterReportProfile Bool}
    (h : types ∈ correlatedPrior.support) :
    types = (fun _ => 0) ∨ types = (fun _ => 1) := by
  by_contra hn
  push Not at hn
  have hz : correlatedPrior types = 0 := by
    simp [correlatedPrior, mix_apply, PMF.pure_apply, hn.1, hn.2]
  exact h hz

private theorem correlated_atom_supported (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (fun _ : Bool => t) ∈ correlatedPrior.support := by
  rcases ht with rfl | rfl
  · exact mem_support_mix_left _ _ _ (by norm_num) (by simp)
  · exact mem_support_mix_right _ _ _ (by norm_num) (by simp)

/-- At both supported types these beliefs are the actual posterior of the
perfectly correlated prior, not an arbitrary assignment of off-path beliefs. -/
theorem correlatedBeliefs_are_posteriors (who : Bool) (t : ℝ) (ht : t = 0 ∨ t = 1) :
    fiberPosterior correlatedPrior (fun types => types who) t = correlatedBeliefs t := by
  have htpos : t ∈ (correlatedPrior.map (fun types => types who)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨fun _ => t, correlated_atom_supported t ht, rfl⟩
  apply pmf_eq_pure_of_support_subset_singleton
  intro types hs
  have h := mem_support_fiberPosterior htpos hs
  simp only [Set.mem_singleton_iff]
  rcases correlatedPrior_support h.2 with rfl | rfl <;>
    funext i <;> exact h.1

theorem correlated_interim_utility (who : Bool) (t r : ℝ) :
    (correlatedMechanism.averageOpponents (correlatedBeliefs t)).utility
      (fun _ => r) who t = t := by
  have hne : (!who) ≠ who := by cases who <;> decide
  simp only [utility, averageOpponents, correlatedBeliefs, expect_pure]
  change t * 0 - -(Profile.update (sig := singleParameterSignature Bool)
    (fun _ => t) who r (!who)) = t
  rw [Profile.update_of_ne (sig := singleParameterSignature Bool) (fun _ => t) r hne]
  ring

/-- Every report is optimal, including at all types in the entire interval,
when conditional beliefs are allowed to vary with true type. -/
theorem correlated_every_report_optimal (who : Bool) (t : ℝ) :
    IsMaxOn (fun r =>
      (correlatedMechanism.averageOpponents (correlatedBeliefs t)).utility
        (fun _ => r) who t) (Icc (0 : ℝ) 1) t := by
  rw [isMaxOn_iff]
  intro r _
  exact le_of_eq ((correlated_interim_utility who t r).trans
    (correlated_interim_utility who t t).symm)

/-- Type-dependent conditional utility changes while every allocation is
zero, refuting an envelope argument that silently freezes those beliefs. -/
theorem correlated_utility_envelope_fails :
    (correlatedMechanism.averageOpponents (correlatedBeliefs 1)).utility
        (fun _ => 1) false 1 ≠
      (correlatedMechanism.averageOpponents (correlatedBeliefs 0)).utility
          (fun _ => 0) false 0 +
        ∫ s in (0 : ℝ)..1,
          (correlatedMechanism.averageOpponents (correlatedBeliefs s)).allocation
            (fun _ => s) false := by
  have hu1 := correlated_interim_utility false 1 1
  have hu0 := correlated_interim_utility false 0 0
  have hz : (∫ s in (0 : ℝ)..1,
      (correlatedMechanism.averageOpponents (correlatedBeliefs s)).allocation
        (fun _ => s) false) = 0 := by
    norm_num [averageOpponents, correlatedBeliefs, expect_pure]
  intro h
  linarith

end GameTheory.Tests.RevenueBoundary
