/-
# Robust welfare bounds for coarse correlated equilibrium

This theorem-only bridge combines the guarded smoothness surface with the
actual-law external-regret characterization of approximate CCE.

Primary reference: T. Roughgarden, “Intrinsic Robustness of the Price of
Anarchy,” STOC 2009.
-/

import GameTheory.Core.Learning
import GameTheory.Core.Welfare

noncomputable section

open scoped BigOperators

namespace GameTheory

open GameTheory.Math.Probability

universe uι

namespace UtilityGame

variable {ι : Type uι}

/-- **Robust smoothness for approximate coarse correlated equilibrium.**
The actual incumbent and deviation laws are integrated by the CCE guard;
smoothness supplies the pure-profile conditional guards. -/
theorem IsSmooth.epsilonCoarseCorrelated_bound [Fintype ι] [DecidableEq ι]
    {G : UtilityGame ι} {lam mu ε : ℝ} (hsmooth : G.IsSmooth lam mu)
    {law : PMF (Profile G.form.sig)}
    (hlaw : IsεCoarseCorrelatedEq G.form G.utility ε law)
    (target : Profile G.form.sig) :
    lam * G.socialWelfare target ≤
      (1 + mu) * G.expectedSocialWelfare law
         + (Fintype.card ι) * ε := by
  have hcert : ∀ i, UtilityIntegrable G.utility i (G.form.outcomeLaw law) ∧
      UtilityIntegrable G.utility i
        (law.bind fun profile => G.form.play (Profile.update profile i (target i))) ∧
      G.externalRegret law i (target i) ≤ ε := by
    intro i
    exact (G.isεCoarseCorrelatedEq_iff_externalRegret_le.mp hlaw) i
      (target i)
  choose hbase hdev hregret using hcert
  let devKernel (i : ι) (profile : Profile G.form.sig) :=
    G.form.play (Profile.update profile i (target i))
  let devValue (i : ι) (profile : Profile G.form.sig) :=
    expectedUtility G.utility i (devKernel i profile)
  let baseValue (i : ι) (profile : Profile G.form.sig) :=
    expectedUtility G.utility i (G.form.play profile)
  have hbaseOuter (i : ι) : PayoffIntegrable law (baseValue i) := by
    exact payoffIntegrable_bind_conditionalExpectation law G.form.play
      (fun outcome => G.utility outcome i) (by
        simpa only [GameForm.outcomeLaw] using hbase i)
  have hdevOuter (i : ι) : PayoffIntegrable law (devValue i) := by
    exact payoffIntegrable_bind_conditionalExpectation law (devKernel i)
      (fun outcome => G.utility outcome i) (hdev i)
  have hdeviations :
      (∑ i, expect law (devValue i)) ≤
        G.expectedSocialWelfare law + (Fintype.card ι) * ε := by
    calc
      (∑ i, expect law (devValue i)) ≤
          ∑ i, (expect law (baseValue i) + ε) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hdevTower := expectedUtility_bind G.utility i law
          (devKernel i) (hdev i)
        have hbaseTower := expectedUtility_outcomeLaw G.form G.utility i law
          (hbase i)
        have hle := hregret i
        unfold externalRegret at hle
        dsimp only [devValue, baseValue] at hdevTower hbaseTower ⊢
        rw [hdevTower, hbaseTower] at hle
        linarith
      _ = G.expectedSocialWelfare law +
          (Fintype.card ι) * ε := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        rw [G.expectedSocialWelfare_eq_expect_profilewise law hbase]
        apply congrArg (fun value : ℝ => value +
          (Fintype.card ι) * ε)
        simpa only [socialWelfare, baseValue] using
          (expect_sum law baseValue hbaseOuter).symm
  have hprofile : PayoffIntegrable law
      (fun profile => G.socialWelfare profile) :=
    G.profilewiseSocialWelfareIntegrable law hbase
  have hleft : PayoffIntegrable law
      (fun profile => lam * G.socialWelfare target -
          mu * G.socialWelfare profile) := by
    apply payoffIntegrable_sub
    · exact payoffIntegrable_constant law
        (lam * G.socialWelfare target)
    · exact payoffIntegrable_const_mul hprofile
  have hright : PayoffIntegrable law
      (fun profile => ∑ i, devValue i profile) :=
    payoffIntegrable_sum law devValue hdevOuter
  have hpointwise : ∀ profile ∈ law.support,
      lam * G.socialWelfare target -
        mu * G.socialWelfare profile ≤
          ∑ i, devValue i profile := by
    intro profile _
    exact hsmooth.inequality profile target
  have hsmoothAverage := expect_mono hpointwise hleft hright
  have hleftValue : expect law
      (fun profile => lam * G.socialWelfare target -
          mu * G.socialWelfare profile) =
      lam * G.socialWelfare target -
        mu * G.expectedSocialWelfare law := by
    rw [expect_sub (payoffIntegrable_constant law
      (lam * G.socialWelfare target))
      (payoffIntegrable_const_mul hprofile)]
    rw [expect_constant, expect_const_mul]
    rw [G.expectedSocialWelfare_eq_expect_profilewise law hbase]
  have hrightValue : expect law (fun profile => ∑ i, devValue i profile)
       = ∑ i, expect law (devValue i) :=
    expect_sum law devValue hdevOuter
  rw [hleftValue, hrightValue] at hsmoothAverage
  linarith

/-- **Robust smoothness for exact coarse correlated equilibrium.** -/
theorem IsSmooth.coarseCorrelated_bound [Fintype ι] [DecidableEq ι]
    {G : UtilityGame ι} {lam mu : ℝ} (hsmooth : G.IsSmooth lam mu)
    {law : PMF (Profile G.form.sig)}
    (hlaw : IsCoarseCorrelatedEq G.form G.preference law)
    (target : Profile G.form.sig) :
    lam * G.socialWelfare target ≤
      (1 + mu) * G.expectedSocialWelfare law := by
  have hbound := hsmooth.epsilonCoarseCorrelated_bound
    ((G.isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero
      (statusQuo := law)).mp hlaw) target
  simpa using hbound

end UtilityGame

end GameTheory
