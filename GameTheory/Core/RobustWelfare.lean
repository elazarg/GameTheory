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
    lam * G.socialWelfare target
        (fun i => hsmooth.integrable target i) ≤
      (1 + mu) * G.expectedSocialWelfare law
        (by
          intro i
          obtain ⟨hbase, _, _⟩ :=
            (G.isεCoarseCorrelatedEq_iff_externalRegret_le.mp hlaw)
              i (target i)
          exact hbase) + (Fintype.card ι) * ε := by
  let hconditional (profile : Profile G.form.sig) (i : ι) :=
    hsmooth.integrable profile i
  have hcert : ∀ i, ∃ hbase : UtilityIntegrable G.utility i
      (G.form.outcomeLaw law), ∃ hdev : UtilityIntegrable G.utility i
      (law.bind fun profile =>
        G.form.play (Profile.update profile i (target i))),
      G.externalRegret law i (target i) hbase hdev ≤ ε := by
    intro i
    exact (G.isεCoarseCorrelatedEq_iff_externalRegret_le.mp hlaw) i
      (target i)
  choose hbase hdev hregret using hcert
  let devKernel (i : ι) (profile : Profile G.form.sig) :=
    G.form.play (Profile.update profile i (target i))
  let devValue (i : ι) (profile : Profile G.form.sig) :=
    expectedUtility G.utility i (devKernel i profile)
      (hconditional (Profile.update profile i (target i)) i)
  let baseValue (i : ι) (profile : Profile G.form.sig) :=
    expectedUtility G.utility i (G.form.play profile)
      (hconditional profile i)
  have hbaseOuter (i : ι) : PayoffIntegrable law (baseValue i) := by
    exact payoffIntegrable_bind_conditionalExpectation law G.form.play
      (fun outcome => G.utility outcome i) (by
        simpa only [GameForm.outcomeLaw] using hbase i)
      (hconditional · i)
  have hdevOuter (i : ι) : PayoffIntegrable law (devValue i) := by
    exact payoffIntegrable_bind_conditionalExpectation law (devKernel i)
      (fun outcome => G.utility outcome i) (hdev i)
      (fun profile => hconditional
        (Profile.update profile i (target i)) i)
  have hdeviations :
      (∑ i, expect law (devValue i) (hdevOuter i)) ≤
        G.expectedSocialWelfare law hbase + (Fintype.card ι) * ε := by
    calc
      (∑ i, expect law (devValue i) (hdevOuter i)) ≤
          ∑ i, (expect law (baseValue i) (hbaseOuter i) + ε) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hdevTower := expectedUtility_bind G.utility i law
          (devKernel i) (hdev i)
          (fun profile => hconditional
            (Profile.update profile i (target i)) i)
        have hbaseTower := expectedUtility_outcomeLaw G.form G.utility i law
          (hbase i) (hconditional · i)
        have hle := hregret i
        unfold externalRegret at hle
        dsimp only [devValue, baseValue] at hdevTower hbaseTower ⊢
        rw [hdevTower, hbaseTower] at hle
        linarith
      _ = G.expectedSocialWelfare law hbase +
          (Fintype.card ι) * ε := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        rw [G.expectedSocialWelfare_eq_expect_profilewise law hbase
          (hconditional ·)]
        apply congrArg (fun value : ℝ => value +
          (Fintype.card ι) * ε)
        simpa only [socialWelfare, baseValue] using
          (expect_sum law baseValue hbaseOuter).symm
  have hprofile : PayoffIntegrable law
      (fun profile => G.socialWelfare profile (hconditional profile)) :=
    G.profilewiseSocialWelfareIntegrable law hbase (hconditional ·)
  have hleft : PayoffIntegrable law
      (fun profile => lam * G.socialWelfare target
        (fun i => hsmooth.integrable target i) -
          mu * G.socialWelfare profile (hconditional profile)) := by
    apply payoffIntegrable_sub
    · exact payoffIntegrable_constant law
        (lam * G.socialWelfare target (fun i => hsmooth.integrable target i))
    · exact payoffIntegrable_const_mul hprofile
  have hright : PayoffIntegrable law
      (fun profile => ∑ i, devValue i profile) :=
    payoffIntegrable_sum law devValue hdevOuter
  have hpointwise : ∀ profile ∈ law.support,
      lam * G.socialWelfare target
          (fun i => hsmooth.integrable target i) -
        mu * G.socialWelfare profile (hconditional profile) ≤
          ∑ i, devValue i profile := by
    intro profile _
    exact hsmooth.inequality profile target
  have hsmoothAverage := expect_mono hpointwise hleft hright
  have hleftValue : expect law
      (fun profile => lam * G.socialWelfare target
        (fun i => hsmooth.integrable target i) -
          mu * G.socialWelfare profile (hconditional profile)) hleft =
      lam * G.socialWelfare target
          (fun i => hsmooth.integrable target i) -
        mu * G.expectedSocialWelfare law hbase := by
    rw [expect_sub (payoffIntegrable_constant law
      (lam * G.socialWelfare target (fun i => hsmooth.integrable target i)))
      (payoffIntegrable_const_mul hprofile)]
    rw [expect_constant, expect_const_mul]
    rw [G.expectedSocialWelfare_eq_expect_profilewise law hbase
      (hconditional ·)]
  have hrightValue : expect law (fun profile => ∑ i, devValue i profile)
      hright = ∑ i, expect law (devValue i) (hdevOuter i) :=
    expect_sum law devValue hdevOuter
  rw [hleftValue, hrightValue] at hsmoothAverage
  linarith

/-- **Robust smoothness for exact coarse correlated equilibrium.** -/
theorem IsSmooth.coarseCorrelated_bound [Fintype ι] [DecidableEq ι]
    {G : UtilityGame ι} {lam mu : ℝ} (hsmooth : G.IsSmooth lam mu)
    {law : PMF (Profile G.form.sig)}
    (hlaw : IsCoarseCorrelatedEq G.form G.preference law)
    (target : Profile G.form.sig) :
    lam * G.socialWelfare target
        (fun i => hsmooth.integrable target i) ≤
      (1 + mu) * G.expectedSocialWelfare law
        (by
          intro i
          obtain ⟨hbase, _, _⟩ :=
            (G.isεCoarseCorrelatedEq_iff_externalRegret_le.mp
              ((G.isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero
                (statusQuo := law)).mp hlaw)) i (target i)
          exact hbase) := by
  have hbound := hsmooth.epsilonCoarseCorrelated_bound
    ((G.isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero
      (statusQuo := law)).mp hlaw) target
  simpa using hbound

end UtilityGame

end GameTheory
