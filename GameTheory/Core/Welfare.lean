/-
# Social welfare and smooth games

Social welfare sums expected utilities under the law being assessed.
Smoothness states the integrability of exactly the pure-profile utilities its
comparison uses.
-/

import GameTheory.Core.Response

noncomputable section

open scoped BigOperators

namespace GameTheory

open GameTheory.Math.Probability

universe uι

namespace UtilityGame

variable {ι : Type uι}

/-- Aggregate expected utility at a pure strategy profile. -/
def socialWelfare [Fintype ι] (G : UtilityGame ι)
    (profile : Profile G.form.sig) : ℝ :=
  ∑ i, expectedUtility G.utility i (G.form.play profile)

/-- Expected social welfare under a law on profiles, evaluated through its
actual induced outcome law. -/
def expectedSocialWelfare [Fintype ι] (G : UtilityGame ι)
    (law : PMF (Profile G.form.sig)) : ℝ :=
  ∑ i, expectedUtility G.utility i (G.form.outcomeLaw law)

/-- A point mass specializes expected welfare to the pure-profile aggregate. -/
theorem expectedSocialWelfare_pure [Fintype ι] (G : UtilityGame ι)
    (profile : Profile G.form.sig) :
    G.expectedSocialWelfare (PMF.pure profile)
       = G.socialWelfare profile := by
  simp [expectedSocialWelfare, socialWelfare, GameForm.outcomeLaw_pure]

/-- Profilewise welfare is integrable when each player's conditional and
aggregate utilities are integrable. -/
theorem profilewiseSocialWelfareIntegrable [Fintype ι]
    (G : UtilityGame ι) (law : PMF (Profile G.form.sig))
    (haggregate : ∀ i,
      UtilityIntegrable G.utility i (G.form.outcomeLaw law)) :
    PayoffIntegrable law (fun profile =>
      G.socialWelfare profile) := by
  let conditional (i : ι) (profile : Profile G.form.sig) :=
    expectedUtility G.utility i (G.form.play profile)
  have houter (i : ι) : PayoffIntegrable law (conditional i) := by
    exact payoffIntegrable_bind_conditionalExpectation law G.form.play
      (fun outcome => G.utility outcome i) (haggregate i)
  simpa [socialWelfare, conditional] using payoffIntegrable_sum law conditional houter

/-- When every conditional profile utility and each aggregate utility are
integrable, expected social welfare also equals the expected pure-profile
aggregate. -/
theorem expectedSocialWelfare_eq_expect_profilewise [Fintype ι]
    (G : UtilityGame ι) (law : PMF (Profile G.form.sig))
    (haggregate : ∀ i,
      UtilityIntegrable G.utility i (G.form.outcomeLaw law)) :
    G.expectedSocialWelfare law =
      expect law (fun profile => G.socialWelfare profile) := by
  classical
  let conditional (i : ι) (profile : Profile G.form.sig) :=
    expectedUtility G.utility i (G.form.play profile)
  have houter (i : ι) : PayoffIntegrable law (conditional i) := by
    exact payoffIntegrable_bind_conditionalExpectation law G.form.play
      (fun outcome => G.utility outcome i) (haggregate i)
  have htower (i : ι) :
      expect (G.form.outcomeLaw law) (fun outcome => G.utility outcome i)
           = expect law (conditional i) := by
    simpa only [GameForm.outcomeLaw, conditional, expectedUtility] using
      expect_bind_tower law G.form.play (fun outcome => G.utility outcome i)
        (haggregate i)
  calc
    G.expectedSocialWelfare law =
        ∑ i, expect (G.form.outcomeLaw law)
          (fun outcome => G.utility outcome i) := rfl
    _ =
        ∑ i, expect law (conditional i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact htower i
    _ = expect law (fun profile => ∑ i, conditional i profile)
         := (expect_sum law conditional houter).symm
    _ = expect law (fun profile => G.socialWelfare profile) := rfl

/-- Smoothness carries a certificate that every pure-profile utility used by
its comparisons is integrable. -/
structure IsSmooth [Fintype ι] [DecidableEq ι]
    (G : UtilityGame ι) (lam mu : ℝ) : Prop where
  integrable : ∀ profile i,
    UtilityIntegrable G.utility i (G.form.play profile)
  inequality : ∀ statusQuo target : Profile G.form.sig,
    lam * G.socialWelfare target -
        mu * G.socialWelfare statusQuo ≤
      ∑ i, expectedUtility G.utility i
        (G.form.play (Profile.update statusQuo i (target i)))

/-- **Smoothness bounds every Nash equilibrium.** The inequality form avoids
division and therefore needs no positivity or nonzero-denominator condition. -/
theorem IsSmooth.nash_bound [Fintype ι] [DecidableEq ι]
    {G : UtilityGame ι} {lam mu : ℝ}
    (hsmooth : G.IsSmooth lam mu)
    {statusQuo : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) statusQuo)
    (target : Profile G.form.sig) :
    lam * G.socialWelfare target ≤
      (1 + mu) * G.socialWelfare statusQuo := by
  have hdeviations :
      (∑ i, expectedUtility G.utility i
          (G.form.play (Profile.update statusQuo i (target i)))) ≤
        G.socialWelfare statusQuo := by
    rw [socialWelfare]
    apply Finset.sum_le_sum
    intro i _
    have hpref := (isNash_iff (F := G.form) statusQuo).1 hnash i (target i)
    exact (euPreference_iff G.utility i (G.form.play statusQuo)
      (G.form.play (Profile.update statusQuo i (target i)))
      (hsmooth.integrable statusQuo i)
      (hsmooth.integrable (Profile.update statusQuo i (target i)) i)).1 hpref
  linarith [hsmooth.inequality statusQuo target]

end UtilityGame

end GameTheory
