/-
# Social welfare and smooth games

Social welfare is an aggregate view of the canonical expected utilities, not a
new game or payoff semantics.  Smoothness likewise quantifies over unilateral
updates in the existing game form.  Its first consumer is the affine
congestion-game price-of-anarchy theorem.

The public surface intentionally stops at an inequality.  It does not define
an optimum, a best or worst equilibrium, or a total-division ratio whose
meaning changes at zero or under the cost-to-welfare sign convention.
-/

import GameTheory.Core.Utility

noncomputable section

open scoped BigOperators

namespace GameTheory

open Probability

universe uι

namespace UtilityGame

variable {ι : Type uι}

/-- Aggregate expected utility at a pure strategy profile.  Player finiteness
is required by this operation, not stored in `UtilityGame`. -/
def socialWelfare [Fintype ι] (G : UtilityGame ι) (profile : Profile G.form.sig) : ℝ :=
  ∑ i, expectedUtility G.utility i (G.form.play profile)

/-- Expected social welfare under a finite-support law on pure profiles.  This
is the expectation of the canonical pure-profile aggregate, not a second
correlated-payoff semantics. -/
def expectedSocialWelfare [Fintype ι] (G : UtilityGame ι)
    (law : FinDist (Profile G.form.sig)) : ℝ :=
  law.expect G.socialWelfare

@[simp]
theorem expectedSocialWelfare_pure [Fintype ι] (G : UtilityGame ι)
    (profile : Profile G.form.sig) :
    G.expectedSocialWelfare (FinDist.pure profile) = G.socialWelfare profile :=
  FinDist.expect_pure ..

/-- Expected social welfare is equivalently the sum of each player's expected
utility under the induced outcome law. -/
theorem expectedSocialWelfare_eq_sum [Fintype ι] (G : UtilityGame ι)
    (law : FinDist (Profile G.form.sig)) :
    G.expectedSocialWelfare law =
      ∑ i, expectedUtility G.utility i (G.form.outcomeLaw law) := by
  unfold expectedSocialWelfare socialWelfare
  simp_rw [expectedUtility_outcomeLaw]
  exact (FinDist.expect_sum_comm law fun i profile =>
    expectedUtility G.utility i (G.form.play profile)).symm

/-- A utility game is `(λ, μ)`-smooth when simultaneous comparison with a
target profile is bounded by the sum of its unilateral target deviations. -/
def IsSmooth [Fintype ι] [DecidableEq ι] (G : UtilityGame ι) (lam mu : ℝ) : Prop :=
  ∀ statusQuo target : Profile G.form.sig,
    lam * G.socialWelfare target - mu * G.socialWelfare statusQuo ≤
      ∑ i, expectedUtility G.utility i
        (G.form.play (Profile.update statusQuo i (target i)))

/-- **Smoothness bounds every Nash equilibrium.**  The inequality form avoids
division and therefore needs no positivity or nonzero-denominator side
condition. -/
theorem IsSmooth.nash_bound [Fintype ι] [DecidableEq ι] {G : UtilityGame ι}
    {lam mu : ℝ} (hsmooth : G.IsSmooth lam mu)
    {statusQuo : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) statusQuo)
    (target : Profile G.form.sig) :
    lam * G.socialWelfare target ≤ (1 + mu) * G.socialWelfare statusQuo := by
  have hdeviations :
      (∑ i, expectedUtility G.utility i
          (G.form.play (Profile.update statusQuo i (target i)))) ≤
        G.socialWelfare statusQuo := by
    rw [socialWelfare]
    exact Finset.sum_le_sum fun i _ => (isNash_iff statusQuo).mp hnash i (target i)
  linarith [hsmooth statusQuo target]

end UtilityGame

end GameTheory
