/-
# Robust welfare bounds for coarse correlated equilibrium

This theorem-only bridge combines the pure smoothness surface with the
finite-law external-regret characterization of approximate coarse correlated
equilibrium.  Keeping the bridge separate lets `Core.Welfare` remain below
learning while the public Core root still exports the robust result.

Mathematical provenance: theorem statements and proof structure are recovered
from `reference/GameTheory-v1/GameTheory/Concepts/Welfare/Smoothness.lean` at
pinned commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Core.Learning
import GameTheory.Core.Welfare

noncomputable section

open scoped BigOperators

namespace GameTheory

open Probability

universe uι

namespace UtilityGame

variable {ι : Type uι}

/-- **Robust smoothness for approximate coarse correlated equilibrium.**  An
`ε`-CCE pays one additive `ε` term per finite player.  Finite support makes
the statement independent of any finiteness assumption on profiles or
outcomes. -/
theorem IsSmooth.epsilonCoarseCorrelated_bound [Fintype ι] [DecidableEq ι]
    {G : UtilityGame ι} {lam mu ε : ℝ} (hsmooth : G.IsSmooth lam mu)
    {law : FinDist (Profile G.form.sig)} (hlaw : G.IsεCoarseCorrelatedEq ε law)
    (target : Profile G.form.sig) :
    lam * G.socialWelfare target ≤
      (1 + mu) * G.expectedSocialWelfare law + (Fintype.card ι) * ε := by
  have hdeviations :
      (∑ i, law.expect (fun profile =>
        expectedUtility G.utility i
          (G.form.play (Profile.update profile i (target i))))) ≤
        G.expectedSocialWelfare law + (Fintype.card ι) * ε := by
    calc
      ∑ i, law.expect (fun profile =>
          expectedUtility G.utility i
            (G.form.play (Profile.update profile i (target i)))) ≤
          ∑ i, (law.expect (fun profile =>
            expectedUtility G.utility i (G.form.play profile)) + ε) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hregret :=
          (G.isεCoarseCorrelatedEq_iff_externalRegret_le.mp hlaw) i (target i)
        unfold externalRegret at hregret
        rw [expectedUtility_bind, expectedUtility_outcomeLaw] at hregret
        linarith
      _ = G.expectedSocialWelfare law + (Fintype.card ι) * ε := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        rw [G.expectedSocialWelfare_eq_sum]
        simp_rw [expectedUtility_outcomeLaw]
  have hsmoothExpected :
      lam * G.socialWelfare target - mu * G.expectedSocialWelfare law ≤
        ∑ i, law.expect (fun profile =>
          expectedUtility G.utility i
            (G.form.play (Profile.update profile i (target i)))) := by
    calc
      lam * G.socialWelfare target - mu * G.expectedSocialWelfare law =
          law.expect fun profile =>
            lam * G.socialWelfare target - mu * G.socialWelfare profile := by
        rw [expectedSocialWelfare]
        calc
          lam * G.socialWelfare target - mu * law.expect G.socialWelfare =
              lam * G.socialWelfare target +
                (-mu) * law.expect G.socialWelfare := by ring
          _ = law.expect (fun _ => lam * G.socialWelfare target) +
                law.expect (fun profile => (-mu) * G.socialWelfare profile) := by
              rw [FinDist.expect_const, FinDist.expect_smul]
          _ = law.expect (fun profile =>
                lam * G.socialWelfare target + (-mu) * G.socialWelfare profile) := by
              rw [FinDist.expect_add]
          _ = law.expect (fun profile =>
                lam * G.socialWelfare target - mu * G.socialWelfare profile) := by
              congr 1
              funext profile
              ring
      _ ≤ law.expect (fun profile => ∑ i,
            expectedUtility G.utility i
              (G.form.play (Profile.update profile i (target i)))) := by
        exact FinDist.expect_mono fun profile _ => hsmooth profile target
      _ = ∑ i, law.expect (fun profile =>
            expectedUtility G.utility i
              (G.form.play (Profile.update profile i (target i)))) :=
        (FinDist.expect_sum_comm law fun i profile =>
          expectedUtility G.utility i
            (G.form.play (Profile.update profile i (target i)))).symm
  linarith

/-- **Robust smoothness for exact coarse correlated equilibrium.**  This is
the zero-tolerance specialization of `epsilonCoarseCorrelated_bound`. -/
theorem IsSmooth.coarseCorrelated_bound [Fintype ι] [DecidableEq ι]
    {G : UtilityGame ι} {lam mu : ℝ} (hsmooth : G.IsSmooth lam mu)
    {law : FinDist (Profile G.form.sig)}
    (hlaw : IsCoarseCorrelatedEq G.form G.preference law)
    (target : Profile G.form.sig) :
    lam * G.socialWelfare target ≤
      (1 + mu) * G.expectedSocialWelfare law := by
  have hbound := hsmooth.epsilonCoarseCorrelated_bound
    ((G.isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero).mp hlaw) target
  simpa using hbound

end UtilityGame

end GameTheory
