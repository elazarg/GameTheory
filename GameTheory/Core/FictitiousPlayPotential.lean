/-
# Empirical potential recurrences

Advancing one empirical marginal is an affine update of the multilinear
potential.  In an exact-potential game, its first-order increment is precisely
the step size times the action's current deviation gain.  These identities are
finite-law algebra; asymptotic estimates live in `Analysis`.
-/

import GameTheory.Core.FictitiousPlay
import GameTheory.Core.MixedPotential

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

namespace UtilityGame

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable (G : UtilityGame.{uι, us, uo} ι)

/-- Advancing one coordinate to its next empirical marginal is affine for the
mixed extension of every pure-profile observable. -/
theorem mixedPotential_update_empiricalMarginal_succ
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ) :
    G.mixedPotential potential
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 2))) =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          G.mixedPotential potential
            (Profile.update mixedProfile who
              (G.empiricalMarginal history who (t + 1))) +
        (1 / (t + 2 : ℝ)) *
          G.mixedPotential potential
            (Profile.update mixedProfile who
              (FinDist.pure (history (t + 1) who))) := by
  rw [G.mixedPotential_update potential mixedProfile who
      (G.empiricalMarginal history who (t + 2)),
    G.empiricalMarginal_succ_expect history who t
      (fun action => G.mixedPotential potential
        (Profile.update mixedProfile who (FinDist.pure action))),
    ← G.mixedPotential_update potential mixedProfile who
      (G.empiricalMarginal history who (t + 1))]

/-- Difference form of the one-coordinate empirical-potential recurrence. -/
theorem mixedPotential_update_empiricalMarginal_succ_sub
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ) :
    G.mixedPotential potential
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 2))) -
      G.mixedPotential potential
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 1))) =
      (1 / (t + 2 : ℝ)) *
        (G.mixedPotential potential
            (Profile.update mixedProfile who
              (FinDist.pure (history (t + 1) who))) -
          G.mixedPotential potential
            (Profile.update mixedProfile who
              (G.empiricalMarginal history who (t + 1)))) := by
  rw [G.mixedPotential_update_empiricalMarginal_succ potential history
    mixedProfile who t]
  have hnonzero : (t + 2 : ℝ) ≠ 0 := by positivity
  field_simp [hnonzero]
  ring

/-- The gain in mixed potential from replacing one marginal by a pure action. -/
def mixedPotentialGain (potential : Profile G.form.sig → ℝ)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) : ℝ :=
  G.mixedPotential potential
      (Profile.update mixedProfile who (FinDist.pure action)) -
    G.mixedPotential potential mixedProfile

/-- If the updated coordinate is still the old empirical marginal, the
potential increment is the step size times the matching pure gain. -/
theorem mixedPotential_update_empiricalMarginal_succ_sub_of_eq
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hcoordinate : mixedProfile who =
      G.empiricalMarginal history who (t + 1)) :
    G.mixedPotential potential
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 2))) -
      G.mixedPotential potential mixedProfile =
      (1 / (t + 2 : ℝ)) *
        G.mixedPotentialGain potential mixedProfile who
          (history (t + 1) who) := by
  have hupdate :
      Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 1)) = mixedProfile := by
    rw [← hcoordinate]
    exact Profile.update_eq_self mixedProfile who
  have hrecurrence :=
    G.mixedPotential_update_empiricalMarginal_succ_sub
      potential history mixedProfile who t
  rw [hupdate] at hrecurrence
  exact hrecurrence

/-- Exact potential identifies every pure mixed-potential gain with the
corresponding expected-utility gain. -/
theorem IsExactPotential.mixedPotentialGain_eq_mixedGain
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    G.mixedPotentialGain potential mixedProfile who action =
      G.mixedGain mixedProfile who action := by
  exact (UtilityGame.IsExactPotential.mixed_pure_diff
    (G := G) hpotential mixedProfile who action).symm

/-- In an exact-potential game, advancing one empirical-belief coordinate has
increment equal to the step size times that player's played gain. -/
theorem IsExactPotential.mixedPotential_belief_update_empiricalMarginal_succ_sub
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    (history : ℕ → Profile G.form.sig) (who : ι) (t : ℕ) :
    G.mixedPotential potential
        (Profile.update (G.empiricalBelief history (t + 1)) who
          (G.empiricalMarginal history who (t + 2))) -
      G.mixedPotential potential (G.empiricalBelief history (t + 1)) =
      (1 / (t + 2 : ℝ)) * G.playedGain history t who := by
  have hcoordinate :
      G.empiricalBelief history (t + 1) who =
        G.empiricalMarginal history who (t + 1) := rfl
  rw [G.mixedPotential_update_empiricalMarginal_succ_sub_of_eq
      potential history (G.empiricalBelief history (t + 1)) who t hcoordinate,
    UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain
      (G := G) hpotential]
  rfl

omit [DecidableEq ι] in
/-- A uniform absolute bound on pure profiles also bounds the multilinear
mixed potential. -/
theorem mixedPotential_abs_le_of_abs_bound
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (mixedProfile : Profile G.form.sig.mixed) :
    |G.mixedPotential potential mixedProfile| ≤ C := by
  unfold mixedPotential
  exact FinDist.abs_expect_le_of_abs_bound _ _ fun profile _ => hbound profile

/-- Every real observable on a finite pure-profile space has a uniform
absolute bound. -/
theorem exists_profile_abs_bound
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (potential : Profile G.form.sig → ℝ) :
    ∃ C : ℝ, ∀ profile, |potential profile| ≤ C := by
  refine ⟨∑ profile : Profile G.form.sig, |potential profile|, ?_⟩
  intro profile
  exact Finset.single_le_sum
    (fun candidate _ => abs_nonneg (potential candidate))
    (Finset.mem_univ profile)

/-- Advancing one marginal by one empirical step changes a bounded mixed
potential by at most `2C/(t+2)`. -/
theorem mixedPotential_update_empiricalMarginal_succ_abs_sub_le
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hcoordinate : mixedProfile who =
      G.empiricalMarginal history who (t + 1)) :
    |G.mixedPotential potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) -
        G.mixedPotential potential mixedProfile| ≤
      (1 / (t + 2 : ℝ)) * (2 * C) := by
  have hrecurrence :=
    G.mixedPotential_update_empiricalMarginal_succ_sub_of_eq
      potential history mixedProfile who t hcoordinate
  have hpure := G.mixedPotential_abs_le_of_abs_bound potential hbound
    (Profile.update mixedProfile who
      (FinDist.pure (history (t + 1) who)))
  have hbase :=
    G.mixedPotential_abs_le_of_abs_bound potential hbound mixedProfile
  have hdiff :
      |G.mixedPotential potential
          (Profile.update mixedProfile who
            (FinDist.pure (history (t + 1) who))) -
        G.mixedPotential potential mixedProfile| ≤ 2 * C := by
    have htriangle := abs_sub
      (G.mixedPotential potential
        (Profile.update mixedProfile who
          (FinDist.pure (history (t + 1) who))))
      (G.mixedPotential potential mixedProfile)
    linarith
  have hstep : 0 ≤ (1 / (t + 2 : ℝ)) := by positivity
  calc
    |G.mixedPotential potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) -
        G.mixedPotential potential mixedProfile| =
        |(1 / (t + 2 : ℝ)) *
          G.mixedPotentialGain potential mixedProfile who
            (history (t + 1) who)| := by rw [hrecurrence]
    _ = (1 / (t + 2 : ℝ)) *
        |G.mixedPotentialGain potential mixedProfile who
          (history (t + 1) who)| := by
      rw [abs_mul, abs_of_nonneg hstep]
    _ ≤ (1 / (t + 2 : ℝ)) * (2 * C) :=
      mul_le_mul_of_nonneg_left hdiff hstep

/-- Advancing another player's marginal changes a fixed pure potential gain by
at most `4C/(t+2)`. -/
theorem mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_of_ne
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed)
    {changed who : ι} (action : G.form.sig.Strategy who)
    (hne : changed ≠ who) (t : ℕ)
    (hcoordinate : mixedProfile changed =
      G.empiricalMarginal history changed (t + 1)) :
    |G.mixedPotentialGain potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) who action -
        G.mixedPotentialGain potential mixedProfile who action| ≤
      (1 / (t + 2 : ℝ)) * (4 * C) := by
  have hcommute :
      Profile.update
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2)))
          who (FinDist.pure action) =
        Profile.update
          (Profile.update mixedProfile who (FinDist.pure action))
          changed (G.empiricalMarginal history changed (t + 2)) :=
    Profile.update_comm mixedProfile hne
      (G.empiricalMarginal history changed (t + 2)) (FinDist.pure action)
  have hpureCoordinate :
      Profile.update mixedProfile who (FinDist.pure action) changed =
        G.empiricalMarginal history changed (t + 1) := by
    rw [Profile.update_of_ne _ _ hne]
    exact hcoordinate
  have hpureStep :=
    G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
      potential hbound history
      (Profile.update mixedProfile who (FinDist.pure action)) changed t
      hpureCoordinate
  have hbaseStep :=
    G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
      potential hbound history mixedProfile changed t hcoordinate
  rw [mixedPotentialGain, mixedPotentialGain, hcommute]
  have hrewrite :
      G.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (FinDist.pure action)) changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) -
        (G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action)) -
          G.mixedPotential potential mixedProfile) =
      (G.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (FinDist.pure action)) changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action))) -
      (G.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential mixedProfile) := by ring
  rw [hrewrite]
  calc
    _ ≤ |G.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (FinDist.pure action)) changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action))| +
      |G.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential mixedProfile| := abs_sub _ _
    _ ≤ (1 / (t + 2 : ℝ)) * (2 * C) +
        (1 / (t + 2 : ℝ)) * (2 * C) := add_le_add hpureStep hbaseStep
    _ = (1 / (t + 2 : ℝ)) * (4 * C) := by ring

/-- Advancing a player's own marginal changes its fixed pure potential gain by
at most `2C/(t+2)`. -/
theorem mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_self
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed)
    {who : ι} (action : G.form.sig.Strategy who) (t : ℕ)
    (hcoordinate : mixedProfile who =
      G.empiricalMarginal history who (t + 1)) :
    |G.mixedPotentialGain potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) who action -
        G.mixedPotentialGain potential mixedProfile who action| ≤
      (1 / (t + 2 : ℝ)) * (2 * C) := by
  have hstep := G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
    potential hbound history mixedProfile who t hcoordinate
  rw [mixedPotentialGain, mixedPotentialGain,
    Profile.update_idem]
  have hrewrite :
      G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action)) -
        G.mixedPotential potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) -
        (G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action)) -
          G.mixedPotential potential mixedProfile) =
      -(G.mixedPotential potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) -
        G.mixedPotential potential mixedProfile) := by ring
  rw [hrewrite, abs_neg]
  exact hstep

/-- Advancing any one marginal changes any fixed pure potential gain by at
most `4C/(t+2)`. -/
theorem mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed)
    {changed who : ι} (action : G.form.sig.Strategy who) (t : ℕ)
    (hcoordinate : mixedProfile changed =
      G.empiricalMarginal history changed (t + 1)) :
    |G.mixedPotentialGain potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) who action -
        G.mixedPotentialGain potential mixedProfile who action| ≤
      (1 / (t + 2 : ℝ)) * (4 * C) := by
  by_cases hsame : changed = who
  · subst changed
    have hself :=
      G.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_self
        potential hbound history mixedProfile action t hcoordinate
    have hC : 0 ≤ C := by
      have hprofile := hbound (history 0)
      exact (abs_nonneg _).trans hprofile
    have hstep : 0 ≤ (1 / (t + 2 : ℝ)) := by positivity
    nlinarith
  · exact G.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_of_ne
      potential hbound history mixedProfile action hsame t hcoordinate

end UtilityGame

end GameTheory
