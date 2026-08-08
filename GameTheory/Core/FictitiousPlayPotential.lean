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

end UtilityGame

end GameTheory
