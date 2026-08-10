/-
# Mixed extensions of exact potential games

The multilinear extension of a pure-profile potential is simply its
expectation under the canonical independent `FinDist` profile law.  Exact
potential differences survive both pure and randomized unilateral changes.
No topology or outcome-carrier finiteness is involved.
-/

import GameTheory.Core.Mixed
import GameTheory.Core.Potential

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {G : UtilityGame.{uι, us, uo} ι}
variable {potential : Profile G.form.sig → ℝ}

namespace GameForm

/-- The multilinear extension of a pure-profile potential. -/
def mixedPotential (G : GameForm ι) (potential : Profile G.sig → ℝ)
    (mixedProfile : Profile G.sig.mixed) : ℝ :=
  (FinDist.pi mixedProfile).expect potential

/-- The mixed potential agrees with the original potential on the canonical
pure embedding. -/
@[simp]
theorem mixedPotential_purify (G : GameForm ι)
    (potential : Profile G.sig → ℝ) (profile : Profile G.sig) :
    G.mixedPotential potential (G.purify profile) = potential profile := by
  unfold mixedPotential
  have hpure : G.purify profile =
      fun i => FinDist.pure (profile i) := rfl
  rw [hpure, FinDist.pi_pure, FinDist.expect_pure]

/-- The mixed potential is affine in every player's own mixed strategy. -/
theorem mixedPotential_update (G : GameForm ι)
    (potential : Profile G.sig → ℝ)
    (mixedProfile : Profile G.sig.mixed) (who : ι)
    (replacement : FinDist (G.sig.Strategy who)) :
    G.mixedPotential potential (Profile.update mixedProfile who replacement) =
      replacement.expect fun action =>
        G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action)) := by
  unfold mixedPotential
  rw [GameForm.pi_update_mixed, FinDist.expect_bind]

end GameForm

namespace UtilityGame

/-- A pure unilateral change has the same expected-utility and mixed-potential
difference as its pointwise pure changes. -/
theorem IsExactPotential.mixed_pure_diff
    (hpotential : IsExactPotential G.form G.utility potential)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (FinDist.pure action))) -
      expectedUtility G.utility who (G.form.mixed.play mixedProfile) =
    G.form.mixedPotential potential
        (Profile.update mixedProfile who (FinDist.pure action)) -
      G.form.mixedPotential potential mixedProfile := by
  have hproduct := GameForm.pi_map_recommendation G.form.sig mixedProfile who
    (fun _ => action)
  rw [FinDist.map_const] at hproduct
  simp only [expectedUtility_bind, GameForm.mixedPotential]
  rw [← hproduct, FinDist.expect_map, FinDist.expect_map,
    ← FinDist.expect_sub, ← FinDist.expect_sub]
  exact FinDist.expect_congr fun profile _ => hpotential who profile action

/-- Arbitrary unilateral randomization has the same expected-utility and
mixed-potential difference. -/
theorem IsExactPotential.mixed_update_diff
    (hpotential : IsExactPotential G.form G.utility potential)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (replacement : FinDist (G.form.sig.Strategy who)) :
    expectedUtility G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who replacement)) -
      expectedUtility G.utility who (G.form.mixed.play mixedProfile) =
    G.form.mixedPotential potential (Profile.update mixedProfile who replacement) -
      G.form.mixedPotential potential mixedProfile := by
  rw [GameForm.mixed_play_update, expectedUtility_bind,
    G.form.mixedPotential_update]
  calc
    replacement.expect (fun action =>
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who (FinDist.pure action)))) -
        expectedUtility G.utility who (G.form.mixed.play mixedProfile) =
      replacement.expect (fun action =>
        expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who (FinDist.pure action))) -
          expectedUtility G.utility who (G.form.mixed.play mixedProfile)) := by
      rw [FinDist.expect_sub, FinDist.expect_const]
    _ = replacement.expect (fun action =>
        G.form.mixedPotential potential
            (Profile.update mixedProfile who (FinDist.pure action)) -
          G.form.mixedPotential potential mixedProfile) :=
      FinDist.expect_congr fun action _ =>
        IsExactPotential.mixed_pure_diff
          (G := G) (potential := potential) hpotential mixedProfile who action
    _ = replacement.expect (fun action =>
          G.form.mixedPotential potential
            (Profile.update mixedProfile who (FinDist.pure action))) -
        G.form.mixedPotential potential mixedProfile := by
      rw [FinDist.expect_sub, FinDist.expect_const]

/-- The mixed extension of an exact-potential game is again exact-potential,
with the expected extension of the original potential. -/
theorem IsExactPotential.mixed
    (hpotential : IsExactPotential G.form G.utility potential) :
    IsExactPotential G.form.mixed G.utility (G.form.mixedPotential potential) :=
  fun who mixedProfile replacement =>
    IsExactPotential.mixed_update_diff
      (G := G) (potential := potential) hpotential mixedProfile who replacement

end UtilityGame

end GameTheory
