/-
# Discounted repeated games

Normalized discounted payoff evaluates the deterministic stage-profile path
from `Basic`. The only infinite object is an ordinary real series; there is no
`FinDist` over infinite histories. The induced strategic form is
`UtilityGame.repeatedForm`, so discounted equilibrium is ordinary `IsNash`.
-/

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import GameTheory.Repeated.Basic

noncomputable section

open scoped BigOperators

namespace GameTheory

universe uι

variable {ι : Type uι}

namespace UtilityGame

/-- Normalized discounted expected payoff of a repeated profile. -/
def discountedPayoff (G : UtilityGame ι) (discount : ℝ)
    (profile : G.RepeatedProfile) (who : ι) : ℝ :=
  (1 - discount) *
    ∑' t : ℕ, discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who

/-- Discounted utility on the existing repeated form. -/
def discountedUtility (G : UtilityGame ι) (discount : ℝ) :
    Utility G.repeatedSignature :=
  fun profile who => G.discountedPayoff discount profile who

/-- Bounded stage payoffs give a summable discounted series whenever the
discount factor lies in `[0, 1)`. -/
theorem summable_discounted_stagePayoff_of_abs_bound
    (G : UtilityGame ι) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    {profile : G.RepeatedProfile} (who : ι)
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) :
    Summable fun t : ℕ =>
      discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who := by
  have hgeom : Summable fun t : ℕ => bound * discount ^ t :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  refine Summable.of_norm_bounded hgeom ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who| =
        discount ^ t *
          |G.stagePayoff (G.repeatedPlay profile t) who| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 t)]
    _ ≤ discount ^ t * bound :=
      mul_le_mul_of_nonneg_left
        (hbound (G.repeatedPlay profile t)) (pow_nonneg hdiscount0 t)
    _ = bound * discount ^ t := by ring

/-- Pointwise dominance of generated stage payoffs implies dominance of
normalized discounted payoffs. -/
theorem discountedPayoff_le_of_forall_stagePayoff_le
    (G : UtilityGame ι) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    {first second : G.RepeatedProfile} (who : ι)
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound)
    (hle : ∀ t : ℕ,
      G.stagePayoff (G.repeatedPlay first t) who ≤
        G.stagePayoff (G.repeatedPlay second t) who) :
    G.discountedPayoff discount first who ≤
      G.discountedPayoff discount second who := by
  have hfirst := G.summable_discounted_stagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who hbound (profile := first)
  have hsecond := G.summable_discounted_stagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who hbound (profile := second)
  have hsum :
      (∑' t : ℕ,
        discount ^ t * G.stagePayoff (G.repeatedPlay first t) who) ≤
      ∑' t : ℕ,
        discount ^ t * G.stagePayoff (G.repeatedPlay second t) who := by
    exact hfirst.tsum_le_tsum
      (fun t => mul_le_mul_of_nonneg_left (hle t)
        (pow_nonneg hdiscount0 t))
      hsecond
  exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hdiscount1.le)

/-- Stationary repetition has the same normalized discounted payoff as its
stage profile. -/
theorem discountedPayoff_stationaryRepeatedProfile
    (G : UtilityGame ι) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : Profile G.form.sig) (who : ι) :
    G.discountedPayoff discount (G.stationaryRepeatedProfile profile) who =
      G.stagePayoff profile who := by
  have hne : 1 - discount ≠ 0 := by linarith
  simp [discountedPayoff, tsum_mul_right,
    tsum_geometric_of_lt_one hdiscount0 hdiscount1, hne]

/-- Stationary repetition of a bounded stage Nash profile is ordinary Nash in
the repeated form under discounted utility. A deviation replaces the player's
whole history-dependent strategy; no repeated-specific equilibrium predicate
is introduced. -/
theorem stationaryRepeatedProfile_isNash_of_isNash_of_bounded
    (G : UtilityGame ι) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig, |G.stagePayoff stage who| ≤ bound) :
    IsNash G.repeatedForm (euPreference (G.discountedUtility discount))
      (G.stationaryRepeatedProfile profile) := by
  rw [isNash_iff]
  intro who deviation
  rw [euPreference_apply]
  simp only [repeatedForm, expectedUtility_pure, discountedUtility]
  obtain ⟨bound, hboundWho⟩ := hbound who
  refine G.discountedPayoff_le_of_forall_stagePayoff_le
    hdiscount0 hdiscount1 who hboundWho ?_
  rw [isNash_iff] at hnash
  intro t
  rw [G.repeatedPlay_update_stationaryRepeatedProfile profile who deviation t]
  rw [G.repeatedPlay_stationaryRepeatedProfile profile t]
  have hstage := hnash who
    (deviation (List.ofFn fun k : Fin t => G.repeatedPlay
      (Profile.update (G.stationaryRepeatedProfile profile) who deviation) k))
  rwa [euPreference_apply] at hstage

end UtilityGame

end GameTheory
