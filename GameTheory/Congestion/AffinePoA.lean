/-
# Affine congestion games and the 5/2 price-of-anarchy bound

Nonnegative affine delays satisfy the Christodoulou--Koutsoupias pairing
inequality.  Aggregating it over resources proves cost smoothness, which the
canonical `UtilityGame.IsSmooth.nash_bound` turns into the pure Nash `5/2`
social-cost bound.

Mathematical provenance: theorem statements and proof structure are recovered
from `reference/GameTheory-v1/GameTheory/Congestion/AffinePoA.lean` at pinned
commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Congestion.Basic
import GameTheory.Core.RobustWelfare

noncomputable section

open scoped BigOperators

open GameTheory.Probability

namespace GameTheory.CongestionGame

universe uι

variable {ι : Type uι} [Fintype ι]

/-- A congestion game is affine when every delay is a nonnegative affine
function of the natural-number load. -/
structure IsAffine (C : CongestionGame ι) (a b : C.Resource → ℝ) : Prop where
  delay_eq : ∀ r n, C.delay r n = a r * n + b r
  a_nonneg : ∀ r, 0 ≤ a r
  b_nonneg : ∀ r, 0 ≤ b r

omit [Fintype ι] in
/-- Affine delays are monotone in the load. -/
theorem IsAffine.delay_mono {C : CongestionGame ι} {a b : C.Resource → ℝ}
    (h : C.IsAffine a b) (r : C.Resource) {m n : ℕ} (hmn : m ≤ n) :
    C.delay r m ≤ C.delay r n := by
  rw [h.delay_eq, h.delay_eq]
  have hcast : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  nlinarith [h.a_nonneg r]

/-- The Christodoulou--Koutsoupias pairing inequality.  The natural-number
loads are essential: the corresponding statement is false for arbitrary real
`y`. -/
theorem ck_inequality (y z : ℕ) :
    (y : ℝ) * (z + 1) ≤ 5 / 3 * (y : ℝ) ^ 2 + 1 / 3 * (z : ℝ) ^ 2 := by
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  rcases Nat.lt_or_ge y 1 with h1 | h1
  · obtain rfl : y = 0 := by omega
    push_cast
    nlinarith
  rcases Nat.lt_or_ge y 2 with h2 | h2
  · obtain rfl : y = 1 := by omega
    rcases Nat.lt_or_ge z 2 with hz2 | hz2
    · have hz : z = 0 ∨ z = 1 := by omega
      rcases hz with rfl | rfl <;> norm_num
    · have hz2' : (2 : ℝ) ≤ z := by exact_mod_cast hz2
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (z : ℝ) - 2)
        (by linarith : (0 : ℝ) ≤ (z : ℝ) - 1)]
  · have h2' : (2 : ℝ) ≤ y := by exact_mod_cast h2
    nlinarith [sq_nonneg (2 * (z : ℝ) - 3 * (y : ℝ))]

/-- Cost-form smoothness of affine congestion games: the total cost of
unilateral deviations from `statusQuo` toward `target` is at most
`(5/3) C(target) + (1/3) C(statusQuo)`. -/
theorem sum_deviation_cost_le [DecidableEq ι] (C : CongestionGame ι)
    {a b : C.Resource → ℝ} (h : C.IsAffine a b)
    (statusQuo target : C.Profile) :
    ∑ i, C.playerCost
        (Profile.update (sig := C.toGameForm.sig) statusQuo i (target i)) i ≤
      5 / 3 * C.socialCost target + 1 / 3 * C.socialCost statusQuo := by
  classical
  have hstep : ∀ i, C.playerCost
      (Profile.update (sig := C.toGameForm.sig) statusQuo i (target i)) i ≤
      ∑ r ∈ C.resources i (target i), C.delay r (C.congestion statusQuo r + 1) := by
    intro i
    rw [playerCost, Profile.update_same]
    refine Finset.sum_le_sum fun r hr => ?_
    rw [C.congestion_update statusQuo i (target i) r, if_pos hr]
    exact h.delay_mono r
      (Nat.add_le_add_right (C.congestionWithout_le_congestion statusQuo i r) 1)
  calc
    ∑ i, C.playerCost
        (Profile.update (sig := C.toGameForm.sig) statusQuo i (target i)) i ≤
        ∑ i, ∑ r ∈ C.resources i (target i),
          C.delay r (C.congestion statusQuo r + 1) :=
      Finset.sum_le_sum fun i _ => hstep i
    _ = ∑ r ∈ C.usedResources target,
          (C.congestion target r : ℝ) * C.delay r (C.congestion statusQuo r + 1) :=
      C.sum_players_sum_resources target _
    _ = ∑ r ∈ C.usedResources statusQuo ∪ C.usedResources target,
          (C.congestion target r : ℝ) * C.delay r (C.congestion statusQuo r + 1) :=
      C.sum_congestion_mul_subset target Finset.subset_union_right _
    _ ≤ 5 / 3 * C.socialCost target + 1 / 3 * C.socialCost statusQuo := by
      rw [C.socialCost_eq_sum_load_delay target,
        C.socialCost_eq_sum_load_delay statusQuo,
        C.sum_congestion_mul_subset target
          (Finset.subset_union_right :
            C.usedResources target ⊆ C.usedResources statusQuo ∪ C.usedResources target),
        C.sum_congestion_mul_subset statusQuo
          (Finset.subset_union_left :
            C.usedResources statusQuo ⊆ C.usedResources statusQuo ∪ C.usedResources target),
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [h.delay_eq, h.delay_eq, h.delay_eq]
      have hck := ck_inequality (C.congestion target r) (C.congestion statusQuo r)
      have ha := h.a_nonneg r
      have hb := h.b_nonneg r
      have hy : (0 : ℝ) ≤ C.congestion target r := Nat.cast_nonneg _
      have hz : (0 : ℝ) ≤ C.congestion statusQuo r := Nat.cast_nonneg _
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hck ha, mul_nonneg hb hy,
        mul_nonneg hb hz]

/-- Social welfare of the induced utility game is negated social cost. -/
theorem socialWelfare_toUtilityGame (C : CongestionGame ι) (profile : C.Profile) :
    C.toUtilityGame.socialWelfare profile = -C.socialCost profile := by
  rw [UtilityGame.socialWelfare, socialCost]
  simp only [toUtilityGame, toGameForm, expectedUtility_pure, utility]
  rw [← Finset.sum_neg_distrib]

/-- Expected social welfare of the induced utility game is negated expected
social cost. -/
theorem expectedSocialWelfare_toUtilityGame (C : CongestionGame ι)
    (law : FinDist C.Profile) :
    C.toUtilityGame.expectedSocialWelfare law = -law.expect C.socialCost := by
  rw [UtilityGame.expectedSocialWelfare]
  calc
    law.expect C.toUtilityGame.socialWelfare =
        law.expect (fun profile => -C.socialCost profile) :=
      FinDist.expect_congr fun profile _ => C.socialWelfare_toUtilityGame profile
    _ =
        law.expect (fun profile => (-1) * C.socialCost profile) := by
      congr 1
      funext profile
      ring
    _ = (-1) * law.expect C.socialCost := by rw [FinDist.expect_smul]
    _ = -law.expect C.socialCost := by ring

/-- Affine congestion games are `(5/3, -1/3)`-smooth in the utility
(negated-cost) convention. -/
theorem isSmooth_of_isAffine [DecidableEq ι] (C : CongestionGame ι)
    {a b : C.Resource → ℝ} (h : C.IsAffine a b) :
    C.toUtilityGame.IsSmooth (5 / 3) (-(1 / 3)) := by
  intro statusQuo target
  rw [socialWelfare_toUtilityGame, socialWelfare_toUtilityGame]
  have hdeviations := C.sum_deviation_cost_le h statusQuo target
  calc
    5 / 3 * -C.socialCost target - -(1 / 3) * -C.socialCost statusQuo =
        -(5 / 3 * C.socialCost target + 1 / 3 * C.socialCost statusQuo) := by ring
    _ ≤ -∑ i, C.playerCost
        (Profile.update (sig := C.toGameForm.sig) statusQuo i (target i)) i := by
      linarith
    _ = ∑ i, expectedUtility C.utility i
        (C.toGameForm.play
          (Profile.update (sig := C.toGameForm.sig) statusQuo i (target i))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => (C.expectedUtility_toGameForm _ i).symm

/-- **The pure price of anarchy of affine congestion games is at most
`5/2`.**  At any pure Nash equilibrium, social cost is bounded by `5/2` times
the social cost of every comparison profile. -/
theorem socialCost_nash_le [DecidableEq ι] (C : CongestionGame ι)
    {a b : C.Resource → ℝ} (h : C.IsAffine a b) {statusQuo : C.Profile}
    (hnash : IsNash C.toGameForm (euPreference C.utility) statusQuo)
    (target : C.Profile) :
    C.socialCost statusQuo ≤ 5 / 2 * C.socialCost target := by
  have hbound := UtilityGame.IsSmooth.nash_bound (C.isSmooth_of_isAffine h) hnash target
  rw [socialWelfare_toUtilityGame, socialWelfare_toUtilityGame] at hbound
  linarith

/-- **Robust price of anarchy of affine congestion games.**  The `5/2` bound
extends from pure Nash equilibria to every coarse correlated equilibrium. -/
theorem correlated_socialCost_le [DecidableEq ι] (C : CongestionGame ι)
    {a b : C.Resource → ℝ} (h : C.IsAffine a b) {law : FinDist C.Profile}
    (hlaw : IsCoarseCorrelatedEq C.toGameForm (euPreference C.utility) law)
    (target : C.Profile) :
    law.expect C.socialCost ≤ 5 / 2 * C.socialCost target := by
  have hbound := UtilityGame.IsSmooth.coarseCorrelated_bound
    (C.isSmooth_of_isAffine h) hlaw target
  rw [C.expectedSocialWelfare_toUtilityGame, C.socialWelfare_toUtilityGame] at hbound
  linarith

end GameTheory.CongestionGame
