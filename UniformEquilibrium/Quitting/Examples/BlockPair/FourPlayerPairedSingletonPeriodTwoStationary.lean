/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwo
import UniformEquilibrium.Quitting.Stationary.Gain
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Stationary profiles of the paired-singleton period-two completion
-/

noncomputable section

namespace GameTheory
namespace FourPlayerPairedSingleton

open StochasticGame Math.Probability Math.PMFProduct

private def stationaryGainZero (y z t : ℝ) : ℝ :=
  y ^ 2 * z * t ^ 2 - y ^ 2 * z * t +
    y * z ^ 2 * t ^ 2 - y * z ^ 2 * t -
    2 * y * z * t ^ 2 + 3 * y * z * t +
    2 * y * z - 4 * z * t + 2 * t - 1

private def stationaryGainOne (x z t : ℝ) : ℝ :=
  x ^ 2 * z ^ 2 * t - x ^ 2 * z * t +
    x * z ^ 2 * t ^ 2 - 2 * x * z ^ 2 * t -
    x * z * t ^ 2 + 3 * x * z * t +
    2 * x * t - 4 * z * t + 2 * z - 1

private def stationaryGainTwo (x y t : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 * t + x ^ 2 * y * t ^ 2 -
    2 * x ^ 2 * y * t - x * y ^ 2 * t -
    x * y * t ^ 2 + 3 * x * y * t -
    4 * x * y + 2 * x + 2 * y * t - 1

private def stationaryGainThree (x y z : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 * z - x ^ 2 * y * z +
    x * y ^ 2 * z ^ 2 - 2 * x * y ^ 2 * z -
    x * y * z ^ 2 + 3 * x * y * z -
    4 * x * y + 2 * x * z + 2 * y - 1

private lemma endpoint_or_interior {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x = 0 ∨ x = 1 ∨ (0 < x ∧ x < 1) := by
  by_cases h0 : x = 0
  · exact Or.inl h0
  by_cases h1 : x = 1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨lt_of_le_of_ne hx0 (Ne.symm h0),
      lt_of_le_of_ne hx1 h1⟩)

private lemma gain_eq_zero_of_interior {x gain : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1)
    (hcontinue : x * gain ≤ 0) (hquit : 0 ≤ (1 - x) * gain) :
    gain = 0 := by
  nlinarith [mul_pos hx0 (sub_pos.mpr hx1)]

private lemma stationaryGainZero_neg_of_lowest_le_t_le_z
    {y z t : ℝ} (hy : 0 < y) (hyt : y ≤ t) (htz : t ≤ z)
    (hz1 : z ≤ 1) (ht1 : t < 1) :
    stationaryGainZero y z t < 0 := by
  have ht : 0 < t := lt_of_lt_of_le hy hyt
  have hz : 0 < z := lt_of_lt_of_le ht htz
  have ht0 : 0 ≤ t := ht.le
  have ht1' : t ≤ 1 := ht1.le
  have hk : t ^ 2 - t ≤ 0 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1')]
  have hky : (t ^ 2 - t) * t ≤ (t ^ 2 - t) * y :=
    mul_le_mul_of_nonpos_left hyt hk
  have hkz : (t ^ 2 - t) * 1 ≤ (t ^ 2 - t) * z :=
    mul_le_mul_of_nonpos_left hz1 hk
  let P := t ^ 3 + t ^ 2 * y + t ^ 2 * z - 3 * t ^ 2 -
    t * y - t * z + 3 * t + 2
  have hP : 0 < P := by
    have hpositive : 0 < (2 * t + 1) * ((t - 1) ^ 2 + 1) :=
      mul_pos (by nlinarith) (by nlinarith [sq_nonneg (t - 1)])
    dsimp [P]
    nlinarith
  have hfirst :
      stationaryGainZero y z t ≤ stationaryGainZero t z t := by
    have hprod : 0 ≤ z * (t - y) * P :=
      mul_nonneg (mul_nonneg hz.le (sub_nonneg.mpr hyt)) hP.le
    dsimp only [P] at hprod
    dsimp [stationaryGainZero]
    nlinarith
  let R := 2 * t ^ 3 + t ^ 2 * z - 4 * t ^ 2 - t * z +
    3 * t - 2
  have hkzt : (t ^ 2 - t) * z ≤ (t ^ 2 - t) * t :=
    mul_le_mul_of_nonpos_left htz hk
  have htCube : t ^ 3 ≤ t ^ 2 := by
    have := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1')
    nlinarith
  have hR : R < 0 := by
    have hquad : -2 * t ^ 2 + 3 * t - 2 < 0 := by
      nlinarith [sq_nonneg (t - 3 / 4)]
    dsimp [R]
    nlinarith
  have hsecond :
      stationaryGainZero t z t ≤ stationaryGainZero t t t := by
    have hprod : 0 ≤ t * (z - t) * (-R) :=
      mul_nonneg (mul_nonneg ht.le (sub_nonneg.mpr htz)) (neg_nonneg.mpr hR.le)
    dsimp only [R] at hprod
    dsimp [stationaryGainZero]
    nlinarith
  let A := t * (1 - t)
  let B := 2 * t ^ 2 + 1
  have hA0 : 0 ≤ A := mul_nonneg ht0 (sub_nonneg.mpr ht1')
  have hA4 : A ≤ 1 / 4 := by
    dsimp [A]
    nlinarith [sq_nonneg (t - 1 / 2)]
  have htSq : t ^ 2 ≤ 1 := by nlinarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB3 : B ≤ 3 := by dsimp [B]; nlinarith
  have hAB : A * B ≤ 3 / 4 := by
    have hnonneg : 0 ≤ (1 / 4 - A) * B :=
      mul_nonneg (sub_nonneg.mpr hA4) hB0
    nlinarith
  have hdiag : stationaryGainZero t t t < 0 := by
    have hfactor : 0 < 1 - A * B := by nlinarith
    have hmul : (t - 1) * (1 - A * B) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr ht1) hfactor
    dsimp [A, B] at hmul
    dsimp [stationaryGainZero]
    nlinarith
  linarith

private lemma stationaryGainZero_neg_of_lowest_le_z_le_t
    {y z t : ℝ} (hy : 0 < y) (hyz : y ≤ z) (hhalf : 1 / 2 ≤ z)
    (hzt : z ≤ t) (ht1 : t < 1) :
    stationaryGainZero y z t < 0 := by
  have hz : 0 < z := lt_of_lt_of_le (by norm_num) hhalf
  have ht : 0 < t := lt_of_lt_of_le hz hzt
  have hz1 : z ≤ 1 := le_trans hzt ht1.le
  let A := y * z * (y + z - 2)
  let B := y * z * (3 - y - z) - 4 * z + 2
  let C := 2 * y * z - 1
  have hy1 : y < 1 := lt_of_le_of_lt hyz (lt_of_le_of_lt hzt ht1)
  have hsum : y + z - 2 ≤ 0 := by nlinarith
  have hA : A ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hy.le hz.le) hsum
  have hrepr : stationaryGainZero y z t = A * t ^ 2 + B * t + C := by
    dsimp [stationaryGainZero, A, B, C]
    ring
  by_cases hB : B ≤ 0
  · have htSq : z ^ 2 ≤ t ^ 2 := by nlinarith
    have hAt : A * t ^ 2 ≤ A * z ^ 2 :=
      mul_le_mul_of_nonpos_left htSq hA
    have hBt : B * t ≤ B * z :=
      mul_le_mul_of_nonpos_left hzt hB
    let P := y * z ^ 2 - y * z + 2 * z ^ 3 - 4 * z ^ 2 +
      3 * z + 2
    have hk : z * (z - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hz.le (sub_nonpos.mpr hz1)
    have hky : z * (z - 1) * z ≤ z * (z - 1) * y :=
      mul_le_mul_of_nonpos_left hyz hk
    have hzSq : z ^ 2 ≤ z := by
      nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hz1)]
    have hP : 0 ≤ P := by
      dsimp [P]
      nlinarith
    have hcompare :
        A * z ^ 2 + B * z + C ≤ stationaryGainZero z z z := by
      have hprod : 0 ≤ z * (z - y) * P :=
        mul_nonneg (mul_nonneg hz.le (sub_nonneg.mpr hyz)) hP
      dsimp only [P] at hprod
      dsimp [stationaryGainZero, A, B, C]
      nlinarith
    have hdiag := stationaryGainZero_neg_of_lowest_le_t_le_z
      hz (le_refl z) (le_refl z) hz1 (lt_of_le_of_lt hzt ht1)
    rw [hrepr]
    linarith
  · have hB0 : 0 ≤ B := (lt_of_not_ge hB).le
    have hAt : A * t ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA (sq_nonneg t)
    have hBt : B * t ≤ B := by
      nlinarith [mul_nonneg hB0 (sub_nonneg.mpr ht1.le)]
    let E := B + C
    have hcompare : E ≤ -(z - 1) ^ 2 * (2 * z - 1) := by
      have hleft : y - z ≤ 0 := sub_nonpos.mpr hyz
      have hright : y + 2 * z - 5 < 0 := by nlinarith
      have hpairs : 0 ≤ (y - z) * (y + 2 * z - 5) :=
        mul_nonneg_of_nonpos_of_nonpos hleft hright.le
      have hprod : 0 ≤ z * (y - z) * (y + 2 * z - 5) := by
        simpa [mul_assoc] using mul_nonneg hz.le hpairs
      dsimp [E, B, C]
      nlinarith
    by_cases hzhalf : z = 1 / 2
    · subst z
      have hAstrict : A * t ^ 2 < 0 := by
        have hAstr : A < 0 := by
          apply mul_neg_of_pos_of_neg (mul_pos hy (by norm_num))
          nlinarith
        exact mul_neg_of_neg_of_pos hAstr (sq_pos_of_pos ht)
      rw [hrepr]
      dsimp [E] at hcompare
      norm_num at hcompare
      linarith
    · have hzhalf' : 1 / 2 < z := lt_of_le_of_ne hhalf (Ne.symm hzhalf)
      have hbound : -(z - 1) ^ 2 * (2 * z - 1) < 0 := by
        have hzlt1 : z < 1 := lt_of_le_of_lt hzt ht1
        have hsquare : 0 < (z - 1) ^ 2 :=
          sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hzlt1))
        exact mul_neg_of_neg_of_pos (neg_neg_of_pos hsquare) (by nlinarith)
      rw [hrepr]
      dsimp [E] at hcompare
      linarith

private lemma stationaryGainThree_neg_of_lowest_le_half
    {x y z : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hyz : y ≤ z)
    (hzhalf : z ≤ 1 / 2) (hx1 : x < 1) :
    stationaryGainThree x y z < 0 := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  have hyhalf : y ≤ 1 / 2 := le_trans hyz hzhalf
  let A := y * z * (y - 1)
  let B := y ^ 2 * z ^ 2 - 2 * y ^ 2 * z - y * z ^ 2 +
    3 * y * z - 4 * y + 2 * z
  let C := 2 * y - 1
  have hy1 : y < 1 := lt_of_le_of_lt hyx hx1
  have hA : A < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hy hz) (sub_neg.mpr hy1)
  have hC : C ≤ 0 := by dsimp [C]; nlinarith
  have hrepr : stationaryGainThree x y z = A * x ^ 2 + B * x + C := by
    dsimp [stationaryGainThree, A, B, C]
    ring
  by_cases hB : B ≤ 0
  · have hAx : A * x ^ 2 < 0 :=
      mul_neg_of_neg_of_pos hA (sq_pos_of_pos hx)
    have hBx : B * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hB hx.le
    rw [hrepr]
    linarith
  · have hB0 : 0 ≤ B := (lt_of_not_ge hB).le
    have hAx : A * x ^ 2 ≤ 0 := (mul_neg_of_neg_of_pos hA (sq_pos_of_pos hx)).le
    have hBx : B * x ≤ B := by
      nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hx1.le)]
    let P := 2 * y ^ 2 * z - 3 * y ^ 2 - 2 * y * z + 5 * y + 4
    have hySq : y ^ 2 ≤ y / 2 := by
      nlinarith [mul_nonneg hy.le (sub_nonneg.mpr hyhalf)]
    have hyzHalf : y * z ≤ y / 2 := by
      nlinarith [mul_nonneg hy.le (sub_nonneg.mpr hzhalf)]
    have hP : 0 < P := by
      have hterm : 0 ≤ 2 * y ^ 2 * z := by positivity
      dsimp [P]
      nlinarith
    have hcompare : B + C ≤ -3 * y * (y + 1) / 4 := by
      have hprod : 0 ≤ (1 - 2 * z) * P :=
        mul_nonneg (by nlinarith) hP.le
      dsimp only [P] at hprod
      dsimp [B, C]
      nlinarith
    have hright : -3 * y * (y + 1) / 4 < 0 := by
      have hsum : 0 < y + 1 := by linarith
      nlinarith [mul_pos hy hsum]
    rw [hrepr]
    linarith

private lemma no_gain_zeros_of_second_coordinate_minimal
    {x y z t : ℝ}
    (_hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (_hy1 : y < 1)
    (_hz : 0 < z) (hz1 : z < 1) (_ht : 0 < t) (ht1 : t < 1)
    (hyx : y ≤ x) (hyz : y ≤ z) (hyt : y ≤ t)
    (hg0 : stationaryGainZero y z t = 0)
    (hg3 : stationaryGainThree x y z = 0) : False := by
  by_cases htz : t ≤ z
  · have hneg := stationaryGainZero_neg_of_lowest_le_t_le_z
      hy hyt htz hz1.le ht1
    linarith
  · have hzt : z ≤ t := (le_of_not_ge htz)
    by_cases hzhalf : z ≤ 1 / 2
    · have hneg := stationaryGainThree_neg_of_lowest_le_half
        hy hyx hyz hzhalf hx1
      linarith
    · have hhalf : 1 / 2 ≤ z := (le_of_not_ge hzhalf)
      have hneg := stationaryGainZero_neg_of_lowest_le_z_le_t
        hy hyz hhalf hzt ht1
      linarith

private lemma stationaryGainZero_swapBoth (x z t : ℝ) :
    stationaryGainZero x t z = stationaryGainOne x z t := by
  dsimp [stationaryGainZero, stationaryGainOne]
  ring

private lemma stationaryGainThree_swapBoth (x y t : ℝ) :
    stationaryGainThree y x t = stationaryGainTwo x y t := by
  dsimp [stationaryGainThree, stationaryGainTwo]
  ring

private lemma stationaryGainZero_rotate (x y z : ℝ) :
    stationaryGainZero z x y = stationaryGainThree x y z := by
  dsimp [stationaryGainZero, stationaryGainThree]
  ring

private lemma stationaryGainThree_rotate (x z t : ℝ) :
    stationaryGainThree t z x = stationaryGainOne x z t := by
  dsimp [stationaryGainThree, stationaryGainOne]
  ring

private lemma stationaryGainOne_rotate (x y t : ℝ) :
    stationaryGainOne t x y = stationaryGainTwo x y t := by
  dsimp [stationaryGainOne, stationaryGainTwo]
  ring

private lemma stationaryGainTwo_rotate (y z t : ℝ) :
    stationaryGainTwo t z y = stationaryGainZero y z t := by
  dsimp [stationaryGainTwo, stationaryGainZero]
  ring

private lemma stationaryGainZero_exchangePairs (x y t : ℝ) :
    stationaryGainZero t y x = stationaryGainTwo x y t := by
  dsimp [stationaryGainZero, stationaryGainTwo]
  ring

private lemma stationaryGainThree_exchangePairs (y z t : ℝ) :
    stationaryGainThree z t y = stationaryGainZero y z t := by
  dsimp [stationaryGainThree, stationaryGainZero]
  ring

private lemma no_fullyMixed_stationaryGain_zeros
    {x y z t : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1)
    (hz : 0 < z) (hz1 : z < 1) (ht : 0 < t) (ht1 : t < 1)
    (hg0 : stationaryGainZero y z t = 0)
    (hg1 : stationaryGainOne x z t = 0)
    (hg2 : stationaryGainTwo x y t = 0)
    (hg3 : stationaryGainThree x y z = 0) : False := by
  by_cases hxy : x ≤ y
  · by_cases hxz : x ≤ z
    · by_cases hxt : x ≤ t
      · apply no_gain_zeros_of_second_coordinate_minimal
          hy hy1 hx hx1 ht ht1 hz hz1 hxy hxt hxz
        · rw [stationaryGainZero_swapBoth]
          exact hg1
        · rw [stationaryGainThree_swapBoth]
          exact hg2
      · have hty : t ≤ y := le_trans (le_of_not_ge hxt) hxy
        have htz : t ≤ z := le_trans (le_of_not_ge hxt) hxz
        apply no_gain_zeros_of_second_coordinate_minimal
          hz hz1 ht ht1 hy hy1 hx hx1 htz hty (le_of_not_ge hxt)
        · rw [stationaryGainZero_exchangePairs]
          exact hg2
        · rw [stationaryGainThree_exchangePairs]
          exact hg0
    · have hzx : z ≤ x := le_of_not_ge hxz
      by_cases hzt : z ≤ t
      · have hzy : z ≤ y := le_trans hzx hxy
        apply no_gain_zeros_of_second_coordinate_minimal
          ht ht1 hz hz1 hx hx1 hy hy1 hzt hzx hzy
        · rw [stationaryGainZero_rotate]
          exact hg3
        · rw [stationaryGainThree_rotate]
          exact hg1
      · have htx : t ≤ x := le_trans (le_of_not_ge hzt) hzx
        have hty : t ≤ y := le_trans htx hxy
        apply no_gain_zeros_of_second_coordinate_minimal
          hz hz1 ht ht1 hy hy1 hx hx1 (le_of_not_ge hzt) hty htx
        · rw [stationaryGainZero_exchangePairs]
          exact hg2
        · rw [stationaryGainThree_exchangePairs]
          exact hg0
  · have hyx : y ≤ x := le_of_not_ge hxy
    by_cases hyz : y ≤ z
    · by_cases hyt : y ≤ t
      · exact no_gain_zeros_of_second_coordinate_minimal
          hx hx1 hy hy1 hz hz1 ht ht1 hyx hyz hyt hg0 hg3
      · have htx : t ≤ x := le_trans (le_of_not_ge hyt) hyx
        have htz : t ≤ z := le_trans (le_of_not_ge hyt) hyz
        apply no_gain_zeros_of_second_coordinate_minimal
          hz hz1 ht ht1 hy hy1 hx hx1 htz (le_of_not_ge hyt) htx
        · rw [stationaryGainZero_exchangePairs]
          exact hg2
        · rw [stationaryGainThree_exchangePairs]
          exact hg0
    · have hzy : z ≤ y := le_of_not_ge hyz
      by_cases hzt : z ≤ t
      · have hzx : z ≤ x := le_trans hzy hyx
        apply no_gain_zeros_of_second_coordinate_minimal
          ht ht1 hz hz1 hx hx1 hy hy1 hzt hzx hzy
        · rw [stationaryGainZero_rotate]
          exact hg3
        · rw [stationaryGainThree_rotate]
          exact hg1
      · have hty : t ≤ y := le_trans (le_of_not_ge hzt) hzy
        have htx : t ≤ x := le_trans hty hyx
        apply no_gain_zeros_of_second_coordinate_minimal
          hz hz1 ht ht1 hy hy1 hx hx1 (le_of_not_ge hzt) hty htx
        · rw [stationaryGainZero_exchangePairs]
          exact hg2
        · rw [stationaryGainThree_exchangePairs]
          exact hg0
private lemma no_stationaryGain_zeros_of_x_one_interior
    {y z t : ℝ}
    (hy : 0 < y) (hy1 : y < 1)
    (hz : 0 < z) (hz1 : z < 1)
    (ht : 0 < t) (ht1 : t < 1)
    (hg1 : stationaryGainOne 1 z t = 0)
    (hg2 : stationaryGainTwo 1 y t = 0)
    (hg3 : stationaryGainThree 1 y z = 0) : False := by
  have htHalf : t < 1 / 2 := by
    by_contra hnot
    have hhalf : 1 / 2 ≤ t := le_of_not_gt hnot
    have hfirst : 0 ≤ (1 - z) * (2 * t - 1) :=
      mul_nonneg (sub_nonneg.mpr hz1.le) (by nlinarith)
    have hsecond : 0 < z * (1 - t) :=
      mul_pos hz (sub_pos.mpr ht1)
    have hthird : 0 ≤ t * (1 - t) * z * (1 - z) := by positivity
    have hid : stationaryGainOne 1 z t =
        (1 - z) * (2 * t - 1) + z * (1 - t) +
          t * (1 - t) * z * (1 - z) := by
      dsimp [stationaryGainOne]
      ring
    rw [hid] at hg1
    nlinarith
  have hyt : y < t := by
    by_contra hnot
    have hty : t ≤ y := le_of_not_gt hnot
    have hsame : stationaryGainThree 1 t z < 0 := by
      have hprod : 0 < 4 * t * (1 - z) := by positivity
      have hid : stationaryGainThree 1 t z =
          stationaryGainOne 1 z t - 4 * t * (1 - z) := by
        dsimp [stationaryGainThree, stationaryGainOne]
        ring
      rw [hid, hg1]
      nlinarith
    let B := (t + y) * z * (z - 1) - (z - 1) ^ 2 - 1
    have hB : B < 0 := by
      have hprod : (t + y) * (z * (z - 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonneg_of_nonpos hz.le (sub_nonpos.mpr hz1.le))
      dsimp [B]
      nlinarith [sq_nonneg (z - 1)]
    have hfactor : (y - t) * B ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hty) hB.le
    have hid : stationaryGainThree 1 y z -
        stationaryGainThree 1 t z = (y - t) * B := by
      dsimp [stationaryGainThree, B]
      ring
    nlinarith
  have htThird : 1 / 3 < t := by
    by_contra hnot
    have htThird' : t ≤ 1 / 3 := le_of_not_gt hnot
    have hcoef : 3 * t - 4 < 0 := by nlinarith
    have hdiff : 0 < (y - t) * (3 * t - 4) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hyt) hcoef
    have hbase : 0 ≤ (1 - t) * (1 - 3 * t) :=
      mul_nonneg (sub_nonneg.mpr ht1.le) (by nlinarith)
    dsimp [stationaryGainTwo] at hg2
    nlinarith
  have hyThird : 1 / 3 < y := by
    by_contra hnot
    have hyThird' : y ≤ 1 / 3 := le_of_not_gt hnot
    have hcoef : 3 * t - 4 < 0 := by nlinarith
    have hdiff : 0 ≤ (y - 1 / 3) * (3 * t - 4) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hyThird') hcoef.le
    dsimp [stationaryGainTwo] at hg2
    nlinarith
  have hyTwoFifths : y < 2 / 5 := by
    by_contra hnot
    have hyTwoFifths' : 2 / 5 ≤ y := le_of_not_gt hnot
    have hcoef : 3 * t - 4 < 0 := by nlinarith
    have hdiff : (y - 2 / 5) * (3 * t - 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hyTwoFifths') hcoef.le
    dsimp [stationaryGainTwo] at hg2
    nlinarith
  let q := 4 * y ^ 2 - 23 * y + 7
  have hq : q < 0 := by
    have hlinear : 4 * y - 65 / 3 < 0 := by nlinarith
    have hprod : (y - 1 / 3) * (4 * y - 65 / 3) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hyThird) hlinear
    dsimp [q]
    nlinarith
  have hGainOneAtY : 0 < stationaryGainOne 1 y t := by
    have hright : 0 < (y - 1) * q :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hy1) hq
    have hid : 9 * y * stationaryGainOne 1 y t =
        (y - 1) * q + stationaryGainTwo 1 y t *
          (3 * t * y ^ 2 - 3 * t * y + y ^ 2 - 11 * y + 7) := by
      dsimp [stationaryGainOne, stationaryGainTwo, q]
      ring
    rw [hg2, zero_mul, add_zero] at hid
    have hmul : 0 < 9 * y * stationaryGainOne 1 y t := by
      rw [hid]
      exact hright
    nlinarith
  have hzy : z < y := by
    by_contra hnot
    have hyz : y ≤ z := le_of_not_gt hnot
    have hAtOne : 0 < stationaryGainOne 1 1 t := by
      dsimp [stationaryGainOne]
      nlinarith
    have hfirst : 0 < (1 - z) * stationaryGainOne 1 y t :=
      mul_pos (sub_pos.mpr hz1) hGainOneAtY
    have hsecond : 0 ≤ (z - y) * stationaryGainOne 1 1 t :=
      mul_nonneg (sub_nonneg.mpr hyz) hAtOne.le
    have hthird :
        0 ≤ t * (1 - t) * (z - y) * (1 - z) * (1 - y) := by
      positivity
    have hid : (1 - y) * stationaryGainOne 1 z t =
        (1 - z) * stationaryGainOne 1 y t +
          (z - y) * stationaryGainOne 1 1 t +
            t * (1 - t) * (z - y) * (1 - z) * (1 - y) := by
      dsimp [stationaryGainOne]
      ring
    rw [hg1] at hid
    nlinarith
  have hneg := stationaryGainZero_neg_of_lowest_le_t_le_z
    hz hzy.le hy1.le (le_refl 1) hy1
  rw [stationaryGainZero_rotate] at hneg
  linarith

private def stationaryGainComplementary
    (x y z t : ℝ) : Prop :=
  (x * stationaryGainZero y z t ≤ 0 ∧
      0 ≤ (1 - x) * stationaryGainZero y z t) ∧
    (y * stationaryGainOne x z t ≤ 0 ∧
      0 ≤ (1 - y) * stationaryGainOne x z t) ∧
    (z * stationaryGainTwo x y t ≤ 0 ∧
      0 ≤ (1 - z) * stationaryGainTwo x y t) ∧
    (t * stationaryGainThree x y z ≤ 0 ∧
      0 ≤ (1 - t) * stationaryGainThree x y z)

private lemma stationaryGainComplementary_swapBoth
    {x y z t : ℝ} (h : stationaryGainComplementary x y z t) :
    stationaryGainComplementary y x t z := by
  rcases h with ⟨h0, h1, h2, h3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [stationaryGainZero_swapBoth] using h1
  · simpa only [stationaryGainZero_swapBoth] using h0
  · simpa only [stationaryGainThree_swapBoth] using h3
  · simpa only [stationaryGainThree_swapBoth] using h2

private lemma stationaryGainComplementary_rotate
    {x y z t : ℝ} (h : stationaryGainComplementary x y z t) :
    stationaryGainComplementary t z x y := by
  rcases h with ⟨h0, h1, h2, h3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [stationaryGainZero_rotate] using h3
  · simpa only [stationaryGainOne_rotate] using h2
  · simpa only [stationaryGainTwo_rotate] using h0
  · simpa only [stationaryGainThree_rotate] using h1

private lemma no_stationaryGainComplementary_of_x_zero
    (y z t : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ¬ stationaryGainComplementary 0 y z t := by
  rintro ⟨hg0, hg1, hg2, hg3⟩
  rcases endpoint_or_interior hy0 hy1 with (rfl | rfl | hy) <;>
    rcases endpoint_or_interior hz0 hz1 with (rfl | rfl | hz) <;>
      rcases endpoint_or_interior ht0 ht1 with (rfl | rfl | ht)
  all_goals (norm_num [stationaryGainComplementary, stationaryGainZero,
    stationaryGainOne, stationaryGainTwo, stationaryGainThree] at * <;> nlinarith)

private lemma no_stationaryGainComplementary_of_x_one
    (y z t : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (habsorbs : y * z * t < 1) :
    ¬ stationaryGainComplementary 1 y z t := by
  rintro ⟨hg0, hg1, hg2, hg3⟩
  rcases endpoint_or_interior hy0 hy1 with (rfl | rfl | hy) <;>
    rcases endpoint_or_interior hz0 hz1 with (rfl | rfl | hz) <;>
      rcases endpoint_or_interior ht0 ht1 with (rfl | rfl | ht)
  all_goals
    first
    | exact no_stationaryGain_zeros_of_x_one_interior
        hy.1 hy.2 hz.1 hz.2 ht.1 ht.2
        (gain_eq_zero_of_interior hy.1 hy.2 hg1.1 hg1.2)
        (gain_eq_zero_of_interior hz.1 hz.2 hg2.1 hg2.2)
        (gain_eq_zero_of_interior ht.1 ht.2 hg3.1 hg3.2)
    | skip
  all_goals (norm_num [stationaryGainComplementary, stationaryGainZero,
    stationaryGainOne, stationaryGainTwo, stationaryGainThree] at * <;> nlinarith)

private lemma no_stationaryGainComplementary_of_x_interior
    (x y z t : ℝ) (hx : 0 < x ∧ x < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ¬ stationaryGainComplementary x y z t := by
  intro hcomp
  rcases endpoint_or_interior hy0 hy1 with (rfl | rfl | hy)
  · exact no_stationaryGainComplementary_of_x_zero
      x t z hx.1.le hx.2.le ht0 ht1 hz0 hz1
      (stationaryGainComplementary_swapBoth hcomp)
  · apply no_stationaryGainComplementary_of_x_one
      x t z hx.1.le hx.2.le ht0 ht1 hz0 hz1
    · have htz : t * z ≤ 1 := by
        nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hz1)]
      nlinarith [mul_le_mul_of_nonneg_right htz hx.1.le]
    · exact stationaryGainComplementary_swapBoth hcomp
  · rcases endpoint_or_interior hz0 hz1 with (rfl | rfl | hz)
    · exact no_stationaryGainComplementary_of_x_zero
        t y x ht0 ht1 hy.1.le hy.2.le hx.1.le hx.2.le
        (stationaryGainComplementary_swapBoth
          (stationaryGainComplementary_rotate hcomp))
    · apply no_stationaryGainComplementary_of_x_one
        t y x ht0 ht1 hy.1.le hy.2.le hx.1.le hx.2.le
      · nlinarith [mul_nonneg ht0 (mul_nonneg hy.1.le hx.1.le),
          mul_le_mul_of_nonneg_right
            (show t * y ≤ 1 by
              nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hy.2.le)]) hx.1.le]
      · exact stationaryGainComplementary_swapBoth
          (stationaryGainComplementary_rotate hcomp)
    · rcases endpoint_or_interior ht0 ht1 with (rfl | rfl | ht)
      · exact no_stationaryGainComplementary_of_x_zero
          z x y hz.1.le hz.2.le hx.1.le hx.2.le hy.1.le hy.2.le
          (stationaryGainComplementary_rotate hcomp)
      · apply no_stationaryGainComplementary_of_x_one
          z x y hz.1.le hz.2.le hx.1.le hx.2.le hy.1.le hy.2.le
        · have hzy : z * y ≤ 1 := by
            nlinarith [mul_nonneg hz.1.le (sub_nonneg.mpr hy.2.le)]
          nlinarith [mul_le_mul_of_nonneg_right hzy hx.1.le]
        · exact stationaryGainComplementary_rotate hcomp
      · rcases hcomp with ⟨hg0, hg1, hg2, hg3⟩
        exact no_fullyMixed_stationaryGain_zeros
          hx.1 hx.2 hy.1 hy.2 hz.1 hz.2 ht.1 ht.2
          (gain_eq_zero_of_interior hx.1 hx.2 hg0.1 hg0.2)
          (gain_eq_zero_of_interior hy.1 hy.2 hg1.1 hg1.2)
          (gain_eq_zero_of_interior hz.1 hz.2 hg2.1 hg2.2)
          (gain_eq_zero_of_interior ht.1 ht.2 hg3.1 hg3.2)

private theorem no_stationaryGainComplementarity_algebra
    (x y z t : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (habsorbs : x * y * z * t < 1) :
    ¬ stationaryGainComplementary x y z t := by
  rcases endpoint_or_interior hx0 hx1 with (rfl | rfl | hx)
  · exact no_stationaryGainComplementary_of_x_zero
      y z t hy0 hy1 hz0 hz1 ht0 ht1
  · apply no_stationaryGainComplementary_of_x_one
      y z t hy0 hy1 hz0 hz1 ht0 ht1
    simpa using habsorbs
  · exact no_stationaryGainComplementary_of_x_interior
      x y z t hx hy0 hy1 hz0 hz1 ht0 ht1

private theorem periodTwo_stationaryGain_zero_raw
    (root : Player → PMF Bool) :
    quittingStationaryGain periodTwoReward root 0 =
      (1 - (root 1 false).toReal *
          ((root 2 false).toReal * (root 3 false).toReal)) *
        ((root 1 true).toReal *
            ((root 2 true).toReal *
                (-(root 3 true).toReal + (root 3 false).toReal) +
              (root 2 false).toReal * (root 3 false).toReal) +
          (root 1 false).toReal *
            ((root 2 true).toReal * (root 3 false).toReal +
              (root 2 false).toReal *
                ((root 3 true).toReal + (root 3 false).toReal))) -
        ((root 1 true).toReal *
            ((root 2 false).toReal *
              ((root 3 true).toReal + (root 3 false).toReal * 4)) +
          (root 1 false).toReal *
            ((root 2 true).toReal * (root 3 true).toReal)) := by
  classical
  unfold quittingStationaryGain quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
    quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    expect_pmfPi_fin4_bool, expect_pmfPi_fin4_bool]
  simp [Fin.prod_univ_succ, quittingRootPayoff, quittingQuitters,
    periodTwoReward, expect_eq_sum]

private theorem periodTwo_stationaryGain_zero
    (root : Player → PMF Bool) :
    quittingStationaryGain periodTwoReward root 0 =
      stationaryGainZero (root 1 false).toReal (root 2 false).toReal
        (root 3 false).toReal := by
  classical
  have h1 := quittingRoot_continueProbability_add_quitProbability root 1
  have h2 := quittingRoot_continueProbability_add_quitProbability root 2
  have h3 := quittingRoot_continueProbability_add_quitProbability root 3
  have h1q : (root 1 true).toReal = 1 - (root 1 false).toReal := by linarith
  have h2q : (root 2 true).toReal = 1 - (root 2 false).toReal := by linarith
  have h3q : (root 3 true).toReal = 1 - (root 3 false).toReal := by linarith
  rw [periodTwo_stationaryGain_zero_raw, h1q, h2q, h3q]
  dsimp [stationaryGainZero]
  ring

private theorem periodTwo_stationaryGain_one_raw
    (root : Player → PMF Bool) :
    quittingStationaryGain periodTwoReward root 1 =
      (1 - (root 0 false).toReal *
          ((root 2 false).toReal * (root 3 false).toReal)) *
        ((root 0 true).toReal *
            (-((root 2 true).toReal * (root 3 true).toReal) +
              (root 2 false).toReal *
                ((root 3 true).toReal + (root 3 false).toReal)) +
          (root 0 false).toReal *
            ((root 2 true).toReal * (root 3 false).toReal +
              (root 2 false).toReal *
                ((root 3 true).toReal + (root 3 false).toReal))) -
        ((root 0 true).toReal *
            ((root 2 true).toReal * (root 3 false).toReal +
              (root 2 false).toReal * ((root 3 false).toReal * 4)) +
          (root 0 false).toReal *
            ((root 2 true).toReal * (root 3 true).toReal)) := by
  classical
  unfold quittingStationaryGain quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
    quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    expect_pmfPi_fin4_bool, expect_pmfPi_fin4_bool]
  simp [Fin.prod_univ_succ, quittingRootPayoff, quittingQuitters,
    periodTwoReward, expect_eq_sum]

private theorem periodTwo_stationaryGain_one
    (root : Player → PMF Bool) :
    quittingStationaryGain periodTwoReward root 1 =
      stationaryGainOne (root 0 false).toReal (root 2 false).toReal
        (root 3 false).toReal := by
  classical
  have h0 := quittingRoot_continueProbability_add_quitProbability root 0
  have h2 := quittingRoot_continueProbability_add_quitProbability root 2
  have h3 := quittingRoot_continueProbability_add_quitProbability root 3
  have h0q : (root 0 true).toReal = 1 - (root 0 false).toReal := by linarith
  have h2q : (root 2 true).toReal = 1 - (root 2 false).toReal := by linarith
  have h3q : (root 3 true).toReal = 1 - (root 3 false).toReal := by linarith
  rw [periodTwo_stationaryGain_one_raw, h0q, h2q, h3q]
  dsimp [stationaryGainOne]
  ring

private theorem periodTwo_stationaryGain_two_raw
    (root : Player → PMF Bool) :
    quittingStationaryGain periodTwoReward root 2 =
      (1 - (root 0 false).toReal *
          ((root 1 false).toReal * (root 3 false).toReal)) *
        ((root 0 true).toReal *
            (-((root 1 true).toReal * (root 3 true).toReal) +
              (root 1 false).toReal * (root 3 false).toReal) +
          (root 0 false).toReal *
            ((root 1 true).toReal *
                ((root 3 true).toReal + (root 3 false).toReal) +
              (root 1 false).toReal *
                ((root 3 true).toReal + (root 3 false).toReal))) -
        ((root 0 true).toReal *
            ((root 1 true).toReal * (root 3 false).toReal +
              (root 1 false).toReal * (root 3 true).toReal) +
          (root 0 false).toReal *
            ((root 1 false).toReal * ((root 3 true).toReal * 4))) := by
  classical
  unfold quittingStationaryGain quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
    quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    expect_pmfPi_fin4_bool, expect_pmfPi_fin4_bool]
  simp [Fin.prod_univ_succ, quittingRootPayoff, quittingQuitters,
    periodTwoReward, expect_eq_sum]

private theorem periodTwo_stationaryGain_two
    (root : Player → PMF Bool) :
    quittingStationaryGain periodTwoReward root 2 =
      stationaryGainTwo (root 0 false).toReal (root 1 false).toReal
        (root 3 false).toReal := by
  classical
  have h0 := quittingRoot_continueProbability_add_quitProbability root 0
  have h1 := quittingRoot_continueProbability_add_quitProbability root 1
  have h3 := quittingRoot_continueProbability_add_quitProbability root 3
  have h0q : (root 0 true).toReal = 1 - (root 0 false).toReal := by linarith
  have h1q : (root 1 true).toReal = 1 - (root 1 false).toReal := by linarith
  have h3q : (root 3 true).toReal = 1 - (root 3 false).toReal := by linarith
  rw [periodTwo_stationaryGain_two_raw, h0q, h1q, h3q]
  dsimp [stationaryGainTwo]
  ring

private theorem periodTwo_stationaryGain_three_raw
    (root : Player → PMF Bool) :
    quittingStationaryGain periodTwoReward root 3 =
      (1 - (root 0 false).toReal *
          ((root 1 false).toReal * (root 2 false).toReal)) *
        ((root 0 true).toReal *
            (-((root 1 true).toReal * (root 2 true).toReal) +
              (root 1 false).toReal *
                ((root 2 true).toReal + (root 2 false).toReal)) +
          (root 0 false).toReal *
            ((root 1 true).toReal * (root 2 false).toReal +
              (root 1 false).toReal *
                ((root 2 true).toReal + (root 2 false).toReal))) -
        ((root 0 true).toReal *
            ((root 1 true).toReal * (root 2 false).toReal) +
          (root 0 false).toReal *
            ((root 1 true).toReal * (root 2 true).toReal +
              (root 1 false).toReal * ((root 2 true).toReal * 4))) := by
  classical
  unfold quittingStationaryGain quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
    quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    expect_pmfPi_fin4_bool, expect_pmfPi_fin4_bool]
  simp [Fin.prod_univ_succ, quittingRootPayoff, quittingQuitters,
    periodTwoReward, expect_eq_sum]

private theorem periodTwo_stationaryGain_three
    (root : Player → PMF Bool) :
    quittingStationaryGain periodTwoReward root 3 =
      stationaryGainThree (root 0 false).toReal (root 1 false).toReal
        (root 2 false).toReal := by
  classical
  have h0 := quittingRoot_continueProbability_add_quitProbability root 0
  have h1 := quittingRoot_continueProbability_add_quitProbability root 1
  have h2 := quittingRoot_continueProbability_add_quitProbability root 2
  have h0q : (root 0 true).toReal = 1 - (root 0 false).toReal := by linarith
  have h1q : (root 1 true).toReal = 1 - (root 1 false).toReal := by linarith
  have h2q : (root 2 true).toReal = 1 - (root 2 false).toReal := by linarith
  rw [periodTwo_stationaryGain_three_raw, h0q, h1q, h2q]
  dsimp [stationaryGainThree]
  ring

theorem periodTwo_not_stationaryGainComplementary_of_absorbs
    (root : Player → PMF Bool)
    (habsorbs : quittingStationaryContinueMass root < 1) :
    ¬ IsQuittingStationaryGainComplementary periodTwoReward root := by
  intro hcomp
  let x := (root 0 false).toReal
  let y := (root 1 false).toReal
  let z := (root 2 false).toReal
  let t := (root 3 false).toReal
  have hnonneg (who : Player) : 0 ≤ (root who false).toReal :=
    ENNReal.toReal_nonneg
  have hleOne (who : Player) : (root who false).toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (root who) false)
  have hproduct : x * y * z * t < 1 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability] at habsorbs
    simpa [x, y, z, t, Fin.prod_univ_succ, mul_assoc] using habsorbs
  apply no_stationaryGainComplementarity_algebra x y z t
      (hnonneg 0) (hleOne 0) (hnonneg 1) (hleOne 1)
      (hnonneg 2) (hleOne 2) (hnonneg 3) (hleOne 3) hproduct
  unfold stationaryGainComplementary
  have h0 := hcomp 0
  have h1 := hcomp 1
  have h2 := hcomp 2
  have h3 := hcomp 3
  have hsum0 := quittingRoot_continueProbability_add_quitProbability root 0
  have hsum1 := quittingRoot_continueProbability_add_quitProbability root 1
  have hsum2 := quittingRoot_continueProbability_add_quitProbability root 2
  have hsum3 := quittingRoot_continueProbability_add_quitProbability root 3
  rw [periodTwo_stationaryGain_zero] at h0
  rw [periodTwo_stationaryGain_one] at h1
  rw [periodTwo_stationaryGain_two] at h2
  rw [periodTwo_stationaryGain_three] at h3
  dsimp [x, y, z, t] at *
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- No absorbing stationary product profile is an exact terminal Nash
profile, even against the full class of behavioral deviations. -/
theorem periodTwo_no_absorbing_stationary_exactTerminalNash
    (root : Player → PMF Bool)
    (habsorbs : quittingStationaryContinueMass root < 1) :
    ¬ (quittingGame periodTwoReward).IsεAsymptoticNash
      (quittingTerminalPayoff periodTwoReward) 0
      (quittingStationaryProfile periodTwoReward root) := by
  intro hnash
  have hroot := isεQuittingRootNash_of_isεAsymptoticNash_stationary
    periodTwoReward root 0 hnash
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      periodTwoReward
      (fun player => quittingTerminalPayoff periodTwoReward
        (quittingStationaryProfile periodTwoReward root) player)
      root).mpr hroot
  have habsorption : 0 < quittingRootAbsorptionMass root := by
    change 0 < 1 - quittingStationaryContinueMass root
    linarith
  have hcomp :=
    (isQuittingStationaryGainComplementary_iff_endpointNash
      periodTwoReward root habsorption).mpr hendpoint
  exact periodTwo_not_stationaryGainComplementary_of_absorbs root habsorbs hcomp

/-- No stationary product profile is an exact terminal equilibrium of the
period-two completion.  The zero-absorption all-Continue boundary is excluded
by its profitable singleton Quit deviation; the absorbing regime is excluded
by stationary-gain complementarity. -/
theorem periodTwo_no_stationary_exactTerminalNash
    (root : Player → PMF Bool) :
    ¬ (quittingGame periodTwoReward).IsεAsymptoticNash
      (quittingTerminalPayoff periodTwoReward) 0
      (quittingStationaryProfile periodTwoReward root) := by
  intro hnash
  by_cases habsorbs : quittingStationaryContinueMass root < 1
  · exact periodTwo_no_absorbing_stationary_exactTerminalNash
      root habsorbs hnash
  · have hmassLe := quittingStationaryContinueMass_le_one root
    have hmass : quittingStationaryContinueMass root = 1 :=
      le_antisymm hmassLe (not_lt.mp habsorbs)
    have hroot : root = quittingAllContinueRoot := by
      funext who
      simpa [quittingAllContinueRoot] using
        (eq_pure_false_of_quittingStationaryContinueMass_eq_one hmass who)
    have hprofile : quittingStationaryProfile periodTwoReward root =
        quittingAlwaysContinueProfile periodTwoReward := by
      rw [hroot]
      rfl
    rw [hprofile] at hnash
    have hcriterion :=
      (isεAsymptoticNash_quittingAlwaysContinue_iff
        periodTwoReward le_rfl).mp hnash 0
    simp [periodTwoReward, quittingSingletonTerminal] at hcriterion
    norm_num at hcriterion

end FourPlayerPairedSingleton
end GameTheory
