import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Separated jitter samples near interior grid boundaries

Clipping an arithmetic progression to the unit interval cannot produce a sample near an interior
uniform grid boundary unless that sample was already in the interval. If sample spacing exceeds
twice the bad-band radius and the total span is shorter than one grid step, at most one sample
can lie in a bad band for a coordinate.
-/

namespace GameTheory.Math

/-- Equally spaced samples clipped to the closed unit interval. -/
def gridJitterSample (q α center : ℚ) (t : ℕ) : ℚ :=
  max 0 (min 1 (q + ((t : ℚ) - center) * α))

private theorem unclipped_of_near_grid {u β : ℚ} {N j : ℕ}
    (hN : 0 < N) (hj : 0 < j) (hjN : j < N) (hβ : β < 1 / (N : ℚ))
    (hnear : |max 0 (min 1 u) - (j : ℚ) / N| ≤ β) : max 0 (min 1 u) = u := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hjq : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have hjNq : (j : ℚ) + 1 ≤ N := by exact_mod_cast hjN
  have hlo : 1 / (N : ℚ) ≤ (j : ℚ) / N :=
    div_le_div_of_nonneg_right hjq hNq.le
  have hhi : (j : ℚ) / N ≤ 1 - 1 / N := by
    apply (div_le_iff₀ hNq).mpr
    have hc : (1 / (N : ℚ)) * N = 1 := one_div_mul_cancel (ne_of_gt hNq)
    nlinarith
  rw [abs_le] at hnear
  have hp : 0 < max 0 (min 1 u) := by linarith [hnear.1]
  have hp1 : max 0 (min 1 u) < 1 := by linarith [hnear.2]
  have hu : 0 < u := by
    by_contra h
    have hu : u ≤ 0 := le_of_not_gt h
    have he : max 0 (min 1 u) = 0 := max_eq_left ((min_le_right _ _).trans hu)
    rw [he] at hp
    linarith
  have hu1 : u < 1 := by
    by_contra h
    have hu : 1 ≤ u := le_of_not_gt h
    have he : max 0 (min 1 u) = 1 := by rw [min_eq_left hu]; norm_num
    rw [he] at hp1
    linarith
  rw [min_eq_right hu1.le, max_eq_right hu.le]

private theorem grid_fraction_separation {N j k : ℕ} (hN : 0 < N) (hne : j ≠ k) :
    1 / (N : ℚ) ≤ |(j : ℚ) / N - (k : ℚ) / N| := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  rw [← sub_div, abs_div, abs_of_pos hNq]
  apply (div_le_div_iff_of_pos_right hNq).mpr
  rcases lt_or_gt_of_ne hne with h | h
  · have hq : (j : ℚ) + 1 ≤ k := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith : (j : ℚ) - k ≤ 0)]
    linarith
  · have hq : (k : ℚ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ j - k)]
    linarith

/-- At most one clipped sample is close to any interior grid boundary. -/
theorem gridJitter_bad_unique {m N : ℕ} (q α center β : ℚ)
    (hm : 0 < m) (hN : 0 < N) (hβ : 0 ≤ β) (hα : 2 * β < α)
    (hspan : ((m - 1 : ℕ) : ℚ) * α + 2 * β < 1 / (N : ℚ))
    (t s : Fin m)
    (ht : ∃ j : ℕ, 0 < j ∧ j < N ∧
      |gridJitterSample q α center t - (j : ℚ) / N| ≤ β)
    (hs : ∃ j : ℕ, 0 < j ∧ j < N ∧
      |gridJitterSample q α center s - (j : ℚ) / N| ≤ β) :
    t = s := by
  have hα0 : 0 < α := by linarith
  have hβN : β < 1 / (N : ℚ) := by
    have hc : (0 : ℚ) ≤ (m - 1 : ℕ) := by positivity
    nlinarith
  obtain ⟨j, hj, hjN, ht⟩ := ht
  obtain ⟨k, hk, hkN, hs⟩ := hs
  have hut := unclipped_of_near_grid hN hj hjN hβN ht
  have hus := unclipped_of_near_grid hN hk hkN hβN hs
  change |max 0 (min 1 (q + ((t.val : ℚ) - center) * α)) - (j : ℚ) / N| ≤ β at ht
  change |max 0 (min 1 (q + ((s.val : ℚ) - center) * α)) - (k : ℚ) / N| ≤ β at hs
  rw [hut] at ht
  rw [hus] at hs
  have htm : (t.val : ℚ) ≤ (m - 1 : ℕ) := by
    exact_mod_cast (show t.val ≤ m - 1 by omega)
  have hsm : (s.val : ℚ) ≤ (m - 1 : ℕ) := by
    exact_mod_cast (show s.val ≤ m - 1 by omega)
  have ht0 : (0 : ℚ) ≤ t.val := by positivity
  have hs0 : (0 : ℚ) ≤ s.val := by positivity
  have hraw : |(q + ((t.val : ℚ) - center) * α) -
      (q + ((s.val : ℚ) - center) * α)| ≤ ((m - 1 : ℕ) : ℚ) * α := by
    rw [abs_le]
    constructor <;> nlinarith
  have hgrid : |(j : ℚ) / N - (k : ℚ) / N| ≤ ((m - 1 : ℕ) : ℚ) * α + 2 * β := by
    rw [abs_le] at ht hs hraw ⊢
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2, hraw.1, hraw.2]
  have hjk : j = k := by
    by_contra hne
    have hsep := grid_fraction_separation hN hne
    linarith
  subst k
  rw [abs_le] at ht hs
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hq : (t.val : ℚ) + 1 ≤ s.val := by exact_mod_cast h
    nlinarith [ht.1, ht.2, hs.1, hs.2]
  · have hq : (s.val : ℚ) + 1 ≤ t.val := by exact_mod_cast h
    nlinarith [ht.1, ht.2, hs.1, hs.2]

/-- Any finite collection of bad sample indices has at most one member. -/
theorem gridJitter_bad_card_le_one {m N : ℕ} (q α center β : ℚ)
    (hm : 0 < m) (hN : 0 < N) (hβ : 0 ≤ β) (hα : 2 * β < α)
    (hspan : ((m - 1 : ℕ) : ℚ) * α + 2 * β < 1 / (N : ℚ))
    (bad : Finset (Fin m))
    (hbad : ∀ t ∈ bad, ∃ j : ℕ, 0 < j ∧ j < N ∧
      |gridJitterSample q α center t - (j : ℚ) / N| ≤ β) : bad.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht s hs
  exact gridJitter_bad_unique q α center β hm hN hβ hα hspan t s (hbad t ht) (hbad s hs)

end GameTheory.Math
