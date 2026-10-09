import Mathlib.Algebra.Order.Field.Power
import GameTheory.Math.GridJitter
import GameTheory.Math.ClippedArithmetic
import Mathlib.Data.Fintype.Fin

/-! Two-coordinate jitter avoids interior grid boundaries at all but two sample indices.
The clipped forty-one-sample progression also stays within twenty spacings of its center. -/

namespace GameTheory.Math

/-- Two coordinate progressions have at most two indices near an interior grid boundary. -/
theorem exists_gridJitter_pair_clearance {m N : ℕ} (x y α center β : ℚ)
    (hm : 0 < m) (hN : 0 < N) (hβ : 0 ≤ β) (hα : 2 * β < α)
    (hspan : ((m - 1 : ℕ) : ℚ) * α + 2 * β < 1 / (N : ℚ)) :
    ∃ bad : Finset (Fin m), bad.card ≤ 2 ∧
      ∀ t, t ∉ bad → ∀ j : ℕ, 0 < j → j < N →
        β < |gridJitterSample x α center t - (j : ℚ) / N| ∧
        β < |gridJitterSample y α center t - (j : ℚ) / N| := by
  classical
  let near (q : ℚ) (t : Fin m) : Prop := ∃ j : ℕ, 0 < j ∧ j < N ∧
    |gridJitterSample q α center t - (j : ℚ) / N| ≤ β
  let bx := Finset.univ.filter (near x)
  let bys := Finset.univ.filter (near y)
  have hbx : bx.card ≤ 1 := gridJitter_bad_card_le_one x α center β
    hm hN hβ hα hspan bx (fun _ ht => (Finset.mem_filter.mp ht).2)
  have hby : bys.card ≤ 1 := gridJitter_bad_card_le_one y α center β
    hm hN hβ hα hspan bys (fun _ ht => (Finset.mem_filter.mp ht).2)
  refine ⟨bx ∪ bys, (Finset.card_union_le _ _).trans (by omega), ?_⟩
  intro t ht j hj hjN
  have hclear (q : ℚ) (hq : t ∉ Finset.univ.filter (near q)) :
      β < |gridJitterSample q α center t - (j : ℚ) / N| := by
    by_contra h
    apply hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, hjN, le_of_not_gt h⟩
  exact ⟨hclear x (fun h => ht (Finset.mem_union_left _ h)),
    hclear y (fun h => ht (Finset.mem_union_right _ h))⟩

/-- Clipping forty-one centered samples cannot increase their distance from a unit input. -/
theorem gridJitter_fortyOne_distance (q α : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hα : 0 ≤ α) (t : Fin 41) : |gridJitterSample q α 20 t - q| ≤ 20 * α := by
  have ht0 : (0 : ℚ) ≤ t.val := by positivity
  have ht40 : (t.val : ℚ) ≤ 40 := by exact_mod_cast (show t.val ≤ 40 by omega)
  have hc := unitClamp_nonexpansive (q + ((t.val : ℚ) - 20) * α) q
  rw [unitClamp_eq_self hq0 hq1] at hc
  change |gridJitterSample q α 20 t - q| ≤ _ at hc
  apply hc.trans
  rw [abs_le]
  constructor <;> nlinarith

/-- Dyadic spacing simultaneously separates forty-one samples and makes their
coarse scaled-displacement variation smaller than one thousand twenty-fourth. -/
theorem gridJitter_fortyOne_dyadic_bounds (b : ℕ) :
    let N : ℚ := 2 ^ b
    let α : ℚ := 1 / 2 ^ (5 * (b + 10))
    0 < α ∧ 0 ≤ α / 4 ∧ 2 * (α / 4) < α ∧
      40 * α + 2 * (α / 4) < 1 / N ∧
      2 * N * (N + 1) ^ 2 * (20 * α) ≤ 1 / 1024 := by
  dsimp only
  let N : ℚ := 2 ^ b
  let α : ℚ := 1 / 2 ^ (5 * (b + 10))
  have hN : 1 ≤ N := one_le_pow₀ (show (1 : ℚ) ≤ 2 by norm_num)
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hα : 0 < α := by dsimp [α]; positivity
  have he : 3 * b + 18 ≤ 5 * (b + 10) := by omega
  have hp : 262144 * N ^ 3 ≤ (2 : ℚ) ^ (5 * (b + 10)) := by
    calc
      _ = (2 : ℚ) ^ (3 * b + 18) := by
        dsimp [N]
        rw [pow_add, Nat.mul_comm 3 b, pow_mul]
        norm_num
        ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) he
  have had : α * (2 : ℚ) ^ (5 * (b + 10)) = 1 := by
    dsimp [α]
    exact one_div_mul_cancel (by positivity)
  have hpα : 262144 * N ^ 3 * α ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hp hα.le
    rw [mul_comm ((2 : ℚ) ^ (5 * (b + 10))) α, had] at hh
    exact hh
  have hN3 : N ≤ N ^ 3 := by
    calc
      N = N * 1 := (mul_one _).symm
      _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hN) hN0.le
      _ = N ^ 3 := by ring
  have hNa : N * α ≤ N ^ 3 * α := mul_le_mul_of_nonneg_right hN3 hα.le
  have hs : (40 * α + 2 * (α / 4)) * N < 1 := by nlinarith only [hNa, hpα]
  have hspan : 40 * α + 2 * (α / 4) < 1 / N :=
    (lt_div_iff₀ hN0).mpr hs
  have hsq : (N + 1) ^ 2 ≤ 4 * N ^ 2 := by nlinarith only [hN]
  have hprod := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 2 * N * (20 * α) by positivity)
  have hv : 2 * N * (N + 1) ^ 2 * (20 * α) ≤ 1 / 1024 := by
    nlinarith only [hprod, hpα]
  exact ⟨hα, div_nonneg hα.le (by norm_num), by linarith, hspan, hv⟩


end GameTheory.Math
