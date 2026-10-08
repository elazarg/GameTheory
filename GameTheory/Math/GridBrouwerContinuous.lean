import GameTheory.Math.GridBrouwerMap
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Semiring

/-! Continuous piecewise affine interpolation of the canonical grid displacement.
The compactly supported vertex hats agree with barycentric coordinates on the
rising-diagonal triangulation, so no discontinuous choice of a cell is needed. -/

namespace GameTheory.Math.Brouwer

open Sperner
open scoped BigOperators

/-- The piecewise linear hat at a vertex of the rising-diagonal triangulation. -/
def vertexHat (i j : ℕ) (p : ℝ × ℝ) : ℝ :=
  max 0 (1 - max |p.1 - i| (max |p.2 - j| |(p.1 - i) - (p.2 - j)|))

theorem continuous_vertexHat (i j : ℕ) : Continuous (vertexHat i j) := by
  unfold vertexHat
  fun_prop

theorem vertexHat_eq_zero_of_horizontal {i j : ℕ} {p : ℝ × ℝ}
    (h : 1 ≤ |p.1 - i|) : vertexHat i j p = 0 := by
  unfold vertexHat
  rw [max_eq_left]
  linarith [le_max_left |p.1 - i| (max |p.2 - j| |(p.1 - i) - (p.2 - j)|)]

theorem vertexHat_eq_zero_of_vertical {i j : ℕ} {p : ℝ × ℝ}
    (h : 1 ≤ |p.2 - j|) : vertexHat i j p = 0 := by
  unfold vertexHat
  rw [max_eq_left]
  have h₁ := le_max_left |p.2 - j| |(p.1 - i) - (p.2 - j)|
  have h₂ := le_max_right |p.1 - i| (max |p.2 - j| |(p.1 - i) - (p.2 - j)|)
  linarith

/-- Outside the four corners of a cell, every vertex hat vanishes on that cell. -/
theorem vertexHat_eq_zero_outside_cell {x y i j : ℕ} {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (h : ¬ ((i = x ∨ i = x + 1) ∧ (j = y ∨ j = y + 1))) :
    vertexHat i j ((x : ℝ) + a, (y : ℝ) + b) = 0 := by
  by_cases hi : i = x ∨ i = x + 1
  · have hj : ¬ (j = y ∨ j = y + 1) := fun hj => h ⟨hi, hj⟩
    apply vertexHat_eq_zero_of_vertical
    by_cases hlt : j < y
    · have hc : (j : ℝ) + 1 ≤ y := by exact_mod_cast (show j + 1 ≤ y by omega)
      rw [abs_of_nonneg] <;> dsimp <;> linarith [hb.1]
    · have hc : (y : ℝ) + 2 ≤ j := by exact_mod_cast (show y + 2 ≤ j by omega)
      rw [abs_of_nonpos] <;> dsimp <;> linarith [hb.2]
  · apply vertexHat_eq_zero_of_horizontal
    by_cases hlt : i < x
    · have hc : (i : ℝ) + 1 ≤ x := by exact_mod_cast (show i + 1 ≤ x by omega)
      rw [abs_of_nonneg] <;> dsimp <;> linarith [ha.1]
    · have hc : (x : ℝ) + 2 ≤ i := by exact_mod_cast (show x + 2 ≤ i by omega)
      rw [abs_of_nonpos] <;> dsimp <;> linarith [ha.2]

theorem vertexHat_lower_origin (x y : ℕ) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    vertexHat x y ((x : ℝ) + a, (y : ℝ) + b) = 1 - a := by
  simp only [vertexHat, add_sub_cancel_left]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg hb,
    abs_of_nonneg (sub_nonneg.mpr hba)]
  have hm : max a (max b (a - b)) = a :=
    max_eq_left (max_le hba (by linarith))
  rw [hm, max_eq_right (by linarith)]

theorem vertexHat_lower_right (x y : ℕ) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    vertexHat (x + 1) y ((x : ℝ) + a, (y : ℝ) + b) = a - b := by
  have hx : (x : ℝ) + a - (x + 1) = a - 1 := by ring
  simp only [vertexHat, Nat.cast_add, Nat.cast_one, hx, add_sub_cancel_left]
  rw [abs_of_nonpos (by linarith), abs_of_nonneg hb,
    abs_of_nonpos (by linarith)]
  have hm : max (-(a - 1)) (max b (- (a - 1 - b))) = 1 - a + b := by
    rw [max_eq_right (show b ≤ -(a - 1 - b) by linarith)]
    rw [max_eq_right (show -(a - 1) ≤ -(a - 1 - b) by linarith)]
    ring
  rw [hm, max_eq_right (by linarith)]
  ring

theorem vertexHat_lower_diagonal (x y : ℕ) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    vertexHat (x + 1) (y + 1) ((x : ℝ) + a, (y : ℝ) + b) = b := by
  have hx : (x : ℝ) + a - (x + 1) = a - 1 := by ring
  have hy : (y : ℝ) + b - (y + 1) = b - 1 := by ring
  have hxy : (a - 1) - (b - 1) = a - b := by ring
  simp only [vertexHat, Nat.cast_add, Nat.cast_one, hx, hy, hxy]
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonneg (by linarith)]
  have hm : max (-(a - 1)) (max (-(b - 1)) (a - b)) = 1 - b := by
    rw [max_eq_left (show a - b ≤ -(b - 1) by linarith)]
    rw [max_eq_right (show -(a - 1) ≤ -(b - 1) by linarith)]
    ring
  rw [hm, max_eq_right (by linarith)]
  ring

theorem vertexHat_lower_opposite (x y : ℕ) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    vertexHat x (y + 1) ((x : ℝ) + a, (y : ℝ) + b) = 0 := by
  have hy : (y : ℝ) + b - (y + 1) = b - 1 := by ring
  simp only [vertexHat, Nat.cast_add, Nat.cast_one, hy, add_sub_cancel_left]
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonneg (by linarith)]
  rw [max_eq_left]
  have h₁ := le_max_right (-(b - 1)) (a - (b - 1))
  have h₂ := le_max_right a (max (-(b - 1)) (a - (b - 1)))
  linarith

theorem vertexHat_swap (i j : ℕ) (p : ℝ × ℝ) :
    vertexHat i j p = vertexHat j i (p.2, p.1) := by
  unfold vertexHat
  simp only [abs_sub_comm (p.1 - i) (p.2 - j)]
  congr 2
  exact max_left_comm _ _ _

/-- The three nonzero hats on a lower triangle are its barycentric weights. -/
theorem vertexHat_lower (x y i j : ℕ) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    vertexHat i j ((x : ℝ) + a, (y : ℝ) + b) =
      if i = x then (if j = y then 1 - a else 0)
      else if i = x + 1 then
        (if j = y then a - b else if j = y + 1 then b else 0)
      else 0 := by
  by_cases hi : i = x
  · subst i
    by_cases hj : j = y
    · subst j
      simpa using vertexHat_lower_origin x y hb hba ha
    · by_cases hj' : j = y + 1
      · subst j
        simpa using vertexHat_lower_opposite x y hb hba ha
      · rw [vertexHat_eq_zero_outside_cell ⟨by linarith, ha⟩ ⟨hb, by linarith⟩
          (by simp [hj, hj'])]
        simp [hj]
  · by_cases hi' : i = x + 1
    · subst i
      by_cases hj : j = y
      · subst j
        simpa using vertexHat_lower_right x y hb hba ha
      · by_cases hj' : j = y + 1
        · subst j
          simpa using vertexHat_lower_diagonal x y hb hba ha
        · rw [vertexHat_eq_zero_outside_cell ⟨by linarith, ha⟩ ⟨hb, by linarith⟩
            (by simp [hj, hj'])]
          simp [hj, hj']
    · rw [vertexHat_eq_zero_outside_cell ⟨by linarith, ha⟩ ⟨hb, by linarith⟩
        (by simp [hi, hi'])]
      simp [hi, hi']

theorem sum_vertexHat_lower (f : ℕ → ℕ → ℝ) {n x y : ℕ}
    (hx : x < n) (hy : y < n) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      vertexHat i j ((x : ℝ) + a, (y : ℝ) + b) * f i j) =
      (1 - a) * f x y + (a - b) * f (x + 1) y + b * f (x + 1) (y + 1) := by
  simp only [vertexHat_lower x y _ _ hb hba ha, ite_mul, zero_mul]
  have hx₀ : x < n + 1 := by omega
  have hx₁ : x + 1 < n + 1 := by omega
  have hy₀ : y < n + 1 := by omega
  have hy₁ : y + 1 < n + 1 := by omega
  simp [Finset.sum_ite, hx₀, hx₁, hy₀, hy₁, add_assoc]

theorem sum_vertexHat_upper (f : ℕ → ℕ → ℝ) {n x y : ℕ}
    (hx : x < n) (hy : y < n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      vertexHat i j ((x : ℝ) + a, (y : ℝ) + b) * f i j) =
      (1 - b) * f x y + a * f (x + 1) (y + 1) + (b - a) * f x (y + 1) := by
  conv_lhs =>
    arg 2
    ext i
    arg 2
    ext j
    arg 1
    rw [vertexHat_swap]
  rw [Finset.sum_comm]
  rw [sum_vertexHat_lower (fun j i => f i j) hy hx ha hab hb]
  ring

/-- Interpolation of the color displacement over all vertices of the finite grid. -/
def globalGridMap (color : ℕ → ℕ → Fin 3) (n : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      vertexHat i j p * ((colorDisplacement (color i j)).1 : ℝ),
    p.2 + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      vertexHat i j p * ((colorDisplacement (color i j)).2 : ℝ))

theorem continuous_globalGridMap (color : ℕ → ℕ → Fin 3) (n : ℕ) :
    Continuous (globalGridMap color n) := by
  unfold globalGridMap
  apply Continuous.prodMk <;>
    apply Continuous.add (by fun_prop) <;>
    apply continuous_finsetSum <;> intro i hi <;>
    apply continuous_finsetSum <;> intro j hj <;>
    exact (continuous_vertexHat i j).mul continuous_const

theorem globalGridMap_lower (color : ℕ → ℕ → Fin 3) {n x y : ℕ}
    (hx : x < n) (hy : y < n) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    globalGridMap color n ((x : ℝ) + a, (y : ℝ) + b) =
      ((x : ℝ) + a +
        ((1 - a) * ((colorDisplacement (color x y)).1 : ℝ) +
          (a - b) * ((colorDisplacement (color (x + 1) y)).1 : ℝ) +
          b * ((colorDisplacement (color (x + 1) (y + 1))).1 : ℝ)),
       (y : ℝ) + b +
        ((1 - a) * ((colorDisplacement (color x y)).2 : ℝ) +
          (a - b) * ((colorDisplacement (color (x + 1) y)).2 : ℝ) +
          b * ((colorDisplacement (color (x + 1) (y + 1))).2 : ℝ))) := by
  apply Prod.ext <;> dsimp [globalGridMap] <;>
    rw [sum_vertexHat_lower _ hx hy hb hba ha]

theorem globalGridMap_upper (color : ℕ → ℕ → Fin 3) {n x y : ℕ}
    (hx : x < n) (hy : y < n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    globalGridMap color n ((x : ℝ) + a, (y : ℝ) + b) =
      ((x : ℝ) + a +
        ((1 - b) * ((colorDisplacement (color x y)).1 : ℝ) +
          a * ((colorDisplacement (color (x + 1) (y + 1))).1 : ℝ) +
          (b - a) * ((colorDisplacement (color x (y + 1))).1 : ℝ)),
       (y : ℝ) + b +
        ((1 - b) * ((colorDisplacement (color x y)).2 : ℝ) +
          a * ((colorDisplacement (color (x + 1) (y + 1))).2 : ℝ) +
          (b - a) * ((colorDisplacement (color x (y + 1))).2 : ℝ))) := by
  apply Prod.ext <;> dsimp [globalGridMap] <;>
    rw [sum_vertexHat_upper _ hx hy ha hab hb]

/-- The real square on which the grid interpolation is a self-map. -/
def InRealGridSquare (n : ℕ) (p : ℝ × ℝ) : Prop :=
  (0 ≤ p.1 ∧ p.1 ≤ n) ∧ (0 ≤ p.2 ∧ p.2 ≤ n)

/-- Closed grid cells cover their square, including its far boundary. -/
theorem exists_real_gridCell {n : ℕ} (hn : 0 < n) {q : ℝ}
    (hq : 0 ≤ q ∧ q ≤ n) :
    ∃ i : ℕ, ∃ a : ℝ, i < n ∧ 0 ≤ a ∧ a ≤ 1 ∧ q = i + a := by
  by_cases hlt : q < n
  · refine ⟨⌊q⌋₊, q - ⌊q⌋₊, (Nat.floor_lt hq.1).mpr hlt, ?_, ?_, ?_⟩
    · exact sub_nonneg.mpr (Nat.floor_le hq.1)
    · linarith [Nat.lt_floor_add_one q]
    · ring
  · have heq : q = n := le_antisymm hq.2 (le_of_not_gt hlt)
    refine ⟨n - 1, 1, by omega, by norm_num, by norm_num, ?_⟩
    rw [heq, Nat.cast_sub (by omega)]
    norm_num

private theorem convexThree_real_bounds {n a b c u v w : ℝ}
    (ha : 0 ≤ a ∧ a ≤ n) (hb : 0 ≤ b ∧ b ≤ n) (hc : 0 ≤ c ∧ c ≤ n)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hs : u + v + w = 1) :
    0 ≤ u * a + v * b + w * c ∧ u * a + v * b + w * c ≤ n := by
  constructor
  · exact add_nonneg (add_nonneg (mul_nonneg hu ha.1) (mul_nonneg hv hb.1))
      (mul_nonneg hw hc.1)
  · have h₁ := mul_le_mul_of_nonneg_left ha.2 hu
    have h₂ := mul_le_mul_of_nonneg_left hb.2 hv
    have h₃ := mul_le_mul_of_nonneg_left hc.2 hw
    nlinarith

private theorem real_vertexImage_mem_square {color : ℕ → ℕ → Fin 3} {n i j : ℕ}
    (hb : GridBoundary color n) (hi : i ≤ n) (hj : j ≤ n) :
    InRealGridSquare n
      (((vertexImage color i j).1 : ℝ), ((vertexImage color i j).2 : ℝ)) := by
  have hv := vertexImage_mem_square hb hi hj
  dsimp only [InRealGridSquare]
  exact ⟨⟨by exact_mod_cast hv.1.1, by exact_mod_cast hv.1.2⟩,
    ⟨by exact_mod_cast hv.2.1, by exact_mod_cast hv.2.2⟩⟩

theorem globalGridMap_lower_mem_square {color : ℕ → ℕ → Fin 3} {n x y : ℕ}
    (hbnd : GridBoundary color n) (hx : x < n) (hy : y < n) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    InRealGridSquare n (globalGridMap color n ((x : ℝ) + a, (y : ℝ) + b)) := by
  have h₀ := real_vertexImage_mem_square hbnd (Nat.le_of_lt hx) (Nat.le_of_lt hy)
  have h₁ := real_vertexImage_mem_square hbnd (show x + 1 ≤ n by omega)
    (Nat.le_of_lt hy)
  have h₂ := real_vertexImage_mem_square hbnd (show x + 1 ≤ n by omega)
    (show y + 1 ≤ n by omega)
  have hs : (1 - a) + (a - b) + b = 1 := by ring
  have hu : 0 ≤ 1 - a := by linarith
  have hv : 0 ≤ a - b := by linarith
  have hX := convexThree_real_bounds h₀.1 h₁.1 h₂.1 hu hv hb hs
  have hY := convexThree_real_bounds h₀.2 h₁.2 h₂.2 hu hv hb hs
  rw [globalGridMap_lower _ hx hy hb hba ha]
  refine ⟨?_, ?_⟩
  · convert hX using 2 <;> dsimp [vertexImage] <;> push_cast <;> ring
  · convert hY using 2 <;> dsimp [vertexImage] <;> push_cast <;> ring

theorem globalGridMap_upper_mem_square {color : ℕ → ℕ → Fin 3} {n x y : ℕ}
    (hbnd : GridBoundary color n) (hx : x < n) (hy : y < n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    InRealGridSquare n (globalGridMap color n ((x : ℝ) + a, (y : ℝ) + b)) := by
  have h₀ := real_vertexImage_mem_square hbnd (Nat.le_of_lt hx) (Nat.le_of_lt hy)
  have h₁ := real_vertexImage_mem_square hbnd (show x + 1 ≤ n by omega)
    (show y + 1 ≤ n by omega)
  have h₂ := real_vertexImage_mem_square hbnd (Nat.le_of_lt hx)
    (show y + 1 ≤ n by omega)
  have hs : (1 - b) + a + (b - a) = 1 := by ring
  have hu : 0 ≤ 1 - b := by linarith
  have hw : 0 ≤ b - a := by linarith
  have hX := convexThree_real_bounds h₀.1 h₁.1 h₂.1 hu ha hw hs
  have hY := convexThree_real_bounds h₀.2 h₁.2 h₂.2 hu ha hw hs
  rw [globalGridMap_upper _ hx hy ha hab hb]
  refine ⟨?_, ?_⟩
  · convert hX using 2 <;> dsimp [vertexImage] <;> push_cast <;> ring
  · convert hY using 2 <;> dsimp [vertexImage] <;> push_cast <;> ring

/-- Boundary exclusions make the globally continuous interpolation a square self-map. -/
theorem globalGridMap_mem_square {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : GridBoundary color n) (hn : 0 < n) {p : ℝ × ℝ}
    (hp : InRealGridSquare n p) : InRealGridSquare n (globalGridMap color n p) := by
  obtain ⟨x, a, hx, ha₀, ha₁, hpx⟩ := exists_real_gridCell hn hp.1
  obtain ⟨y, b, hy, hb₀, hb₁, hpy⟩ := exists_real_gridCell hn hp.2
  have heq : p = ((x : ℝ) + a, (y : ℝ) + b) := Prod.ext hpx hpy
  rw [heq]
  by_cases hba : b ≤ a
  · exact globalGridMap_lower_mem_square hb hx hy hb₀ hba ha₁
  · exact globalGridMap_upper_mem_square hb hx hy ha₀ (le_of_not_ge hba) hb₁

/-- Rescale grid interpolation to the unit square without changing its color semantics. -/
noncomputable def normalizedGridMap (color : ℕ → ℕ → Fin 3) (n : ℕ)
    (p : ℝ × ℝ) : ℝ × ℝ :=
  let q := globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)
  (q.1 / n, q.2 / n)

theorem continuous_normalizedGridMap (color : ℕ → ℕ → Fin 3) (n : ℕ) :
    Continuous (normalizedGridMap color n) := by
  unfold normalizedGridMap
  have h : Continuous (fun p : ℝ × ℝ => ((n : ℝ) * p.1, (n : ℝ) * p.2)) := by
    fun_prop
  exact (((continuous_globalGridMap color n).comp h).fst.div_const _).prodMk
    (((continuous_globalGridMap color n).comp h).snd.div_const _)

theorem normalizedGridMap_mem_unitSquare {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : GridBoundary color n) (hn : 0 < n) {p : ℝ × ℝ}
    (hp : InRealGridSquare 1 p) : InRealGridSquare 1 (normalizedGridMap color n p) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : InRealGridSquare n ((n : ℝ) * p.1, (n : ℝ) * p.2) := by
    refine ⟨⟨mul_nonneg hn'.le hp.1.1, ?_⟩, ⟨mul_nonneg hn'.le hp.2.1, ?_⟩⟩
    · simpa using mul_le_mul_of_nonneg_left hp.1.2 hn'.le
    · simpa using mul_le_mul_of_nonneg_left hp.2.2 hn'.le
  have hf := globalGridMap_mem_square hb hn hq
  dsimp only [InRealGridSquare, normalizedGridMap]
  rw [Nat.cast_one]
  refine ⟨⟨div_nonneg hf.1.1 hn'.le, ?_⟩, ⟨div_nonneg hf.2.1 hn'.le, ?_⟩⟩
  · exact (div_le_one hn').mpr hf.1.2
  · exact (div_le_one hn').mpr hf.2.2

end GameTheory.Math.Brouwer
