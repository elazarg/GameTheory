import GameTheory.Math.GridJitterPair
import GameTheory.Math.GridBrouwerLipschitz
import GameTheory.Math.RobustFeedback

/-! Centered clipped samples perturb each coordinate of the grid displacement by a
quantified amount, independent of the vertex coloring. -/
namespace GameTheory.Math.Brouwer

/-- The scaled displacement at a jitter sample differs by at most twenty spacings
multiplied by its Lipschitz constant, in each coordinate. -/
theorem gridJitter_scaled_displacement_error (color : ℕ → ℕ → Fin 3) (n : ℕ)
    (x y α : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hα : 0 ≤ α) (t : Fin 41) :
    let p : ℝ × ℝ := (x, y)
    let s : ℝ × ℝ := (gridJitterSample x α 20 t, gridJitterSample y α 20 t)
    |((globalGridMap color n ((n : ℝ) * s.1, (n : ℝ) * s.2)).1 - (n : ℝ) * s.1) -
      ((globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)).1 - (n : ℝ) * p.1)| ≤
        (2 * (n : ℝ) * (n + 1) ^ 2) * (20 * (α : ℝ)) ∧
    |((globalGridMap color n ((n : ℝ) * s.1, (n : ℝ) * s.2)).2 - (n : ℝ) * s.2) -
      ((globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)).2 - (n : ℝ) * p.2)| ≤
        (2 * (n : ℝ) * (n + 1) ^ 2) * (20 * (α : ℝ)) := by
  dsimp only
  have hx : |(gridJitterSample x α 20 t : ℝ) - (x : ℝ)| ≤ 20 * (α : ℝ) := by
    exact_mod_cast gridJitter_fortyOne_distance x α hx0 hx1 hα t
  have hy : |(gridJitterSample y α 20 t : ℝ) - (y : ℝ)| ≤ 20 * (α : ℝ) := by
    exact_mod_cast gridJitter_fortyOne_distance y α hy0 hy1 hα t
  have hd : dist ((gridJitterSample x α 20 t : ℝ), (gridJitterSample y α 20 t : ℝ))
      ((x : ℝ), (y : ℝ)) ≤ 20 * (α : ℝ) := by
    simpa only [Prod.dist_eq, Real.dist_eq] using max_le hx hy
  have hf := (globalGridMap_scaled_fst_displacement_lipschitz color n).dist_le_mul
    ((gridJitterSample x α 20 t : ℝ), (gridJitterSample y α 20 t : ℝ)) ((x : ℝ), (y : ℝ))
  have hg := (globalGridMap_scaled_snd_displacement_lipschitz color n).dist_le_mul
    ((gridJitterSample x α 20 t : ℝ), (gridJitterSample y α 20 t : ℝ)) ((x : ℝ), (y : ℝ))
  simp only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] at hf hg
  have hm := mul_le_mul_of_nonneg_left hd
    (show (0 : ℝ) ≤ 2 * (n : ℝ) * (n + 1) ^ 2 by positivity)
  exact ⟨hf.trans hm, hg.trans hm⟩

/-- Approximate displacement samples and projected feedback yield a small residual
of the canonical map, tolerating two exceptional samples. -/
theorem gridJitter_feedback_residual {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hbnd : Sperner.GridBoundary color n) (hn : 0 < n)
    (x y α : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hα : 0 ≤ α) (bad : Finset (Fin 41)) (hb : bad.card ≤ 2)
    (fx fy : Fin 41 → ℝ) (ε θ ρ : ℝ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hgood : ∀ t, t ∉ bad →
      |fx t - ((globalGridMap color n
        ((n : ℝ) * gridJitterSample x α 20 t, (n : ℝ) * gridJitterSample y α 20 t)).1 -
          (n : ℝ) * gridJitterSample x α 20 t)| ≤ ε ∧
      |fy t - ((globalGridMap color n
        ((n : ℝ) * gridJitterSample x α 20 t, (n : ℝ) * gridJitterSample y α 20 t)).2 -
          (n : ℝ) * gridJitterSample y α 20 t)| ≤ ε)
    (hexceptional : ∀ t ∈ bad,
      |fx t - ((globalGridMap color n ((n : ℝ) * x, (n : ℝ) * y)).1 - (n : ℝ) * x)|
        ≤ 25 / 8 ∧
      |fy t - ((globalGridMap color n ((n : ℝ) * x, (n : ℝ) * y)).2 - (n : ℝ) * y)|
        ≤ 25 / 8)
    (hfeedback : |(x : ℝ) - max 0 (min 1 (x + θ * ((∑ t, fx t) / 41)))| ≤ ρ ∧
      |(y : ℝ) - max 0 (min 1 (y + θ * ((∑ t, fy t) / 41)))| ≤ ρ)
    (hsample : ε + (2 * (n : ℝ) * (n + 1) ^ 2) * (20 * (α : ℝ)) ≤ 1 / 512)
    (hround : ρ / θ + (2 * (n : ℝ) * (n + 1) ^ 2) * ρ ≤ 1 / 512) :
    |(globalGridMap color n ((n : ℝ) * x, (n : ℝ) * y)).1 - (n : ℝ) * x| ≤ 1 / 6 ∧
    |(globalGridMap color n ((n : ℝ) * x, (n : ℝ) * y)).2 - (n : ℝ) * y| ≤ 1 / 6 := by
  have hx0r : (0 : ℝ) ≤ x := by exact_mod_cast hx0
  have hx1r : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have hy0r : (0 : ℝ) ≤ y := by exact_mod_cast hy0
  have hy1r : (y : ℝ) ≤ 1 := by exact_mod_cast hy1
  have hp : InRealGridSquare 1 ((x : ℝ), (y : ℝ)) := by
    simpa only [InRealGridSquare, Prod.fst, Prod.snd, Nat.cast_one] using
      And.intro (And.intro hx0r hx1r) (And.intro hy0r hy1r)
  have hf := globalGridMap_scaled_fst_displacement_inward hbnd hn hp
  have hg := globalGridMap_scaled_snd_displacement_inward hbnd hn hp
  have hαr : (0 : ℝ) ≤ α := by exact_mod_cast hα
  have he0 : 0 ≤ ε + (2 * (n : ℝ) * (n + 1) ^ 2) * (20 * (α : ℝ)) := by positivity
  have hgood' (t : Fin 41) (ht : t ∉ bad) := hgood t ht
  have hd (t : Fin 41) := gridJitter_scaled_displacement_error color n
    x y α hx0 hx1 hy0 hy1 hα t
  constructor
  · apply robustFeedback_fortyOne_residual bad hb fx (x : ℝ) θ _ _ ρ _
      hx0r hx1r hθ he0 hsample _ _ hfeedback.1 hf.1 hf.2
      hround
    · intro t ht
      have hs := abs_sub_le (fx t)
        ((globalGridMap color n
          ((n : ℝ) * gridJitterSample x α 20 t, (n : ℝ) * gridJitterSample y α 20 t)).1 -
            (n : ℝ) * gridJitterSample x α 20 t)
        ((globalGridMap color n ((n : ℝ) * x, (n : ℝ) * y)).1 - (n : ℝ) * x)
      exact hs.trans (add_le_add (hgood' t ht).1 (hd t).1)
    · exact fun t ht => (hexceptional t ht).1
  · apply robustFeedback_fortyOne_residual bad hb fy (y : ℝ) θ _ _ ρ _
      hy0r hy1r hθ he0 hsample _ _ hfeedback.2 hg.1 hg.2
      hround
    · intro t ht
      have hs := abs_sub_le (fy t)
        ((globalGridMap color n
          ((n : ℝ) * gridJitterSample x α 20 t, (n : ℝ) * gridJitterSample y α 20 t)).2 -
            (n : ℝ) * gridJitterSample y α 20 t)
        ((globalGridMap color n ((n : ℝ) * x, (n : ℝ) * y)).2 - (n : ℝ) * y)
      exact hs.trans (add_le_add (hgood' t ht).2 (hd t).2)
    · exact fun t ht => (hexceptional t ht).2

end GameTheory.Math.Brouwer
