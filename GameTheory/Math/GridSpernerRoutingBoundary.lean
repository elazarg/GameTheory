import GameTheory.Math.GridSpernerRouting

/-! Inactive padding separates the routing tiles from the outer Sperner boundary.
Boundary clipping uses only two colors in each collar, so it creates no new
trichromatic triangle. Every answer therefore decodes to a non-source endpoint. -/

namespace GameTheory.Math.GridWire

open Sperner EndOfLine

private theorem no_trichromatic_avoiding : ∀ a b c excluded : Fin 3,
    a ≠ excluded → b ≠ excluded → c ≠ excluded → ¬Trichromatic a b c := by decide

private theorem corner_bounds (t : GridTriangle) (p : Fin 3) :
    t.x ≤ (corner t p).1 ∧ (corner t p).1 ≤ t.x + 1 ∧
      t.y ≤ (corner t p).2 ∧ (corner t p).2 ≤ t.y + 1 := by
  cases hu : t.upper <;> fin_cases p <;> simp [corner, hu]

private theorem canonical_ne_zero_of_large_x {n M x y : ℕ} {P S : ℕ → ℕ}
    (hx : 6 * (3 * n * n + 2) ≤ x) : gridSpernerRoutingColor n P S M x y ≠ 0 := by
  unfold gridSpernerRoutingColor standardGridColor
  split_ifs <;> try decide
  all_goals first | exact gridSpernerRoutingInterior_ne_zero_of_large_x hx | omega

private theorem canonical_ne_one_of_large_y {n M x y : ℕ} {P S : ℕ → ℕ}
    (hy : 6 * (6 * n + 2) ≤ y) : gridSpernerRoutingColor n P S M x y ≠ 1 := by
  unfold gridSpernerRoutingColor standardGridColor
  split_ifs <;> try decide
  all_goals first | exact gridSpernerRoutingInterior_ne_one_of_large_y hy | omega

/-- Below the top and right boundary, local enforcement leaves routing colors unchanged. -/
theorem gridSpernerRoutingColor_eq_interior {n M x y : ℕ} (P S : ℕ → ℕ)
    (hx : x < M) (hy : y < M) :
    gridSpernerRoutingColor n P S M x y = gridSpernerRoutingInterior n P S x y := by
  by_cases hy0 : y = 0
  · subst y
    simp only [gridSpernerRoutingColor, standardGridColor, ite_true,
      gridSpernerRoutingInterior_bottom]
  · have hborder : ¬(x = M ∨ y = M) := by omega
    simp only [gridSpernerRoutingColor, standardGridColor, hy0, hborder, ite_false]
    by_cases hx0 : x = 0
    · subst x
      simp [gridSpernerRoutingInterior_left]
    · simp [hx0]

/-- A trichromatic triangle cannot meet the clipped top or right padding collar. -/
theorem gridSpernerRouting_trichromatic_strict {n M : ℕ} {P S : ℕ → ℕ}
    (hwidth : 6 * (3 * n * n + 2) < M) (hheight : 6 * (6 * n + 2) < M)
    {t : GridTriangle} (hv : ValidTriangle M t)
    (ht : Trichromatic (gridSpernerRoutingColor n P S M (corner t 0).1 (corner t 0).2)
      (gridSpernerRoutingColor n P S M (corner t 1).1 (corner t 1).2)
      (gridSpernerRoutingColor n P S M (corner t 2).1 (corner t 2).2)) :
    t.x + 1 < M ∧ t.y + 1 < M := by
  constructor
  · by_contra hn
    have hcut : 6 * (3 * n * n + 2) ≤ t.x := by
      have h := hv.1
      omega
    have hcolor (p : Fin 3) :
        gridSpernerRoutingColor n P S M (corner t p).1 (corner t p).2 ≠ 0 :=
      canonical_ne_zero_of_large_x (hcut.trans (corner_bounds t p).1)
    exact no_trichromatic_avoiding _ _ _ 0 (hcolor 0) (hcolor 1) (hcolor 2) ht
  · by_contra hn
    have hcut : 6 * (6 * n + 2) ≤ t.y := by
      have h := hv.2
      omega
    have hcolor (p : Fin 3) :
        gridSpernerRoutingColor n P S M (corner t p).1 (corner t p).2 ≠ 1 :=
      canonical_ne_one_of_large_y (hcut.trans (corner_bounds t p).2.2.1)
    exact no_trichromatic_avoiding _ _ _ 1 (hcolor 0) (hcolor 1) (hcolor 2) ht

/-- Every finite Sperner answer decodes to a bounded endpoint other than the known source. -/
theorem gridSpernerRouting_endpoint_label {n M : ℕ} {P S : ℕ → ℕ}
    (hn : 0 < n) (hSi : S 0 < n) (hp0 : P 0 = 0) (hs0 : S 0 ≠ 0)
    (hlink : P (S 0) = 0) (hP : ∀ i, i < n → P i < n) (hS : ∀ i, i < n → S i < n)
    (hwidth : 6 * (3 * n * n + 2) < M) (hheight : 6 * (6 * n + 2) < M)
    {t : GridTriangle} (hv : ValidTriangle M t)
    (ht : Trichromatic (gridSpernerRoutingColor n P S M (corner t 0).1 (corner t 0).2)
      (gridSpernerRoutingColor n P S M (corner t 1).1 (corner t 1).2)
      (gridSpernerRoutingColor n P S M (corner t 2).1 (corner t 2).2)) :
    t.x = 8 ∧ t.y / 36 < n ∧ t.y / 36 ≠ 0 ∧ IsEndpoint P S (t.y / 36) := by
  have hb := gridSpernerRouting_trichromatic_strict hwidth hheight hv ht
  have heq (p : Fin 3) : gridSpernerRoutingColor n P S M (corner t p).1 (corner t p).2 =
      gridSpernerRoutingInterior n P S (corner t p).1 (corner t p).2 :=
    gridSpernerRoutingColor_eq_interior P S
      (lt_of_le_of_lt (corner_bounds t p).2.1 hb.1)
      (lt_of_le_of_lt (corner_bounds t p).2.2.2 hb.2)
  rw [heq 0, heq 1, heq 2] at ht
  obtain ⟨i, hi, hne, he, hx, hy⟩ :=
    gridSpernerRoutingInterior_endpoint_label hn hSi hp0 hs0 hlink hP hS ht
  have hdiv : t.y / 36 = i := by omega
  exact ⟨hx, by rw [hdiv]; exact hi, by rw [hdiv]; exact hne, by rw [hdiv]; exact he⟩

end GameTheory.Math.GridWire
