/-
# Mean comparisons under affine maps of payoffs

A mean comparison sees only the order of two sums of draws, so it is unchanged
when every payoff of both laws is moved by the same increasing affine map. The
map may differ from size to size, so computational mean dominance is invariant
under per-size positive affine rescaling. Shifting one side only is shifting the
other side the opposite way, which is how payoff tolerances enter mean tests.
Point masses compare deterministically.
-/
import GameTheory.Math.Probability.Indistinguishability

noncomputable section

namespace GameTheory.Math.Probability

/-- The gap is antisymmetric: swapping the two laws negates it. -/
theorem meanComparisonGap_swap (X Y : PMF ℝ) (m : ℕ) :
    meanComparisonGap Y X m = -meanComparisonGap X Y m := by
  rw [meanComparisonGap_eq_aheadProb_sub, meanComparisonGap_eq_aheadProb_sub]
  ring

/-! ## Shifts -/

/-- Shift every payoff of an ensemble by `ε κ`. -/
def shiftEnsemble (ε : ℕ → ℝ) (X : ℕ → PMF ℝ) : ℕ → PMF ℝ :=
  fun κ => (X κ).map (· + ε κ)

/-- Shifting the tested side up is shifting the reference down. -/
theorem aheadProb_map_add_left (X Y : PMF ℝ) (e : ℝ) (m : ℕ) :
    aheadProb (X.map (· + e)) Y m = aheadProb X (Y.map (· + -e)) m := by
  rw [aheadProb_eq_bind, aheadProb_eq_bind, sampleSum_map_add_const, sampleSum_map_add_const]
  have hlaw : ((sampleSum X m).map (· + m * e)).bind
        (fun s => (sampleSum Y m).map fun t => decide (t < s)) =
      (sampleSum X m).bind
        (fun s => ((sampleSum Y m).map (· + m * -e)).map fun t => decide (t < s)) := by
    rw [PMF.bind_map]
    congr 1
    funext s
    rw [Function.comp_apply, PMF.map_comp]
    congr 1
    funext t
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr ⟨fun h => by linarith, fun h => by linarith⟩
  rw [hlaw]

/-- Shifting the reference up is shifting the tested side down. -/
theorem aheadProb_map_add_right (X Y : PMF ℝ) (e : ℝ) (m : ℕ) :
    aheadProb Y (X.map (· + e)) m = aheadProb (Y.map (· + -e)) X m := by
  rw [aheadProb_eq_bind, aheadProb_eq_bind, sampleSum_map_add_const, sampleSum_map_add_const]
  have hlaw : (sampleSum Y m).bind
        (fun s => ((sampleSum X m).map (· + m * e)).map fun t => decide (t < s)) =
      ((sampleSum Y m).map (· + m * -e)).bind
        (fun s => (sampleSum X m).map fun t => decide (t < s)) := by
    rw [PMF.bind_map]
    congr 1
    funext s
    rw [Function.comp_apply, PMF.map_comp]
    congr 1
    funext t
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr ⟨fun h => by linarith, fun h => by linarith⟩
  rw [hlaw]

/-- Indistinguishability by the mean tests against the reference shifted down
is indistinguishability of the shifted ensembles by the mean tests against the
reference. -/
theorem MeanTestIndistinguishable.shift {Y X X' : ℕ → PMF ℝ} (ε : ℕ → ℝ)
    (h : MeanTestIndistinguishable (shiftEnsemble (fun κ => -ε κ) Y) X X') :
    MeanTestIndistinguishable Y (shiftEnsemble ε X) (shiftEnsemble ε X') := by
  intro d
  obtain ⟨hbeat, hbeaten⟩ := h d
  constructor
  · simpa only [shiftEnsemble, aheadProb_map_add_left] using hbeat
  · simpa only [shiftEnsemble, aheadProb_map_add_right] using hbeaten

/-! ## Positive affine maps of both sides -/

/-- Scaling both sides by a positive factor leaves the ahead probability unchanged. -/
theorem aheadProb_map_mul {a : ℝ} (ha : 0 < a) (X Y : PMF ℝ) (m : ℕ) :
    aheadProb (X.map (a * ·)) (Y.map (a * ·)) m = aheadProb X Y m := by
  rw [aheadProb_eq_bind, aheadProb_eq_bind, sampleSum_map_mul, sampleSum_map_mul, PMF.bind_map]
  congr 3
  funext s
  rw [Function.comp_apply, PMF.map_comp]
  congr 1
  funext t
  simp only [Function.comp_apply, mul_lt_mul_iff_right₀ ha]

/-- Shifting both sides by the same amount leaves the ahead probability
unchanged. -/
theorem aheadProb_map_add (X Y : PMF ℝ) (e : ℝ) (m : ℕ) :
    aheadProb (X.map (· + e)) (Y.map (· + e)) m = aheadProb X Y m := by
  rw [aheadProb_map_add_left, PMF.map_comp]
  have hid : ((· + -e) ∘ (· + e) : ℝ → ℝ) = id := by
    funext x
    simp
  rw [hid, PMF.map_id]

/-- The gap is invariant under a common increasing affine map of payoffs. -/
theorem meanComparisonGap_map_affine {a : ℝ} (ha : 0 < a) (b : ℝ) (X Y : PMF ℝ) (m : ℕ) :
    meanComparisonGap (X.map fun x => a * x + b) (Y.map fun x => a * x + b) m =
      meanComparisonGap X Y m := by
  have hsplit : ∀ Z : PMF ℝ, Z.map (fun x => a * x + b) = (Z.map (a * ·)).map (· + b) :=
    fun Z => by rw [PMF.map_comp]; rfl
  rw [hsplit, hsplit, meanComparisonGap_eq_aheadProb_sub, meanComparisonGap_eq_aheadProb_sub,
    aheadProb_map_add, aheadProb_map_add, aheadProb_map_mul ha, aheadProb_map_mul ha]

/-- **Computational mean dominance is invariant under per-size positive affine
rescaling** of both ensembles. -/
theorem computationallyMeanDominates_map_affine {a : ℕ → ℝ} (ha : ∀ κ, 0 < a κ) (b : ℕ → ℝ)
    (X Y : ℕ → PMF ℝ) :
    ComputationallyMeanDominates (fun κ => (X κ).map fun x => a κ * x + b κ)
        (fun κ => (Y κ).map fun x => a κ * x + b κ) ↔
      ComputationallyMeanDominates X Y := by
  simp only [ComputationallyMeanDominates, meanComparisonGap_map_affine (ha _)]

/-! ## Point masses -/

/-- Sure payoffs are ahead exactly when larger. -/
theorem aheadProb_pure (x y : ℝ) (m : ℕ) :
    aheadProb (PMF.pure x) (PMF.pure y) m = if (m : ℝ) * y < m * x then 1 else 0 := by
  rw [aheadProb_eq_bind, sampleSum_pure, sampleSum_pure, PMF.pure_bind, PMF.pure_map]
  by_cases h : (m : ℝ) * y < m * x <;> simp [h]

/-- A sure payoff falls behind a larger one with certainty. -/
theorem meanComparisonGap_pure_of_lt {x y : ℝ} (hxy : x < y) {m : ℕ} (hm : 1 ≤ m) :
    meanComparisonGap (PMF.pure x) (PMF.pure y) m = 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlt : (m : ℝ) * x < m * y := mul_lt_mul_of_pos_left hxy hmpos
  rw [meanComparisonGap_eq_aheadProb_sub, aheadProb_pure, aheadProb_pure]
  simp only [hlt, not_lt.mpr hlt.le, ↓reduceIte]
  norm_num

end GameTheory.Math.Probability
