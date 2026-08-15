/-
# Finite matrix-game values

A finite real matrix is presented through the canonical deterministic
`GameForm`, mixed extension, and saddle-point theorem.  This adapter is enough
to select its value and prove that the value is nonexpansive in the entries;
there is no parallel simplex or equilibrium API.
-/

import GameTheory.Analysis.Minimax
import GameTheory.Core.MatrixGame

noncomputable section

namespace GameTheory.MatrixGame

open GameTheory GameTheory.Math.Probability

universe u

section Value

variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

private instance actionFintype :
    ∀ i, Fintype ((form I J).sig.Strategy i) :=
  Fin.cases
    (inferInstanceAs (Fintype I))
    (fun i => Fin.cases
      (inferInstanceAs (Fintype J))
      (fun k : Fin 0 => k.elim0) i)

private instance actionNonempty :
    ∀ i, Nonempty ((form I J).sig.Strategy i) :=
  Fin.cases
    (inferInstanceAs (Nonempty I))
    (fun i => Fin.cases
      (inferInstanceAs (Nonempty J))
      (fun k : Fin 0 => k.elim0) i)

/-- The value selected from the existing finite minimax theorem. -/
noncomputable def value (A : I → J → ℝ) : ℝ :=
  Classical.choose
    (exists_value (F := form I J) (utility A) (utility_isZeroSum A))

/-- A saddle profile witnessing `value`. -/
noncomputable def valueProfile (A : I → J → ℝ) :
    Profile (form I J).sig.mixed :=
  Classical.choose
    (Classical.choose_spec
      (exists_value (F := form I J) (utility A) (utility_isZeroSum A)))

private theorem value_spec (A : I → J → ℝ) :
    (∀ row : FinDist I,
        expectedUtility (utility A) 0
          ((form I J).mixed.play (Profile.update (valueProfile A) 0 row)) ≤
            value A) ∧
      (∀ col : FinDist J,
        value A ≤
          expectedUtility (utility A) 0
            ((form I J).mixed.play
              (Profile.update (valueProfile A) 1 col))) := by
  have hspec := Classical.choose_spec
    (Classical.choose_spec
      (exists_value (F := form I J) (utility A) (utility_isZeroSum A)))
  exact ⟨hspec.1, hspec.2.1⟩

/-- The selected saddle profile realizes the selected matrix value. -/
theorem valueProfile_expectedUtility (A : I → J → ℝ) :
    expectedUtility (utility A) 0
        ((form I J).mixed.play (valueProfile A)) = value A := by
  apply le_antisymm
  · simpa using (value_spec A).1 (valueProfile A 0)
  · simpa using (value_spec A).2 (valueProfile A 1)

/-- The selected profile is a saddle point in the canonical mixed extension. -/
theorem valueProfile_isSaddlePoint (A : I → J → ℝ) :
    IsSaddlePoint (F := form I J) (utility A) (valueProfile A) := by
  refine ⟨fun row => ?_, fun col => ?_⟩
  · exact (value_spec A).1 row |>.trans_eq
      (valueProfile_expectedUtility A).symm
  · exact (valueProfile_expectedUtility A).le.trans ((value_spec A).2 col)

/-- The row component of the selected value profile. -/
noncomputable def valueRow (A : I → J → ℝ) : FinDist I :=
  valueProfile A 0

/-- The column component of the selected value profile. -/
noncomputable def valueColumn (A : I → J → ℝ) : FinDist J :=
  valueProfile A 1

theorem mixedProfile_valueProfile (A : I → J → ℝ) :
    mixedProfile (valueRow A) (valueColumn A) = valueProfile A := by
  funext player
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) player with rfl | rfl
  · rfl
  · rfl

/-- The selected row and column realize the selected matrix value. -/
theorem expectedPayoff_valueProfile (A : I → J → ℝ) :
    expectedPayoff A (valueRow A) (valueColumn A) = value A := by
  rw [expectedPayoff, mixedProfile_valueProfile]
  exact valueProfile_expectedUtility A

/-- The selected row guarantees the matrix value against every column. -/
theorem valueRow_guarantees (A : I → J → ℝ) :
    RowGuarantees A (valueRow A) (value A) := by
  intro col
  have h := (value_spec A).2 col
  rw [← mixedProfile_valueProfile A, mixedProfile_update_one] at h
  simpa only [expectedPayoff] using h

/-- The selected column caps the row payoff at the matrix value. -/
theorem valueColumn_caps (A : I → J → ℝ) :
    ColumnCaps A (valueColumn A) (value A) := by
  intro row
  have h := (value_spec A).1 row
  rw [← mixedProfile_valueProfile A, mixedProfile_update_zero] at h
  simpa only [expectedPayoff] using h

/-- Any saddle point realizes the selected matrix value. -/
theorem expectedPayoff_eq_value_of_isSaddlePoint (A : I → J → ℝ)
    {row : FinDist I} {col : FinDist J}
    (hsaddle : IsSaddlePoint (F := form I J) (utility A)
      (mixedProfile row col)) :
    expectedPayoff A row col = value A := by
  calc
    expectedPayoff A row col =
        expectedUtility (utility A) 0
          ((form I J).mixed.play (mixedProfile row col)) := rfl
    _ = expectedUtility (utility A) 0
          ((form I J).mixed.play (valueProfile A)) :=
      hsaddle.value_eq (valueProfile_isSaddlePoint A)
    _ = value A := valueProfile_expectedUtility A

/-- If a row and a column secure the same scalar from opposite sides, that
scalar is the matrix value. -/
theorem common_guarantee_eq_value (A : I → J → ℝ) {w : ℝ}
    (hrow : IsRowGuarantee A w) (hcol : IsColumnCap A w) :
    w = value A := by
  obtain ⟨row, hrow⟩ := hrow
  obtain ⟨col, hcol⟩ := hcol
  apply le_antisymm
  · exact (hrow (valueColumn A)).trans (valueColumn_caps A row)
  · exact (valueRow_guarantees A col).trans (hcol (valueRow A))

/-- Mixed rows that guarantee the selected value. -/
def optimalRowStrategies (A : I → J → ℝ) : Set (FinDist I) :=
  {row | RowGuarantees A row (value A)}

/-- Mixed columns that cap the row payoff at the selected value. -/
def optimalColumnStrategies (A : I → J → ℝ) : Set (FinDist J) :=
  {col | ColumnCaps A col (value A)}

theorem mem_optimalRowStrategies_iff (A : I → J → ℝ) (row : FinDist I) :
    row ∈ optimalRowStrategies A ↔
      ∀ col : FinDist J, value A ≤ expectedPayoff A row col :=
  Iff.rfl

theorem mem_optimalColumnStrategies_iff (A : I → J → ℝ) (col : FinDist J) :
    col ∈ optimalColumnStrategies A ↔
      ∀ row : FinDist I, expectedPayoff A row col ≤ value A :=
  Iff.rfl

/-- A row/column pair is optimal exactly when its canonical mixed profile is a
saddle point. -/
theorem optimal_pairs_iff_isSaddlePoint (A : I → J → ℝ)
    (row : FinDist I) (col : FinDist J) :
    row ∈ optimalRowStrategies A ∧ col ∈ optimalColumnStrategies A ↔
      IsSaddlePoint (F := form I J) (utility A) (mixedProfile row col) := by
  constructor
  · rintro ⟨hrow, hcol⟩
    have hrow' : RowGuarantees A row (value A) := hrow
    have hcol' : ColumnCaps A col (value A) := hcol
    have hp : expectedPayoff A row col = value A :=
      le_antisymm (hcol' row) (hrow' col)
    rw [isSaddlePoint_iff_guarantees_caps]
    simpa only [hp] using And.intro hrow' hcol'
  · intro hsaddle
    have hp := expectedPayoff_eq_value_of_isSaddlePoint A hsaddle
    rw [isSaddlePoint_iff_guarantees_caps] at hsaddle
    have hrow : RowGuarantees A row (value A) := by
      simpa only [hp] using hsaddle.1
    have hcol : ColumnCaps A col (value A) := by
      simpa only [hp] using hsaddle.2
    exact ⟨hrow, hcol⟩

/-- Matrix-optimal pairs are exactly canonical mixed Nash equilibria. -/
theorem optimal_pairs_iff_isNash (A : I → J → ℝ)
    (row : FinDist I) (col : FinDist J) :
    row ∈ optimalRowStrategies A ∧ col ∈ optimalColumnStrategies A ↔
      IsNash (form I J).mixed (euPreference (utility A))
        (mixedProfile row col) := by
  rw [isNash_iff_isSaddlePoint (utility_isZeroSum A)]
  exact optimal_pairs_iff_isSaddlePoint A row col

/-- Any canonical mixed Nash profile realizes the selected matrix value. -/
theorem expectedPayoff_eq_value_of_isNash (A : I → J → ℝ)
    {row : FinDist I} {col : FinDist J}
    (hnash : IsNash (form I J).mixed (euPreference (utility A))
      (mixedProfile row col)) :
    expectedPayoff A row col = value A :=
  expectedPayoff_eq_value_of_isSaddlePoint A
    ((isNash_iff_isSaddlePoint (utility_isZeroSum A)).1 hnash)

/-- At least one mixed row guarantees the matrix value. -/
theorem optimalRowStrategies_nonempty (A : I → J → ℝ) :
    (optimalRowStrategies A).Nonempty :=
  ⟨valueRow A, valueRow_guarantees A⟩

/-- At least one mixed column caps the row payoff at the matrix value. -/
theorem optimalColumnStrategies_nonempty (A : I → J → ℝ) :
    (optimalColumnStrategies A).Nonempty :=
  ⟨valueColumn A, valueColumn_caps A⟩

omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
private theorem expected_mono {A B : I → J → ℝ} {δ : ℝ}
    (h : ∀ i j, A i j ≤ B i j + δ) (law : FinDist (I × J)) :
    expectedUtility (utility A) 0 law ≤
      expectedUtility (utility B) 0 law + δ := by
  calc
    expectedUtility (utility A) 0 law
        ≤ law.expect (fun outcome => utility B outcome 0 + δ) :=
      FinDist.expect_mono fun outcome _ => h outcome.1 outcome.2
    _ = expectedUtility (utility B) 0 law + δ := by
      rw [FinDist.expect_add, FinDist.expect_const]
      rfl

/-- A pointwise additive perturbation changes the matrix value by at most the
same amount in the corresponding direction. -/
theorem value_le_of_entrywise_le {A B : I → J → ℝ} {δ : ℝ}
    (h : ∀ i j, A i j ≤ B i j + δ) : value A ≤ value B + δ := by
  let hybrid := Profile.update (valueProfile A) 1 (valueProfile B 1)
  have hA := (value_spec A).2 (valueProfile B 1)
  have hAB := expected_mono h ((form I J).mixed.play hybrid)
  have hB := (value_spec B).1 (valueProfile A 0)
  have hhybrid : hybrid =
      Profile.update (valueProfile B) 0 (valueProfile A 0) :=
    update_one_eq_update_zero (valueProfile A) (valueProfile B)
  rw [show Profile.update (valueProfile A) 1 (valueProfile B 1) =
      Profile.update (valueProfile B) 0 (valueProfile A 0) from
    update_one_eq_update_zero (valueProfile A) (valueProfile B)] at hA
  rw [hhybrid] at hAB
  exact hA.trans (hAB.trans (by linarith [hB]))

/-- The finite matrix-game value is nonexpansive in its entries. -/
theorem abs_value_sub_le_of_entrywise_abs_le {A B : I → J → ℝ} {δ : ℝ}
    (h : ∀ i j, |A i j - B i j| ≤ δ) : |value A - value B| ≤ δ := by
  rw [abs_sub_le_iff]
  constructor
  · have hAB : ∀ i j, A i j ≤ B i j + δ := by
      intro i j
      have := (abs_le.mp (h i j)).2
      linarith
    have := value_le_of_entrywise_le hAB
    linarith
  · have hBA : ∀ i j, B i j ≤ A i j + δ := by
      intro i j
      have := (abs_le.mp (h i j)).1
      linarith
    have := value_le_of_entrywise_le hBA
    linarith

end Value

end GameTheory.MatrixGame
