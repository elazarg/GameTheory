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

omit [Nonempty I] [Nonempty J] in
private noncomputable def saddleProfile (A : I → J → ℝ) :
    Profile (form I J).sig.mixed :=
  Classical.choose (exists_isSaddlePoint (F := form I J) (utility A)
    (utility_isZeroSum A) (hasIntegrableUtility A))

private theorem saddleProfile_isSaddlePoint (A : I → J → ℝ) :
    IsSaddlePoint (F := form I J) (utility A) (saddleProfile A) :=
  Classical.choose_spec (exists_isSaddlePoint (F := form I J) (utility A)
    (utility_isZeroSum A) (hasIntegrableUtility A))

omit [Nonempty I] [Nonempty J] in
/-- A finite matrix integrates every outcome law. -/
private theorem lawIntegrable (A : I → J → ℝ) (who : Fin 2)
    (law : PMF (form I J).sig.Outcome) : UtilityIntegrable (utility A) who law :=
  payoffIntegrable_of_finite law (fun outcome => utility A outcome who)

private theorem saddleProfile_spec (A : I → J → ℝ) :
    (∀ row : PMF I,
      UtilityIntegrable (utility A) 0
          ((form I J).mixed.play
            (Profile.update (saddleProfile A) 0 row)) ∧
        expectedUtility (utility A) 0
          ((form I J).mixed.play
            (Profile.update (saddleProfile A) 0 row)) ≤
          expectedUtility (utility A) 0
            ((form I J).mixed.play (saddleProfile A))) ∧
    (∀ col : PMF J,
      UtilityIntegrable (utility A) 0
          ((form I J).mixed.play
            (Profile.update (saddleProfile A) 1 col)) ∧
        expectedUtility (utility A) 0
          ((form I J).mixed.play (saddleProfile A)) ≤
          expectedUtility (utility A) 0
            ((form I J).mixed.play
              (Profile.update (saddleProfile A) 1 col))) :=
  ⟨fun row => ⟨lawIntegrable A 0 _, (euPreference_iff _ _ _ _ (lawIntegrable A 0 _)
      (lawIntegrable A 0 _)).1 ((saddleProfile_isSaddlePoint A).1 row)⟩,
    fun col => ⟨lawIntegrable A 0 _, (euPreference_iff _ _ _ _ (lawIntegrable A 0 _)
      (lawIntegrable A 0 _)).1 ((saddleProfile_isSaddlePoint A).2 col)⟩⟩

omit [Nonempty I] [Nonempty J] in
/-- For a finite matrix, row security is the real comparison against every
column. -/
theorem rowGuarantees_iff (A : I → J → ℝ) (row : PMF I) (v : ℝ) :
    RowGuarantees A row v ↔ ∀ col : PMF J, v ≤ expectedPayoff A row col := by
  refine forall_congr' fun col => ?_
  rw [extendedExpectedUtility_eq (lawIntegrable A 0 _), EReal.coe_le_coe_iff]
  exact ⟨fun h => h.2, fun h => ⟨(lawIntegrable A 0 _).hasExpectation, h⟩⟩

omit [Nonempty I] [Nonempty J] in
/-- For a finite matrix, column capping is the real comparison against every
row. -/
theorem columnCaps_iff (A : I → J → ℝ) (col : PMF J) (v : ℝ) :
    ColumnCaps A col v ↔ ∀ row : PMF I, expectedPayoff A row col ≤ v := by
  refine forall_congr' fun row => ?_
  rw [extendedExpectedUtility_eq (lawIntegrable A 0 _), EReal.coe_le_coe_iff]
  exact ⟨fun h => h.2, fun h => ⟨(lawIntegrable A 0 _).hasExpectation, h⟩⟩

/-- A saddle profile witnessing `value`. -/
noncomputable def valueProfile (A : I → J → ℝ) :
    Profile (form I J).sig.mixed := saddleProfile A

/-- The value selected from the finite minimax theorem. -/
noncomputable def value (A : I → J → ℝ) : ℝ :=
  expectedUtility (utility A) 0
    ((form I J).mixed.play (valueProfile A))

private theorem value_spec (A : I → J → ℝ) :
    (∀ row : PMF I,
      UtilityIntegrable (utility A) 0
          ((form I J).mixed.play (Profile.update (valueProfile A) 0 row)) ∧
        expectedUtility (utility A) 0
          ((form I J).mixed.play (Profile.update (valueProfile A) 0 row)) ≤
          value A) ∧
    (∀ col : PMF J,
      UtilityIntegrable (utility A) 0
          ((form I J).mixed.play (Profile.update (valueProfile A) 1 col)) ∧
        value A ≤ expectedUtility (utility A) 0
          ((form I J).mixed.play (Profile.update (valueProfile A) 1 col))) := by
  exact saddleProfile_spec A

/-- The selected saddle profile realizes the selected matrix value. -/
theorem valueProfile_expectedUtility (A : I → J → ℝ) :
    expectedUtility (utility A) 0
        ((form I J).mixed.play (valueProfile A))
         = value A := rfl

/-- The selected profile is a saddle point in the canonical mixed extension. -/
theorem valueProfile_isSaddlePoint (A : I → J → ℝ) :
    IsSaddlePoint (F := form I J) (utility A) (valueProfile A) := by
  exact saddleProfile_isSaddlePoint A

/-- The row component of the selected value profile. -/
noncomputable def valueRow (A : I → J → ℝ) : PMF I :=
  valueProfile A 0

/-- The column component of the selected value profile. -/
noncomputable def valueColumn (A : I → J → ℝ) : PMF J :=
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
  unfold expectedPayoff
  have hlaw :
      (form I J).mixed.play (mixedProfile (valueRow A) (valueColumn A)) =
        (form I J).mixed.play (valueProfile A) :=
    congrArg ((form I J).mixed.play) (mixedProfile_valueProfile A)
  exact (expectedUtility_congr_law (utility A) 0 hlaw
    ).trans (valueProfile_expectedUtility A)

/-- The selected row guarantees the matrix value against every column. -/
theorem valueRow_guarantees (A : I → J → ℝ) :
    RowGuarantees A (valueRow A) (value A) := by
  rw [rowGuarantees_iff]
  intro col
  have h := (value_spec A).2 col
  rw [← mixedProfile_valueProfile A, mixedProfile_update_one] at h
  simpa only [expectedPayoff] using h.2

/-- The selected column caps the row payoff at the matrix value. -/
theorem valueColumn_caps (A : I → J → ℝ) :
    ColumnCaps A (valueColumn A) (value A) := by
  rw [columnCaps_iff]
  intro row
  have h := (value_spec A).1 row
  rw [← mixedProfile_valueProfile A, mixedProfile_update_zero] at h
  simpa only [expectedPayoff] using h.2

/-- Any saddle point realizes the selected matrix value. -/
theorem expectedPayoff_eq_value_of_isSaddlePoint (A : I → J → ℝ)
    {row : PMF I} {col : PMF J}
    (hsaddle : IsSaddlePoint (F := form I J) (utility A)
      (mixedProfile row col)) :
    expectedPayoff A row col = value A := by
  obtain ⟨-, -, heq⟩ :=
    IsSaddlePoint.value_eq hsaddle (valueProfile_isSaddlePoint A)
  rw [extendedExpectedUtility_eq (lawIntegrable A 0 _),
    extendedExpectedUtility_eq (lawIntegrable A 0 _), EReal.coe_eq_coe_iff] at heq
  simpa only [expectedPayoff, value,
    valueProfile, saddleProfile] using heq

/-- If a row and a column secure the same scalar from opposite sides, that
scalar is the matrix value. -/
theorem common_guarantee_eq_value (A : I → J → ℝ) {w : ℝ}
    (hrow : IsRowGuarantee A w) (hcol : IsColumnCap A w) :
    w = value A := by
  obtain ⟨row, hrow⟩ := hrow
  obtain ⟨col, hcol⟩ := hcol
  rw [rowGuarantees_iff] at hrow
  rw [columnCaps_iff] at hcol
  apply le_antisymm
  · exact (hrow (valueColumn A)).trans ((columnCaps_iff A _ _).1 (valueColumn_caps A) row)
  · exact ((rowGuarantees_iff A _ _).1 (valueRow_guarantees A) col).trans (hcol (valueRow A))

/-- Mixed rows that guarantee the selected value. -/
def optimalRowStrategies (A : I → J → ℝ) : Set (PMF I) :=
  {row | RowGuarantees A row (value A)}

/-- Mixed columns that cap the row payoff at the selected value. -/
def optimalColumnStrategies (A : I → J → ℝ) : Set (PMF J) :=
  {col | ColumnCaps A col (value A)}

theorem mem_optimalRowStrategies_iff (A : I → J → ℝ) (row : PMF I) :
    row ∈ optimalRowStrategies A ↔
      ∀ col : PMF J, value A ≤ expectedPayoff A row col :=
  rowGuarantees_iff A row (value A)

theorem mem_optimalColumnStrategies_iff (A : I → J → ℝ) (col : PMF J) :
    col ∈ optimalColumnStrategies A ↔
      ∀ row : PMF I, expectedPayoff A row col ≤ value A :=
  columnCaps_iff A col (value A)

/-- A row/column pair is optimal exactly when its canonical mixed profile is a
saddle point. -/
theorem optimal_pairs_iff_isSaddlePoint (A : I → J → ℝ)
    (row : PMF I) (col : PMF J) :
    row ∈ optimalRowStrategies A ∧ col ∈ optimalColumnStrategies A ↔
      IsSaddlePoint (F := form I J) (utility A) (mixedProfile row col) := by
  constructor
  · rintro ⟨hrow, hcol⟩
    rw [mem_optimalRowStrategies_iff] at hrow
    rw [mem_optimalColumnStrategies_iff] at hcol
    have hp : expectedPayoff A row col = value A := le_antisymm (hcol row) (hrow col)
    rw [isSaddlePoint_iff_guarantees_caps A row col (lawIntegrable A 0 _),
      rowGuarantees_iff, columnCaps_iff, hp]
    exact ⟨hrow, hcol⟩
  · intro hsaddle
    have hp := expectedPayoff_eq_value_of_isSaddlePoint A hsaddle
    rw [isSaddlePoint_iff_guarantees_caps A row col (lawIntegrable A 0 _),
      rowGuarantees_iff, columnCaps_iff, hp] at hsaddle
    exact ⟨(mem_optimalRowStrategies_iff A row).2 hsaddle.1,
      (mem_optimalColumnStrategies_iff A col).2 hsaddle.2⟩

/-- Matrix-optimal pairs are exactly canonical mixed Nash equilibria. -/
theorem optimal_pairs_iff_isNash (A : I → J → ℝ)
    (row : PMF I) (col : PMF J) :
    row ∈ optimalRowStrategies A ∧ col ∈ optimalColumnStrategies A ↔
      IsNash (form I J).mixed (euPreference (utility A))
        (mixedProfile row col) := by
  rw [isNash_iff_isSaddlePoint (utility_isZeroSum A)]
  exact optimal_pairs_iff_isSaddlePoint A row col

/-- Any canonical mixed Nash profile realizes the selected matrix value. -/
theorem expectedPayoff_eq_value_of_isNash (A : I → J → ℝ)
    {row : PMF I} {col : PMF J}
    (hnash : IsNash (form I J).mixed (euPreference (utility A))
      (mixedProfile row col)) :
    expectedPayoff A row col = value A :=
  expectedPayoff_eq_value_of_isSaddlePoint A
    ((isNash_iff_isSaddlePoint (utility_isZeroSum A)).1 hnash)

/-- Correlating the players' mixed strategies cannot move a matrix game off its
value: every coarse correlated equilibrium of the mixed extension gives the row
player exactly the value. -/
theorem expectedUtility_eq_value_of_isCoarseCorrelatedEq (A : I → J → ℝ)
    {law : PMF (Profile (form I J).sig.mixed)}
    (hcce : IsCoarseCorrelatedEq (form I J).mixed (euPreference (utility A)) law) :
    expectedUtility (utility A) 0 ((form I J).mixed.outcomeLaw law)
         = value A := by
  have hnash := (valueProfile_isSaddlePoint A).isNash (utility_isZeroSum A)
  have hvalue := hcce.extendedExpectedUtility_eq_of_zeroSum (utility_isZeroSum A) hnash 0
  rw [extendedExpectedUtility_eq (lawIntegrable A 0 _),
    extendedExpectedUtility_eq (lawIntegrable A 0 _), EReal.coe_eq_coe_iff] at hvalue
  exact hvalue

/-- At least one mixed row guarantees the matrix value. -/
theorem optimalRowStrategies_nonempty (A : I → J → ℝ) :
    (optimalRowStrategies A).Nonempty :=
  ⟨valueRow A, valueRow_guarantees A⟩

/-- At least one mixed column caps the row payoff at the matrix value. -/
theorem optimalColumnStrategies_nonempty (A : I → J → ℝ) :
    (optimalColumnStrategies A).Nonempty :=
  ⟨valueColumn A, valueColumn_caps A⟩

omit [Nonempty I] [Nonempty J] in
private theorem expected_mono {A B : I → J → ℝ} {δ : ℝ}
    (h : ∀ i j, A i j ≤ B i j + δ) (law : PMF (I × J)) :
    expectedUtility (utility A) 0 law ≤
      expectedUtility (utility B) 0 law
         + δ := by
  let fA : I × J → ℝ := fun outcome => A outcome.1 outcome.2
  let fB : I × J → ℝ := fun outcome => B outcome.1 outcome.2
  have hA : PayoffIntegrable law fA := payoffIntegrable_of_finite law fA
  have hB : PayoffIntegrable law fB := payoffIntegrable_of_finite law fB
  have hδ : PayoffIntegrable law (fun _ : I × J => δ) :=
    payoffIntegrable_constant law δ
  have hsum : PayoffIntegrable law (fun outcome => fB outcome + δ) :=
    payoffIntegrable_add hB hδ
  calc
    expectedUtility (utility A) 0 law
        ≤ expect law (fun outcome => fB outcome + δ) := by
      apply expect_mono (fun outcome _ => ?_) hA hsum
      exact h outcome.1 outcome.2
    _ = expectedUtility (utility B) 0 law + δ := by
      rw [expect_add hB hδ, expect_constant law δ]
      rfl

/-- A pointwise additive perturbation changes the matrix value by at most the
same amount in the corresponding direction. -/
theorem value_le_of_entrywise_le {A B : I → J → ℝ} {δ : ℝ}
    (h : ∀ i j, A i j ≤ B i j + δ) : value A ≤ value B + δ := by
  let hybrid := Profile.update (valueProfile A) 1 (valueProfile B 1)
  obtain ⟨hAguard, hA⟩ := (value_spec A).2 (valueProfile B 1)
  obtain ⟨hBguard, hB⟩ := (value_spec B).1 (valueProfile A 0)
  have hhybrid : hybrid =
      Profile.update (valueProfile B) 0 (valueProfile A 0) :=
    update_one_eq_update_zero (valueProfile A) (valueProfile B)
  let law := (form I J).mixed.play hybrid
  have hlawB : law = (form I J).mixed.play
      (Profile.update (valueProfile B) 0 (valueProfile A 0)) :=
    congrArg (form I J).mixed.play hhybrid
  have hBtransport := expectedUtility_congr_law (utility B) 0 hlawB
  have hB' : expectedUtility (utility B) 0 law ≤ value B := by
    rw [hBtransport]
    exact hB
  have hA' : value A ≤ expectedUtility (utility A) 0 law := by
    simpa only [law, hybrid] using hA
  exact (hA'.trans (expected_mono h law)).trans
    (by simpa only [add_comm] using add_le_add_right hB' δ)

/-- A constant matrix has that constant as its value. -/
theorem value_const (c : ℝ) : value (fun (_ : I) (_ : J) => c) = c :=
  expect_constant _ c

/-- An entrywise absolute bound also bounds the matrix value. -/
theorem abs_value_le_of_entrywise_abs_le {A : I → J → ℝ} {bound : ℝ}
    (h : ∀ i j, |A i j| ≤ bound) : |value A| ≤ bound :=
  expect_abs_le_of_bounded
    ((abs_nonneg _).trans (h (Classical.arbitrary I) (Classical.arbitrary J)))
    fun outcome => h outcome.1 outcome.2

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
