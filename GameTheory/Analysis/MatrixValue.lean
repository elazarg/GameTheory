/-
# Finite matrix-game values

A finite real matrix is presented through the canonical deterministic
`GameForm`, mixed extension, and saddle-point theorem.  This adapter is enough
to select its value and prove that the value is nonexpansive in the entries;
there is no parallel simplex or equilibrium API.
-/

import GameTheory.Analysis.Minimax

noncomputable section

namespace GameTheory.MatrixGame

open GameTheory Probability

universe u

/-- The dependent action family of a row/column matrix game. -/
abbrev Action (I J : Type u) : Fin 2 → Type u :=
  Fin.cons I (Fin.cons J fun k : Fin 0 => k.elim0)

set_option linter.checkUnivs false in
/-- A matrix game as the canonical deterministic game form. -/
@[reducible]
def form (I J : Type u) : GameForm (Fin 2) where
  sig :=
    { Strategy := Action I J
      Outcome := I × J }
  play profile := FinDist.pure (profile 0, profile 1)

/-- Turn the row payoff into a zero-sum two-player utility. -/
def utility {I J : Type u} (A : I → J → ℝ) : I × J → Fin 2 → ℝ :=
  fun outcome => Fin.cons (A outcome.1 outcome.2)
    (Fin.cons (-A outcome.1 outcome.2) fun k : Fin 0 => k.elim0)

@[simp]
theorem utility_zero {I J : Type u} (A : I → J → ℝ) (outcome : I × J) :
    utility A outcome 0 = A outcome.1 outcome.2 := rfl

@[simp]
theorem utility_one {I J : Type u} (A : I → J → ℝ) (outcome : I × J) :
    utility A outcome 1 = -A outcome.1 outcome.2 := rfl

theorem utility_isZeroSum {I J : Type u} (A : I → J → ℝ) :
    IsZeroSum (utility A) := by
  intro outcome
  rw [Fin.sum_univ_two]
  simp

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
