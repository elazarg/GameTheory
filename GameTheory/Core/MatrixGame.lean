/-
# Finite matrix-game semantics

Rectangular real matrices compile to the canonical deterministic `GameForm`.
Mixed row/column profiles, their expected payoff, and security predicates are
static and topology-free; existence and selected values remain in Analysis.
-/

import GameTheory.Core.ZeroSum

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

/-- Assemble independent row and column laws into the canonical mixed
profile. -/
def mixedProfile {I J : Type u} (row : FinDist I) (col : FinDist J) :
    Profile (form I J).sig.mixed :=
  Fin.cons row (Fin.cons col fun k : Fin 0 => k.elim0)

/-- Assemble one pure row and column into the canonical pure profile. -/
def pureProfile {I J : Type u} (row : I) (col : J) :
    Profile (form I J).sig :=
  Fin.cons row (Fin.cons col fun k : Fin 0 => k.elim0)

@[simp]
theorem pureProfile_zero {I J : Type u} (row : I) (col : J) :
    pureProfile row col 0 = row := rfl

@[simp]
theorem pureProfile_one {I J : Type u} (row : I) (col : J) :
    pureProfile row col 1 = col := rfl

@[simp]
theorem mixedProfile_zero {I J : Type u} (row : FinDist I) (col : FinDist J) :
    mixedProfile row col 0 = row := rfl

@[simp]
theorem mixedProfile_one {I J : Type u} (row : FinDist I) (col : FinDist J) :
    mixedProfile row col 1 = col := rfl

@[simp]
theorem mixedProfile_pure {I J : Type u} (row : I) (col : J) :
    mixedProfile (FinDist.pure row) (FinDist.pure col) =
      (form I J).purify (pureProfile row col) := by
  funext player
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) player with rfl | rfl
  · rfl
  · rfl

@[simp]
theorem mixedProfile_update_zero {I J : Type u}
    (row row' : FinDist I) (col : FinDist J) :
    Profile.update (mixedProfile row col) 0 row' = mixedProfile row' col := by
  funext player
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) player with rfl | rfl
  · simp
  · simp [mixedProfile]

@[simp]
theorem mixedProfile_update_one {I J : Type u}
    (row : FinDist I) (col col' : FinDist J) :
    Profile.update (mixedProfile row col) 1 col' = mixedProfile row col' := by
  funext player
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) player with rfl | rfl
  · simp [mixedProfile]
  · simp

/-- Expected payoff to the row player under independent mixed play. -/
def expectedPayoff {I J : Type u} (A : I → J → ℝ)
    (row : FinDist I) (col : FinDist J) : ℝ :=
  expectedUtility (utility A) 0
    ((form I J).mixed.play (mixedProfile row col))

theorem expectedUtility_zero_mixedProfile {I J : Type u}
    (A : I → J → ℝ) (row : FinDist I) (col : FinDist J) :
    expectedUtility (utility A) 0
        ((form I J).mixed.play (mixedProfile row col)) =
      expectedPayoff A row col :=
  rfl

theorem expectedUtility_one_mixedProfile {I J : Type u}
    (A : I → J → ℝ) (row : FinDist I) (col : FinDist J) :
    expectedUtility (utility A) 1
        ((form I J).mixed.play (mixedProfile row col)) =
      -expectedPayoff A row col := by
  exact (utility_isZeroSum A).expectedUtility_one _

/-- A mixed row guarantees payoff at least `v` against every mixed column. -/
def RowGuarantees {I J : Type u} (A : I → J → ℝ)
    (row : FinDist I) (v : ℝ) : Prop :=
  ∀ col : FinDist J, v ≤ expectedPayoff A row col

/-- A mixed column caps the row payoff at `v` against every mixed row. -/
def ColumnCaps {I J : Type u} (A : I → J → ℝ)
    (col : FinDist J) (v : ℝ) : Prop :=
  ∀ row : FinDist I, expectedPayoff A row col ≤ v

/-- Some mixed row guarantees `v`. -/
def IsRowGuarantee {I J : Type u} (A : I → J → ℝ) (v : ℝ) : Prop :=
  ∃ row : FinDist I, RowGuarantees A row v

/-- Some mixed column caps the row payoff at `v`. -/
def IsColumnCap {I J : Type u} (A : I → J → ℝ) (v : ℝ) : Prop :=
  ∃ col : FinDist J, ColumnCaps A col v

/-- The canonical saddle inequalities are exactly mutual row security and
column capping at the realized payoff. -/
theorem isSaddlePoint_iff_guarantees_caps {I J : Type u}
    (A : I → J → ℝ) (row : FinDist I) (col : FinDist J) :
    IsSaddlePoint (F := form I J) (utility A) (mixedProfile row col) ↔
      RowGuarantees A row (expectedPayoff A row col) ∧
        ColumnCaps A col (expectedPayoff A row col) := by
  constructor
  · intro hsaddle
    constructor
    · intro col'
      simpa only [expectedPayoff, mixedProfile_update_one] using hsaddle.2 col'
    · intro row'
      simpa only [expectedPayoff, mixedProfile_update_zero] using hsaddle.1 row'
  · rintro ⟨hrow, hcol⟩
    constructor
    · intro row'
      simpa only [expectedPayoff, mixedProfile_update_zero] using hcol row'
    · intro col'
      simpa only [expectedPayoff, mixedProfile_update_one] using hrow col'

end GameTheory.MatrixGame
