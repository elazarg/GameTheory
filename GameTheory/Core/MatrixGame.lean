/-
# Matrix-game semantics

Rectangular real matrices compile to the canonical deterministic `GameForm`.
Mixed row/column profiles, their expected payoff, and security predicates are
static and topology-free; existence and selected values remain in Analysis.
-/

import GameTheory.Core.ZeroSum

noncomputable section

namespace GameTheory.MatrixGame

open GameTheory GameTheory.Math.Probability

universe u

/-- The dependent action family of a row/column matrix game. -/
abbrev Action (I J : Type u) : Fin 2 → Type u
  | 0 => I
  | 1 => J

/-- A matrix game as the canonical deterministic game form. -/
@[reducible]
def form (I J : Type u) : GameForm (Fin 2) where
  sig :=
    { Strategy := Action I J
      Outcome := I × J }
  play profile := PMF.pure (profile 0, profile 1)

-- The row and column carriers remain universe-polymorphic even though the linter
-- sees their universe only through the resulting bundled form.

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

/-- A payoff matrix as a canonical two-player zero-sum utility game. -/
@[reducible]
def utilityGame {I J : Type u} (A : I → J → ℝ) : UtilityGame (Fin 2) where
  form := form I J
  utility := utility A

/-- Row marginal of a possibly correlated law over pure matrix profiles. -/
def rowMarginal {I J : Type u}
    (statusQuo : PMF (Profile (form I J).sig)) : PMF I :=
  statusQuo.map fun profile => profile 0

/-- Column marginal of a possibly correlated law over pure matrix profiles. -/
def columnMarginal {I J : Type u}
    (statusQuo : PMF (Profile (form I J).sig)) : PMF J :=
  statusQuo.map fun profile => profile 1

/-- The outcome law of a correlated matrix trace is its payoff-pair image. -/
theorem correlatedPlay_eq_map {I J : Type u}
    (statusQuo : PMF (Profile (form I J).sig)) :
    (form I J).outcomeLaw statusQuo =
      statusQuo.map (fun profile => (profile 0, profile 1)) := by
  exact (show statusQuo.bind
    (PMF.pure ∘ fun profile => (profile 0, profile 1)) = _ from
    PMF.bind_pure_comp _ _)

/-- A fixed row replacement samples only the original column marginal. -/
theorem rowReplacement_eq_map {I J : Type u}
    (statusQuo : PMF (Profile (form I J).sig)) (row : I) :
    (statusQuo.bind fun profile =>
      (form I J).play (Profile.update profile 0 row)) =
        (columnMarginal statusQuo).map (fun col => (row, col)) := by
  calc
    _ = statusQuo.map (fun profile => (row, profile 1)) := by
      exact (show statusQuo.bind
        (PMF.pure ∘ fun profile => (row, profile 1)) = _ from
        PMF.bind_pure_comp _ _)
    _ = (columnMarginal statusQuo).map (fun col => (row, col)) := by
      rw [columnMarginal, PMF.map_comp]
      rfl

/-- A fixed column replacement samples only the original row marginal. -/
theorem columnReplacement_eq_map {I J : Type u}
    (statusQuo : PMF (Profile (form I J).sig)) (col : J) :
    (statusQuo.bind fun profile =>
      (form I J).play (Profile.update profile 1 col)) =
        (rowMarginal statusQuo).map (fun row => (row, col)) := by
  calc
    _ = statusQuo.map (fun profile => (profile 0, col)) := by
      exact (show statusQuo.bind
        (PMF.pure ∘ fun profile => (profile 0, col)) = _ from
        PMF.bind_pure_comp _ _)
    _ = (rowMarginal statusQuo).map (fun row => (row, col)) := by
      rw [rowMarginal, PMF.map_comp]
      rfl

/-- Integration of correlated incumbent payoff for the row player. -/
theorem correlatedIntegrable_zero {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig))
    (h : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1))) :
    UtilityIntegrable (utility A) 0 ((form I J).outcomeLaw statusQuo) := by
  rw [correlatedPlay_eq_map]
  exact (payoffIntegrable_map_iff _ _ _).2 h

/-- Integration of correlated incumbent payoff for the column player. -/
theorem correlatedIntegrable_one {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig))
    (h : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1))) :
    UtilityIntegrable (utility A) 1 ((form I J).outcomeLaw statusQuo) := by
  rw [correlatedPlay_eq_map]
  exact (payoffIntegrable_map_iff _ _ _).2 (payoffIntegrable_neg h)

/-- Integration of the actual pure-row replacement law. -/
theorem rowReplacementIntegrable {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (row : I)
    (h : PayoffIntegrable (columnMarginal statusQuo) (A row)) :
    UtilityIntegrable (utility A) 0
      (statusQuo.bind fun profile =>
        (form I J).play (Profile.update profile 0 row)) := by
  rw [rowReplacement_eq_map]
  exact (payoffIntegrable_map_iff _ _ _).2 h

/-- Integration of the actual pure-column replacement law. -/
theorem columnReplacementIntegrable {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (col : J)
    (h : PayoffIntegrable (rowMarginal statusQuo)
      (fun row => A row col)) :
    UtilityIntegrable (utility A) 1
      (statusQuo.bind fun profile =>
        (form I J).play (Profile.update profile 1 col)) := by
  rw [columnReplacement_eq_map]
  exact (payoffIntegrable_map_iff _ _ _).2 (payoffIntegrable_neg h)

/-- Every deterministic matrix profile has integrable utility, without any
finiteness assumptions on its action carriers. -/
theorem hasIntegrableUtility {I J : Type u} (A : I → J → ℝ) :
    (form I J).HasIntegrableUtility (utility A) := by
  intro who profile
  exact payoffIntegrable_pure (profile 0, profile 1)
    (fun outcome => utility A outcome who)

/-- Assemble independent row and column laws into the canonical mixed
profile. -/
def mixedProfile {I J : Type u} (row : PMF I) (col : PMF J) :
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
theorem mixedProfile_zero {I J : Type u} (row : PMF I) (col : PMF J) :
    mixedProfile row col 0 = row := rfl

@[simp]
theorem mixedProfile_one {I J : Type u} (row : PMF I) (col : PMF J) :
    mixedProfile row col 1 = col := rfl

@[simp]
theorem mixedProfile_pure {I J : Type u} (row : I) (col : J) :
    mixedProfile (PMF.pure row) (PMF.pure col) =
      (form I J).purify (pureProfile row col) := by
  funext player
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) player with rfl | rfl
  · rfl
  · rfl

@[simp]
theorem mixedProfile_update_zero {I J : Type u}
    (row row' : PMF I) (col : PMF J) :
    Profile.update (mixedProfile row col) 0 row' = mixedProfile row' col := by
  funext player
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) player with rfl | rfl
  · rfl
  · rfl

@[simp]
theorem mixedProfile_update_one {I J : Type u}
    (row : PMF I) (col col' : PMF J) :
    Profile.update (mixedProfile row col) 1 col' = mixedProfile row col' := by
  funext player
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) player with rfl | rfl
  · rfl
  · rfl

/-- Expected payoff to the row player under independent mixed play. -/
def expectedPayoff {I J : Type u} (A : I → J → ℝ)
    (row : PMF I) (col : PMF J) : ℝ :=
  expectedUtility (utility A) 0
    ((form I J).mixed.play (mixedProfile row col))

/-- A fixed row leaves only the column draw random. -/
theorem mixed_play_pure_row {I J : Type u} (row : I) (col : PMF J) :
    (form I J).mixed.play (mixedProfile (PMF.pure row) col) =
      col.map (fun current => (row, current)) := by
  have hsame : Profile.update (mixedProfile (PMF.pure row) col) 1 col =
      mixedProfile (PMF.pure row) col := Profile.update_eq_self _ 1
  calc
    (form I J).mixed.play (mixedProfile (PMF.pure row) col) =
        col.bind (fun current =>
          (form I J).mixed.play
            (Profile.update (mixedProfile (PMF.pure row) col) 1
              (PMF.pure current))) := by
      rw [← hsame]
      exact GameForm.mixed_play_update (form I J)
        (mixedProfile (PMF.pure row) col) 1 col
    _ = col.map (fun current => (row, current)) := by
      have hpure (current : J) :
          (form I J).mixed.play
            (Profile.update (mixedProfile (PMF.pure row) col) 1
              (PMF.pure current)) = PMF.pure (row, current) := by
        rw [mixedProfile_update_one, mixedProfile_pure,
          GameForm.mixed_play_purify]
        rfl
      calc
        _ = col.bind (fun current => PMF.pure (row, current)) := by
          apply congrArg (PMF.bind col)
          funext current
          exact hpure current
        _ = col.map (fun current => (row, current)) := PMF.bind_pure_comp _ _

/-- A fixed column leaves only the row draw random. -/
theorem mixed_play_pure_column {I J : Type u} (row : PMF I) (col : J) :
    (form I J).mixed.play (mixedProfile row (PMF.pure col)) =
      row.map (fun current => (current, col)) := by
  have hsame : Profile.update (mixedProfile row (PMF.pure col)) 0 row =
      mixedProfile row (PMF.pure col) := Profile.update_eq_self _ 0
  calc
    (form I J).mixed.play (mixedProfile row (PMF.pure col)) =
        row.bind (fun current =>
          (form I J).mixed.play
            (Profile.update (mixedProfile row (PMF.pure col)) 0
              (PMF.pure current))) := by
      rw [← hsame]
      exact GameForm.mixed_play_update (form I J)
        (mixedProfile row (PMF.pure col)) 0 row
    _ = row.map (fun current => (current, col)) := by
      have hpure (current : I) :
          (form I J).mixed.play
            (Profile.update (mixedProfile row (PMF.pure col)) 0
              (PMF.pure current)) = PMF.pure (current, col) := by
        rw [mixedProfile_update_zero, mixedProfile_pure,
          GameForm.mixed_play_purify]
        rfl
      calc
        _ = row.bind (fun current => PMF.pure (current, col)) := by
          apply congrArg (PMF.bind row)
          funext current
          exact hpure current
        _ = row.map (fun current => (current, col)) := PMF.bind_pure_comp _ _

theorem integrable_pure_row {I J : Type u} (A : I → J → ℝ)
    (row : I) (col : PMF J) (h : PayoffIntegrable col (A row)) :
    UtilityIntegrable (utility A) 0
      ((form I J).mixed.play (mixedProfile (PMF.pure row) col)) := by
  rw [mixed_play_pure_row]
  exact (payoffIntegrable_map_iff _ _ _).2 h

theorem integrable_pure_column {I J : Type u} (A : I → J → ℝ)
    (row : PMF I) (col : J)
    (h : PayoffIntegrable row (fun current => A current col)) :
    UtilityIntegrable (utility A) 0
      ((form I J).mixed.play (mixedProfile row (PMF.pure col))) := by
  rw [mixed_play_pure_column]
  exact (payoffIntegrable_map_iff _ _ _).2 h

/-- With a pure row, payoff is expectation against the actual column law. -/
theorem expectedPayoff_pure_row {I J : Type u} (A : I → J → ℝ)
    (row : I) (col : PMF J) :
    expectedPayoff A (PMF.pure row) col =
      expect col (A row) := by
  calc
    expectedPayoff A (PMF.pure row) col =
        expectedUtility (utility A) 0
          (col.map (fun current => (row, current))) :=
      expectedUtility_congr_law (utility A) 0
        (mixed_play_pure_row row col)
    _ = expect col (A row) := by
      rw [expectedUtility_map]
      rfl

/-- With a pure column, payoff is expectation against the actual row law. -/
theorem expectedPayoff_pure_column {I J : Type u} (A : I → J → ℝ)
    (row : PMF I) (col : J) :
    expectedPayoff A row (PMF.pure col) =
      expect row (fun current => A current col) := by
  calc
    expectedPayoff A row (PMF.pure col) =
        expectedUtility (utility A) 0
          (row.map (fun current => (current, col))) :=
      expectedUtility_congr_law (utility A) 0
        (mixed_play_pure_column row col)
    _ = expect row (fun current => A current col) := by
      rw [expectedUtility_map]
      rfl

/-- Matrix payoff is affine in the row law under the actual joint and conditional guards. -/
theorem expectedPayoff_eq_expect_rows {I J : Type u} (A : I → J → ℝ)
    (row : PMF I) (col : PMF J)
    (hjoint : UtilityIntegrable (utility A) 0
      ((form I J).mixed.play (mixedProfile row col))) :
    PayoffIntegrable row (fun current => expect col (A current)) ∧
      expectedPayoff A row col =
        expect row (fun current => expect col (A current)) := by
  let q : I → PMF (I × J) := fun current =>
    col.map (fun currentCol => (current, currentCol))
  let f : I × J → ℝ := fun outcome => A outcome.1 outcome.2
  have hsame : Profile.update (mixedProfile row col) 0 row =
      mixedProfile row col := Profile.update_eq_self _ 0
  have hplay : (form I J).mixed.play (mixedProfile row col) = row.bind q := by
    calc
      _ = row.bind (fun current =>
          (form I J).mixed.play (mixedProfile (PMF.pure current) col)) := by
        rw [← hsame]
        simpa only [mixedProfile_update_zero] using
          GameForm.mixed_play_update (form I J) (mixedProfile row col) 0 row
      _ = row.bind q := by
        apply congrArg (PMF.bind row)
        funext current
        exact mixed_play_pure_row current col
  have hbind : PayoffIntegrable (row.bind q) f :=
    payoffIntegrable_congr_law hplay hjoint
  have hbranch (current : I) :
      expect (q current) f =
        expect col (A current) := by
    exact expect_map (fun currentCol => (current, currentCol)) col f
  have houter := payoffIntegrable_bind_conditionalExpectation row q f hbind
  have houter' : PayoffIntegrable row
      (fun current => expect col (A current)) :=
    payoffIntegrable_congr_on_support (fun current _ => hbranch current) houter
  refine ⟨houter', ?_⟩
  calc
    expectedPayoff A row col = expect (row.bind q) f := by
      exact expectedUtility_congr_law (utility A) 0 hplay
    _ = expect row (fun current => expect (q current) f)
           := expect_bind_tower row q f hbind
    _ = expect row (fun current => expect col (A current)) := by
      exact expect_congr_on_support (fun current _ => hbranch current)

/-- Matrix payoff is affine in the column law under the actual joint and
conditional guards. -/
theorem expectedPayoff_eq_expect_columns {I J : Type u} (A : I → J → ℝ)
    (row : PMF I) (col : PMF J)
    (hjoint : UtilityIntegrable (utility A) 0
      ((form I J).mixed.play (mixedProfile row col))) :
    PayoffIntegrable col
        (fun current => expect row (fun currentRow => A currentRow current)) ∧
      expectedPayoff A row col =
        expect col (fun current =>
          expect row (fun currentRow => A currentRow current)) := by
  let q : J → PMF (I × J) := fun current =>
    row.map (fun currentRow => (currentRow, current))
  let f : I × J → ℝ := fun outcome => A outcome.1 outcome.2
  have hsame : Profile.update (mixedProfile row col) 1 col =
      mixedProfile row col := Profile.update_eq_self _ 1
  have hplay : (form I J).mixed.play (mixedProfile row col) = col.bind q := by
    calc
      _ = col.bind (fun current =>
          (form I J).mixed.play (mixedProfile row (PMF.pure current))) := by
        rw [← hsame]
        simpa only [mixedProfile_update_one] using
          GameForm.mixed_play_update (form I J) (mixedProfile row col) 1 col
      _ = col.bind q := by
        apply congrArg (PMF.bind col)
        funext current
        exact mixed_play_pure_column row current
  have hbind : PayoffIntegrable (col.bind q) f :=
    payoffIntegrable_congr_law hplay hjoint
  have hbranch (current : J) :
      expect (q current) f =
        expect row (fun currentRow => A currentRow current) := by
    exact expect_map (fun currentRow => (currentRow, current)) row f
  have houter := payoffIntegrable_bind_conditionalExpectation col q f hbind
  have houter' : PayoffIntegrable col
      (fun current => expect row (fun currentRow => A currentRow current)) :=
    payoffIntegrable_congr_on_support (fun current _ => hbranch current) houter
  refine ⟨houter', ?_⟩
  calc
    expectedPayoff A row col = expect (col.bind q) f := by
      exact expectedUtility_congr_law (utility A) 0 hplay
    _ = expect col (fun current => expect (q current) f)
           := expect_bind_tower col q f hbind
    _ = expect col (fun current =>
          expect row (fun currentRow => A currentRow current)) := by
      exact expect_congr_on_support (fun current _ => hbranch current)

/-- A separable matrix payoff is the difference of its marginal values. -/
theorem expectedPayoff_sub {I J : Type u} (rowValue : I → ℝ)
    (colValue : J → ℝ) (row : PMF I) (col : PMF J)
    (hjoint : UtilityIntegrable
      (utility (fun currentRow currentCol =>
        rowValue currentRow - colValue currentCol)) 0
      ((form I J).mixed.play (mixedProfile row col)))
    (hrow : PayoffIntegrable row rowValue)
    (hcol : PayoffIntegrable col colValue) :
    expectedPayoff (fun currentRow currentCol =>
        rowValue currentRow - colValue currentCol) row col =
      expect row rowValue - expect col colValue := by
  let c := expect col colValue
  obtain ⟨houter, haverage⟩ := expectedPayoff_eq_expect_rows
    (fun currentRow currentCol => rowValue currentRow - colValue currentCol)
    row col hjoint
  have hbranch (current : I) :
      expect col (fun currentCol => rowValue current - colValue currentCol)
           = rowValue current - c := by
    calc
      _ = expect col (fun _ => rowValue current) -
          expect col colValue :=
        expect_sub (payoffIntegrable_constant col (rowValue current)) hcol
      _ = _ := by rw [expect_constant]
  calc
    _ = expect row (fun current =>
          expect col (fun currentCol => rowValue current - colValue currentCol)) := haverage
    _ = expect row (fun current => rowValue current - c) :=
      expect_congr_on_support (fun current _ => hbranch current)
    _ = expect row rowValue -
          expect row (fun _ => c) :=
      expect_sub hrow (payoffIntegrable_constant row c)
    _ = _ := by rw [expect_constant]

theorem expectedUtility_zero_mixedProfile {I J : Type u}
    (A : I → J → ℝ) (row : PMF I) (col : PMF J) :
    expectedUtility (utility A) 0
        ((form I J).mixed.play (mixedProfile row col)) =
      expectedPayoff A row col :=
  rfl

theorem expectedUtility_one_mixedProfile {I J : Type u}
    (A : I → J → ℝ) (row : PMF I) (col : PMF J) :
    expectedUtility (utility A) 1
        ((form I J).mixed.play (mixedProfile row col)) =
      -expectedPayoff A row col := by
  exact (utility_isZeroSum A).expectedUtility_one _

/-- A mixed row guarantees payoff at least `v` against every mixed column. -/
def RowGuarantees {I J : Type u} (A : I → J → ℝ)
    (row : PMF I) (v : ℝ) : Prop :=
  ∀ col : PMF J, UtilityIntegrable (utility A) 0
    ((form I J).mixed.play (mixedProfile row col)) ∧
      v ≤ expectedPayoff A row col

/-- A mixed column caps the row payoff at `v` against every mixed row. -/
def ColumnCaps {I J : Type u} (A : I → J → ℝ)
    (col : PMF J) (v : ℝ) : Prop :=
  ∀ row : PMF I, UtilityIntegrable (utility A) 0
    ((form I J).mixed.play (mixedProfile row col)) ∧
      expectedPayoff A row col ≤ v

/-- Some mixed row guarantees `v`. -/
def IsRowGuarantee {I J : Type u} (A : I → J → ℝ) (v : ℝ) : Prop :=
  ∃ row : PMF I, RowGuarantees A row v

/-- Some mixed column caps the row payoff at `v`. -/
def IsColumnCap {I J : Type u} (A : I → J → ℝ) (v : ℝ) : Prop :=
  ∃ col : PMF J, ColumnCaps A col v

/-- The canonical saddle inequalities are exactly mutual row security and
column capping at the realized payoff. -/
theorem isSaddlePoint_iff_guarantees_caps {I J : Type u}
    (A : I → J → ℝ) (row : PMF I) (col : PMF J) :
    IsSaddlePoint (F := form I J) (utility A) (mixedProfile row col) ↔
      UtilityIntegrable (utility A) 0
          ((form I J).mixed.play (mixedProfile row col)) ∧
        RowGuarantees A row (expectedPayoff A row col) ∧
          ColumnCaps A col (expectedPayoff A row col) := by
  constructor
  · intro hsaddle
    rcases hsaddle with ⟨hbase, hrow, hcol⟩
    refine ⟨hbase, ?_, ?_⟩
    · intro col'
      obtain ⟨hdev, hle⟩ := hcol col'
      exact ⟨hdev, hle⟩
    · intro row'
      obtain ⟨hdev, hle⟩ := hrow row'
      exact ⟨hdev, hle⟩
  · rintro ⟨hbase, hrow, hcol⟩
    refine ⟨hbase, ?_, ?_⟩
    · intro row'
      obtain ⟨hdev, hle⟩ := hcol row'
      exact ⟨hdev, hle⟩
    · intro col'
      obtain ⟨hdev, hle⟩ := hrow col'
      exact ⟨hdev, hle⟩

end GameTheory.MatrixGame
