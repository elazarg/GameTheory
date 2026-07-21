/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.ZeroSum.Minimax
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.ZeroSum.MatrixGame.Rectangular

/-!
# Zero-Sum Matrix Games

This file provides a small matrix-game layer on top of `KernelGame`.  A square
matrix game is represented by its row-player payoff matrix `A : S → S → ℝ`; the
column player receives the negative payoff.

The first theorem package is for antisymmetric games.  If
`A x y = - A y x`, then the mixed value is zero and there is a mixed strategy
that is optimal for both roles.

The second package exposes the matrix-game saddle condition and its connection
to mixed Nash equilibria of the induced zero-sum `KernelGame`.

The third package defines the value of a finite matrix game through saddle
points and characterizes optimal row/column strategy pairs as saddle points.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace MatrixGame

/-- Antisymmetry of the row-player payoff matrix. -/
def IsAntisymmetric {S : Type} (A : Square S) : Prop :=
  ∀ x y, A x y = - A y x

variable {S : Type}

/-- An antisymmetric matrix has zero diagonal. -/
theorem IsAntisymmetric.diag_zero {A : Square S} (hA : IsAntisymmetric A) (x : S) :
    A x x = 0 := by
  have h := hA x x
  linarith

open Classical in
/-- The zero-sum `KernelGame` induced by a square payoff matrix. -/
noncomputable def toKernelGame (A : Square S) : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ : Fin 2 => S)
    fun s i => if i = 0 then A (s 0) (s 1) else - A (s 0) (s 1)

@[simp] theorem toKernelGame_payoff_row (A : Square S) (s : Fin 2 → S) :
    (toKernelGame A).utility s 0 = A (s 0) (s 1) := by
  simp [toKernelGame, KernelGame.ofPureEU]

@[simp] theorem toKernelGame_payoff_col (A : Square S) (s : Fin 2 → S) :
    (toKernelGame A).utility s 1 = - A (s 0) (s 1) := by
  simp [toKernelGame, KernelGame.ofPureEU]

@[simp] theorem toKernelGame_eu_row (A : Square S) (s : Fin 2 → S) :
    (toKernelGame A).eu s 0 = A (s 0) (s 1) := by
  simp [toKernelGame, KernelGame.ofPureEU, KernelGame.eu]

@[simp] theorem toKernelGame_eu_col (A : Square S) (s : Fin 2 → S) :
    (toKernelGame A).eu s 1 = - A (s 0) (s 1) := by
  simp [toKernelGame, KernelGame.ofPureEU, KernelGame.eu]

open Classical in
/-- The induced matrix game is zero-sum. -/
theorem toKernelGame_isZeroSum (A : Square S) :
    (toKernelGame A).IsZeroSum := by
  intro s
  simp [toKernelGame, KernelGame.ofPureEU, Fin.sum_univ_two]

section MixedAdapter

variable [Fintype S] (A : Square S)

open Classical in
/-- Pure profiles of a two-player square matrix game are pairs of actions. -/
def profilePairEquiv : (Fin 2 → S) ≃ S × S where
  toFun s := (s 0, s 1)
  invFun p := fun i => if i = 0 then p.1 else p.2
  left_inv := by
    intro s
    funext i
    fin_cases i <;> simp
  right_inv := by
    intro p
    ext <;> simp

open Classical in
/-- A mixed profile for the row and column players of a square matrix game. -/
noncomputable def mixedProfile (row col : PMF S) :
    KernelGame.Profile (toKernelGame A).mixedExtension :=
  fun i => if i = 0 then row else col

omit [Fintype S] in
@[simp] theorem mixedProfile_zero (row col : PMF S) :
    mixedProfile A row col 0 = row := by
  simp [mixedProfile]

omit [Fintype S] in
@[simp] theorem mixedProfile_one (row col : PMF S) :
    mixedProfile A row col 1 = col := by
  simp [mixedProfile]

open Classical in
/-- The mixed-extension utility of the row player is the matrix game's expected
payoff. -/
theorem mixedExtension_eu_row_eq_expectedPayoff (row col : PMF S) :
    (toKernelGame A).mixedExtension.eu (mixedProfile A row col) 0 =
      expectedPayoff A row col := by
  haveI : Finite (toKernelGame A).Outcome := by
    change Finite (Fin 2 → S)
    infer_instance
  haveI : Fintype (KernelGame.Profile (toKernelGame A)) := by
    change Fintype (Fin 2 → S)
    infer_instance
  rw [KernelGame.mixedExtension_eu]
  rw [Math.Probability.expect_eq_sum]
  trans ∑ p : KernelGame.Profile (toKernelGame A),
      (row (p 0)).toReal * (col (p 1)).toReal * A (p 0) (p 1)
  · apply Finset.sum_congr rfl
    intro p _
    have hpmf :
        ((Math.PMFProduct.pmfPi (mixedProfile A row col)) p).toReal =
          (row (p 0)).toReal * (col (p 1)).toReal := by
      change
        ((Math.PMFProduct.pmfPi (A := fun _ : Fin 2 => S)
          (fun i => if i = 0 then row else col)) p).toReal =
          (row (p 0)).toReal * (col (p 1)).toReal
      simp [Math.PMFProduct.pmfPi_apply, Fin.prod_univ_two, ENNReal.toReal_mul]
    rw [hpmf]
    simp [toKernelGame, KernelGame.eu_ofPureEU]
  · rw [expectedPayoff]
    let e : KernelGame.Profile (toKernelGame A) ≃ S × S := profilePairEquiv (S := S)
    calc
      (∑ p : KernelGame.Profile (toKernelGame A),
          (row (p 0)).toReal * (col (p 1)).toReal * A (p 0) (p 1))
          = ∑ p : S × S, (row p.1).toReal * (col p.2).toReal * A p.1 p.2 :=
            Fintype.sum_equiv e
              (fun p : KernelGame.Profile (toKernelGame A) =>
                (row (p 0)).toReal * (col (p 1)).toReal * A (p 0) (p 1))
              (fun p : S × S =>
                (row p.1).toReal * (col p.2).toReal * A p.1 p.2)
              (by intro p; rfl)
      _ = ∑ x : S, ∑ y : S, (row x).toReal * (col y).toReal * A x y :=
            Fintype.sum_prod_type
              (fun p : S × S => (row p.1).toReal * (col p.2).toReal * A p.1 p.2)

open Classical in
/-- The mixed-extension utility of the column player is the negated matrix-game
expected payoff. -/
theorem mixedExtension_eu_col_eq_neg_expectedPayoff (row col : PMF S) :
    (toKernelGame A).mixedExtension.eu (mixedProfile A row col) 1 =
      - expectedPayoff A row col := by
  haveI : Finite (toKernelGame A).mixedExtension.Outcome := by
    change Finite (toKernelGame A).Outcome
    change Finite (Fin 2 → S)
    infer_instance
  have hneg :=
    (KernelGame.mixedExtension_isZeroSum (G := toKernelGame A)
      (toKernelGame_isZeroSum A)).eu_neg
      (mixedProfile A row col)
  rw [mixedExtension_eu_row_eq_expectedPayoff] at hneg
  linarith

end MixedAdapter

section Saddle

variable [Fintype S] (A : Square S)

/-- A mixed saddle point of a matrix game: the row player cannot improve by
changing the row mix and the column player cannot lower the row payoff by
changing the column mix. -/
def IsSaddlePoint (row col : PMF S) : Prop :=
  (∀ row' : PMF S, expectedPayoff A row' col ≤ expectedPayoff A row col) ∧
  (∀ col' : PMF S, expectedPayoff A row col ≤ expectedPayoff A row col')

theorem IsSaddlePoint.row_le {row col row' : PMF S}
    (h : IsSaddlePoint A row col) :
    expectedPayoff A row' col ≤ expectedPayoff A row col :=
  h.1 row'

theorem IsSaddlePoint.le_col {row col col' : PMF S}
    (h : IsSaddlePoint A row col) :
    expectedPayoff A row col ≤ expectedPayoff A row col' :=
  h.2 col'

open Classical in
omit [Fintype S] in
private theorem update_mixedProfile_row (row row' col : PMF S) :
    Function.update (mixedProfile A row col) 0 row' =
      mixedProfile A row' col := by
  funext i
  fin_cases i <;> simp [mixedProfile]

open Classical in
omit [Fintype S] in
private theorem update_mixedProfile_col (row col col' : PMF S) :
    Function.update (mixedProfile A row col) 1 col' =
      mixedProfile A row col' := by
  funext i
  fin_cases i <;> simp [mixedProfile]

open Classical in
/-- Mixed Nash equilibria of the induced zero-sum `KernelGame` are exactly
matrix-game saddle points. -/
theorem mixedNash_iff_isSaddlePoint (row col : PMF S) :
    (toKernelGame A).mixedExtension.IsNash (mixedProfile A row col) ↔
      IsSaddlePoint A row col := by
  constructor
  · intro hN
    constructor
    · intro row'
      have h := hN 0 row'
      rw [update_mixedProfile_row, mixedExtension_eu_row_eq_expectedPayoff,
        mixedExtension_eu_row_eq_expectedPayoff] at h
      exact h
    · intro col'
      have h := hN 1 col'
      rw [update_mixedProfile_col, mixedExtension_eu_col_eq_neg_expectedPayoff,
        mixedExtension_eu_col_eq_neg_expectedPayoff] at h
      linarith
  · intro hS who s'
    have hwho : who = 0 ∨ who = 1 := by
      fin_cases who <;> simp
    rcases hwho with rfl | rfl
    · let row' : PMF S := s'
      change (toKernelGame A).mixedExtension.eu (mixedProfile A row col) 0 ≥
        (toKernelGame A).mixedExtension.eu
          (Function.update (mixedProfile A row col) 0 row') 0
      rw [update_mixedProfile_row, mixedExtension_eu_row_eq_expectedPayoff,
        mixedExtension_eu_row_eq_expectedPayoff]
      exact hS.row_le
    · let col' : PMF S := s'
      change (toKernelGame A).mixedExtension.eu (mixedProfile A row col) 1 ≥
        (toKernelGame A).mixedExtension.eu
          (Function.update (mixedProfile A row col) 1 col') 1
      rw [update_mixedProfile_col, mixedExtension_eu_col_eq_neg_expectedPayoff,
        mixedExtension_eu_col_eq_neg_expectedPayoff]
      exact neg_le_neg (hS.le_col (col' := col'))

open Classical in
/-- Matrix-game saddle points are exactly saddle points of the induced mixed
`KernelGame`. -/
theorem kernel_isSaddlePoint_iff_isSaddlePoint (row col : PMF S) :
    (toKernelGame A).mixedExtension.IsSaddlePoint (mixedProfile A row col) ↔
      IsSaddlePoint A row col := by
  rw [KernelGame.isSaddlePoint_iff_isNash, mixedNash_iff_isSaddlePoint]

open Classical in
/-- At a matrix-game saddle point, every pure row in the support of the row
mixed strategy earns exactly the saddle payoff. -/
theorem support_complementarity_row {row col : PMF S}
    (hS : IsSaddlePoint A row col) {x : S} (hx : row x ≠ 0) :
    (∑ y : S, (col y).toReal * A x y) = expectedPayoff A row col := by
  let f : S → ℝ := fun z => ∑ y : S, (col y).toReal * A z y
  have hrow : ∀ z : S, f z ≤ expectedPayoff A row col := by
    intro z
    have h := hS.row_le (row' := PMF.pure z)
    rwa [expectedPayoff_pure_row] at h
  have havg : expectedPayoff A row col = ∑ z : S, (row z).toReal * f z := by
    unfold expectedPayoff f
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  by_contra hne
  have hlt : f x < expectedPayoff A row col := lt_of_le_of_ne (hrow x) hne
  have hnonneg :
      ∀ z : S, 0 ≤ (row z).toReal * (expectedPayoff A row col - f z) := by
    intro z
    exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hrow z))
  have hpos :
      0 < (row x).toReal * (expectedPayoff A row col - f x) := by
    exact mul_pos (ENNReal.toReal_pos hx (PMF.apply_ne_top _ _))
      (sub_pos.mpr hlt)
  have hsum_pos :
      0 < ∑ z : S, (row z).toReal * (expectedPayoff A row col - f z) :=
    Finset.sum_pos' (fun z _ => hnonneg z) ⟨x, Finset.mem_univ x, hpos⟩
  have hsum_zero :
      ∑ z : S, (row z).toReal * (expectedPayoff A row col - f z) = 0 := by
    calc
      ∑ z : S, (row z).toReal * (expectedPayoff A row col - f z)
          = ∑ z : S, ((row z).toReal * expectedPayoff A row col -
              (row z).toReal * f z) := by
            apply Finset.sum_congr rfl
            intro z _
            ring
      _ = (∑ z : S, (row z).toReal * expectedPayoff A row col) -
            ∑ z : S, (row z).toReal * f z := by
            rw [Finset.sum_sub_distrib]
      _ = expectedPayoff A row col - ∑ z : S, (row z).toReal * f z := by
            rw [← Finset.sum_mul, Math.Probability.pmf_toReal_sum_one, one_mul]
      _ = 0 := by rw [← havg, sub_self]
  linarith

open Classical in
/-- At a matrix-game saddle point, every pure column in the support of the
column mixed strategy gives exactly the saddle payoff to the row player. -/
theorem support_complementarity_column {row col : PMF S}
    (hS : IsSaddlePoint A row col) {y : S} (hy : col y ≠ 0) :
    (∑ x : S, (row x).toReal * A x y) = expectedPayoff A row col := by
  let f : S → ℝ := fun z => ∑ x : S, (row x).toReal * A x z
  have hcol : ∀ z : S, expectedPayoff A row col ≤ f z := by
    intro z
    have h := hS.le_col (col' := PMF.pure z)
    rwa [expectedPayoff_pure_col] at h
  have havg : expectedPayoff A row col = ∑ z : S, (col z).toReal * f z := by
    unfold expectedPayoff f
    calc
      (∑ x : S, ∑ z : S, (row x).toReal * (col z).toReal * A x z)
          = ∑ z : S, ∑ x : S, (row x).toReal * (col z).toReal * A x z := by
            rw [Finset.sum_comm]
      _ = ∑ z : S, (col z).toReal * ∑ x : S, (row x).toReal * A x z := by
            apply Finset.sum_congr rfl
            intro z _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
  by_contra hne
  have hne' : expectedPayoff A row col ≠ f y := by
    intro h
    exact hne (by simpa [f] using h.symm)
  have hlt : expectedPayoff A row col < f y := lt_of_le_of_ne (hcol y) hne'
  have hnonneg :
      ∀ z : S, 0 ≤ (col z).toReal * (f z - expectedPayoff A row col) := by
    intro z
    exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hcol z))
  have hpos :
      0 < (col y).toReal * (f y - expectedPayoff A row col) := by
    exact mul_pos (ENNReal.toReal_pos hy (PMF.apply_ne_top _ _))
      (sub_pos.mpr hlt)
  have hsum_pos :
      0 < ∑ z : S, (col z).toReal * (f z - expectedPayoff A row col) :=
    Finset.sum_pos' (fun z _ => hnonneg z) ⟨y, Finset.mem_univ y, hpos⟩
  have hsum_zero :
      ∑ z : S, (col z).toReal * (f z - expectedPayoff A row col) = 0 := by
    calc
      ∑ z : S, (col z).toReal * (f z - expectedPayoff A row col)
          = ∑ z : S, ((col z).toReal * f z -
              (col z).toReal * expectedPayoff A row col) := by
            apply Finset.sum_congr rfl
            intro z _
            ring
      _ = (∑ z : S, (col z).toReal * f z) -
            ∑ z : S, (col z).toReal * expectedPayoff A row col := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ z : S, (col z).toReal * f z) - expectedPayoff A row col := by
            rw [← Finset.sum_mul, Math.Probability.pmf_toReal_sum_one, one_mul]
      _ = 0 := by rw [← havg, sub_self]
  linarith

open Classical in
/-- If every pure row in the support of a mixed row strategy has the same payoff
against a column mix, then the mixed row strategy has that payoff. -/
theorem expectedPayoff_eq_of_forall_support_row {row col : PMF S} {v : ℝ}
    (h : ∀ x : S, row x ≠ 0 → (∑ y : S, (col y).toReal * A x y) = v) :
    expectedPayoff A row col = v := by
  rw [expectedPayoff]
  calc
    (∑ x : S, ∑ y : S, (row x).toReal * (col y).toReal * A x y)
        = ∑ x : S, (row x).toReal * (∑ y : S, (col y).toReal * A x y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ x : S, (row x).toReal * v := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : row x = 0
          · simp [hx]
          · rw [h x hx]
    _ = v := by
          rw [← Finset.sum_mul, Math.Probability.pmf_toReal_sum_one, one_mul]

end Saddle

section Value

variable [Fintype S] [Nonempty S] (A : Square S)

open Classical in
/-- Finite square matrix games have mixed saddle points. -/
theorem exists_saddlePoint :
    ∃ (row col : PMF S), IsSaddlePoint A row col := by
  haveI : Finite (toKernelGame A).Outcome := by
    change Finite (Fin 2 → S)
    infer_instance
  haveI : ∀ i, Finite ((toKernelGame A).Strategy i) := by
    intro i
    change Finite S
    infer_instance
  haveI : ∀ i, Nonempty ((toKernelGame A).Strategy i) := by
    intro i
    change Nonempty S
    infer_instance
  obtain ⟨_v, σ, hN, _hv, _hlow, _hcap⟩ :=
    KernelGame.von_neumann_minimax (toKernelGame A) (toKernelGame_isZeroSum A)
  refine ⟨σ 0, σ 1, ?_⟩
  have hprof : mixedProfile A (σ 0) (σ 1) = σ := by
    funext i
    fin_cases i <;> simp [mixedProfile]
  rw [← hprof] at hN
  exact (mixedNash_iff_isSaddlePoint (A := A) (σ 0) (σ 1)).1 hN

open Classical in
private theorem exists_saddlePoint_pair :
    ∃ p : PMF S × PMF S, IsSaddlePoint A p.1 p.2 := by
  obtain ⟨row, col, hS⟩ := exists_saddlePoint A
  exact ⟨(row, col), hS⟩

open Classical in
private noncomputable def selectedSaddlePoint (A : Square S) : PMF S × PMF S :=
  Classical.choose (exists_saddlePoint_pair A)

open Classical in
private theorem selectedSaddlePoint_isSaddlePoint :
    IsSaddlePoint A (selectedSaddlePoint A).1 (selectedSaddlePoint A).2 :=
  Classical.choose_spec (exists_saddlePoint_pair A)

open Classical in
/-- The value of a finite square matrix game, defined from an arbitrary mixed
saddle point.  The theorem `value_eq_of_saddlePoint` shows this is independent
of the chosen saddle point. -/
noncomputable def value : ℝ :=
  expectedPayoff A (selectedSaddlePoint A).1 (selectedSaddlePoint A).2

open Classical in
/-- Every mixed saddle point realizes the matrix-game value. -/
theorem value_eq_of_saddlePoint {row col : PMF S}
    (hS : IsSaddlePoint A row col) :
    expectedPayoff A row col = value A := by
  let row₀ : PMF S := (selectedSaddlePoint A).1
  let col₀ : PMF S := (selectedSaddlePoint A).2
  have hT : IsSaddlePoint A row₀ col₀ := by
    simpa [row₀, col₀] using selectedSaddlePoint_isSaddlePoint (A := A)
  have hval : value A = expectedPayoff A row₀ col₀ := rfl
  have h1 : expectedPayoff A row₀ col ≤ expectedPayoff A row col :=
    hS.row_le
  have h2 : expectedPayoff A row col ≤ expectedPayoff A row col₀ :=
    hS.le_col
  have h3 : expectedPayoff A row col₀ ≤ expectedPayoff A row₀ col₀ :=
    hT.row_le
  have h4 : expectedPayoff A row₀ col₀ ≤ expectedPayoff A row₀ col :=
    hT.le_col
  rw [hval]
  exact le_antisymm (le_trans h2 h3) (le_trans h4 h1)

/-- A row mixed strategy guarantees the row player at least `v`. -/
def RowGuarantees (row : PMF S) (v : ℝ) : Prop :=
  ∀ col : PMF S, v ≤ expectedPayoff A row col

/-- A column mixed strategy guarantees that the row player's payoff is at most
`v`. -/
def ColumnCaps (col : PMF S) (v : ℝ) : Prop :=
  ∀ row : PMF S, expectedPayoff A row col ≤ v

/-- A scalar is a row-player guarantee when some row mixed strategy guarantees it. -/
def IsPlayerIGuarantee (v : ℝ) : Prop :=
  ∃ row : PMF S, RowGuarantees A row v

/-- A scalar is a column-player guarantee when some column mixed strategy caps
the row player's payoff at it. -/
def IsPlayerIIGuarantee (v : ℝ) : Prop :=
  ∃ col : PMF S, ColumnCaps A col v

open Classical in
/-- If both players can guarantee the same scalar, that scalar is the
matrix-game value. -/
theorem common_guarantee_eq_value {w : ℝ}
    (hrow : IsPlayerIGuarantee A w) (hcol : IsPlayerIIGuarantee A w) :
    w = value A := by
  obtain ⟨row, hrow⟩ := hrow
  obtain ⟨col, hcol⟩ := hcol
  let row₀ : PMF S := (selectedSaddlePoint A).1
  let col₀ : PMF S := (selectedSaddlePoint A).2
  have hS : IsSaddlePoint A row₀ col₀ := by
    simpa [row₀, col₀] using selectedSaddlePoint_isSaddlePoint (A := A)
  have hval : value A = expectedPayoff A row₀ col₀ := rfl
  have hw_le_value : w ≤ value A := by
    rw [hval]
    exact le_trans (hrow col₀) (hS.row_le (row' := row))
  have hvalue_le_w : value A ≤ w := by
    rw [hval]
    exact le_trans (hS.le_col (col' := col)) (hcol row₀)
  exact le_antisymm hw_le_value hvalue_le_w

/-- Row strategies that guarantee the value. -/
def optimalRowStrategies : Set (PMF S) :=
  { row | RowGuarantees A row (value A) }

/-- Column strategies that cap the row player's payoff at the value. -/
def optimalColumnStrategies : Set (PMF S) :=
  { col | ColumnCaps A col (value A) }

/-- Membership in the row-optimal strategy set unfolds to guaranteeing the
value against every column mix. -/
theorem mem_optimalRowStrategies_iff_expectedPayoff_ge (row : PMF S) :
    row ∈ optimalRowStrategies A ↔
      ∀ col : PMF S, value A ≤ expectedPayoff A row col :=
  Iff.rfl

/-- Membership in the column-optimal strategy set unfolds to capping the row
player's payoff at the value against every row mix. -/
theorem mem_optimalColumnStrategies_iff_expectedPayoff_le (col : PMF S) :
    col ∈ optimalColumnStrategies A ↔
      ∀ row : PMF S, expectedPayoff A row col ≤ value A :=
  Iff.rfl

open Classical in
/-- A row/column pair is optimal exactly when it is a saddle point. -/
theorem optimal_pairs_iff_saddle_point (row col : PMF S) :
    row ∈ optimalRowStrategies A ∧ col ∈ optimalColumnStrategies A ↔
      IsSaddlePoint A row col := by
  constructor
  · rintro ⟨hrow, hcol⟩
    have hp : expectedPayoff A row col = value A :=
      le_antisymm (hcol row) (hrow col)
    constructor
    · intro row'
      calc
        expectedPayoff A row' col ≤ value A := hcol row'
        _ = expectedPayoff A row col := hp.symm
    · intro col'
      calc
        expectedPayoff A row col = value A := hp
        _ ≤ expectedPayoff A row col' := hrow col'
  · intro hS
    have hp := value_eq_of_saddlePoint (A := A) hS
    constructor
    · intro col'
      calc
        value A = expectedPayoff A row col := hp.symm
        _ ≤ expectedPayoff A row col' := hS.le_col
    · intro row'
      calc
        expectedPayoff A row' col ≤ expectedPayoff A row col := hS.row_le
        _ = value A := hp

open Classical in
/-- Matrix-game optimal row/column pairs are exactly mixed Nash equilibria of
the induced zero-sum `KernelGame`. -/
theorem optimal_pairs_iff_mixedNash (row col : PMF S) :
    row ∈ optimalRowStrategies A ∧ col ∈ optimalColumnStrategies A ↔
      (toKernelGame A).mixedExtension.IsNash (mixedProfile A row col) := by
  rw [mixedNash_iff_isSaddlePoint, optimal_pairs_iff_saddle_point]

open Classical in
/-- Matrix-game optimal row/column pairs are exactly mixed saddle points of the
induced zero-sum `KernelGame`. -/
theorem optimal_pairs_iff_kernel_saddlePoint (row col : PMF S) :
    row ∈ optimalRowStrategies A ∧ col ∈ optimalColumnStrategies A ↔
      (toKernelGame A).mixedExtension.IsSaddlePoint (mixedProfile A row col) := by
  rw [kernel_isSaddlePoint_iff_isSaddlePoint, optimal_pairs_iff_saddle_point]

open Classical in
/-- A mixed Nash equilibrium of the induced zero-sum `KernelGame` realizes the
matrix-game value. -/
theorem value_eq_mixedExtension_eu_of_mixedNash {row col : PMF S}
    (hN : (toKernelGame A).mixedExtension.IsNash (mixedProfile A row col)) :
    (toKernelGame A).mixedExtension.eu (mixedProfile A row col) 0 = value A := by
  rw [mixedExtension_eu_row_eq_expectedPayoff]
  exact value_eq_of_saddlePoint A ((mixedNash_iff_isSaddlePoint (A := A) row col).1 hN)

/-- The row-optimal strategy set is nonempty. -/
theorem optimalRowStrategies_nonempty :
    (optimalRowStrategies A).Nonempty := by
  obtain ⟨row, col, hS⟩ := exists_saddlePoint A
  exact ⟨row, ((optimal_pairs_iff_saddle_point (A := A) row col).2 hS).1⟩

/-- The column-optimal strategy set is nonempty. -/
theorem optimalColumnStrategies_nonempty :
    (optimalColumnStrategies A).Nonempty := by
  obtain ⟨row, col, hS⟩ := exists_saddlePoint A
  exact ⟨col, ((optimal_pairs_iff_saddle_point (A := A) row col).2 hS).2⟩

end Value

section ExpectedPayoff

variable [Fintype S] {A : Square S}

open Classical in
/-- In an antisymmetric matrix game, swapping the two mixed strategies negates
the row player's expected payoff. -/
theorem expectedPayoff_swap_of_antisymmetric (hA : IsAntisymmetric A)
    (row col : PMF S) :
    expectedPayoff A row col = - expectedPayoff A col row := by
  unfold expectedPayoff
  calc
    (∑ x : S, ∑ y : S, (row x).toReal * (col y).toReal * A x y)
        = ∑ x : S, ∑ y : S, (row x).toReal * (col y).toReal * (- A y x) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          rw [hA x y]
    _ = - ∑ x : S, ∑ y : S, (col x).toReal * (row y).toReal * A x y := by
          rw [Finset.sum_comm]
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro y _
          ring

open Classical in
/-- Playing the same mixed strategy against itself has expected payoff zero in
an antisymmetric matrix game. -/
theorem expectedPayoff_self_eq_zero_of_antisymmetric (hA : IsAntisymmetric A)
    (μ : PMF S) :
    expectedPayoff A μ μ = 0 := by
  have hswap := expectedPayoff_swap_of_antisymmetric (A := A) hA μ μ
  linarith

end ExpectedPayoff

section AntisymmetricValue

variable [Finite S] [Nonempty S] {A : Square S}

open Classical in
private theorem minimax_profile :
    ∃ (v : ℝ) (σ : KernelGame.Profile (toKernelGame A).mixedExtension),
      (toKernelGame A).mixedExtension.IsNash σ ∧
      (toKernelGame A).mixedExtension.eu σ 0 = v ∧
      (∀ col : PMF S,
        (toKernelGame A).mixedExtension.eu (mixedProfile A (σ 0) col) 0 ≥ v) ∧
      (∀ row : PMF S,
        (toKernelGame A).mixedExtension.eu (mixedProfile A row (σ 1)) 0 ≤ v) := by
  haveI : Finite (toKernelGame A).Outcome := by
    change Finite (Fin 2 → S)
    infer_instance
  haveI : ∀ i, Finite ((toKernelGame A).Strategy i) := by
    intro i
    change Finite S
    infer_instance
  haveI : ∀ i, Nonempty ((toKernelGame A).Strategy i) := by
    intro i
    change Nonempty S
    infer_instance
  obtain ⟨v, σ, hN, hv, hlow, hcap⟩ :=
    KernelGame.von_neumann_minimax (toKernelGame A) (toKernelGame_isZeroSum A)
  refine ⟨v, σ, hN, hv, ?_, ?_⟩
  · intro col
    have hprof : Function.update σ 1 col = mixedProfile A (σ 0) col := by
      funext i
      fin_cases i <;> simp [mixedProfile]
    have h := hlow col
    rwa [hprof] at h
  · intro row
    have hprof : Function.update σ 0 row = mixedProfile A row (σ 1) := by
      funext i
      fin_cases i <;> simp [mixedProfile]
    have h := hcap row
    rwa [hprof] at h

open Classical in
/-- Antisymmetric finite square matrix games have mixed value zero. -/
theorem antisymmetric_value_zero (hA : IsAntisymmetric A) :
    ∃ σ : KernelGame.Profile (toKernelGame A).mixedExtension,
      (toKernelGame A).mixedExtension.IsNash σ ∧
      (toKernelGame A).mixedExtension.eu σ 0 = 0 := by
  letI : Fintype S := Fintype.ofFinite S
  obtain ⟨v, σ, hN, hv, hlow, hcap⟩ := minimax_profile (A := A)
  have hself_row :
      (toKernelGame A).mixedExtension.eu (mixedProfile A (σ 0) (σ 0)) 0 = 0 := by
    rw [mixedExtension_eu_row_eq_expectedPayoff]
    exact expectedPayoff_self_eq_zero_of_antisymmetric hA (σ 0)
  have hself_col :
      (toKernelGame A).mixedExtension.eu (mixedProfile A (σ 1) (σ 1)) 0 = 0 := by
    rw [mixedExtension_eu_row_eq_expectedPayoff]
    exact expectedPayoff_self_eq_zero_of_antisymmetric hA (σ 1)
  have hv_le_zero : v ≤ 0 := by
    have := hlow (σ 0)
    linarith
  have hv_ge_zero : 0 ≤ v := by
    have := hcap (σ 1)
    linarith
  refine ⟨σ, hN, ?_⟩
  linarith

end AntisymmetricValue

section AntisymmetricOptimal

variable [Fintype S] [Nonempty S] {A : Square S}

open Classical in
/-- In an antisymmetric finite square matrix game, some mixed strategy is
optimal for both the row and column roles. -/
theorem antisymmetric_exists_optimal_strategy (hA : IsAntisymmetric A) :
    ∃ μ : PMF S,
      (∀ ν : PMF S, 0 ≤ expectedPayoff A μ ν) ∧
      (∀ ν : PMF S, expectedPayoff A ν μ ≤ 0) := by
  obtain ⟨v, σ, _hN, _hv, hlow, hcap⟩ := minimax_profile (A := A)
  have hself_row :
      (toKernelGame A).mixedExtension.eu (mixedProfile A (σ 0) (σ 0)) 0 = 0 := by
    rw [mixedExtension_eu_row_eq_expectedPayoff]
    exact expectedPayoff_self_eq_zero_of_antisymmetric hA (σ 0)
  have hv_le_zero : v ≤ 0 := by
    have := hlow (σ 0)
    linarith
  have hself_col :
      (toKernelGame A).mixedExtension.eu (mixedProfile A (σ 1) (σ 1)) 0 = 0 := by
    rw [mixedExtension_eu_row_eq_expectedPayoff]
    exact expectedPayoff_self_eq_zero_of_antisymmetric hA (σ 1)
  have hv_ge_zero : 0 ≤ v := by
    have := hcap (σ 1)
    linarith
  have hv0 : v = 0 := le_antisymm hv_le_zero hv_ge_zero
  refine ⟨σ 0, ?_, ?_⟩
  · intro ν
    have h := hlow ν
    rw [mixedExtension_eu_row_eq_expectedPayoff] at h
    linarith
  · intro ν
    have hrow := hlow ν
    rw [mixedExtension_eu_row_eq_expectedPayoff] at hrow
    have hswap := expectedPayoff_swap_of_antisymmetric (A := A) hA ν (σ 0)
    linarith

open Classical in
/-- An antisymmetric finite square matrix game has a mixed column strategy
that makes every pure row payoff non-positive. -/
theorem antisymmetric_exists_column_strategy_payoff_nonpos (hA : IsAntisymmetric A) :
    ∃ μ : PMF S, ∀ x : S, (∑ y : S, (μ y).toReal * A x y) ≤ 0 := by
  obtain ⟨μ, _hrow, hcol⟩ := antisymmetric_exists_optimal_strategy (A := A) hA
  refine ⟨μ, fun x => ?_⟩
  have h := hcol (PMF.pure x)
  rwa [expectedPayoff_pure_row] at h

end AntisymmetricOptimal

end MatrixGame

end GameTheory
