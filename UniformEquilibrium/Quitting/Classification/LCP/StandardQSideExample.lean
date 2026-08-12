/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Gate

/-!
# An exact four-player witness for the corrected-core standard-Q side

This file proves that the algebraic necessary condition for a quitting-game
counterexample is satisfiable already with four players.  The corrected core
of the displayed four-player singleton comparison table is a three-cycle.
That `3 × 3` principal matrix is textbook standard Q and has no homogeneous
simplex solution.

The standard-Q proof is constructive: for arbitrary `q`, one of the empty,
three two-coordinate, or full complementary supports supplies an explicit
LCP solution.  No numerical search or unproved matrix-classification result
is used.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification
namespace StandardQSideExample

open Finset Math.LinearProgramming

abbrev CorePlayer := Fin 3

/-- The cyclic `3 × 3` standard-Q block. -/
def cyclicMatrix : CorePlayer → CorePlayer → ℝ := fun who owner =>
  if who = 0 then
    if owner = 0 then 0 else if owner = 1 then -1 else 2
  else if who = 1 then
    if owner = 0 then 2 else if owner = 1 then 0 else -1
  else
    if owner = 0 then -1 else if owner = 1 then 2 else 0

private def emptySolution (q : CorePlayer → ℝ)
    (hq : ∀ i, 0 ≤ q i) : StandardLCPSolution cyclicMatrix q where
  weight := 0
  weight_nonneg := by intro i; simp
  residual_nonneg := by intro i; simpa using hq i
  complementary := by intro i; simp

private def pairZeroOneSolution (q : CorePlayer → ℝ)
    (h0 : 0 ≤ q 0) (h1 : q 1 ≤ 0)
    (hout : 0 ≤ q 2 + q 1 / 2 + 2 * q 0) :
    StandardLCPSolution cyclicMatrix q where
  weight := ![-q 1 / 2, q 0, 0]
  weight_nonneg := by
    intro i
    fin_cases i <;> simp <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;> simp [cyclicMatrix, Fin.sum_univ_succ]
    all_goals linarith
  complementary := by
    intro i
    fin_cases i <;> simp [cyclicMatrix, Fin.sum_univ_succ]

private def pairOneTwoSolution (q : CorePlayer → ℝ)
    (h1 : 0 ≤ q 1) (h2 : q 2 ≤ 0)
    (hout : 0 ≤ q 0 + q 2 / 2 + 2 * q 1) :
    StandardLCPSolution cyclicMatrix q where
  weight := ![0, -q 2 / 2, q 1]
  weight_nonneg := by
    intro i
    fin_cases i <;> simp <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;> simp [cyclicMatrix, Fin.sum_univ_succ]
    all_goals linarith
  complementary := by
    intro i
    fin_cases i <;> simp [cyclicMatrix, Fin.sum_univ_succ]

private def pairTwoZeroSolution (q : CorePlayer → ℝ)
    (h2 : 0 ≤ q 2) (h0 : q 0 ≤ 0)
    (hout : 0 ≤ q 1 + q 0 / 2 + 2 * q 2) :
    StandardLCPSolution cyclicMatrix q where
  weight := ![q 2, 0, -q 0 / 2]
  weight_nonneg := by
    intro i
    fin_cases i <;> simp <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;> simp [cyclicMatrix, Fin.sum_univ_succ]
    all_goals linarith
  complementary := by
    intro i
    fin_cases i <;> simp [cyclicMatrix, Fin.sum_univ_succ]

private def fullSolution (q : CorePlayer → ℝ)
    (h0 : 2 * q 0 + 4 * q 1 + q 2 ≤ 0)
    (h1 : q 0 + 2 * q 1 + 4 * q 2 ≤ 0)
    (h2 : 4 * q 0 + q 1 + 2 * q 2 ≤ 0) :
    StandardLCPSolution cyclicMatrix q where
  weight := fun i =>
    if i = 0 then -(2 * q 0 + 4 * q 1 + q 2) / 7
    else if i = 1 then -(q 0 + 2 * q 1 + 4 * q 2) / 7
    else -(4 * q 0 + q 1 + 2 * q 2) / 7
  weight_nonneg := by
    intro i
    fin_cases i <;> simp [show (2 : CorePlayer) ≠ 0 by decide,
      show (2 : CorePlayer) ≠ 1 by decide] <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;> simp [cyclicMatrix, Fin.sum_univ_succ,
      show (2 : CorePlayer) ≠ 0 by decide,
      show (2 : CorePlayer) ≠ 1 by decide]
    all_goals linarith
  complementary := by
    intro i
    fin_cases i
    · norm_num [cyclicMatrix, Fin.sum_univ_succ,
        show (2 : CorePlayer) ≠ 0 by decide,
        show (2 : CorePlayer) ≠ 1 by decide]
      right
      ring
    · norm_num [cyclicMatrix, Fin.sum_univ_succ,
        show (2 : CorePlayer) ≠ 0 by decide,
        show (2 : CorePlayer) ≠ 1 by decide]
      right
      ring
    · norm_num [cyclicMatrix, Fin.sum_univ_succ,
        show (2 : CorePlayer) ≠ 0 by decide,
        show (2 : CorePlayer) ≠ 1 by decide]
      right
      have hq : ∀ h : 2 < 3, q ⟨2, h⟩ = q 2 := by
        intro h
        congr 1
      rw [hq]
      ring

/-- The cyclic block is a textbook standard Q-matrix. -/
theorem cyclicMatrix_standardQ : IsStandardQMatrix cyclicMatrix := by
  intro q
  by_cases hq0 : 0 ≤ q 0
  · by_cases hq1 : 0 ≤ q 1
    · by_cases hq2 : 0 ≤ q 2
      · exact ⟨emptySolution q (by intro i; fin_cases i <;> assumption)⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hpair12 : 0 ≤ q 0 + q 2 / 2 + 2 * q 1
        · exact ⟨pairOneTwoSolution q hq1 hq2' hpair12⟩
        · exact ⟨fullSolution q (by linarith) (by linarith) (by linarith)⟩
    · have hq1' : q 1 ≤ 0 := le_of_lt (lt_of_not_ge hq1)
      by_cases hq2 : 0 ≤ q 2
      · by_cases hpair01 : 0 ≤ q 2 + q 1 / 2 + 2 * q 0
        · exact ⟨pairZeroOneSolution q hq0 hq1' hpair01⟩
        · exact ⟨fullSolution q (by linarith) (by linarith) (by linarith)⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hpair01 : 0 ≤ q 2 + q 1 / 2 + 2 * q 0
        · exact ⟨pairZeroOneSolution q hq0 hq1' hpair01⟩
        · exact ⟨fullSolution q (by linarith) (by linarith) (by linarith)⟩
  · have hq0' : q 0 ≤ 0 := le_of_lt (lt_of_not_ge hq0)
    by_cases hq1 : 0 ≤ q 1
    · by_cases hq2 : 0 ≤ q 2
      · by_cases hpair20 : 0 ≤ q 1 + q 0 / 2 + 2 * q 2
        · exact ⟨pairTwoZeroSolution q hq2 hq0' hpair20⟩
        · exact ⟨fullSolution q (by linarith) (by linarith) (by linarith)⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hpair12 : 0 ≤ q 0 + q 2 / 2 + 2 * q 1
        · exact ⟨pairOneTwoSolution q hq1 hq2' hpair12⟩
        · exact ⟨fullSolution q (by linarith) (by linarith) (by linarith)⟩
    · have hq1' : q 1 ≤ 0 := le_of_lt (lt_of_not_ge hq1)
      by_cases hq2 : 0 ≤ q 2
      · by_cases hpair20 : 0 ≤ q 1 + q 0 / 2 + 2 * q 2
        · exact ⟨pairTwoZeroSolution q hq2 hq0' hpair20⟩
        · exact ⟨fullSolution q (by linarith) (by linarith) (by linarith)⟩
      · exact ⟨fullSolution q (by linarith) (by linarith) (by linarith)⟩

/-- The cyclic block has no homogeneous simplex-LCP solution. -/
theorem cyclicMatrix_noHomogeneous :
    ¬HasHomogeneousSimplexSolution cyclicMatrix := by
  rintro ⟨weight, hresidual, hcomplementary⟩
  let x : ℝ := weight 0
  let y : ℝ := weight 1
  let z : ℝ := weight 2
  have hx : 0 ≤ x := weight.property.1 0
  have hy : 0 ≤ y := weight.property.1 1
  have hz : 0 ≤ z := weight.property.1 2
  have htotal : x + (y + z) = 1 := by
    have h := weight.property.2
    have hsum : (∑ i : CorePlayer, weight.val i) =
        weight.val 0 + (weight.val 1 + weight.val 2) := by
      simp [Fin.sum_univ_succ]
    rw [hsum] at h
    change x + (y + z) = 1 at h
    exact h
  have hr0 : singletonLCPResidual cyclicMatrix weight 0 = -y + 2 * z := by
    dsimp only [x, y, z]
    simp [singletonLCPResidual, wsum, dotProduct, cyclicMatrix,
      Fin.sum_univ_succ]
    ring
  have hr1 : singletonLCPResidual cyclicMatrix weight 1 = 2 * x - z := by
    dsimp only [x, y, z]
    simp [singletonLCPResidual, wsum, dotProduct, cyclicMatrix,
      Fin.sum_univ_succ]
    ring
  have hr2 : singletonLCPResidual cyclicMatrix weight 2 = -x + 2 * y := by
    dsimp only [x, y, z]
    simp [singletonLCPResidual, wsum, dotProduct, cyclicMatrix,
      Fin.sum_univ_succ]
    ring
  have hsum : x * y + x * z + y * z = 0 := by
    have h0 := hcomplementary 0
    have h1 := hcomplementary 1
    have h2 := hcomplementary 2
    rw [hr0] at h0
    rw [hr1] at h1
    rw [hr2] at h2
    change x * (-y + 2 * z) = 0 at h0
    change y * (2 * x - z) = 0 at h1
    change z * (-x + 2 * y) = 0 at h2
    nlinarith
  have hxy : x * y = 0 := by
    nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
  have hxz : x * z = 0 := by
    nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
  have hyz : y * z = 0 := by
    nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
  by_cases hx0 : x = 0
  · by_cases hy0 : y = 0
    · have hz1 : z = 1 := by linarith
      have h := hresidual 1
      rw [hr1, hx0, hz1] at h
      norm_num at h
    · have hz0 : z = 0 := (mul_eq_zero.mp hyz).resolve_left hy0
      have hy1 : y = 1 := by linarith
      have h := hresidual 0
      rw [hr0, hy1, hz0] at h
      norm_num at h
  · have hy0 : y = 0 := (mul_eq_zero.mp hxy).resolve_left hx0
    have hz0 : z = 0 := (mul_eq_zero.mp hxz).resolve_left hx0
    have hx1 : x = 1 := by linarith
    have h := hresidual 2
    rw [hr2, hx1, hy0] at h
    norm_num at h

section Reindex

variable {α β : Type} [Fintype α] [Fintype β]

/-- Transport a standard LCP solution along an equivalence of index types. -/
def reindexStandardLCPSolution (e : α ≃ β) {M : α → α → ℝ}
    {q : β → ℝ}
    (solution : StandardLCPSolution M (fun i => q (e i))) :
    StandardLCPSolution (reindexMatrix e M) q where
  weight := fun i => solution.weight (e.symm i)
  weight_nonneg := fun i => solution.weight_nonneg (e.symm i)
  residual_nonneg := by
    intro i
    have h := solution.residual_nonneg (e.symm i)
    change 0 ≤ q i + ∑ j : β,
      solution.weight (e.symm j) * M (e.symm i) (e.symm j)
    have hsum : (∑ j : β,
        solution.weight (e.symm j) * M (e.symm i) (e.symm j)) =
        ∑ j : α, solution.weight j * M (e.symm i) j := by
      exact Equiv.sum_comp e.symm
        (fun j => solution.weight j * M (e.symm i) j)
    rw [hsum]
    simpa using h
  complementary := by
    intro i
    have h := solution.complementary (e.symm i)
    change solution.weight (e.symm i) *
      (q i + ∑ j : β,
        solution.weight (e.symm j) * M (e.symm i) (e.symm j)) = 0
    have hsum : (∑ j : β,
        solution.weight (e.symm j) * M (e.symm i) (e.symm j)) =
        ∑ j : α, solution.weight j * M (e.symm i) j := by
      exact Equiv.sum_comp e.symm
        (fun j => solution.weight j * M (e.symm i) j)
    rw [hsum]
    simpa using h

/-- Textbook standard-Q is invariant under reindexing. -/
theorem isStandardQMatrix_reindexMatrix (e : α ≃ β) (M : α → α → ℝ)
    (hQ : IsStandardQMatrix M) :
    IsStandardQMatrix (reindexMatrix e M) := by
  intro q
  obtain ⟨solution⟩ := hQ (fun i => q (e i))
  exact ⟨reindexStandardLCPSolution e solution⟩

end Reindex

section Realization

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Realize an arbitrary matrix as singleton terminal rewards.  Rewards of
larger coalitions are immaterial here and are assigned using one chosen
member. -/
def singletonRewardOfMatrix (M : α → α → ℝ) :
    {S : Finset α // S.Nonempty} → Payoff α := fun S who =>
  M who (Classical.choose S.2)

omit [Fintype α] [DecidableEq α] in
private theorem singletonRewardOfMatrix_singleton (M : α → α → ℝ)
    (who owner : α) :
    singletonRewardOfMatrix M (quittingProjectiveSingletonTerminal owner) who =
      M who owner := by
  unfold singletonRewardOfMatrix quittingProjectiveSingletonTerminal
  congr 1
  have hmem := Classical.choose_spec (Finset.singleton_nonempty owner)
  simpa using hmem

/-- Every real zero-diagonal matrix is exactly realizable as the normalized
singleton comparison matrix of a quitting reward table. -/
theorem normalizedSoloMatrix_singletonRewardOfMatrix
    (M : α → α → ℝ) (hdiag : ∀ i, M i i = 0) :
    normalizedSoloMatrix (singletonRewardOfMatrix M) = M := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  funext who owner
  simp only [quittingProjectiveLCPMatrix]
  rw [singletonRewardOfMatrix_singleton,
    singletonRewardOfMatrix_singleton, hdiag who, sub_zero]

end Realization

/-! ## Four-player embedding -/

abbrev Player := Option CorePlayer

/-- The witness has exactly four players. -/
theorem player_card : Fintype.card Player = 4 := by decide

/-- The cyclic successor, which gives every core row a distinct negative
comparison witness. -/
def next : CorePlayer → CorePlayer
  | 0 => 1
  | 1 => 2
  | 2 => 0

theorem next_ne (i : CorePlayer) : next i ≠ i := by
  fin_cases i <;> decide

@[simp] theorem cyclicMatrix_next (i : CorePlayer) :
    cyclicMatrix i (next i) = -1 := by
  fin_cases i
  · norm_num [next, cyclicMatrix]
  · simp [next, cyclicMatrix, show (2 : CorePlayer) ≠ 0 by decide,
      show (2 : CorePlayer) ≠ 1 by decide]
  · simp [next, cyclicMatrix, show (2 : CorePlayer) ≠ 0 by decide,
      show (2 : CorePlayer) ≠ 1 by decide]

/-- A four-player zero-diagonal comparison matrix.  The three `some` players
carry the cyclic block; the `none` player has only positive off-diagonal
comparisons and is removed by the first corrected screen. -/
def fourMatrix : Player → Player → ℝ
  | some i, some j => cyclicMatrix i j
  | some _, none => 1
  | none, some _ => 1
  | none, none => 0

@[simp] theorem fourMatrix_diagonal (i : Player) : fourMatrix i i = 0 := by
  cases i with
  | none => rfl
  | some i => fin_cases i <;> norm_num [fourMatrix, cyclicMatrix]

theorem some_mem_normalLayer (n : ℕ) (i : CorePlayer) :
    some i ∈ normalLayer fourMatrix n := by
  induction n generalizing i with
  | zero => simp [normalLayer]
  | succ n ih =>
      apply (mem_normalLayer_succ fourMatrix n (some i)).2
      refine ⟨ih i, some (next i), ih (next i), ?_, ?_⟩
      · intro h
        exact next_ne i (Option.some.inj h)
      · simp [fourMatrix]

theorem none_not_mem_normalLayer_one :
    none ∉ normalLayer fourMatrix 1 := by
  intro h
  obtain ⟨_, witness, _, hne, hle⟩ :=
    (mem_normalLayer_succ fourMatrix 0 none).mp h
  cases witness with
  | none => exact hne rfl
  | some witness => norm_num [fourMatrix] at hle

theorem mem_normalCore_iff (player : Player) :
    player ∈ normalCore fourMatrix ↔ ∃ i, player = some i := by
  constructor
  · intro h
    cases player with
    | none =>
        exact False.elim (none_not_mem_normalLayer_one
          ((mem_normalCore fourMatrix none).mp h 1))
    | some i => exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact (mem_normalCore fourMatrix (some i)).2
      (fun n => some_mem_normalLayer n i)

/-- The embedding of the three cyclic players into the corrected core. -/
def coreEmbedding (i : CorePlayer) : normalCore fourMatrix :=
  ⟨some i, (mem_normalCore_iff (some i)).2 ⟨i, rfl⟩⟩

/-- The evident identification of the corrected core with the cyclic block. -/
def coreEquiv : CorePlayer ≃ normalCore fourMatrix :=
  Equiv.ofBijective coreEmbedding ⟨by
    intro first second h
    have hval := congrArg (fun player => player.1) h
    exact Option.some.inj hval, by
    intro player
    obtain ⟨i, hi⟩ := (mem_normalCore_iff player.1).mp player.2
    exact ⟨i, Subtype.ext hi.symm⟩⟩

@[simp] theorem coreEquiv_apply (i : CorePlayer) :
    (coreEquiv i).1 = some i := rfl

theorem normalPlayerMatrix_eq_reindex :
    normalPlayerMatrix fourMatrix = reindexMatrix coreEquiv cyclicMatrix := by
  funext receiver owner
  let i := coreEquiv.symm receiver
  let j := coreEquiv.symm owner
  have hreceiver : receiver = coreEquiv i := by
    exact (coreEquiv.apply_symm_apply receiver).symm
  have howner : owner = coreEquiv j := by
    exact (coreEquiv.apply_symm_apply owner).symm
  rw [hreceiver, howner]
  simp [normalPlayerMatrix, principalMatrix, reindexMatrix, fourMatrix]

/-- The four-player matrix has nonempty corrected core. -/
theorem fourMatrix_hasNormalPlayers : HasNormalPlayers fourMatrix := by
  exact ⟨some 0, (mem_normalCore_iff (some 0)).2 ⟨0, rfl⟩⟩

/-- Its corrected principal matrix is textbook standard Q. -/
theorem fourMatrix_normal_standardQ :
    IsStandardQMatrix (normalPlayerMatrix fourMatrix) := by
  rw [normalPlayerMatrix_eq_reindex]
  exact isStandardQMatrix_reindexMatrix coreEquiv cyclicMatrix
    cyclicMatrix_standardQ

/-- Its corrected principal matrix has no homogeneous simplex solution. -/
theorem fourMatrix_normal_noHomogeneous :
    ¬HasHomogeneousSimplexSolution (normalPlayerMatrix fourMatrix) := by
  rw [normalPlayerMatrix_eq_reindex]
  intro h
  exact cyclicMatrix_noHomogeneous
    ((singletonLCPFeasible_reindexMatrix_iff coreEquiv cyclicMatrix).mp h)

/-- The explicit four-player quitting reward table realizing `fourMatrix`. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  singletonRewardOfMatrix fourMatrix

theorem normalizedSoloMatrix_reward : normalizedSoloMatrix reward = fourMatrix :=
  normalizedSoloMatrix_singletonRewardOfMatrix fourMatrix fourMatrix_diagonal

/-- **Exact satisfiability of the four-player algebraic necessary
condition.**  This reward table lies on the corrected-core standard-Q side:
the core is nonempty, its principal matrix has no homogeneous simplex
solution, and it is textbook standard Q. -/
theorem reward_standardQMatrixSide : StandardQMatrixSide reward := by
  refine
    { normal_nonempty := ?_
      no_homogeneous := ?_
      normal_standardQ := ?_ }
  · rw [normalizedSoloMatrix_reward]
    exact fourMatrix_hasNormalPlayers
  · change ¬HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward))
    rw [normalizedSoloMatrix_reward]
    exact fourMatrix_normal_noHomogeneous
  · change IsStandardQMatrix
      (normalPlayerMatrix (normalizedSoloMatrix reward))
    rw [normalizedSoloMatrix_reward]
    exact fourMatrix_normal_standardQ

end StandardQSideExample
end QuittingLCPClassification
end GameTheory

namespace GameTheory.QuittingLCPClassification.StandardQSideExample

#print axioms cyclicMatrix_standardQ
#print axioms cyclicMatrix_noHomogeneous
#print axioms normalizedSoloMatrix_singletonRewardOfMatrix
#print axioms reward_standardQMatrixSide

end GameTheory.QuittingLCPClassification.StandardQSideExample
