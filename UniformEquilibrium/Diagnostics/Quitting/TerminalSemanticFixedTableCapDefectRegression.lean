/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFixedTableDiffuseIncidenceRegression

/-!
# The fixed-table diffuse regression at its displayed cap

The base fixed-table regression evaluates the generating root's small
Nash defect against the prescribed payoff `0`, while uniqueness of the exact
cap correspondence is stated against the semantic envelope.  Those two
continuation vectors must not be silently identified.

For the same fixed table the intended stronger statement is nevertheless
true.  Against the displayed envelope cap `[0,q,0]`, the generating root has
total defect `2q-q^2`, while its terminal-law opponent incidence stays at
least `1/2`.  Hence no constant depending only on this fixed reward table can
linearly charge incidence by the *cap-local* root defect either.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

namespace QuittingFixedTableCapDefectRegression

open QuittingFixedTableDiffuseIncidenceRegression

/-- Root coordinate defect depends only on the matching coordinate of the
continuation vector. -/
theorem coordinateNashDefect_continuation_congr
    (first second : Payoff Player) (candidate : Player -> PMF Bool)
    (who : Player) (hcoordinate : first who = second who) :
    quittingRootCoordinateNashDefect reward first candidate who =
      quittingRootCoordinateNashDefect reward second candidate who := by
  unfold quittingRootCoordinateNashDefect
  have hsuccessor : quittingRootSuccessorPayoff reward first candidate who =
      quittingRootSuccessorPayoff reward second candidate who := by
    exact quittingRootExpectedPayoff_continuation_congr
      reward first second candidate who hcoordinate
  have hquit : quittingRootQuitPayoff reward first candidate who =
      quittingRootQuitPayoff reward second candidate who :=
    quittingRootQuitPayoff_continuation_invariant
      reward first second candidate who
  have hcontinue : quittingRootContinuePayoff reward first candidate who =
      quittingRootContinuePayoff reward second candidate who := by
    unfold quittingRootContinuePayoff
    exact quittingRootExpectedPayoff_continuation_congr reward first second
      (Function.update candidate who (PMF.pure false)) who hcoordinate
  rw [hsuccessor, hquit, hcontinue]

theorem cap_eq_update_zero_debtor (n : ℕ) :
    (pair n).2 = Function.update (fun _ : Player => 0) debtor (q n) := by
  rw [(pair_coordinates n).2]
  funext who
  fin_cases who <;> simp [debtor]

theorem root_opponentContinueMass_debtor (n : ℕ) :
    quittingRootOpponentContinueMass (root n) debtor = 1 - q n := by
  unfold quittingRootOpponentContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {owner, debtor, switch} by decide]
  simp [root, owner, debtor, switch]

theorem cap_quitPayoff_debtor (n : ℕ) :
    quittingRootQuitPayoff reward (pair n).2 (root n) debtor = 0 := by
  rw [quittingRootQuitPayoff_continuation_invariant reward (pair n).2
    (fun _ => 0) (root n) debtor]
  exact generating_quitPayoff_debtor n

theorem cap_continuePayoff_debtor (n : ℕ) :
    quittingRootContinuePayoff reward (pair n).2 (root n) debtor =
      2 * q n - (q n) ^ 2 := by
  rw [cap_eq_update_zero_debtor]
  have hadd := quittingRootContinuePayoff_update_add
    reward (fun _ : Player => 0) (root n) debtor (q n)
  simp only [zero_add] at hadd
  rw [hadd, generating_continuePayoff_debtor,
    root_opponentContinueMass_debtor]
  ring

theorem cap_successorPayoff_debtor (n : ℕ) :
    quittingRootSuccessorPayoff reward (pair n).2 (root n) debtor = 0 := by
  have hsure : QuittingRootHasSureQuitter (root n) := by
    refine ⟨debtor, ?_⟩
    simp [root, debtor]
  have hinvariant := quittingRootExpectedPayoff_eq_of_hasSureQuitter
    reward (root n) hsure (pair n).2 (fun _ => 0) debtor
  change quittingRootSuccessorPayoff reward (pair n).2 (root n) debtor =
    quittingRootSuccessorPayoff reward (fun _ => 0) (root n) debtor
    at hinvariant
  rw [hinvariant]
  exact generating_successorPayoff_debtor n

/-- The sole cap-local defect is the sure quitter's refusal gain
`2q-q^2`. -/
theorem cap_coordinateNashDefect (n : ℕ) (who : Player) :
    quittingRootCoordinateNashDefect reward (pair n).2 (root n) who =
      if who = debtor then 2 * q n - (q n) ^ 2 else 0 := by
  by_cases hwho : who = debtor
  · subst who
    rw [if_pos rfl]
    unfold quittingRootCoordinateNashDefect
    rw [cap_quitPayoff_debtor, cap_continuePayoff_debtor,
      cap_successorPayoff_debtor]
    have hq0 := q_pos n
    have hq1 := q_le_one n
    rw [max_eq_right]
    · ring
    · nlinarith
  · rw [if_neg hwho]
    have hcoordinate : (pair n).2 who = (fun _ : Player => 0) who := by
      rw [(pair_coordinates n).2]
      fin_cases who <;> simp [debtor] at hwho ⊢
    rw [coordinateNashDefect_continuation_congr
      (pair n).2 (fun _ => 0) (root n) who hcoordinate]
    rw [generating_coordinateNashDefect]
    simp [hwho]

theorem cap_totalNashDefect (n : ℕ) :
    quittingRootTotalNashDefect reward (pair n).2 (root n) =
      2 * q n - (q n) ^ 2 := by
  unfold quittingRootTotalNashDefect
  simp_rw [cap_coordinateNashDefect]
  rw [show (Finset.univ : Finset Player) = {owner, debtor, switch} by decide]
  simp [owner, debtor, switch]

theorem cap_totalNashDefect_pos (n : ℕ) :
    0 < quittingRootTotalNashDefect reward (pair n).2 (root n) := by
  rw [cap_totalNashDefect]
  nlinarith [q_pos n, q_le_one n]

theorem cap_totalNashDefect_le_two_mul_q (n : ℕ) :
    quittingRootTotalNashDefect reward (pair n).2 (root n) ≤ 2 * q n := by
  rw [cap_totalNashDefect]
  nlinarith [sq_nonneg (q n)]

theorem cap_totalNashDefect_tendsto_zero :
    Tendsto (fun n =>
      quittingRootTotalNashDefect reward (pair n).2 (root n))
      atTop (nhds 0) := by
  have hq : Tendsto (fun n : ℕ => q n) atTop (nhds 0) := by
    have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hshift : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2))
        atTop (nhds 0) := by
      apply (hzero.comp (tendsto_add_atTop_nat 1)).congr'
      exact Filter.Eventually.of_forall fun n => by
        simp [Nat.cast_add]
        ring
    simpa [q] using hshift
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  rw [show (fun n =>
      quittingRootTotalNashDefect reward (pair n).2 (root n)) =
        fun n => 2 * q n - (q n) ^ 2 by
      funext n
      exact cap_totalNashDefect n]
  simpa using (htwo.mul hq).sub (hq.pow 2)

/-- No table-dependent linear incidence price exists even when the defect is
evaluated at the displayed semantic envelope cap. -/
theorem no_fixedTable_linear_incidence_le_capTotalNashDefect :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        quittingTerminalTotalOpponentIncidenceMass owner (mass n) ≤
          C * quittingRootTotalNashDefect reward (pair n).2 (root n) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * C)
  have hden : (0 : ℝ) < n + 2 := by positivity
  have hratio : 2 * C / (n + 2 : ℝ) < 1 / 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hlower := totalOpponentIncidence_ge_half n
  have hupper := hbound n
  have hdefectUpper := cap_totalNashDefect_le_two_mul_q n
  have hscaled : C *
      quittingRootTotalNashDefect reward (pair n).2 (root n) ≤
        2 * C / (n + 2 : ℝ) := by
    calc
      C * quittingRootTotalNashDefect reward (pair n).2 (root n) ≤
          C * (2 * q n) := mul_le_mul_of_nonneg_left hdefectUpper hC
      _ = 2 * C / (n + 2 : ℝ) := by
        unfold q
        ring
  linarith

/-- Complete cap-local passport. -/
theorem fixedTable_capIncidence_defect_tendsToZero_uniqueAllContinue :
    (∀ n, 1 / 2 ≤
      quittingTerminalTotalOpponentIncidenceMass owner (mass n)) ∧
      Tendsto (fun n =>
        quittingRootTotalNashDefect reward (pair n).2 (root n))
        atTop (nhds 0) ∧
      (∀ n candidate,
        IsεQuittingRootNash reward (pair n).2 0 candidate ->
          candidate = (quittingAllContinueRoot : Player -> PMF Bool)) := by
  exact ⟨totalOpponentIncidence_ge_half, cap_totalNashDefect_tendsto_zero,
    exact_capNash_forces_allContinue⟩

end QuittingFixedTableCapDefectRegression

end GameTheory
