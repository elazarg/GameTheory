/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Math.Probability
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Mechanism.InformationalGame

/-!
# Vickrey-Clarke-Groves (VCG) Mechanism

The VCG mechanism generalizes the Vickrey auction: each player reports
their type, an efficient allocation is chosen, and payments are set so
that each player's incentive aligns with social welfare maximization.
The key result is that truthful reporting is a dominant strategy.

## Main definitions

* `VCGSetup` — a VCG problem: types, outcomes, valuations, efficient allocation
* `VCGSetup.vcgPayment` — the VCG payment rule
* `VCGSetup.trueUtility` — player's true utility (true valuation - payment)

## Main results

* `vcg_truthful` — truthful reporting is dominant-strategy IC in VCG
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A VCG setup specifies types, outcomes, valuations, an efficient allocation
    rule, and per-player h-functions (independent of own report). -/
structure VCGSetup (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- Type space for each player. -/
  Θ : ι → Type
  /-- Outcome space. -/
  Outcome : Type
  /-- Valuation: player `i`'s value for outcome `o` given their type. -/
  val : (i : ι) → Θ i → Outcome → ℝ
  /-- The efficient allocation rule: given reports, picks the outcome
      maximizing total reported value. -/
  alloc : (∀ i, Θ i) → Outcome
  /-- The allocation is efficient: it maximizes total reported value. -/
  alloc_efficient : ∀ (θ : ∀ i, Θ i) (o : Outcome),
    ∑ i, val i (θ i) (alloc θ) ≥ ∑ i, val i (θ i) o
  /-- The h-function for player `i`: depends only on others' reports. -/
  h : (i : ι) → (∀ j, Θ j) → ℝ
  /-- The h-function ignores player `i`'s own report. -/
  h_indep : ∀ i, Math.Probability.IndependentOfCoordinate i (h i)

namespace VCGSetup

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (V : VCGSetup ι)

/-- VCG payment for player `i` given reports `report`:
    `p_i = h_i(report_{-i}) - Σ_{j≠i} v_j(report_j, alloc(report))`. -/
noncomputable def vcgPayment (report : ∀ i, V.Θ i) (i : ι) : ℝ :=
  V.h i report - ∑ j ∈ Finset.univ.filter (· ≠ i), V.val j (report j) (V.alloc report)

/-- Player `i`'s true utility when their true type is `θ_i` and the
    reported profile is `report`: `v_i(θ_i, alloc(report)) - payment`. -/
noncomputable def trueUtility (i : ι) (θ_i : V.Θ i) (report : ∀ j, V.Θ j) : ℝ :=
  V.val i θ_i (V.alloc report) - V.vcgPayment report i

/-- True utility decomposes as: `v_i(θ_i, alloc) + Σ_{j≠i} v_j(report_j, alloc) - h_i`. -/
theorem trueUtility_eq (i : ι) (θ_i : V.Θ i) (report : ∀ j, V.Θ j) :
    V.trueUtility i θ_i report =
    V.val i θ_i (V.alloc report) +
    ∑ j ∈ Finset.univ.filter (· ≠ i), V.val j (report j) (V.alloc report) -
    V.h i report := by
  simp only [trueUtility, vcgPayment]; ring

/-- Truthful reporting is a dominant strategy in VCG.

    When player `i` with true type `θ_i` reports truthfully, the allocation
    maximizes `Σ_j v_j(θ_j, o)`. Any misreport changes the allocation to
    one that does not maximize this sum with true types, while the h-function
    is unaffected. -/
theorem vcg_truthful (θ : ∀ i, V.Θ i) (i : ι) (θ'_i : V.Θ i) :
    V.trueUtility i (θ i) θ ≥
    V.trueUtility i (θ i) (Function.update θ i θ'_i) := by
  rw [V.trueUtility_eq i (θ i) θ, V.trueUtility_eq i (θ i) (Function.update θ i θ'_i)]
  -- h_i is independent of i's report
  have hh : V.h i θ = V.h i (Function.update θ i θ'_i) := V.h_indep i θ θ'_i
  -- Others' reports don't change
  have hothers : ∑ j ∈ Finset.univ.filter (· ≠ i),
      V.val j (Function.update θ i θ'_i j) (V.alloc (Function.update θ i θ'_i)) =
      ∑ j ∈ Finset.univ.filter (· ≠ i),
      V.val j (θ j) (V.alloc (Function.update θ i θ'_i)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [Function.update_of_ne hj]
  rw [hothers, hh]
  -- Efficiency: Σ_j v_j(θ_j, alloc(θ)) ≥ Σ_j v_j(θ_j, alloc(θ'))
  have heff := V.alloc_efficient θ (V.alloc (Function.update θ i θ'_i))
  -- Split the full sum: Σ_j v_j(θ_j, o) = v_i(θ_i, o) + Σ_{j≠i} v_j(θ_j, o)
  have hsplit (o : V.Outcome) : ∑ j, V.val j (θ j) o =
      V.val i (θ i) o + ∑ j ∈ Finset.univ.filter (· ≠ i), V.val j (θ j) o := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1; apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp [Finset.mem_erase, Finset.mem_filter]
  rw [hsplit, hsplit] at heff
  linarith

/-! ## Informational-game view -/

/-- The direct VCG mechanism as a prior-free informational game: signals are
true types, actions are reports, and payoff is true quasi-linear VCG utility. -/
noncomputable def toInformationalGame : InformationalGame ι where
  Signal := V.Θ
  Act := V.Θ
  utility := fun θ report => fun i => V.trueUtility i (θ i) report

/-- Truthful reporting in the informational-game view of a VCG setup. -/
def truthfulStrategy : V.toInformationalGame.StrategyProfile :=
  fun _ θi => θi

@[simp] theorem toInformationalGame_play_truthful (θ : V.toInformationalGame.SignalProfile) :
    V.toInformationalGame.play V.truthfulStrategy θ = θ := by
  funext i
  simp [InformationalGame.play, truthfulStrategy, toInformationalGame]

/-- VCG truthfulness as ex-post equilibrium of the direct informational game. -/
theorem truthfulStrategy_isExPostEq :
    V.toInformationalGame.IsExPostEq V.truthfulStrategy := by
  intro θ i report
  change V.trueUtility i (θ i)
      (V.toInformationalGame.play V.truthfulStrategy θ) ≥
    V.trueUtility i (θ i)
      (Function.update (V.toInformationalGame.play V.truthfulStrategy θ) i report)
  rw [V.toInformationalGame_play_truthful]
  exact V.vcg_truthful θ i report

end VCGSetup

end GameTheory
