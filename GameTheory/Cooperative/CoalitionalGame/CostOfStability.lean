/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Cooperative.CoalitionalGame.Core
import GameTheory.Cooperative.CoalitionalGame.Convex
import GameTheory.Cooperative.CoalitionalGame.Additive
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Cost of stability

The *cost of stability* (Bachrach–Elkind–Meir–Pasechnik–Zuckerman–Rothe–Rosenschein,
*The Cost of Stability in Coalitional Games*, 2009) of a TU game is the smallest
external subsidy that must be injected into the grand coalition to make the core
nonempty: with a supplement of `Δ` paid to the players, can they divide
`v(N) + Δ` so that no coalition has an incentive to deviate?

## Main definitions

* `CoalGame.IsStabilizable G Δ` — a subsidy of `Δ` admits a coalition-rational allocation
* `CoalGame.costOfStability G` — the least nonnegative stabilizing subsidy

## Main results

* `isStabilizable_zero_iff_core` — zero subsidy stabilizes iff the core is nonempty
* `IsStabilizable.mono` — stabilizability is preserved by increasing the subsidy
* `exists_stabilizable` — a large enough subsidy always stabilizes
* `costOfStability_nonneg` — the cost of stability is nonnegative
* `costOfStability_le` — any nonnegative stabilizing subsidy bounds it
* `costOfStability_eq_zero_of_core` — a nonempty core means zero cost of stability
* `costOfStability_eq_zero_of_nonneg_unanimityCoeff` / `costOfStability_additiveGame_eq_zero`
  — stable classes (nonnegative Harsanyi dividends; additive games) need no subsidy

Only the direction *nonempty core ⇒ zero cost* is formalized here. The converse
(*zero cost ⇒ nonempty core*) requires an infimum-attainment / LP-duality
argument — the infimum could a priori be `0` without `0` lying in the set — and
is left to follow-on work.
-/

open scoped BigOperators

namespace GameTheory

namespace CoalGame

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- The game `G` is *stabilizable with subsidy `Δ`* if injecting a total external
payment of `Δ` into the grand coalition admits a coalition-rational division: some
allocation `x` with `∑ x = v(N) + Δ` under which every coalition `S` receives at
least its own value `v(S)`. For `Δ = 0` this is exactly membership of the core. -/
def IsStabilizable (G : CoalGame ι) (Δ : ℝ) : Prop :=
  ∃ x : ι → ℝ, (∑ i, x i = G.v Finset.univ + Δ) ∧
    ∀ S : Finset ι, G.v S ≤ ∑ i ∈ S, x i

/-- A zero subsidy stabilizes the game exactly when its core is nonempty. -/
theorem isStabilizable_zero_iff_core (G : CoalGame ι) :
    G.IsStabilizable 0 ↔ ∃ x, G.IsCore x := by
  constructor
  · rintro ⟨x, heff, hcr⟩
    exact ⟨x, by rw [add_zero] at heff; exact heff, fun S => hcr S⟩
  · rintro ⟨x, heff, hcr⟩
    exact ⟨x, by rw [add_zero]; exact heff, fun S => hcr S⟩

/-- Increasing the subsidy preserves stabilizability: the extra surplus can be
handed to any single player without breaking any coalition's rationality. -/
theorem IsStabilizable.mono [Nonempty ι] {G : CoalGame ι} {Δ Δ' : ℝ}
    (h : G.IsStabilizable Δ) (hΔ : Δ ≤ Δ') : G.IsStabilizable Δ' := by
  obtain ⟨x, heff, hcr⟩ := h
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨Function.update x i₀ (x i₀ + (Δ' - Δ)), ?_, ?_⟩
  · rw [Finset.sum_update_of_mem (Finset.mem_univ i₀)]
    have hsplit := Finset.add_sum_erase Finset.univ x (Finset.mem_univ i₀)
    rw [heff, Finset.erase_eq] at hsplit
    linarith [hsplit]
  · intro S
    by_cases hi₀ : i₀ ∈ S
    · rw [Finset.sum_update_of_mem hi₀]
      have hge := hcr S
      have heq := Finset.add_sum_erase S x hi₀
      rw [Finset.erase_eq] at heq
      have hd : 0 ≤ Δ' - Δ := by linarith
      linarith [hge, heq]
    · rw [Finset.sum_congr rfl (fun i hi => by
        rw [Function.update_apply, if_neg (show ¬ i = i₀ by rintro rfl; exact hi₀ hi)])]
      exact hcr S

/-- A large enough subsidy always stabilizes the game: pay every player the
maximum coalition value, which dominates every coalition's worth. -/
theorem exists_stabilizable [Nonempty ι] (G : CoalGame ι) :
    ∃ Δ, 0 ≤ Δ ∧ G.IsStabilizable Δ := by
  classical
  have hne : (Finset.univ : Finset (Finset ι)).Nonempty := ⟨∅, Finset.mem_univ ∅⟩
  set c : ℝ := (Finset.univ : Finset (Finset ι)).sup' hne G.v with hc
  have hc_nonneg : 0 ≤ c := by
    have := Finset.le_sup' G.v (Finset.mem_univ (∅ : Finset ι))
    rwa [G.v_empty] at this
  have hvc : ∀ S : Finset ι, G.v S ≤ c := fun S => Finset.le_sup' G.v (Finset.mem_univ S)
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have : 1 ≤ Fintype.card ι := Fintype.card_pos
    exact_mod_cast this
  refine ⟨(Fintype.card ι : ℝ) * c - G.v Finset.univ, ?_, ?_⟩
  · nlinarith [hvc Finset.univ, hc_nonneg, hcard,
      mul_nonneg (show (0 : ℝ) ≤ (Fintype.card ι : ℝ) - 1 by linarith) hc_nonneg]
  · refine ⟨fun _ => c, ?_, ?_⟩
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    · intro S
      rw [Finset.sum_const, nsmul_eq_mul]
      rcases Finset.eq_empty_or_nonempty S with rfl | hSne
      · simp [G.v_empty]
      · have h1 : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSne
        calc G.v S ≤ c := hvc S
          _ = 1 * c := (one_mul c).symm
          _ ≤ (S.card : ℝ) * c := mul_le_mul_of_nonneg_right h1 hc_nonneg

/-- The set of nonnegative stabilizing subsidies is bounded below (by `0`). -/
theorem stabilizable_set_bddBelow (G : CoalGame ι) :
    BddBelow {Δ : ℝ | 0 ≤ Δ ∧ G.IsStabilizable Δ} :=
  ⟨0, fun _ hΔ => hΔ.1⟩

/-- The **cost of stability**: the least nonnegative subsidy that stabilizes the
game. -/
noncomputable def costOfStability (G : CoalGame ι) : ℝ :=
  sInf {Δ : ℝ | 0 ≤ Δ ∧ G.IsStabilizable Δ}

/-- Any nonnegative stabilizing subsidy is an upper bound for the cost of
stability. -/
theorem costOfStability_le {G : CoalGame ι} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (h : G.IsStabilizable Δ) : G.costOfStability ≤ Δ :=
  csInf_le G.stabilizable_set_bddBelow ⟨hΔ, h⟩

/-- The cost of stability is nonnegative. -/
theorem costOfStability_nonneg [Nonempty ι] (G : CoalGame ι) :
    0 ≤ G.costOfStability := by
  obtain ⟨Δ, hΔ0, hΔ⟩ := G.exists_stabilizable
  exact le_csInf ⟨Δ, hΔ0, hΔ⟩ (fun _ hb => hb.1)

/-- If the core is nonempty, the cost of stability is zero: no subsidy is needed. -/
theorem costOfStability_eq_zero_of_core [Nonempty ι] {G : CoalGame ι}
    (h : ∃ x, G.IsCore x) : G.costOfStability = 0 := by
  have h0 : G.IsStabilizable 0 := (isStabilizable_zero_iff_core G).2 h
  exact le_antisymm (G.costOfStability_le le_rfl h0) (G.costOfStability_nonneg)

/-- A game with nonnegative unanimity-basis (Harsanyi-dividend) coefficients has
zero cost of stability: its Shapley value already lies in the core. -/
theorem costOfStability_eq_zero_of_nonneg_unanimityCoeff [Nonempty ι] {G : CoalGame ι}
    (hcoeff : ∀ S : Finset ι, 0 ≤ G.unanimityCoeff S) : G.costOfStability = 0 :=
  costOfStability_eq_zero_of_core ⟨_, G.shapleyValue_isCore_of_nonneg_unanimityCoeff hcoeff⟩

/-- An additive game has zero cost of stability: the weight vector is itself in the
core (with equality on every coalition). -/
theorem costOfStability_additiveGame_eq_zero [Nonempty ι] (α : ι → ℝ) :
    (additiveGame α).costOfStability = 0 :=
  costOfStability_eq_zero_of_core ⟨α, rfl, fun _ => le_refl _⟩

end CoalGame

end GameTheory
