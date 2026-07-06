/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Congestion.Basic
import GameTheory.Concepts.Potential.PotentialFIP
import GameTheory.Concepts.Potential.PotentialWellFounded

/-!
# Rosenthal's potential

Rosenthal (1973): every congestion game admits an exact potential — the
negated sum, over resources, of the cumulative delays up to the current load.
Through the library's potential-game cluster this yields pure Nash existence,
the finite improvement property, and weak acyclicity of better-response
dynamics.

## Main results

* `CongestionGame.isExactPotential` — Rosenthal's theorem
* `CongestionGame.nash_exists` — pure Nash equilibria exist
* `CongestionGame.no_infinite_improving_path` — the finite improvement property
* `CongestionGame.weaklyAcyclic` — better-response dynamics reach a Nash
  equilibrium from every profile
-/

open scoped BigOperators

namespace GameTheory

namespace CongestionGame

variable {ι : Type} [Fintype ι]

open Classical in
/-- Rosenthal's potential function: negative sum over resources of cumulative delay. -/
noncomputable def potential (C : CongestionGame ι) (σ : C.Profile) : ℝ :=
  - ∑ r : C.Resource, ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1)

open Classical in
/-- Rosenthal's theorem: the potential function is an exact potential
    for the congestion game. -/
theorem isExactPotential (C : CongestionGame ι) :
    C.toKernelGame.IsExactPotential C.potential := by
  classical
  intro who (σ : C.Profile) (s' : C.StrategySet who)
  simp only [toKernelGame, KernelGame.eu_ofEU, playerCost, potential, Function.update_self]
  set σ' := Function.update σ who s'
  suffices h : ∑ r ∈ C.resources who (σ who), C.delay r (C.congestion σ r) -
      ∑ r ∈ C.resources who s', C.delay r (C.congestion σ' r) =
      ∑ r, ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1) -
      ∑ r, ∑ k ∈ Finset.range (C.congestion σ' r), C.delay r (k + 1) by
    change -(∑ r ∈ C.resources who s', C.delay r (C.congestion σ' r)) -
          -(∑ r ∈ C.resources who (σ who), C.delay r (C.congestion σ r)) =
        -(∑ r, ∑ k ∈ Finset.range (C.congestion σ' r), C.delay r (k + 1)) -
          -(∑ r, ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1))
    linarith
  have h_sum_eq : ∀ (S : Finset C.Resource) (f : C.Resource → ℝ),
      ∑ r ∈ S, f r = ∑ r, if r ∈ S then f r else 0 := by
    intro S f; conv_rhs => rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h_sum_eq (C.resources who (σ who)), h_sum_eq (C.resources who s')]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  set n := C.congestionWithout σ who r
  rw [C.congestion_decompose σ who r, C.congestion_update σ who s' r]
  by_cases hold : r ∈ C.resources who (σ who) <;> by_cases hnew : r ∈ C.resources who s'
  · simp [hold, hnew]
  · simp only [hold, hnew, ite_true, ite_false, add_zero]
    rw [Finset.sum_range_succ]; ring
  · simp only [hold, hnew, ite_true, ite_false, add_zero]
    rw [Finset.sum_range_succ]; ring
  · simp [hold, hnew]

open Classical in
/-- Congestion games have Nash equilibria (via Rosenthal's potential). -/
theorem nash_exists (C : CongestionGame ι) [∀ i, Nonempty (C.StrategySet i)] :
    ∃ σ : C.Profile, C.toKernelGame.IsNash σ := by
  haveI (i : ι) : Fintype (C.toKernelGame.Strategy i) := C.instFintypeStrategy i
  haveI (i : ι) : Nonempty (C.toKernelGame.Strategy i) := ‹∀ i, Nonempty (C.StrategySet i)› i
  exact C.isExactPotential.nash_exists

open Classical in
/-- Congestion games have the finite improvement property. -/
theorem no_infinite_improving_path (C : CongestionGame ι) :
    ¬ ∃ (path : ℕ → C.Profile),
        ∀ n, C.toKernelGame.ImprovingStep (path n) (path (n + 1)) := by
  haveI (i : ι) : Finite (C.toKernelGame.Strategy i) :=
    @Fintype.finite _ (C.instFintypeStrategy i)
  exact C.isExactPotential.no_infinite_improving_path

open Classical in
/-- Better-response dynamics in a congestion game reach a Nash equilibrium
from every starting profile. -/
theorem weaklyAcyclic (C : CongestionGame ι) :
    C.toKernelGame.WeaklyAcyclic := by
  haveI (i : ι) : Finite (C.toKernelGame.Strategy i) :=
    @Fintype.finite _ (C.instFintypeStrategy i)
  haveI : Finite (KernelGame.Profile C.toKernelGame) := by
    exact Pi.finite
  exact C.isExactPotential.weaklyAcyclic

end CongestionGame

end GameTheory
