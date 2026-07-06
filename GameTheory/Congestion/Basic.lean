/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import Math.Probability

/-!
# Congestion games

In a congestion game each of finitely many players chooses a strategy that
occupies a finite set of resources, and the cost of each resource depends
only on how many players use it (its congestion). Player costs sum the
delays of the occupied resources. The resource and strategy types themselves
are unconstrained: aggregate quantities are supported on the finitely many
resources a profile occupies (`usedResources`), and strategy-set finiteness
appears only as a hypothesis on the theorems that genuinely need it.

This file provides the model and its congestion-counting toolkit. Rosenthal's
potential and its consequences live in `GameTheory.Congestion.Rosenthal`,
smoothness and price-of-anarchy bounds in `GameTheory.Congestion.AffinePoA`,
and the Pigou/Braess routing instances in `GameTheory.Congestion.Examples`.

## Main definitions

* `CongestionGame` — resources, per-player strategy sets, occupied resources,
  and congestion-dependent delays
* `CongestionGame.congestion` / `congestionWithout` — resource load counting
* `CongestionGame.playerCost` — sum of delays on the chosen resources
* `CongestionGame.socialCost` — total cost over all players
* `CongestionGame.toKernelGame` — the induced strategic game
  (utility = negative cost)

## Main results

* `congestion_decompose` / `congestion_update` — the deviation calculus of
  resource loads underlying both Rosenthal's potential and smoothness bounds
* `socialCost_eq_sum_load_delay` — social cost aggregates by resource:
  each occupied resource contributes its load times its delay
* `sum_congestion_mul_subset` — load-weighted sums extend from `usedResources`
  to any superset, the device for comparing aggregates across profiles
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

/-- A congestion game: finitely many players each choose a strategy occupying
a finite set of resources, and per-resource delays depend only on the load.
The resource and strategy types are otherwise arbitrary — finiteness enters
only where it is mathematically necessary (Nash existence, improvement
termination, finite-outcome bounds), as hypotheses on those theorems. -/
structure CongestionGame (ι : Type) [Fintype ι] where
  /-- The type of resources. -/
  Resource : Type
  /-- Abstract per-player strategy types; the resources a strategy occupies
  are given by `resources`. -/
  StrategySet : ι → Type
  /-- Which resources a strategy uses. -/
  resources : ∀ i, StrategySet i → Finset Resource
  /-- Delay/cost function for each resource, depending on congestion count. -/
  delay : Resource → ℕ → ℝ

namespace CongestionGame

variable {ι : Type} [Fintype ι]

/-- Profile type for a congestion game. -/
abbrev Profile (C : CongestionGame ι) := ∀ i, C.StrategySet i

open Classical in
/-- Count how many players use resource `r` under profile `σ`. -/
noncomputable def congestion (C : CongestionGame ι) (σ : C.Profile)
    (r : C.Resource) : ℕ :=
  (Finset.univ.filter fun i => r ∈ C.resources i (σ i)).card

open Classical in
/-- The resources actually occupied under profile `σ`. Aggregate quantities
(social-cost decompositions, Rosenthal's potential) are supported here, which
keeps the theory independent of any global finiteness of `Resource`. -/
noncomputable def usedResources (C : CongestionGame ι) (σ : C.Profile) :
    Finset C.Resource :=
  Finset.univ.biUnion fun i => C.resources i (σ i)

open Classical in
@[simp] theorem mem_usedResources {C : CongestionGame ι} {σ : C.Profile}
    {r : C.Resource} :
    r ∈ C.usedResources σ ↔ ∃ i, r ∈ C.resources i (σ i) := by
  simp [usedResources]

theorem resources_subset_usedResources (C : CongestionGame ι) (σ : C.Profile)
    (i : ι) : C.resources i (σ i) ⊆ C.usedResources σ :=
  fun _ hr => mem_usedResources.mpr ⟨i, hr⟩

open Classical in
/-- Unused resources carry no load. -/
theorem congestion_eq_zero_of_not_mem_usedResources {C : CongestionGame ι}
    {σ : C.Profile} {r : C.Resource} (h : r ∉ C.usedResources σ) :
    C.congestion σ r = 0 := by
  rw [congestion, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact fun hri => h (mem_usedResources.mpr ⟨i, hri⟩)

open Classical in
/-- Player `who`'s cost: sum of delays on their chosen resources. -/
noncomputable def playerCost (C : CongestionGame ι) (σ : C.Profile) (who : ι) : ℝ :=
  ∑ r ∈ C.resources who (σ who), C.delay r (C.congestion σ r)

open Classical in
/-- The social cost of a profile: total cost over all players. -/
noncomputable def socialCost (C : CongestionGame ι) (σ : C.Profile) : ℝ :=
  ∑ i, C.playerCost σ i

open Classical in
/-- Convert to a `KernelGame` with utility = negative cost. The outcome
carrier is the pure profile, so it is finite whenever the strategy sets are —
which lets finite-outcome results (mixed extensions, robust price-of-anarchy
bounds for coarse correlated equilibria) instantiate directly. -/
noncomputable def toKernelGame (C : CongestionGame ι) : KernelGame ι :=
  KernelGame.ofPureEU C.StrategySet (fun σ i => -C.playerCost σ i)

@[simp] theorem eu_toKernelGame (C : CongestionGame ι) (σ : C.Profile) (i : ι) :
    C.toKernelGame.eu σ i = -C.playerCost σ i := by
  simp [toKernelGame]

open Classical in
/-- Congestion excluding player `who`: count of other players using resource `r`. -/
noncomputable def congestionWithout (C : CongestionGame ι) (σ : C.Profile)
    (who : ι) (r : C.Resource) : ℕ :=
  (Finset.univ.filter fun i => i ≠ who ∧ r ∈ C.resources i (σ i)).card

open Classical in
/-- Congestion = other players' congestion + player `who`'s indicator. -/
theorem congestion_decompose (C : CongestionGame ι) (σ : C.Profile)
    (who : ι) (r : C.Resource) :
    C.congestion σ r = C.congestionWithout σ who r +
      if r ∈ C.resources who (σ who) then 1 else 0 := by
  simp only [congestion, congestionWithout]
  set S := Finset.univ.filter fun i => r ∈ C.resources i (σ i)
  set T := Finset.univ.filter fun i => i ≠ who ∧ r ∈ C.resources i (σ i)
  have hT_eq : T = S.erase who := by
    ext i; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      true_and, T, S, ne_eq]
  rw [hT_eq]
  split_ifs with h
  · have hm : who ∈ S := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]; exact h
    have : 0 < S.card := Finset.card_pos.mpr ⟨who, hm⟩
    rw [Finset.card_erase_of_mem hm]; omega
  · have hm : who ∉ S := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]; exact h
    rw [Finset.erase_eq_self.mpr hm]; omega

open Classical in
/-- Other players' congestion is invariant under `Function.update` for `who`. -/
theorem congestionWithout_update [DecidableEq ι] (C : CongestionGame ι) (σ : C.Profile)
    (who : ι) (s' : C.StrategySet who) (r : C.Resource) :
    C.congestionWithout (Function.update σ who s') who r =
    C.congestionWithout σ who r := by
  simp only [congestionWithout]
  congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, h⟩; exact ⟨hne, by rwa [Function.update_of_ne hne] at h⟩
  · rintro ⟨hne, h⟩; exact ⟨hne, by rwa [Function.update_of_ne hne]⟩

open Classical in
/-- Congestion after `Function.update`: others' congestion + new indicator. -/
theorem congestion_update [DecidableEq ι] (C : CongestionGame ι) (σ : C.Profile)
    (who : ι) (s' : C.StrategySet who) (r : C.Resource) :
    C.congestion (Function.update σ who s') r =
    C.congestionWithout σ who r +
    if r ∈ C.resources who s' then 1 else 0 := by
  have h := congestion_decompose C (Function.update σ who s') who r
  simp only [Function.update_self] at h
  rw [h, congestionWithout_update]

open Classical in
/-- Loads never exceed the other players' load by more than one. -/
theorem congestion_le_congestionWithout_add_one (C : CongestionGame ι)
    (σ : C.Profile) (who : ι) (r : C.Resource) :
    C.congestion σ r ≤ C.congestionWithout σ who r + 1 := by
  rw [congestion_decompose C σ who r]
  split_ifs <;> omega

open Classical in
/-- Other players' loads are bounded by the full load. -/
theorem congestionWithout_le_congestion (C : CongestionGame ι)
    (σ : C.Profile) (who : ι) (r : C.Resource) :
    C.congestionWithout σ who r ≤ C.congestion σ r := by
  rw [congestion_decompose C σ who r]
  split_ifs <;> omega

open Classical in
/-- Per-resource quantities summed over each player's chosen resources
aggregate by load: resource `r` is counted `congestion σ r` times. -/
theorem sum_players_sum_resources (C : CongestionGame ι) (σ : C.Profile)
    (f : C.Resource → ℝ) :
    ∑ i, ∑ r ∈ C.resources i (σ i), f r
      = ∑ r ∈ C.usedResources σ, (C.congestion σ r : ℝ) * f r := by
  have h : ∀ i, ∑ r ∈ C.resources i (σ i), f r
      = ∑ r ∈ C.usedResources σ, if r ∈ C.resources i (σ i) then f r else 0 := by
    intro i
    conv_rhs => rw [Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr (C.resources_subset_usedResources σ i)]
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul]
  rfl

open Classical in
/-- Load-weighted per-resource sums are supported on the used resources, so
they extend to any superset. -/
theorem sum_congestion_mul_subset (C : CongestionGame ι) (σ : C.Profile)
    {S : Finset C.Resource} (hS : C.usedResources σ ⊆ S) (f : C.Resource → ℝ) :
    ∑ r ∈ C.usedResources σ, (C.congestion σ r : ℝ) * f r
      = ∑ r ∈ S, (C.congestion σ r : ℝ) * f r :=
  Finset.sum_subset hS fun r _ hr => by
    rw [congestion_eq_zero_of_not_mem_usedResources hr]
    simp

open Classical in
/-- Social cost aggregates by resource: each occupied resource contributes
its delay taken with multiplicity its load. -/
theorem socialCost_eq_sum_load_delay (C : CongestionGame ι) (σ : C.Profile) :
    C.socialCost σ
      = ∑ r ∈ C.usedResources σ,
          (C.congestion σ r : ℝ) * C.delay r (C.congestion σ r) := by
  rw [socialCost]
  simp only [playerCost]
  exact C.sum_players_sum_resources σ _

end CongestionGame

end GameTheory
