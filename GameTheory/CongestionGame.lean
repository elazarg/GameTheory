import GameTheory.GameProperties
import GameTheory.SolutionConcepts
import GameTheory.PotentialFIP
import GameTheory.PotentialWellFounded

/-!
# Congestion Games

A congestion game has a finite set of resources. Each player chooses a
subset of resources (their strategy), and the cost/payoff for each resource
depends only on how many players use it (congestion). Rosenthal (1973)
proved that every congestion game admits an exact potential function.

## Main definitions

* `CongestionGame` — congestion game structure
* `CongestionGame.toKernelGame` — embedding into `KernelGame`
* `CongestionGame.potential` — Rosenthal's potential function

## Main results

* `CongestionGame.isExactPotential` — Rosenthal's theorem: the potential is exact
-/

open scoped BigOperators

namespace GameTheory

/-- A congestion game: players choose subsets of resources, payoffs depend on congestion. -/
structure CongestionGame (ι : Type) [Fintype ι] where
  /-- The type of resources. -/
  Resource : Type
  [instFintypeResource : Fintype Resource]
  /-- Each player's strategy is a `Finset` of resources. -/
  StrategySet : ι → Type
  [instFintypeStrategy : ∀ i, Fintype (StrategySet i)]
  /-- Which resources a strategy uses. -/
  resources : ∀ i, StrategySet i → Finset Resource
  /-- Delay/cost function for each resource, depending on congestion count. -/
  delay : Resource → ℕ → ℝ

attribute [instance] CongestionGame.instFintypeResource CongestionGame.instFintypeStrategy

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
/-- Player `who`'s cost: sum of delays on their chosen resources. -/
noncomputable def playerCost (C : CongestionGame ι) (σ : C.Profile) (who : ι) : ℝ :=
  ∑ r ∈ C.resources who (σ who), C.delay r (C.congestion σ r)

open Classical in
/-- Convert to a `KernelGame` with utility = negative cost. -/
noncomputable def toKernelGame (C : CongestionGame ι) : KernelGame ι :=
  KernelGame.ofEU C.StrategySet (fun σ i => -C.playerCost σ i)

open Classical in
/-- Rosenthal's potential function: negative sum over resources of cumulative delay. -/
noncomputable def potential (C : CongestionGame ι) (σ : C.Profile) : ℝ :=
  - ∑ r : C.Resource, ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1)

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
theorem congestionWithout_update (C : CongestionGame ι) (σ : C.Profile)
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
theorem congestion_update (C : CongestionGame ι) (σ : C.Profile)
    (who : ι) (s' : C.StrategySet who) (r : C.Resource) :
    C.congestion (Function.update σ who s') r =
    C.congestionWithout σ who r +
    if r ∈ C.resources who s' then 1 else 0 := by
  have h := congestion_decompose C (Function.update σ who s') who r
  simp only [Function.update_self] at h
  rw [h, congestionWithout_update]

open Classical in
/-- Rosenthal's theorem: the potential function is an exact potential
    for the congestion game. -/
theorem isExactPotential (C : CongestionGame ι) :
    C.toKernelGame.IsExactPotential C.potential := by
  intro who σ s'
  simp only [toKernelGame, KernelGame.eu_ofEU, playerCost, potential, Function.update_self]
  set σ' := Function.update σ who s'
  -- Reduce -A - (-B) = -C - (-D) to B - A = D - C
  suffices h : ∑ r ∈ C.resources who (σ who), C.delay r (C.congestion σ r) -
      ∑ r ∈ C.resources who s', C.delay r (C.congestion σ' r) =
      ∑ r, ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1) -
      ∑ r, ∑ k ∈ Finset.range (C.congestion σ' r), C.delay r (k + 1) by linarith
  -- Convert finset sums to full indicator sums
  have h_sum_eq : ∀ (S : Finset C.Resource) (f : C.Resource → ℝ),
      ∑ r ∈ S, f r = ∑ r, if r ∈ S then f r else 0 := by
    intro S f; conv_rhs => rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h_sum_eq (C.resources who (σ who)), h_sum_eq (C.resources who s')]
  -- Convert ∑f - ∑g to ∑(f-g) on both sides
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  -- Per-resource equality
  apply Finset.sum_congr rfl
  intro r _
  set n := C.congestionWithout σ who r
  rw [C.congestion_decompose σ who r, C.congestion_update σ who s' r]
  by_cases hold : r ∈ C.resources who (σ who) <;> by_cases hnew : r ∈ C.resources who s'
  · -- Both use r: same congestion, terms cancel
    simp [hold, hnew]
  · -- Old only: congestion n+1 → n
    simp only [hold, hnew, ite_true, ite_false, add_zero]
    rw [Finset.sum_range_succ]; ring
  · -- New only: congestion n → n+1
    simp only [hold, hnew, ite_true, ite_false, add_zero]
    rw [Finset.sum_range_succ]; ring
  · -- Neither: same congestion, both zero
    simp [hold, hnew]

set_option linter.unusedFintypeInType false in
open Classical in
/-- Congestion games have Nash equilibria (via Rosenthal's potential). -/
theorem nash_exists (C : CongestionGame ι) [∀ i, Nonempty (C.StrategySet i)] :
    ∃ σ : C.Profile, C.toKernelGame.IsNash σ := by
  haveI (i : ι) : Fintype (C.toKernelGame.Strategy i) := C.instFintypeStrategy i
  haveI (i : ι) : Nonempty (C.toKernelGame.Strategy i) := ‹∀ i, Nonempty (C.StrategySet i)› i
  exact C.isExactPotential.nash_exists

open Classical in
/-- Congestion games have the finite improvement property:
    no infinite sequence of improving deviations exists. -/
theorem no_infinite_improving_path (C : CongestionGame ι) :
    ¬ ∃ (path : ℕ → C.Profile),
        ∀ n, C.toKernelGame.ImprovingStep (path n) (path (n + 1)) := by
  haveI (i : ι) : Finite (C.toKernelGame.Strategy i) :=
    @Fintype.finite _ (C.instFintypeStrategy i)
  exact C.isExactPotential.no_infinite_improving_path

end CongestionGame

end GameTheory
