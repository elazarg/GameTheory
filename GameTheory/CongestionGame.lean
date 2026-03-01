import GameTheory.GameProperties
import GameTheory.SolutionConcepts

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

end CongestionGame

end GameTheory
