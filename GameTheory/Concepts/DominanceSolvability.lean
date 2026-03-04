import GameTheory.Concepts.StrictDominance
import GameTheory.Concepts.DominanceNash
import Math.Probability

/-!
# Dominance Solvability

A game is dominance-solvable if every player has a strictly dominant
strategy. In such a game, there is a unique Nash equilibrium.

## Main definitions

* `IsDominanceSolvable` — every player has a strictly dominant strategy

## Main results

* `IsDominanceSolvable.unique_nash` — the unique Nash equilibrium
* `IsDominanceSolvable.nash_is_dominant` — the Nash profile consists of dominant strategies
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] (G : KernelGame ι)

/-- A game is dominance-solvable if every player has a strictly dominant strategy. -/
def IsDominanceSolvable : Prop :=
  ∀ who : ι, ∃ s : G.Strategy who, G.IsStrictDominant who s

open Classical in
/-- The dominant strategy profile. -/
noncomputable def IsDominanceSolvable.dominantProfile
    (h : G.IsDominanceSolvable) : Profile G :=
  fun i => (h i).choose

/-- The dominant strategy profile is Nash (follows from dominant_is_nash). -/
theorem IsDominanceSolvable.isNash (h : G.IsDominanceSolvable) :
    G.IsNash (h.dominantProfile G) := by
  classical
  apply dominant_is_nash
  intro i
  have hdom := (h i).choose_spec
  exact hdom.toDominant

open Classical in
/-- In a dominance-solvable game, the Nash equilibrium is unique:
    any Nash profile must use the dominant strategy for each player. -/
theorem IsDominanceSolvable.nash_unique
    (h : G.IsDominanceSolvable) {σ : Profile G} (hN : G.IsNash σ) :
    σ = h.dominantProfile G := by
  funext i
  have hdom := (h i).choose_spec
  have hbr : G.IsBestResponse i σ (σ i) := by
    intro s'
    have h := hN i s'
    convert h using 2
    exact Function.update_eq_self i σ
  exact hdom.unique_best_response σ hbr

/-- Combining: the dominant profile is the unique Nash equilibrium. -/
theorem IsDominanceSolvable.exists_unique_nash (h : G.IsDominanceSolvable) :
    ∃! σ : Profile G, G.IsNash σ :=
  ⟨h.dominantProfile G, h.isNash G, fun _ hN => (h.nash_unique G hN)⟩

end KernelGame

end GameTheory
