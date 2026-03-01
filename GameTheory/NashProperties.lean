import GameTheory.SolutionConcepts
import GameTheory.BestResponse

/-!
# Nash Equilibrium Properties

General properties and characterizations of Nash equilibria.

## Main results

* `isNash_iff_allBestResponse` — Nash ↔ all players play best responses
* `isNash_iff_no_improving` — Nash ↔ no improving deviation exists
* `isNash_of_all_dominant` — if every strategy is dominant, any profile is Nash
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

open Classical in
/-- Nash equilibrium ↔ every player plays a best response to the profile. -/
theorem isNash_iff_allBestResponse (G : KernelGame ι) {σ : Profile G} :
    G.IsNash σ ↔ ∀ who, G.IsBestResponse who σ (σ who) := by
  constructor
  · intro hN who s'
    have h := hN who s'
    convert h using 2
    exact Function.update_eq_self who σ
  · intro h who s'
    have h1 := h who s'
    have : Function.update σ who (σ who) = σ := Function.update_eq_self who σ
    rw [this] at h1
    exact h1

open Classical in
/-- Nash equilibrium ↔ no player has a strictly improving deviation. -/
theorem isNash_iff_no_improving (G : KernelGame ι) {σ : Profile G} :
    G.IsNash σ ↔ ¬ ∃ (who : ι) (s' : G.Strategy who),
      G.eu (Function.update σ who s') who > G.eu σ who := by
  constructor
  · intro hN ⟨who, s', himprove⟩
    have := hN who s'
    linarith
  · intro h who s'
    by_contra hlt
    push_neg at hlt
    exact h ⟨who, s', hlt⟩

/-- If every player's strategy is dominant, then any profile is Nash.
    This is a generalization of `dominant_is_nash` that doesn't require
    matching the profile to the dominant strategies. -/
theorem isNash_of_allDominant (G : KernelGame ι) {σ : Profile G}
    (h : ∀ i, G.IsDominant i (σ i)) : G.IsNash σ :=
  @dominant_is_nash _ G _ h

open Classical in
/-- Nash is preserved by a player replacing their strategy with another
    best response (when both are best responses). -/
theorem isNash_update_bestResponse
    {G : KernelGame ι} {σ : Profile G} (hN : G.IsNash σ)
    {who : ι} {s' : G.Strategy who}
    (hbr : G.IsBestResponse who σ s') :
    G.eu (Function.update σ who s') who = G.eu σ who := by
  apply le_antisymm
  · have := hN who s'; linarith
  · have h1 := hbr (σ who)
    rw [Function.update_eq_self] at h1
    linarith

open Classical in
/-- In Nash equilibrium, all best responses yield the same EU as the
    equilibrium strategy. -/
theorem nash_bestResponse_eu_eq
    {G : KernelGame ι} {σ : Profile G} (hN : G.IsNash σ)
    {who : ι} {s' : G.Strategy who}
    (hbr : G.IsBestResponse who σ s') :
    G.eu (Function.update σ who s') who = G.eu σ who :=
  isNash_update_bestResponse hN hbr

end KernelGame

end GameTheory
