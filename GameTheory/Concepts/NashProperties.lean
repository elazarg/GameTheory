import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.Deviation
import Math.Probability

/-!
# Nash Equilibrium Properties

General properties and characterizations of Nash equilibria.

## Main results

* `isNash_iff_allBestResponse` — Nash ↔ all players play best responses
* `isNash_iff_no_improving` — Nash ↔ no improving deviation exists
* `isNash_of_all_dominant` — if every strategy is dominant, any profile is Nash
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

open Classical in
/-- Nash equilibrium ↔ every player plays a best response to the profile. -/
theorem isNash_iff_allBestResponse (G : KernelGame ι) {σ : Profile G} :
    G.IsNash σ ↔ ∀ who, G.IsBestResponse who σ (σ who) := by
  simpa using (isNash_iff_bestResponse (G := G) σ)

/-- Preference-parameterized counterpart:
    Nash-for `pref` iff every player plays a best response-for `pref`. -/
theorem isNashFor_iff_allBestResponseFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop) (σ : Profile G) :
    G.IsNashFor pref σ ↔ ∀ who, G.IsBestResponseFor pref who σ (σ who) := by
  simpa using (isNashFor_iff_bestResponseFor (G := G) pref σ)

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
    push Not at hlt
    exact h ⟨who, s', hlt⟩

open Classical in
/-- Nash equilibrium ↔ no strictly improving unilateral deviation map exists. -/
theorem isNash_iff_no_improving_unilateralDeviation (G : KernelGame ι) {σ : Profile G} :
    G.IsNash σ ↔ ¬ ∃ (who : ι) (dev : G.Strategy who → G.Strategy who),
      G.euAfterDeviation who (G.unilateralDeviation who dev) σ > G.eu σ who := by
  constructor
  · intro hN ⟨who, dev, himprove⟩
    have hle := hN who (dev (σ who))
    have hnot :
        ¬ G.euAfterDeviation who (G.unilateralDeviation who dev) σ > G.eu σ who := by
      simpa [KernelGame.euAfterDeviation, KernelGame.unilateralDeviation] using not_lt_of_ge hle
    exact hnot himprove
  · intro h who s'
    by_contra hlt
    have himprove :
        G.euAfterDeviation who (G.unilateralDeviation who (fun _ => s')) σ > G.eu σ who := by
      simpa [KernelGame.euAfterDeviation, KernelGame.unilateralDeviation] using hlt
    exact h ⟨who, fun _ => s', himprove⟩

/-- If every player's strategy is dominant, then any profile is Nash.
    This is a generalization of `dominant_is_nash` that doesn't require
    matching the profile to the dominant strategies. -/
theorem isNash_of_allDominant (G : KernelGame ι) {σ : Profile G}
    (h : ∀ i, G.IsDominant i (σ i)) : G.IsNash σ :=
  G.dominant_is_nash σ h

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
