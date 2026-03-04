import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.ApproximateNash
import Math.Probability

/-!
# Best Response Dynamics

Best response dynamics is a natural process where players iteratively
update their strategies to best-respond to the current profile.

## Main definitions

* `ImprovementPath` — a sequence of profiles where each step is a
  single-player improving deviation
* `IsBetterResponse` — a strategy that strictly improves EU

## Main results

* `improvementPath_nash_stable` — Nash equilibria are fixed points of BR dynamics
* `strictNash_absorbing` — strict Nash equilibria are absorbing states
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} (G : KernelGame ι)

open Classical in
/-- An improving deviation: player `who` switches from `σ who` to `s'`
    and strictly improves their EU. -/
structure ImprovingDeviation (σ : Profile G) where
  who : ι
  newStrategy : G.Strategy who
  improves : G.eu (Function.update σ who newStrategy) who > G.eu σ who

/-- A Nash equilibrium has no improving deviations. -/
theorem no_improving_deviation_iff_nash {σ : Profile G} :
    IsEmpty (G.ImprovingDeviation σ) ↔ G.IsNash σ := by
  constructor
  · intro hemp who s'
    by_contra h
    push_neg at h
    exact (hemp.false ⟨who, s', h⟩).elim
  · intro hN
    constructor
    intro ⟨who, s', himprove⟩
    have := hN who s'
    linarith

open Classical in
/-- A strict Nash equilibrium is absorbing: any single-player deviation
    strictly decreases the deviator's EU. -/
theorem strictNash_absorbing {σ : Profile G} (hstrict : G.IsStrictNash σ) :
    ∀ (who : ι) (s' : G.Strategy who), s' ≠ σ who →
      G.eu (Function.update σ who s') who < G.eu σ who :=
  hstrict

open Classical in
/-- In an ε-Nash equilibrium, any improving deviation must improve by at most ε. -/
theorem εNash_bounded_improvement {ε : ℝ} {σ : Profile G}
    (hε : G.IsεNash ε σ) (who : ι) (s' : G.Strategy who) :
    G.eu (Function.update σ who s') who ≤ G.eu σ who + ε := by
  have := hε who s'
  linarith

end KernelGame

end GameTheory
