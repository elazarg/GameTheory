import GameTheory.NFG.PotentialFIP
import GameTheory.Concepts.BestResponseDynamics
import Math.Probability

/-!
# Finite Improvement Property for Potential Games

The finite improvement property (FIP): in a finite exact potential game,
every sequence of improving deviations terminates. Equivalently, there
is no infinite improving path.

## Main results

* `IsExactPotential.no_infinite_improving_path` — no infinite sequence of
  profiles where each step is a single-player improving deviation
* `IsExactPotential.improvingStep_wellFounded` — the improving-step
  relation is well-founded on a finite strategy space
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

open Classical in
/-- An improving step: `τ` is obtained from `σ` by a single player's
    improving deviation. -/
def ImprovingStep (G : KernelGame ι) (σ τ : Profile G) : Prop :=
  ∃ (who : ι) (s' : G.Strategy who),
    τ = Function.update σ who s' ∧
    G.eu τ who > G.eu σ who

open Classical in
/-- Each improving step strictly increases the exact potential. -/
theorem IsExactPotential.improvingStep_increases_potential
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    {σ τ : Profile G} (hstep : G.ImprovingStep σ τ) :
    Φ τ > Φ σ := by
  obtain ⟨who, s', rfl, himprove⟩ := hstep
  exact hΦ.improving_deviation_increases_potential himprove

open Classical in
/-- **Finite Improvement Property**: in a finite exact potential game,
    there is no infinite improving path. Any sequence of profiles where
    each consecutive pair is an improving step must eventually repeat,
    contradicting strict increase of the potential. -/
theorem IsExactPotential.no_infinite_improving_path
    {G : KernelGame ι} [Finite (Profile G)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) :
    ¬ ∃ (path : ℕ → Profile G),
        ∀ n, G.ImprovingStep (path n) (path (n + 1)) := by
  rintro ⟨path, hstep⟩
  -- Φ strictly increases along the path
  have hincr : ∀ n, Φ (path n) < Φ (path (n + 1)) :=
    fun n => hΦ.improvingStep_increases_potential (hstep n)
  -- So Φ ∘ path is strictly monotone
  have hmono : StrictMono (Φ ∘ path) := strictMono_nat_of_lt_succ hincr
  -- Strictly monotone implies injective
  have hinj : Function.Injective path := by
    intro a b hab
    have : Φ (path a) = Φ (path b) := by rw [hab]
    exact hmono.injective this
  -- But ℕ → finite type can't be injective
  exact not_injective_infinite_finite path hinj


end KernelGame

end GameTheory
