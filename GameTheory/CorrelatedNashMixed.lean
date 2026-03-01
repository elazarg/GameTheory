import GameTheory.SolutionConcepts
import GameTheory.NashExistenceMixed
import GameTheory.CorrelatedEqProperties

/-!
# GameTheory.CorrelatedNashMixed

Relates correlated expected utility under point-mass distributions to standard
expected utility, and establishes how deviation distributions simplify under
point-mass (pure) and product (mixed) profile distributions.

Provides:
- `correlatedEu_pure` — correlated EU under `PMF.pure σ` equals `eu σ`
- `constDeviateDistribution_pure` — constant deviation under a point mass
  yields a point mass at the deviated profile
- `deviateDistribution_pure` — recommendation-dependent deviation under a
  point mass yields a point mass at the deviated profile
- `deviateDistribution_pmfPi` — deviation of a product distribution equals
  the product with the deviated component's pushforward
- `correlatedEu_eq_expect_eu` — correlated EU is the expectation of EU
  over the profile distribution
- `mixed_nash_isCorrelatedEq` — a mixed Nash profile induces a CE
- `correlatedEq_exists` — every finite game has a correlated equilibrium
- `coarseCorrelatedEq_exists` — corollary: every finite game has a CCE
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} {G : KernelGame ι}

/-- Correlated EU under a point-mass distribution equals the standard EU. -/
theorem correlatedEu_pure (σ : Profile G) (who : ι) :
    G.correlatedEu (PMF.pure σ) who = G.eu σ who := by
  simp [correlatedEu, eu, correlatedOutcome, Kernel.pushforward]

open Classical in
/-- Constant deviation under a point-mass distribution yields a point mass at
the deviated profile. -/
theorem constDeviateDistribution_pure (σ : Profile G)
    (who : ι) (s' : G.Strategy who) :
    G.constDeviateDistribution (PMF.pure σ) who s' =
      PMF.pure (Function.update σ who s') := by
  simp [constDeviateDistribution, PMF.pure_bind]

/-- Recommendation-dependent deviation under a point-mass distribution yields a
point mass at the deviated profile. -/
theorem deviateDistribution_pure (σ : Profile G)
    (who : ι) (dev : G.Strategy who → G.Strategy who) :
    G.deviateDistribution (PMF.pure σ) who dev =
      PMF.pure (G.deviateProfile σ who dev) := by
  simp [deviateDistribution, PMF.pure_bind]

set_option linter.unusedFintypeInType false in
open Classical in
/-- Deviation of a product distribution equals the product with the deviated
    component replaced by the pushforward of the original through `dev`. -/
theorem deviateDistribution_pmfPi
    {G : KernelGame ι}
    [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) :
    G.deviateDistribution (pmfPi σ) who dev =
      pmfPi (Function.update σ who (PMF.map dev (σ who))) := by
  unfold deviateDistribution deviateProfile
  exact pmfPi_bind_update_map σ who dev

set_option linter.unusedFintypeInType false in
/-- Correlated EU is the expectation of standard EU over the profile
    distribution. -/
theorem correlatedEu_eq_expect_eu [Fintype (Profile G)] [Fintype G.Outcome]
    (μ : PMF (Profile G)) (who : ι) :
    G.correlatedEu μ who = expect μ (fun σ => G.eu σ who) := by
  simp [correlatedEu, eu, correlatedOutcome, Kernel.pushforward, expect_bind]

set_option linter.unusedFintypeInType false in
open Classical in
/-- A mixed Nash profile induces a correlated equilibrium on pure profiles
    via the independent product distribution `pmfPi σ`.

    For any deviation function `dev`, the deviated distribution
    `deviateDistribution (pmfPi σ) who dev` equals
    `pmfPi (update σ who (PMF.map dev (σ who)))`. By Nash optimality,
    the pushforward mixed strategy `PMF.map dev (σ who)` cannot improve
    player `who`'s EU. -/
theorem mixed_nash_isCorrelatedEq
    {G : KernelGame ι}
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [Fintype G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ) :
    G.IsCorrelatedEq (pmfPi σ) := by
  intro who dev
  have hN' : G.mixedExtension.eu σ who ≥
      G.mixedExtension.eu (Function.update σ who (PMF.map dev (σ who))) who :=
    hN who (PMF.map dev (σ who))
  have hbase :
      G.correlatedEu (pmfPi σ) who = G.mixedExtension.eu σ who := by
    rw [G.correlatedEu_eq_expect_eu (μ := pmfPi σ) who]
    symm; exact G.mixedExtension_eu σ who
  have hdev :
      G.correlatedEu (G.deviateDistribution (pmfPi σ) who dev) who =
      G.mixedExtension.eu
        (Function.update σ who (PMF.map dev (σ who))) who := by
    rw [G.correlatedEu_eq_expect_eu
      (μ := G.deviateDistribution (pmfPi σ) who dev) who]
    rw [G.mixedExtension_eu
      (Function.update σ who (PMF.map dev (σ who))) who]
    rw [G.deviateDistribution_pmfPi σ who dev]
  rw [hbase, hdev]
  exact hN'

set_option linter.unusedFintypeInType false in
open Classical in
/-- Every finite game has a correlated equilibrium. -/
theorem correlatedEq_exists
    (G : KernelGame ι)
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Fintype G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCorrelatedEq μ := by
  obtain ⟨σ, hN⟩ := G.mixed_nash_exists
  exact ⟨pmfPi σ, G.mixed_nash_isCorrelatedEq σ hN⟩

set_option linter.unusedFintypeInType false in
open Classical in
/-- A mixed Nash profile induces a coarse correlated equilibrium.
    Corollary of `mixed_nash_isCorrelatedEq` via `toCoarseCorrelatedEq`. -/
theorem mixed_nash_isCoarseCorrelatedEq
    {G : KernelGame ι}
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [Fintype G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ) :
    G.IsCoarseCorrelatedEq (pmfPi σ) :=
  (G.mixed_nash_isCorrelatedEq σ hN).toCoarseCorrelatedEq

set_option linter.unusedFintypeInType false in
open Classical in
/-- Every finite game has a coarse correlated equilibrium.
    Corollary of `correlatedEq_exists` via `toCoarseCorrelatedEq`. -/
theorem coarseCorrelatedEq_exists
    (G : KernelGame ι)
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Fintype G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCoarseCorrelatedEq μ := by
  obtain ⟨μ, hCE⟩ := G.correlatedEq_exists
  exact ⟨μ, hCE.toCoarseCorrelatedEq⟩

end KernelGame
end GameTheory
