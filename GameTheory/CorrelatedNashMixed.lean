import GameTheory.SolutionConcepts
import GameTheory.NashExistenceMixed

/-!
# GameTheory.CorrelatedNashMixed

Relates correlated expected utility under point-mass distributions to standard
expected utility, and establishes how deviation distributions simplify under
point-mass (pure) profile distributions.

Provides:
- `correlatedEu_pure` — correlated EU under `PMF.pure σ` equals `eu σ`
- `constDeviateDistribution_pure` — constant deviation under a point mass
  yields a point mass at the deviated profile
- `deviateDistribution_pure` — recommendation-dependent deviation under a
  point mass yields a point mass at the deviated profile
- `correlatedEu_eq_expect_eu` — correlated EU is the expectation of EU
  over the profile distribution
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} {G : KernelGame ι}

/-- Correlated EU under a point-mass distribution equals the standard EU.

Under `PMF.pure σ`, `correlatedOutcome` reduces to `outcomeKernel σ`
(by `correlatedOutcome_pure`), and both `correlatedEu` and `eu` compute
`expect (outcomeKernel σ) (fun ω => utility ω who)`. -/
theorem correlatedEu_pure (σ : Profile G) (who : ι) :
    G.correlatedEu (PMF.pure σ) who = G.eu σ who := by
  simp [correlatedEu, eu, correlatedOutcome, Kernel.pushforward]

open Classical in
/-- Constant deviation under a point-mass distribution yields a point mass at
the deviated profile. `constDeviateDistribution (PMF.pure σ) who s'` reduces
to `PMF.pure (Function.update σ who s')` since `PMF.pure_bind` collapses
the `bind`. -/
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
/-- Constant deviation of a product mixed profile distribution is product update
    with a point mass at the deviating action. -/
theorem constDeviateDistribution_pmfPi
    {G : KernelGame ι}
    [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (s' : G.Strategy who) :
    G.constDeviateDistribution (pmfPi σ) who s' =
      pmfPi (Function.update σ who (PMF.pure s')) := by
  unfold constDeviateDistribution
  simpa using (pmfPi_bind_update_pure σ who s')

set_option linter.unusedFintypeInType false in
/-- Correlated EU is the expectation of standard EU over the profile distribution.

By unfolding `correlatedEu` and `correlatedOutcome` we get
`expect (μ.bind outcomeKernel) (fun ω => utility ω who)`, which by
`expect_bind` equals `expect μ (fun σ => expect (outcomeKernel σ) (fun ω => utility ω who))`,
i.e., `expect μ (fun σ => eu σ who)`. -/
theorem correlatedEu_eq_expect_eu [Fintype (Profile G)] [Fintype G.Outcome]
    (μ : PMF (Profile G)) (who : ι) :
    G.correlatedEu μ who = expect μ (fun σ => G.eu σ who) := by
  simp [correlatedEu, eu, correlatedOutcome, Kernel.pushforward, expect_bind]

set_option linter.unusedFintypeInType false in
open Classical in
/-- A mixed Nash profile induces a coarse correlated equilibrium on pure profiles
    via the independent product distribution `pmfPi σ`. -/
theorem mixed_nash_isCoarseCorrelatedEq
    {G : KernelGame ι}
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [Fintype G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ) :
    G.IsCoarseCorrelatedEq (pmfPi σ) := by
  intro who s'
  have hN' : G.mixedExtension.eu σ who ≥
      G.mixedExtension.eu (Function.update σ who (PMF.pure s')) who :=
    hN who (PMF.pure s')
  have hbase :
      G.correlatedEu (pmfPi σ) who = G.mixedExtension.eu σ who := by
    rw [G.correlatedEu_eq_expect_eu (μ := pmfPi σ) who]
    symm
    exact G.mixedExtension_eu σ who
  have hdev :
      G.correlatedEu
          (G.constDeviateDistribution (pmfPi σ) who s') who
        =
      G.mixedExtension.eu (Function.update σ who (PMF.pure s')) who := by
    rw [G.correlatedEu_eq_expect_eu
      (μ := G.constDeviateDistribution (pmfPi σ) who s') who]
    rw [G.mixedExtension_eu (Function.update σ who (PMF.pure s')) who]
    rw [G.constDeviateDistribution_pmfPi σ who s']
  rw [hbase, hdev]
  exact hN'

set_option linter.unusedFintypeInType false in
open Classical in
/-- Every finite game has a coarse correlated equilibrium. -/
theorem coarseCorrelatedEq_exists
    (G : KernelGame ι)
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Fintype G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCoarseCorrelatedEq μ := by
  obtain ⟨σ, hN⟩ := G.mixed_nash_exists
  exact ⟨pmfPi σ, G.mixed_nash_isCoarseCorrelatedEq σ hN⟩

end KernelGame
end GameTheory
