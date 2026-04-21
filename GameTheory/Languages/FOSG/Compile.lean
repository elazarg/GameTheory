import GameTheory.Core.KernelGame
import GameTheory.Languages.FOSG.Execution

/-!
# GameTheory.Languages.FOSG.Compile

Compilation of FOSGs into `KernelGame`.

The induced `KernelGame` uses legal behavioral strategies as the strategy sets
and terminal realized histories as outcomes. Since `KernelGame` expects a PMF
on outcomes, this bridge is available under an explicit normalization
assumption on the terminal-history mass function.
-/

namespace GameTheory

open Math.Probability
open scoped BigOperators

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- The terminal-history mass function normalizes to a probability law on
legal behavioral profiles. -/
def HasNormalizedTerminalLaw
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal] : Prop := by
  classical
  exact ∀ σ : G.LegalBehavioralProfile,
    ∑ h : G.History, History.terminalWeight (G := G) σ.toProfile h = 1

/-- The terminal-history law induced by a legal behavioral profile, assuming
normalization. -/
noncomputable def terminalLawPMF
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) : PMF G.History := by
  classical
  exact PMF.ofFintype
    (fun h => History.terminalWeight (G := G) σ.toProfile h)
    (hNorm σ)

@[simp] theorem terminalLawPMF_apply
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    G.terminalLawPMF hNorm σ h = History.terminalWeight (G := G) σ.toProfile h := by
  simp [terminalLawPMF, PMF.ofFintype_apply]

/-- The `KernelGame` induced by a FOSG whose terminal-history law normalizes on
legal behavioral profiles. -/
noncomputable def toKernelGame
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw) : KernelGame ι where
  Strategy := fun i => G.LegalBehavioralStrategy i
  Outcome := G.History
  utility := fun h i => History.utility h i
  outcomeKernel := fun σ => G.terminalLawPMF hNorm σ

@[simp] theorem toKernelGame_outcomeKernel
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) :
    (G.toKernelGame hNorm).outcomeKernel σ = G.terminalLawPMF hNorm σ := rfl

/-- Expected utility in the induced `KernelGame` is exactly the terminal-history
sum computed from the native FOSG execution semantics. -/
theorem toKernelGame_eu_eq
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) (i : ι) :
    (G.toKernelGame hNorm).eu σ i =
      ∑ h : G.History,
        (History.terminalWeight (G := G) σ.toProfile h).toReal * History.utility h i := by
  rw [KernelGame.eu]
  simp [toKernelGame, terminalLawPMF, expect_eq_sum]

end FOSG

end GameTheory
