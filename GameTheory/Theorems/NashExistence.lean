import GameTheory.Concepts.NashExistenceMixed
import GameTheory.Concepts.SemanticSolutionConcepts
import GameTheory.Model.SemanticGame

/-! Canonical mixed Nash existence entry point. -/

namespace GameTheory
namespace SemanticGame

open KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι]

set_option linter.unusedFintypeInType false
/-- Semantic-form mixed Nash existence: for finite player and strategy spaces,
the mixed extension of a semantic game has a Nash equilibrium. -/
theorem mixed_nash_exists (G : SemanticGame ι)
    [∀ i, Fintype ((G.toKernelGame).Strategy i)] [∀ i, Nonempty ((G.toKernelGame).Strategy i)]
    [Fintype (G.toKernelGame).Outcome] :
    ∃ σ : ∀ i, PMF ((G.toKernelGame).Strategy i), (G.toKernelGame.mixedExtension).IsNash σ :=
  G.toKernelGame.mixed_nash_exists
set_option linter.unusedFintypeInType true

end SemanticGame
end GameTheory
