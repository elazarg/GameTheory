import GameTheory.NFG.MinimaxTheorem
import GameTheory.Model.SemanticGame

/-!
# Canonical Minimax Theorem Entry

Semantic-form statement for two-player zero-sum finite games.
-/

namespace GameTheory
namespace Theorems
namespace SemanticGame

open KernelGame

set_option linter.unusedFintypeInType false
/-- Semantic-form von Neumann minimax theorem, transported from `KernelGame`. -/
theorem von_neumann_minimax (G : SemanticGame (Fin 2))
    [Fintype G.toKernelGame.Outcome]
    [∀ i, Fintype (G.toKernelGame.Strategy i)]
    [∀ i, Nonempty (G.toKernelGame.Strategy i)]
    (hzs : G.toKernelGame.IsZeroSum) :
    ∃ (v : ℝ) (σ : KernelGame.Profile G.toKernelGame.mixedExtension),
      G.toKernelGame.mixedExtension.IsNash σ ∧
      G.toKernelGame.mixedExtension.eu σ 0 = v ∧
      (∀ s₁, G.toKernelGame.mixedExtension.eu (Function.update σ 1 s₁) 0 ≥ v) ∧
      (∀ s₀, G.toKernelGame.mixedExtension.eu (Function.update σ 0 s₀) 0 ≤ v) :=
  KernelGame.von_neumann_minimax G.toKernelGame hzs
set_option linter.unusedFintypeInType true

end SemanticGame
end Theorems
end GameTheory
