import GameTheory.EFG.OneShotDeviation
import GameTheory.Compilers.EFG

/-!
# Canonical One-Shot Deviation Principle Entry

Abstract principle first, with EFG as immediate instantiation.
-/

namespace GameTheory
namespace Theorems

/-- Abstract one-shot deviation principle schema. -/
def OneShotDeviationPrinciple {σ : Type}
    (GlobalStable LocalStable : σ → Prop) : Prop :=
  ∀ x, GlobalStable x ↔ LocalStable x

namespace EFG

/-- EFG instantiation of the one-shot deviation principle. -/
theorem oneShotDeviation_principle (G : _root_.EFG.EFGGame) [Fintype G.Outcome]
    (hpi : _root_.EFG.IsPerfectInfo G.tree) :
    OneShotDeviationPrinciple
      (fun σ : _root_.EFG.PureProfile G.inf => G.IsSubgamePerfectEq σ)
      (fun σ : _root_.EFG.PureProfile G.inf => _root_.EFG.HasNoOneShotDeviation G σ) := by
  intro σ
  exact Compiler.EFG.strategic_oneShotDeviation_iff_spe G σ hpi

end EFG

end Theorems
end GameTheory
