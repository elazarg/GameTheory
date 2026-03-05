import GameTheory.EFG.Zermelo
import GameTheory.Sequential.ProtoZermelo
import GameTheory.Sequential.ProtoSPE
import GameTheory.Bridge.MAID_EFG
import GameTheory.Compilers.EFG
import GameTheory.Compilers.Protocol
import GameTheory.Concepts.SemanticSolutionConcepts

/-!
# Canonical Zermelo Theorem Entry

Semantic-facing wrapper for finite perfect-information EFGs.
-/

namespace GameTheory
namespace Theorems

namespace EFG

set_option linter.unusedFintypeInType false
/-- Zermelo corollary in EFG form: existence of a pure SPE. -/
theorem zermelo_spe (G : _root_.EFG.EFGGame) [Fintype G.Outcome]
    (hpi : _root_.EFG.IsPerfectInfo G.tree) :
    ∃ σ : _root_.EFG.PureProfile G.inf, G.IsSubgamePerfectEq σ :=
  _root_.EFG.zermelo G hpi

set_option linter.unusedFintypeInType false
/-- Zermelo corollary in semantic-game form (compiled strategic EFG semantics). -/
theorem zermelo_semantic_nash (G : _root_.EFG.EFGGame) [Fintype G.Outcome]
    (hpi : _root_.EFG.IsPerfectInfo G.tree) :
    ∃ σ : _root_.EFG.PureProfile G.inf,
      (Compiler.EFG.compileStrategic G).IsNash σ := by
  obtain ⟨σ, hspe⟩ := zermelo_spe G hpi
  exact ⟨σ, Compiler.EFG.strategic_spe_implies_nash G σ hspe⟩

set_option linter.unusedFintypeInType true

end EFG

namespace Sequential

set_option linter.unusedFintypeInType false
/-- Zermelo corollary in protocol form: existence of a pure SPE. -/
theorem zermelo_spe
    {n : Nat} {S V A Sig : Type}
    [Fintype S] [Fintype V] [Fintype A] [Fintype Sig]
    [Nonempty (Option A)]
    (G : _root_.GameTheory.Protocol n S V A Sig)
    (u : S → Fin n → ℝ)
    (hPI : G.IsPerfectInfo)
    (hseq : G.IsSequential)
    (hVS : G.ViewSeparated) :
    ∃ σ : _root_.GameTheory.PureProfile n V A, G.IsSubgamePerfect u σ :=
  _root_.GameTheory.Protocol.zermelo G u hPI hseq hVS

set_option linter.unusedFintypeInType false
/-- Zermelo corollary in semantic-game form (compiled protocol semantics). -/
theorem zermelo_semantic_nash
    {n : Nat} {S V A Sig : Type}
    [Fintype S] [Fintype V] [Fintype A] [Fintype Sig]
    [Nonempty (Option A)]
    (G : _root_.GameTheory.Protocol n S V A Sig)
    (u : S → Fin n → ℝ)
    (hPI : G.IsPerfectInfo)
    (hseq : G.IsSequential)
    (hVS : G.ViewSeparated) :
    ∃ σ : _root_.GameTheory.PureProfile n V A,
      (Compiler.Protocol.compile G u).IsNash σ := by
  obtain ⟨σ, hspe⟩ := zermelo_spe G u hPI hseq hVS
  have hN : (G.toKernelGame u).IsNash σ := G.spe_implies_isNash u σ hspe
  exact ⟨σ, (Compiler.Protocol.isNash_iff G u σ).2 hN⟩

set_option linter.unusedFintypeInType true

end Sequential

namespace MAID

set_option linter.unusedFintypeInType false
/-- MAID corollary via MAID→EFG: if the induced EFG is perfect-info, Zermelo yields pure SPE. -/
theorem zermelo_spe_via_efg
    {m n : Nat}
    {S : _root_.MAID.Struct (Fin m) n}
    (sem : _root_.MAID.Sem S) (pol : _root_.MAID.Policy S)
    [Fintype (_root_.MAID.TAssign S)]
    (hpi : _root_.EFG.IsPerfectInfo (_root_.MAID_EFG.maidToEFG S sem pol).tree) :
    ∃ σ : _root_.EFG.PureProfile (_root_.MAID_EFG.maidInfoS S),
      (_root_.MAID_EFG.maidToEFG S sem pol).IsSubgamePerfectEq σ := by
  let G := _root_.MAID_EFG.maidToEFG S sem pol
  haveI : Fintype G.Outcome := by
    simpa [G] using (inferInstance : Fintype (_root_.MAID.TAssign S))
  simpa [G] using (_root_.EFG.zermelo G hpi)

set_option linter.unusedFintypeInType false
/-- MAID corollary via MAID→EFG in semantic-game form. -/
theorem zermelo_semantic_nash_via_efg
    {m n : Nat}
    {S : _root_.MAID.Struct (Fin m) n}
    (sem : _root_.MAID.Sem S) (pol : _root_.MAID.Policy S)
    [Fintype (_root_.MAID.TAssign S)]
    (hpi : _root_.EFG.IsPerfectInfo (_root_.MAID_EFG.maidToEFG S sem pol).tree) :
    ∃ σ : _root_.EFG.PureProfile (_root_.MAID_EFG.maidInfoS S),
      (Compiler.EFG.compileStrategic (_root_.MAID_EFG.maidToEFG S sem pol)).IsNash σ := by
  let G := _root_.MAID_EFG.maidToEFG S sem pol
  haveI : Fintype G.Outcome := by
    simpa [G] using (inferInstance : Fintype (_root_.MAID.TAssign S))
  simpa [G] using EFG.zermelo_semantic_nash G hpi

set_option linter.unusedFintypeInType true

end MAID

end Theorems
end GameTheory
