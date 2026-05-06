import GameTheory.Languages.Expressiveness.MAID_EFG
import GameTheory.Languages.Expressiveness.EFG_FOSG

/-!
# GameTheory.Languages.Expressiveness.Tests

Smoke checks for the expressiveness packaging layer.  These are intentionally
lightweight: the substantive bridge proofs live in `GameTheory.Languages.Bridges`.
-/

namespace GameTheory
namespace Languages
namespace Expressiveness

noncomputable section

example {ι κ : Type} (e : ι ≃ κ) (G : KernelGame κ) :
    KernelGame ι :=
  KernelGame.reindex e G

example (ι : Type) : EquivalenceLens ι :=
  protocolLens ι

example (ι : Type) : EquivalenceLens ι :=
  utilityDistributionLens ι

example (ι : Type) : EquivalenceLens ι :=
  profileMapUtilityDistributionLens ι

example (ι : Type) : EquivalenceLens ι :=
  expectedUtilityLens ι

example (m : Nat) :
    (utilityDistributionLens (Fin m)).ExpressiveEq
      (MAIDLanguage m) (MAIDEFGLanguage m) :=
  maid_expressiveEq_maidefg m

example (m : Nat) :
    (utilityDistributionLens (Fin m)).ExpressiveEq
      (MAIDLanguage m) (CausalContextFreeEFGLanguage m) :=
  maid_expressiveEq_causalContextFreeEFG m

example (G : EFG.EFGGame) :
    IsMAIDEFGTree G ↔ IsCausalContextFreeEFGTree G :=
  isMAIDEFGTree_iff_isCausalContextFreeEFGTree G

example (ι : Type) [DecidableEq ι] [Fintype ι] :
    Reduction (BoundedFOSGLanguage ι) (FOSGPlainEFGLanguage ι)
      ProfileMapUtilityDistributionSimulation :=
  boundedFOSGToPlainEFGProfileMapReduction ι

end

end Expressiveness
end Languages
end GameTheory
