/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

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

example (ι : Type) : PreorderLens ι :=
  profileMapUtilityDistributionSimulationLens ι

example (ι : Type) : EquivalenceLens ι :=
  expectedUtilityLens ι

example {ι : Type} {G H K : KernelGame ι}
    (f : ExpectedUtilityMap G H) (g : ExpectedUtilityMap H K) :
    ExpectedUtilityMap G K :=
  ExpectedUtilityMap.comp g f

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

example (ι : Type) [DecidableEq ι] [Fintype ι] :
    (profileMapUtilityDistributionSimulationLens ι).ExpressiveLe
      (BoundedFOSGLanguage ι) (FOSGPlainEFGLanguage ι) :=
  boundedFOSG_expressiveLe_plainEFG_profileMap ι

example (m : Nat) (X : MAIDPresentation m) :
    (MAIDLanguage m).compile X = MAID.toKernelGame X.struct X.sem :=
  rfl

example (m : Nat) (X : MAIDPresentation m) :
    (MAIDEFGLanguage m).compile X =
      (MAID_EFG.maidToEFG X.struct X.sem (MAID.defaultPolicy X.struct)).toKernelGame :=
  rfl

end

end Expressiveness
end Languages
end GameTheory
