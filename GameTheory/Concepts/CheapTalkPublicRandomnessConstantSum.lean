/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.CheapTalkPublicRandomness
import GameTheory.Concepts.ConstantSumCorrelated

/-!
# Constant-Sum Consequences of Cheap Talk as Public Randomness

This file keeps the two-player constant/zero-sum value corollaries separate
from the core cheap-talk/public-randomness representation.
-/

noncomputable section

namespace GameTheory

namespace KernelGame
namespace CheapTalkExtension

variable {G : KernelGame (Fin 2)}

/-- In a two-player constant-sum game, any cheap-talk profile whose induced
public regime is a public-correlated equilibrium has the base Nash value. -/
theorem InducesPublicCorrelatedEq.constantSum_mixedExtension_eu_eq_base_nash
    (C : G.CheapTalkExtension) [Finite G.Outcome]
    [∀ i, Finite (C.Msg i)] [∀ i, Finite (C.game.Strategy i)]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {τ : Profile C.game.mixedExtension}
    (hpub : C.InducesPublicCorrelatedEq τ)
    {σ : Profile G} (hN : G.IsNash σ) :
    C.game.mixedExtension.eu τ 0 = G.eu σ 0 := by
  rw [C.mixedExtension_eu_eq_correlatedEu_mixedActionLaw τ 0]
  exact hcs.correlated_eq_eu_eq_nash hN
    (hpub.mixedActionLaw_isCorrelatedEq C)

/-- In a two-player constant-sum game, every mixed Nash equilibrium of the
cheap-talk extension has the base Nash value. -/
theorem mixedNash_constantSum_mixedExtension_eu_eq_base_nash
    (C : G.CheapTalkExtension) [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {τ : Profile C.game.mixedExtension}
    (hNτ : C.game.mixedExtension.IsNash τ)
    {σ : Profile G} (hN : G.IsNash σ) :
    C.game.mixedExtension.eu τ 0 = G.eu σ 0 := by
  rw [C.mixedExtension_eu_eq_correlatedEu_mixedActionLaw τ 0]
  exact hcs.correlated_eq_eu_eq_nash hN
    (C.mixedNash_mixedActionLaw_isCorrelatedEq τ hNτ)

/-- Zero-sum specialization of
`constantSum_mixedExtension_eu_eq_base_nash`. -/
theorem InducesPublicCorrelatedEq.zeroSum_mixedExtension_eu_eq_base_nash
    (C : G.CheapTalkExtension) [Finite G.Outcome]
    [∀ i, Finite (C.Msg i)] [∀ i, Finite (C.game.Strategy i)]
    (hzs : G.IsZeroSum)
    {τ : Profile C.game.mixedExtension}
    (hpub : C.InducesPublicCorrelatedEq τ)
    {σ : Profile G} (hN : G.IsNash σ) :
    C.game.mixedExtension.eu τ 0 = G.eu σ 0 :=
  hpub.constantSum_mixedExtension_eu_eq_base_nash C (c := 0) hzs hN

/-- Zero-sum specialization of
`mixedNash_constantSum_mixedExtension_eu_eq_base_nash`. -/
theorem mixedNash_zeroSum_mixedExtension_eu_eq_base_nash
    (C : G.CheapTalkExtension) [Finite G.Outcome]
    (hzs : G.IsZeroSum)
    {τ : Profile C.game.mixedExtension}
    (hNτ : C.game.mixedExtension.IsNash τ)
    {σ : Profile G} (hN : G.IsNash σ) :
    C.game.mixedExtension.eu τ 0 = G.eu σ 0 :=
  C.mixedNash_constantSum_mixedExtension_eu_eq_base_nash (c := 0) hzs hNτ hN

end CheapTalkExtension
end KernelGame

end GameTheory
