/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.ApproximateNash
import GameTheory.Concepts.Foundations.GameMorphism

/-!
# Approximate Equilibrium under Game Isomorphism

Exact expected-utility isomorphisms preserve ε-Nash equilibrium and ε-best
response with the same approximation parameter.
-/

namespace GameTheory
namespace KernelGame
namespace EUGameIsomorphism

variable {ι : Type} [DecidableEq ι] {G H : KernelGame ι}

/-- Exact expected-utility relabeling preserves ε-Nash equilibrium without
changing ε. -/
theorem isεNash_iff (e : EUGameIsomorphism G H) (ε : ℝ) (σ : Profile G) :
    G.IsεNash ε σ ↔ H.IsεNash ε (e.profileEquiv σ) := by
  unfold KernelGame.IsεNash
  refine forall_congr' fun who => (e.stratEquiv who).forall_congr' fun s' => ?_
  rw [← e.eu_profileEquiv σ who,
    ← e.eu_update_preserved σ who ((e.stratEquiv who).symm s')]
  simp

/-- Exact expected-utility relabeling preserves ε-best response without
changing ε. -/
theorem isεBestResponse_iff (e : EUGameIsomorphism G H) (ε : ℝ)
    (who : ι) (σ : Profile G) (s : G.Strategy who) :
    G.IsεBestResponse ε who σ s ↔
      H.IsεBestResponse ε who (e.profileEquiv σ) (e.stratEquiv who s) := by
  unfold KernelGame.IsεBestResponse
  refine (e.stratEquiv who).forall_congr' fun s' => ?_
  rw [← e.eu_update_preserved σ who s,
    ← e.eu_update_preserved σ who ((e.stratEquiv who).symm s')]
  simp

end EUGameIsomorphism
end KernelGame
end GameTheory
