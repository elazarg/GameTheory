/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Core.GameProperties

/-!
# Potential Games under Game Isomorphism

Potential functions are reindexed through the profile equivalence. Exact,
weighted exact, and ordinal potential identities are invariant under an exact
expected-utility relabeling.
-/

namespace GameTheory
namespace KernelGame
namespace EUGameIsomorphism

variable {ι : Type} [DecidableEq ι] {G H : KernelGame ι}

open Classical in
/-- Exact-potential identities are invariant under expected-utility game
isomorphism. -/
theorem isExactPotential_iff (e : EUGameIsomorphism G H) (Φ : Profile G → ℝ) :
    G.IsExactPotential Φ ↔ H.IsExactPotential (e.profileFunctionEquiv Φ) := by
  unfold KernelGame.IsExactPotential
  refine forall_congr' fun who =>
    e.profileEquiv.forall_congr' fun τ =>
      (e.stratEquiv who).forall_congr' fun s' => ?_
  rw [← e.eu_update_preserved (e.profileEquiv.symm τ) who
      ((e.stratEquiv who).symm s'),
    ← e.eu_profileEquiv (e.profileEquiv.symm τ) who]
  simp [profileFunctionEquiv_apply]

open Classical in
/-- Weighted exact-potential identities transport with the same player
weights. -/
theorem isWeightedExactPotential_iff (e : EUGameIsomorphism G H)
    (Φ : Profile G → ℝ) (w : ι → ℝ) :
    G.IsWeightedExactPotential Φ w ↔
      H.IsWeightedExactPotential (e.profileFunctionEquiv Φ) w := by
  unfold KernelGame.IsWeightedExactPotential
  refine and_congr Iff.rfl ?_
  refine forall_congr' fun who =>
    e.profileEquiv.forall_congr' fun τ =>
      (e.stratEquiv who).forall_congr' fun s' => ?_
  rw [← e.eu_update_preserved (e.profileEquiv.symm τ) who
      ((e.stratEquiv who).symm s'),
    ← e.eu_profileEquiv (e.profileEquiv.symm τ) who]
  simp [profileFunctionEquiv_apply]

open Classical in
/-- Ordinal-potential improvement comparisons are invariant under
expected-utility game isomorphism. -/
theorem isOrdinalPotential_iff (e : EUGameIsomorphism G H) (Φ : Profile G → ℝ) :
    G.IsOrdinalPotential Φ ↔ H.IsOrdinalPotential (e.profileFunctionEquiv Φ) := by
  unfold KernelGame.IsOrdinalPotential
  refine forall_congr' fun who =>
    e.profileEquiv.forall_congr' fun τ =>
      (e.stratEquiv who).forall_congr' fun s' => ?_
  rw [← e.eu_update_preserved (e.profileEquiv.symm τ) who
      ((e.stratEquiv who).symm s'),
    ← e.eu_profileEquiv (e.profileEquiv.symm τ) who]
  simp [profileFunctionEquiv_apply]

end EUGameIsomorphism
end KernelGame
end GameTheory
