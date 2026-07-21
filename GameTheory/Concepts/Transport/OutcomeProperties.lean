/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameIsomorphism
import GameTheory.Core.GameProperties

/-!
# Outcome Properties under Protocol Isomorphism

Raw-outcome properties are not determined by strategic expected utilities:
unreachable outcomes may carry arbitrary utilities. A protocol isomorphism
together with pointwise utility compatibility does preserve these properties,
because its outcome equivalence reindexes every raw outcome.
-/

namespace GameTheory
namespace KernelGame
namespace ProtocolIsomorphism

variable {ι : Type} {G H : KernelGame ι}

/-- Identical-interest utility at every raw outcome is invariant under a
utility-compatible protocol isomorphism. -/
theorem isTeamGame_iff (e : ProtocolIsomorphism G H)
    (hutil : ∀ ω : G.Outcome,
      H.utility (e.outcomeEquiv ω) = G.utility ω) :
    G.IsTeamGame ↔ H.IsTeamGame := by
  constructor
  · intro h τ i j
    let ω := e.outcomeEquiv.symm τ
    calc
      H.utility τ i = H.utility (e.outcomeEquiv ω) i := by simp [ω]
      _ = G.utility ω i := congrFun (hutil ω) i
      _ = G.utility ω j := h ω i j
      _ = H.utility (e.outcomeEquiv ω) j := (congrFun (hutil ω) j).symm
      _ = H.utility τ j := by simp [ω]
  · intro h ω i j
    calc
      G.utility ω i = H.utility (e.outcomeEquiv ω) i :=
        (congrFun (hutil ω) i).symm
      _ = H.utility (e.outcomeEquiv ω) j := h (e.outcomeEquiv ω) i j
      _ = G.utility ω j := congrFun (hutil ω) j

/-- Constant-sum utility at every raw outcome is invariant under a
utility-compatible protocol isomorphism. -/
theorem isConstantSum_iff [Fintype ι] (e : ProtocolIsomorphism G H)
    (hutil : ∀ ω : G.Outcome,
      H.utility (e.outcomeEquiv ω) = G.utility ω)
    (c : ℝ) :
    G.IsConstantSum c ↔ H.IsConstantSum c := by
  constructor
  · intro h τ
    let ω := e.outcomeEquiv.symm τ
    calc
      (∑ i : ι, H.utility τ i) =
          ∑ i : ι, H.utility (e.outcomeEquiv ω) i := by simp [ω]
      _ = ∑ i : ι, G.utility ω i := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrFun (hutil ω) i
      _ = c := h ω
  · intro h ω
    calc
      (∑ i : ι, G.utility ω i) =
          ∑ i : ι, H.utility (e.outcomeEquiv ω) i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (congrFun (hutil ω) i).symm
      _ = c := h (e.outcomeEquiv ω)

/-- Zero-sum utility at every raw outcome is invariant under a
utility-compatible protocol isomorphism. -/
theorem isZeroSum_iff [Fintype ι] (e : ProtocolIsomorphism G H)
    (hutil : ∀ ω : G.Outcome,
      H.utility (e.outcomeEquiv ω) = G.utility ω) :
    G.IsZeroSum ↔ H.IsZeroSum := by
  unfold KernelGame.IsZeroSum
  exact e.isConstantSum_iff hutil 0

end ProtocolIsomorphism
end KernelGame
end GameTheory
