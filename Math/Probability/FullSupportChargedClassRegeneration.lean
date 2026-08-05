/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.ChargedClassSupportRank
import Math.Probability.FiniteKernelRegeneration

/-!
# Regeneration in the full-support positive-class branch

When the selected positive communicating class equals the whole active
occupation support, every active state reaches its positive-charge
representative.  The fixed-kernel finite regeneration theorem then gives a
uniform path-length bound and a positive bounded-step minorization constant.

This is a support-level entry fact.  It does not establish punishment
credibility, target compatibility, or an analytic power law in an external
parameter.
-/

noncomputable section

namespace Math
namespace Probability

variable {S I : Type*}

namespace EntryReachablePositiveChargedCirculation

variable [Fintype S] [Fintype I] [DecidableEq S]
  {kernel : I → PMF S} {source : I → S}
  {charge : I → ℝ} {entry : S}

namespace PositiveCommunicatingClass

/-- Fixed-kernel regeneration data retained together with the same-rank,
closed-support, and positive-charge facts of the full-support branch. -/
structure FullSupportRegeneration
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C) where
  regeneration :
    FiniteKernelRegeneration C.activeKernel P.representative
  hittingMinorization :
    FiniteHittingMinorization
      C.activeKernel P.representative
  same_rank : P.supportRank = C.activeSupportRank
  active_closed :
    IsPMFClosed C.activeKernel
      (Finset.univ : Finset (ActiveState C))
  aggregate_charge_pos :
    0 < C.communicationClassCharge P.representative

/-- The same-rank full-active-support branch has a uniform bounded-step
regeneration constant at the positive-charge representative. -/
theorem exists_fullSupportRegeneration
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C)
    (hfull : P.IsFullActiveSupportClass) :
    Nonempty (FullSupportRegeneration C P) := by
  rcases hfull with
    ⟨-, same_rank, active_closed, communicates,
      aggregate_charge_pos⟩
  obtain ⟨regeneration⟩ :=
    exists_finiteKernelRegeneration
      C.activeKernel P.representative
      (fun source => communicates source P.representative)
  obtain ⟨hittingMinorization⟩ :=
    exists_finiteHittingMinorization
      C.activeKernel P.representative
      (fun source => communicates source P.representative)
  exact ⟨{
    regeneration := regeneration
    hittingMinorization := hittingMinorization
    same_rank := same_rank
    active_closed := active_closed
    aggregate_charge_pos := aggregate_charge_pos
  }⟩

end PositiveCommunicatingClass

end EntryReachablePositiveChargedCirculation

end Probability
end Math
