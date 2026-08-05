/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.EntryReachableChargedClass

/-!
# Support-rank dichotomy for positive communicating classes

The finite support rank of an active occupation is the cardinality of its
positive source support.  A selected positive communicating class either
uses a proper subset, and its cardinality is strictly smaller, or it is the
whole active support.  In the latter case the active kernel itself is one
closed communicating class carrying positive aggregate charge.
-/

noncomputable section

namespace Math
namespace Probability

open Finset

variable {S I : Type*}

namespace EntryReachablePositiveChargedCirculation

variable [Fintype S] [Fintype I] [DecidableEq S]
  {kernel : I → PMF S} {source : I → S}
  {charge : I → ℝ} {entry : S}

/-- Cardinality rank of the full positive source support. -/
def activeSupportRank
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) : ℕ :=
  Fintype.card (ActiveState C)

/-- Cardinality rank of one selected communicating class. -/
def PositiveCommunicatingClass.supportRank
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C) : ℕ :=
  P.closedClass.states.card

/-- The selected class is a proper active-support child, with strict
cardinality rank decrease. -/
def PositiveCommunicatingClass.HasProperSupportRankDescent
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C) : Prop :=
  P.closedClass.states ⊂
      (Finset.univ : Finset (ActiveState C)) ∧
    P.supportRank < C.activeSupportRank

/-- The selected class is the whole active support.  This branch records
the corresponding same-rank equality, global communication, and positive
aggregate charge. -/
def PositiveCommunicatingClass.IsFullActiveSupportClass
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C) : Prop :=
    P.closedClass.states =
      (Finset.univ : Finset (ActiveState C)) ∧
    P.supportRank = C.activeSupportRank ∧
    IsPMFClosed C.activeKernel
      (Finset.univ : Finset (ActiveState C)) ∧
    (∀ left right : ActiveState C,
      PMFReachable C.activeKernel left right) ∧
    0 < C.communicationClassCharge P.representative

namespace PositiveCommunicatingClass

/-- The packaged class is exactly the canonical communication class of its
positive-charge representative. -/
theorem states_eq_communicationClass
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C) :
    P.closedClass.states =
      pmfCommunicationClass C.activeKernel P.representative := by
  rw [P.closedClass.states_eq_communicationClass,
    P.closedClass_entry]

/-- Proper inclusion in the active support gives strict cardinality rank
decrease. -/
theorem supportRank_lt_activeSupportRank
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C)
    (hproper :
      P.closedClass.states ⊂
        (Finset.univ : Finset (ActiveState C))) :
    P.supportRank < C.activeSupportRank := by
  exact Finset.card_lt_card hproper

/-- Exact finite support-rank dichotomy. -/
theorem properSupportRankDescent_or_fullActiveSupport
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C) :
    P.HasProperSupportRankDescent ∨
      P.IsFullActiveSupportClass := by
  by_cases hfull :
      P.closedClass.states =
        (Finset.univ : Finset (ActiveState C))
  · right
    refine ⟨hfull, ?_, ?_, ?_, P.charge_pos⟩
    · simp [supportRank, activeSupportRank, hfull]
    · simpa [hfull] using P.closedClass.closed
    · intro left right
      apply P.closedClass.communicates
      · simp [hfull]
      · simp [hfull]
  · left
    have hproper :
        P.closedClass.states ⊂
          (Finset.univ : Finset (ActiveState C)) :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, hfull⟩
    exact
      ⟨hproper,
        supportRank_lt_activeSupportRank C P hproper⟩

end PositiveCommunicatingClass

end EntryReachablePositiveChargedCirculation

end Probability
end Math
