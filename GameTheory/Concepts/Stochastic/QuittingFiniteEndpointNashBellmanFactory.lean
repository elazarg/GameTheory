/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteNashBellmanFactory

/-!
# Arbitrary-endpoint finite Nash--Bellman chains

The zero-boundary factory is only a specialization of the compact serial
Nash--Bellman predecessor relation.  This module starts the same backward
iteration from any payoff vector in the canonical reward cube.  The projected
finite chain therefore ends at the supplied vector and otherwise has exactly
the same Bellman, Nash, and boundedness guarantees as the zero-anchor factory.

The root stored at and after the endpoint is the all-Continue simplex root.
It is only a presentation coordinate of the terminal anchor; consumers are
free to splice an actual continuation at the cutoff.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A bounded payoff vector, paired with the all-Continue presentation root,
as an element of the canonical Nash--Bellman box. -/
def quittingEndpointBoundaryAnchor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward) :
    (canonicalQuittingNashBellmanSerialRelation reward).box := by
  refine ⟨(endpoint, quittingAllContinueSimplexRoot), ?_⟩
  change endpoint ∈ Set.Icc
    (fun _ => -quittingRewardBound reward)
    (fun _ => quittingRewardBound reward)
  constructor
  · intro who
    exact (abs_le.mp (hendpoint who)).1
  · intro who
    exact (abs_le.mp (hendpoint who)).2

/-- Backward predecessor iteration from an arbitrary bounded endpoint.  At and
after the cutoff the state stays at the endpoint anchor. -/
def quittingFiniteEndpointNashBellmanState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) : QuittingNashBellmanPoint ι :=
  if time ≤ cutoff then
    compactSerialIteratedPredecessor
      (canonicalQuittingNashBellmanSerialRelation reward)
      (cutoff - time)
      (quittingEndpointBoundaryAnchor reward endpoint hendpoint)
  else
    quittingEndpointBoundaryAnchor reward endpoint hendpoint

/-- Every arbitrary-endpoint factory state remains in the canonical box. -/
theorem quittingFiniteEndpointNashBellmanState_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) :
    quittingFiniteEndpointNashBellmanState reward endpoint hendpoint cutoff time ∈
      quittingNashBellmanBox (quittingRewardBound reward) := by
  classical
  unfold quittingFiniteEndpointNashBellmanState
  split_ifs
  · exact (compactSerialIteratedPredecessor
      (canonicalQuittingNashBellmanSerialRelation reward) _
      (quittingEndpointBoundaryAnchor reward endpoint hendpoint)).property
  · exact (quittingEndpointBoundaryAnchor reward endpoint hendpoint).property

/-- At and after the cutoff, the state is literally the supplied anchor. -/
theorem quittingFiniteEndpointNashBellmanState_eq_anchor_of_cutoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingFiniteEndpointNashBellmanState reward endpoint hendpoint cutoff time =
      quittingEndpointBoundaryAnchor reward endpoint hendpoint := by
  classical
  by_cases hreverse : time ≤ cutoff
  · have heq : time = cutoff := le_antisymm hreverse htime
    subst time
    simp [quittingFiniteEndpointNashBellmanState]
  · simp [quittingFiniteEndpointNashBellmanState, hreverse]

/-- Adjacent pre-cutoff states satisfy the exact Nash--Bellman edge relation. -/
theorem quittingFiniteEndpointNashBellmanState_related
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) (htime : time < cutoff) :
    IsQuittingNashBellmanEdge reward
      (quittingFiniteEndpointNashBellmanState reward endpoint hendpoint cutoff time)
      (quittingFiniteEndpointNashBellmanState reward endpoint hendpoint cutoff
        (time + 1)) := by
  classical
  have htime0 : time ≤ cutoff := htime.le
  have htime1 : time + 1 ≤ cutoff := by omega
  unfold quittingFiniteEndpointNashBellmanState
  rw [if_pos htime0, if_pos htime1]
  have hsub : cutoff - time = (cutoff - (time + 1)) + 1 := by omega
  rw [hsub, compactSerialIteratedPredecessor_succ]
  exact (canonicalQuittingNashBellmanSerialRelation reward).predecessor_related _

/-- Payoff path projected from the arbitrary-endpoint state path. -/
def quittingFiniteEndpointNashBellmanValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) : Payoff ι :=
  (quittingFiniteEndpointNashBellmanState reward endpoint hendpoint cutoff time).1

/-- Root path projected from the arbitrary-endpoint state path. -/
def quittingFiniteEndpointNashBellmanRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) : ι → PMF Bool :=
  quittingRootOfSimplex
    (quittingFiniteEndpointNashBellmanState reward endpoint hendpoint cutoff time).2

/-- Factory values equal the supplied endpoint at and after the cutoff. -/
theorem quittingFiniteEndpointNashBellmanValue_eq_endpoint_of_cutoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingFiniteEndpointNashBellmanValue reward endpoint hendpoint cutoff time =
      endpoint := by
  rw [quittingFiniteEndpointNashBellmanValue,
    quittingFiniteEndpointNashBellmanState_eq_anchor_of_cutoff_le
      reward endpoint hendpoint cutoff time htime]
  rfl

/-- Factory roots use the all-Continue presentation at and after the cutoff. -/
theorem quittingFiniteEndpointNashBellmanRoots_eq_allContinue_of_cutoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingFiniteEndpointNashBellmanRoots reward endpoint hendpoint cutoff time =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  rw [quittingFiniteEndpointNashBellmanRoots,
    quittingFiniteEndpointNashBellmanState_eq_anchor_of_cutoff_le
      reward endpoint hendpoint cutoff time htime]
  exact quittingRootOfSimplex_allContinueSimplexRoot

/-- Exact policy evaluation before the cutoff. -/
theorem quittingFiniteEndpointNashBellmanValue_eq_successor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) (htime : time < cutoff) :
    quittingFiniteEndpointNashBellmanValue reward endpoint hendpoint cutoff time =
      quittingRootSuccessorPayoff reward
        (quittingFiniteEndpointNashBellmanValue reward endpoint hendpoint cutoff
          (time + 1))
        (quittingFiniteEndpointNashBellmanRoots reward endpoint hendpoint cutoff
          time) :=
  (quittingFiniteEndpointNashBellmanState_related
    reward endpoint hendpoint cutoff time htime).1

/-- Every pre-cutoff root is exact Nash against the next displayed value. -/
theorem quittingFiniteEndpointNashBellmanRoots_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) (htime : time < cutoff) :
    IsεQuittingRootNash reward
      (quittingFiniteEndpointNashBellmanValue reward endpoint hendpoint cutoff
        (time + 1)) 0
      (quittingFiniteEndpointNashBellmanRoots reward endpoint hendpoint cutoff
        time) := by
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward
      (quittingFiniteEndpointNashBellmanValue reward endpoint hendpoint cutoff
        (time + 1))
      (quittingFiniteEndpointNashBellmanRoots reward endpoint hendpoint cutoff
        time)).1
    (quittingFiniteEndpointNashBellmanState_related
      reward endpoint hendpoint cutoff time htime).2

/-- Every projected factory value stays in the canonical reward cube. -/
theorem abs_quittingFiniteEndpointNashBellmanValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff time : ℕ) (who : ι) :
    |quittingFiniteEndpointNashBellmanValue reward endpoint hendpoint cutoff
        time who| ≤ quittingRewardBound reward := by
  have hmem := quittingFiniteEndpointNashBellmanState_mem
    reward endpoint hendpoint cutoff time
  exact abs_le.mpr ⟨hmem.1 who, hmem.2 who⟩

/-- **Finite arbitrary-endpoint Nash--Bellman factory.** -/
theorem exists_finiteEndpointExactQuittingNashBellmanChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : Payoff ι)
    (hendpoint : ∀ who, |endpoint who| ≤ quittingRewardBound reward)
    (cutoff : ℕ) :
    ∃ (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι),
      (∀ time, cutoff ≤ time →
        roots time = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      value cutoff = endpoint ∧
      (∀ time, time < cutoff →
        value time = quittingRootSuccessorPayoff reward
          (value (time + 1)) (roots time)) ∧
      (∀ time, time < cutoff →
        IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) ∧
      ∀ time who, |value time who| ≤ quittingRewardBound reward := by
  exact ⟨quittingFiniteEndpointNashBellmanRoots reward endpoint hendpoint cutoff,
    quittingFiniteEndpointNashBellmanValue reward endpoint hendpoint cutoff,
    quittingFiniteEndpointNashBellmanRoots_eq_allContinue_of_cutoff_le
      reward endpoint hendpoint cutoff,
    quittingFiniteEndpointNashBellmanValue_eq_endpoint_of_cutoff_le
      reward endpoint hendpoint cutoff cutoff le_rfl,
    quittingFiniteEndpointNashBellmanValue_eq_successor
      reward endpoint hendpoint cutoff,
    quittingFiniteEndpointNashBellmanRoots_isZeroNash
      reward endpoint hendpoint cutoff,
    abs_quittingFiniteEndpointNashBellmanValue_le
      reward endpoint hendpoint cutoff⟩

end GameTheory
