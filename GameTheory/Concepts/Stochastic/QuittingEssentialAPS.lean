/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFleschSuccessor
import Mathlib.Analysis.Convex.Hull

/-!
# Essential APS certificates for the singleton-flow stratum

This file formalizes the algebraic part of the essential APS construction for
undiscounted quitting games. The operator is baseline invariant: instead of
normalizing every own-singleton payoff to zero, all continuation values are
required to dominate

`quittingSoloBaseline reward who = r_who({who})`.

There are two related prefix notions, and the distinction is load-bearing for
nonconvex continuation sets.

* `quittingEssentialAPSPrefix` is the full algebraic APS prefix
  `co ({R_owner} ∪ E)` intersected with the active face and the viability
  region. Thus it convexifies arbitrary continuation sets exactly as stated by
  the convex-hull display in the paper.
* `quittingSegmentEssentialAPSPrefix` records one concrete path segment
  `current = p R_owner + (1-p) next` with `next ∈ E`.

The segment prefix is always contained in the full prefix, but the reverse
inclusion need not hold when `E` is nonconvex. The owner-indexed essential APS
operator and its greatest fixed family use the full convex-hull prefix.
Executable finite-cycle certificates use the stronger segment relation and
are then embedded into the algebraic operator.

The proper segment prefix further requires `p ∈ (0,1)`. The zero-mass lemmas
record the exact false-progress pathology: a pinned continuation can reproduce
itself with `p = 0`, so algebraic fixed-point membership alone is not an
executable absorption path.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A continuation payoff is individually viable when every player receives
at least the payoff from quitting alone. Under the paper's normalization this
is coordinatewise nonnegativity. -/
def QuittingEssentialAPSViable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) : Prop :=
  ∀ who, quittingSoloBaseline reward who ≤ value who

/-- The constant solo-quitter endpoint for `owner`, provided it is viable. -/
def quittingEssentialAPSTerminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) : Set (Payoff ι) :=
  {value |
    value = quittingSoloReward reward owner ∧
      QuittingEssentialAPSViable reward value}

/-- The full algebraic APS prefix

`co ({R_owner} ∪ E) ∩ H_owner ∩ viable`.

No convexity hypothesis on `E` is required: `convexHull` performs the required
convexification. -/
def quittingEssentialAPSPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) : Set (Payoff ι) :=
  {current |
    QuittingEssentialAPSViable reward current ∧
      current ∈ convexHull ℝ
        (Set.insert (quittingSoloReward reward owner) E) ∧
      current owner = quittingSoloReward reward owner owner}

/-- Membership expansion for the full convex-hull prefix. -/
theorem mem_quittingEssentialAPSPrefix_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) (current : Payoff ι) :
    current ∈ quittingEssentialAPSPrefix reward owner E ↔
      QuittingEssentialAPSViable reward current ∧
        current ∈ convexHull ℝ
          (Set.insert (quittingSoloReward reward owner) E) ∧
        current owner = quittingSoloReward reward owner owner :=
  Iff.rfl

/-- The full convex-hull prefix is monotone in its continuation set. -/
theorem quittingEssentialAPSPrefix_mono
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E F : Set (Payoff ι)} (hEF : E ⊆ F) :
    quittingEssentialAPSPrefix reward owner E ⊆
      quittingEssentialAPSPrefix reward owner F := by
  intro current hcurrent
  rcases hcurrent with ⟨hviable, hconvex, hactive⟩
  refine ⟨hviable, ?_, hactive⟩
  apply convexHull_mono ?_ hconvex
  intro value hvalue
  rcases Set.mem_insert_iff.mp hvalue with hroot | hE
  · subst value
    exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (hEF hE)

/-- One path-compatible prefix with one selected continuation from `E`. For a
nonconvex `E`, this is generally smaller than
`quittingEssentialAPSPrefix reward owner E`. -/
def quittingSegmentEssentialAPSPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) : Set (Payoff ι) :=
  {current |
    QuittingEssentialAPSViable reward current ∧
      ∃ p ∈ Set.Icc (0 : ℝ) 1, ∃ next ∈ E,
        current = quittingSingletonArcPayoff p
          (quittingSoloReward reward owner) next ∧
        current owner = quittingSoloReward reward owner owner}

/-- Membership expansion for the one-continuation segment prefix. -/
theorem mem_quittingSegmentEssentialAPSPrefix_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) (current : Payoff ι) :
    current ∈ quittingSegmentEssentialAPSPrefix reward owner E ↔
      QuittingEssentialAPSViable reward current ∧
        ∃ p ∈ Set.Icc (0 : ℝ) 1, ∃ next ∈ E,
          current = quittingSingletonArcPayoff p
            (quittingSoloReward reward owner) next ∧
          current owner = quittingSoloReward reward owner owner :=
  Iff.rfl

/-- The segment prefix is monotone in its continuation set. -/
theorem quittingSegmentEssentialAPSPrefix_mono
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E F : Set (Payoff ι)} (hEF : E ⊆ F) :
    quittingSegmentEssentialAPSPrefix reward owner E ⊆
      quittingSegmentEssentialAPSPrefix reward owner F := by
  intro current hcurrent
  rcases hcurrent with
    ⟨hviable, p, hp, next, hnext, harc, hactive⟩
  exact ⟨hviable, p, hp, next, hEF hnext, harc, hactive⟩

/-- Pointwise singleton-arc notation agrees with the module convex
combination. -/
theorem quittingSingletonArcPayoff_eq_smul_add
    (p : ℝ) (root next : Payoff ι) :
    quittingSingletonArcPayoff p root next =
      p • root + (1 - p) • next := by
  funext who
  simp [quittingSingletonArcPayoff]

/-- Every one-continuation segment prefix belongs to the full convex-hull
prefix, even when the continuation set itself is nonconvex. -/
theorem quittingSegmentEssentialAPSPrefix_subset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) :
    quittingSegmentEssentialAPSPrefix reward owner E ⊆
      quittingEssentialAPSPrefix reward owner E := by
  intro current hcurrent
  rcases hcurrent with
    ⟨hviable, p, hp, next, hnext, harc, hactive⟩
  refine ⟨hviable, ?_, hactive⟩
  let root := quittingSoloReward reward owner
  have hroot : root ∈ convexHull ℝ (Set.insert root E) :=
    subset_convexHull ℝ _ (Set.mem_insert root E)
  have hnextHull : next ∈ convexHull ℝ (Set.insert root E) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem root hnext)
  have hcombo :
      p • root + (1 - p) • next ∈
        convexHull ℝ (Set.insert root E) :=
    (convex_iff_add_mem.mp (convex_convexHull ℝ _))
      hroot hnextHull hp.1 (sub_nonneg.mpr hp.2) (by ring)
  rw [harc, quittingSingletonArcPayoff_eq_smul_add]
  exact hcombo

/-- Union of the continuation sets attached to exact Flesch successors of
`owner`. The algebraic operator convexifies only after forming this union. -/
def quittingEssentialAPSSuccessorSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) : Set (Payoff ι) :=
  {next | ∃ successor,
    QuittingFleschSuccessor reward owner successor ∧
      next ∈ family successor}

@[simp] theorem mem_quittingEssentialAPSSuccessorSet_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) (next : Payoff ι) :
    next ∈ quittingEssentialAPSSuccessorSet reward family owner ↔
      ∃ successor,
        QuittingFleschSuccessor reward owner successor ∧
          next ∈ family successor :=
  Iff.rfl

/-- The successor continuation union is monotone in the owner-indexed family. -/
theorem quittingEssentialAPSSuccessorSet_mono
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E F : ι → Set (Payoff ι)} (hEF : E ≤ F) :
    quittingEssentialAPSSuccessorSet reward E owner ⊆
      quittingEssentialAPSSuccessorSet reward F owner := by
  intro next hnext
  rcases hnext with ⟨successor, hsuccessor, hmem⟩
  exact ⟨successor, hsuccessor, hEF successor hmem⟩

/-- Owner-indexed algebraic essential APS step. A nonterminal prefix is formed
from the full convex hull of the solo reward together with the union of all
exact-successor continuation sets. -/
def quittingEssentialAPSOwnerStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) : Set (Payoff ι) :=
  {current |
    current ∈ quittingEssentialAPSTerminal reward owner ∨
      current ∈ quittingEssentialAPSPrefix reward owner
        (quittingEssentialAPSSuccessorSet reward family owner)}

/-- The full convex-hull essential APS operator on owner-indexed payoff sets. -/
def quittingEssentialAPSOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) : ι → Set (Payoff ι) :=
  fun owner ↦ quittingEssentialAPSOwnerStep reward family owner

/-- Monotonicity of the owner-indexed algebraic essential APS operator. -/
theorem monotone_quittingEssentialAPSOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Monotone (quittingEssentialAPSOperator reward) := by
  intro E F hEF owner current hcurrent
  change current ∈ quittingEssentialAPSOwnerStep reward E owner at hcurrent
  change current ∈ quittingEssentialAPSOwnerStep reward F owner
  rcases hcurrent with hterminal | hprefix
  · exact Or.inl hterminal
  · exact Or.inr <|
      quittingEssentialAPSPrefix_mono reward owner
        (quittingEssentialAPSSuccessorSet_mono reward owner hEF) hprefix

/-- Segment-level owner step used to expose the stronger path-compatible
subrelation of the algebraic operator. -/
def quittingSegmentEssentialAPSOwnerStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) : Set (Payoff ι) :=
  {current |
    current ∈ quittingEssentialAPSTerminal reward owner ∨
      current ∈ quittingSegmentEssentialAPSPrefix reward owner
        (quittingEssentialAPSSuccessorSet reward family owner)}

/-- Every segment-level owner step is accepted by the full algebraic owner
step. -/
theorem quittingSegmentEssentialAPSOwnerStep_subset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) :
    quittingSegmentEssentialAPSOwnerStep reward family owner ⊆
      quittingEssentialAPSOwnerStep reward family owner := by
  intro current hcurrent
  rcases hcurrent with hterminal | hsegment
  · exact Or.inl hterminal
  · exact Or.inr <|
      quittingSegmentEssentialAPSPrefix_subset reward owner
        (quittingEssentialAPSSuccessorSet reward family owner) hsegment

/-- A self-generating family for the full algebraic operator. -/
def IsQuittingEssentialAPSSubinvariant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) : Prop :=
  ∀ owner, family owner ⊆ quittingEssentialAPSOperator reward family owner

/-- Exact fixed-point form of algebraic essential APS invariance. -/
def IsQuittingEssentialAPSInvariant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) : Prop :=
  quittingEssentialAPSOperator reward family = family

/-- Every invariant family is self-generating. -/
theorem IsQuittingEssentialAPSInvariant.subinvariant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {family : ι → Set (Payoff ι)}
    (hinvariant : IsQuittingEssentialAPSInvariant reward family) :
    IsQuittingEssentialAPSSubinvariant reward family := by
  intro owner current hcurrent
  rw [hinvariant]
  exact hcurrent

/-- A supplied algebraic essential-APS packet with a distinguished initial
payoff. Executable progress is a separate field in concrete certificates. -/
structure QuittingEssentialAPSPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  carrier : ι → Set (Payoff ι)
  initialOwner : ι
  initialValue : Payoff ι
  initial_mem : initialValue ∈ carrier initialOwner
  selfGenerating : IsQuittingEssentialAPSSubinvariant reward carrier

/-- The distinguished value of a packet has a terminal or full-convex-hull
one-step decomposition. -/
theorem QuittingEssentialAPSPacket.initial_decomposition
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingEssentialAPSPacket reward) :
    packet.initialValue ∈
      quittingEssentialAPSOperator reward packet.carrier
        packet.initialOwner :=
  packet.selfGenerating packet.initialOwner packet.initial_mem

/-- Proper positive-mass segment prefix. The open interval excludes both the
fake zero-mass edge and a sure terminal jump disguised as a continuation edge. -/
def quittingProperEssentialAPSPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) : Set (Payoff ι) :=
  {current |
    QuittingEssentialAPSViable reward current ∧
      ∃ p ∈ Set.Ioo (0 : ℝ) 1, ∃ next ∈ E,
        current = quittingSingletonArcPayoff p
          (quittingSoloReward reward owner) next ∧
        current owner = quittingSoloReward reward owner owner}

/-- Every proper segment prefix is an ordinary segment prefix. -/
theorem quittingProperEssentialAPSPrefix_subset_segment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) :
    quittingProperEssentialAPSPrefix reward owner E ⊆
      quittingSegmentEssentialAPSPrefix reward owner E := by
  intro current hcurrent
  rcases hcurrent with
    ⟨hviable, p, hp, next, hnext, harc, hactive⟩
  exact ⟨hviable, p, ⟨hp.1.le, hp.2.le⟩,
    next, hnext, harc, hactive⟩

/-- Every proper segment prefix is accepted by the full convex-hull prefix. -/
theorem quittingProperEssentialAPSPrefix_subset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (E : Set (Payoff ι)) :
    quittingProperEssentialAPSPrefix reward owner E ⊆
      quittingEssentialAPSPrefix reward owner E :=
  (quittingProperEssentialAPSPrefix_subset_segment reward owner E).trans
    (quittingSegmentEssentialAPSPrefix_subset reward owner E)

/-- Proper owner step: every nonterminal edge chooses one exact-successor
continuation and carries strictly positive, strictly subunit absorption mass. -/
def quittingProperEssentialAPSOwnerStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) : Set (Payoff ι) :=
  {current |
    current ∈ quittingEssentialAPSTerminal reward owner ∨
      current ∈ quittingProperEssentialAPSPrefix reward owner
        (quittingEssentialAPSSuccessorSet reward family owner)}

/-- Every proper owner step is accepted by the full algebraic operator. -/
theorem quittingProperEssentialAPSOwnerStep_subset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι)) (owner : ι) :
    quittingProperEssentialAPSOwnerStep reward family owner ⊆
      quittingEssentialAPSOwnerStep reward family owner := by
  intro current hcurrent
  rcases hcurrent with hterminal | hproper
  · exact Or.inl hterminal
  · exact Or.inr <|
      quittingProperEssentialAPSPrefix_subset reward owner
        (quittingEssentialAPSSuccessorSet reward family owner) hproper

/-- **Zero-mass segment pathology.** A viable continuation whose active
coordinate is pinned reproduces itself by choosing `p = 0`. -/
theorem mem_quittingSegmentEssentialAPSPrefix_of_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)} {value : Payoff ι}
    (hviable : QuittingEssentialAPSViable reward value)
    (hvalue : value ∈ E)
    (hactive : value owner = quittingSoloReward reward owner owner) :
    value ∈ quittingSegmentEssentialAPSPrefix reward owner E := by
  refine ⟨hviable, 0, ⟨le_rfl, zero_le_one⟩,
    value, hvalue, ?_, hactive⟩
  funext who
  simp [quittingSingletonArcPayoff]

/-- The zero-mass segment witness also gives membership in the full algebraic
prefix. -/
theorem mem_quittingEssentialAPSPrefix_of_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {E : Set (Payoff ι)} {value : Payoff ι}
    (hviable : QuittingEssentialAPSViable reward value)
    (hvalue : value ∈ E)
    (hactive : value owner = quittingSoloReward reward owner owner) :
    value ∈ quittingEssentialAPSPrefix reward owner E :=
  quittingSegmentEssentialAPSPrefix_subset reward owner E
    (mem_quittingSegmentEssentialAPSPrefix_of_zero reward owner
      hviable hvalue hactive)

/-- The same zero-mass pathology lifts to the full owner step whenever one
successor set contains the pinned value. -/
theorem mem_quittingEssentialAPSOwnerStep_of_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    {owner successor : ι} {value : Payoff ι}
    (hsuccessor : QuittingFleschSuccessor reward owner successor)
    (hviable : QuittingEssentialAPSViable reward value)
    (hvalue : value ∈ family successor)
    (hactive : value owner = quittingSoloReward reward owner owner) :
    value ∈ quittingEssentialAPSOwnerStep reward family owner := by
  exact Or.inr <|
    mem_quittingEssentialAPSPrefix_of_zero reward owner hviable
      ⟨successor, hsuccessor, hvalue⟩ hactive

end GameTheory
