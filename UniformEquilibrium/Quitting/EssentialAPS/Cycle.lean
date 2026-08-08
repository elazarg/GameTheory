/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.FixedPoint
import UniformEquilibrium.Quitting.Cycles.SingletonArcCycle

/-!
# Finite executable essential-APS cycles

The general essential APS operator is a full-convex-hull algebraic
self-generation condition. This file gives a finite executable certificate
that carries the stronger one-segment progress data and feeds the already
verified singleton-flow mesh and terminal-to-uniform compilers.

A certificate consists of a cyclic list of active owners, positive coarse
absorption masses, coarse continuation values, and exact singleton arc
equations. Consecutive owners are distinct. Under singleton genericity, the
two-arc extraction theorem proves that every seam follows the Flesch successor
graph; the graph relation is not an independent certificate field.

The capstones make the division of labor explicit:

* `carrier_subinvariant` embeds every proper segment cycle into the larger
  convex-hull essential APS operator;
* `coarse_mem_greatest` puts every displayed value in the carrier-restricted
  greatest algebraic fixed family;
* `opponentContracts` derives the compiler's contraction condition from
  positive mass and the change of owner at every seam;
* `isUniformEquilibriumPayoff` compiles the selected value to one fixed-target
  uniform payoff.

This is a complete positive result for supplied finite singleton-flow cycles,
not a claim that every point of the convexified essential-APS fixed family is
executable or that general quitting equilibria lie in this stratum.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [DecidableEq ι]

/-- A finite, proper essential-APS cycle together with all quantitative data
needed by the existing singleton-flow compiler. -/
structure QuittingEssentialAPSCycleCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (L : ℕ) where
  owner : Fin L → ι
  hazard : Fin L → ℝ
  coarse : Fin L → Payoff ι
  initial : Fin L
  intensityBound : ℝ
  collisionBound : ℝ
  hazard_pos : ∀ block, 0 < hazard block
  hazard_lt_one : ∀ block, hazard block < 1
  intensity_le : ∀ block,
    quittingMeshIntensity (hazard block) ≤ intensityBound
  collisionBound_nonneg : 0 ≤ collisionBound
  arc : ∀ block,
    coarse block = quittingSingletonArcPayoff (hazard block)
      (quittingSoloReward reward (owner block))
      (coarse (finRotate L block))
  active : ∀ block,
    coarse block (owner block) =
      quittingSoloReward reward (owner block) (owner block)
  viable : ∀ block, QuittingEssentialAPSViable reward (coarse block)
  collision_le : ∀ block other, other ≠ owner block →
    max (quittingSingletonCollisionReward reward (owner block) other -
      quittingSoloReward reward other other) 0 ≤ collisionBound
  owner_changes : ∀ block,
    owner block ≠ owner (finRotate L block)
  singleton_generic : IsQuittingSoloGeneric reward

namespace QuittingEssentialAPSCycleCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {L : ℕ}

/-- Owner-indexed carrier displayed by a finite certificate. -/
def carrier
    (certificate : QuittingEssentialAPSCycleCertificate reward L)
    (owner : ι) : Set (Payoff ι) :=
  {value | ∃ block,
    certificate.owner block = owner ∧ certificate.coarse block = value}

@[simp] theorem coarse_mem_carrier
    (certificate : QuittingEssentialAPSCycleCertificate reward L)
    (block : Fin L) :
    certificate.coarse block ∈
      certificate.carrier (certificate.owner block) := by
  exact ⟨block, rfl, rfl⟩

/-- Every consecutive pair of blocks follows an edge of the exact Flesch
successor graph. -/
theorem successor
    (certificate : QuittingEssentialAPSCycleCertificate reward L)
    (block : Fin L) :
    QuittingFleschSuccessor reward (certificate.owner block)
      (certificate.owner (finRotate L block)) := by
  exact quittingFleschSuccessor_of_consecutive_arcs
    reward certificate.singleton_generic
    (certificate.owner_changes block)
    (certificate.hazard_pos block)
    (certificate.hazard_lt_one block)
    (certificate.hazard_pos (finRotate L block))
    (certificate.hazard_lt_one (finRotate L block)).le
    (certificate.arc block)
    (certificate.arc (finRotate L block))
    (certificate.active block)
    (certificate.active (finRotate L block))
    (certificate.viable
      (finRotate L (finRotate L block)) (certificate.owner block))
    (certificate.viable block
      (certificate.owner (finRotate L block)))

/-- Consecutive owners in a proper Flesch cycle are different. -/
theorem owner_ne_next
    (certificate : QuittingEssentialAPSCycleCertificate reward L)
    (block : Fin L) :
    certificate.owner block ≠
      certificate.owner (finRotate L block) :=
  certificate.owner_changes block

/-- Every player faces a strictly contracting opponent-survival factor around
the cycle. If the distinguished initial block belongs to `who`, its successor
does not; otherwise the initial block itself supplies the strict factor. All
factors are positive because every hazard is strictly below one. -/
theorem opponentContracts
    (certificate : QuittingEssentialAPSCycleCertificate reward L)
    (who : ι) :
    (∏ block : Fin L,
      if who = certificate.owner block then 1
      else 1 - certificate.hazard block) < 1 := by
  let factor : Fin L → ℝ := fun block ↦
    if who = certificate.owner block then 1
    else 1 - certificate.hazard block
  have hpositive : ∀ block ∈ Finset.univ, 0 < factor block := by
    intro block _
    simp only [factor]
    split
    · norm_num
    · exact sub_pos.mpr (certificate.hazard_lt_one block)
  have hle : ∀ block ∈ Finset.univ, factor block ≤ (1 : ℝ) := by
    intro block _
    simp only [factor]
    split
    · exact le_rfl
    · exact sub_le_self 1 (certificate.hazard_pos block).le
  have hstrict : ∃ block ∈ Finset.univ, factor block < (1 : ℝ) := by
    by_cases hwho : who = certificate.owner certificate.initial
    · refine ⟨finRotate L certificate.initial, Finset.mem_univ _, ?_⟩
      have hnext : who ≠
          certificate.owner (finRotate L certificate.initial) := by
        intro h
        exact certificate.owner_changes certificate.initial
          (hwho.symm.trans h)
      simp only [factor, if_neg hnext]
      linarith [certificate.hazard_pos
        (finRotate L certificate.initial)]
    · refine ⟨certificate.initial, Finset.mem_univ _, ?_⟩
      simp only [factor, if_neg hwho]
      linarith [certificate.hazard_pos certificate.initial]
  have hproduct := Finset.prod_lt_prod hpositive hle hstrict
  simpa only [Finset.prod_const_one, Finset.card_univ, one_pow,
    factor] using hproduct

/-- Every displayed coarse value is a proper positive-mass segment prefix.
Its next coarse value belongs to the union of exact-successor continuation
sets used by the algebraic owner operator. -/
theorem coarse_mem_properPrefix
    (certificate : QuittingEssentialAPSCycleCertificate reward L)
    (block : Fin L) :
    certificate.coarse block ∈
      quittingProperEssentialAPSPrefix reward (certificate.owner block)
        (quittingEssentialAPSSuccessorSet reward certificate.carrier
          (certificate.owner block)) := by
  refine ⟨certificate.viable block,
    certificate.hazard block,
    ⟨certificate.hazard_pos block, certificate.hazard_lt_one block⟩,
    certificate.coarse (finRotate L block), ?_,
    certificate.arc block, certificate.active block⟩
  exact ⟨certificate.owner (finRotate L block),
    certificate.successor block,
    ⟨finRotate L block, rfl, rfl⟩⟩

/-- The carrier of a finite proper cycle is self-generating for the full
convex-hull essential APS operator. The supplied segment witness is stronger
than the algebraic membership recorded here. -/
theorem carrier_subinvariant
    (certificate : QuittingEssentialAPSCycleCertificate reward L) :
    IsQuittingEssentialAPSSubinvariant reward certificate.carrier := by
  intro owner value hvalue
  rcases hvalue with ⟨block, howner, hcoarse⟩
  subst owner
  subst value
  change certificate.coarse block ∈
    quittingEssentialAPSOwnerStep reward certificate.carrier
      (certificate.owner block)
  exact Or.inr <|
    quittingProperEssentialAPSPrefix_subset reward
      (certificate.owner block)
      (quittingEssentialAPSSuccessorSet reward certificate.carrier
        (certificate.owner block))
      (certificate.coarse_mem_properPrefix block)

/-- The displayed carrier is also subinvariant inside itself. -/
theorem carrier_subinvariantWithin
    (certificate : QuittingEssentialAPSCycleCertificate reward L) :
    IsQuittingEssentialAPSSubinvariantWithin reward
      certificate.carrier certificate.carrier := by
  intro owner value hvalue
  exact ⟨hvalue, certificate.carrier_subinvariant owner hvalue⟩

/-- Every displayed coarse value belongs to the carrier-restricted greatest
algebraic essential-APS fixed family. -/
theorem coarse_mem_greatest
    (certificate : QuittingEssentialAPSCycleCertificate reward L)
    (block : Fin L) :
    certificate.coarse block ∈
      quittingEssentialAPSGreatestFamily reward certificate.carrier
        (certificate.owner block) := by
  exact quittingEssentialAPSFamily_le_greatest reward
    certificate.carrier certificate.carrier
    certificate.carrier_subinvariantWithin
    (certificate.owner block) (certificate.coarse_mem_carrier block)

/-- The finite cycle, viewed as a distinguished algebraic essential-APS
packet. -/
def toPacket
    (certificate : QuittingEssentialAPSCycleCertificate reward L) :
    QuittingEssentialAPSPacket reward where
  carrier := certificate.carrier
  initialOwner := certificate.owner certificate.initial
  initialValue := certificate.coarse certificate.initial
  initial_mem := certificate.coarse_mem_carrier certificate.initial
  selfGenerating := certificate.carrier_subinvariant

/-- Fixed-m terminal compilation. The exploitability bound is exactly the
existing mesh bound `collisionBound * intensityBound / m`, and the terminal
payoff is exactly the selected coarse value. -/
theorem isTerminalNash_and_hasValue
    [Fintype ι]
    (certificate : QuittingEssentialAPSCycleCertificate reward L)
    (m : ℕ) (hm : 0 < m) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (certificate.collisionBound * certificate.intensityBound /
          (m : ℝ))
        (quittingCyclicBehaviorProfile reward
          (quittingSingletonArcCycleRoot certificate.owner
            certificate.hazard m
            (fun block ↦ (certificate.hazard_pos block).le)
            certificate.hazard_lt_one)
          (quittingSingletonMeshInitialPhase certificate.initial m hm)) ∧
      quittingTerminalPayoff reward
          (quittingCyclicBehaviorProfile reward
            (quittingSingletonArcCycleRoot certificate.owner
              certificate.hazard m
              (fun block ↦ (certificate.hazard_pos block).le)
              certificate.hazard_lt_one)
            (quittingSingletonMeshInitialPhase certificate.initial m hm)) =
        certificate.coarse certificate.initial := by
  exact singletonArcCycle_isTerminalNash_and_hasValue
    reward certificate.owner certificate.hazard certificate.coarse
    certificate.initial m hm
    (aStar := certificate.intensityBound)
    (D := certificate.collisionBound)
    (fun block ↦ (certificate.hazard_pos block).le)
    certificate.hazard_lt_one certificate.intensity_le
    certificate.collisionBound_nonneg certificate.arc certificate.active
    (fun block who ↦ certificate.viable block who)
    certificate.collision_le certificate.opponentContracts

/-- **Finite essential-APS cycle compiler.** The selected coarse value is a
uniform-equilibrium payoff of the quitting game from its live state. -/
theorem isUniformEquilibriumPayoff
    [Fintype ι]
    (certificate : QuittingEssentialAPSCycleCertificate reward L) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (certificate.coarse certificate.initial) := by
  exact singletonArcCycle_isUniformEquilibriumPayoff
    reward certificate.owner certificate.hazard certificate.coarse
    certificate.initial
    (aStar := certificate.intensityBound)
    (D := certificate.collisionBound)
    (fun block ↦ (certificate.hazard_pos block).le)
    certificate.hazard_lt_one certificate.intensity_le
    certificate.collisionBound_nonneg certificate.arc certificate.active
    (fun block who ↦ certificate.viable block who)
    certificate.collision_le certificate.opponentContracts

end QuittingEssentialAPSCycleCertificate

end GameTheory
