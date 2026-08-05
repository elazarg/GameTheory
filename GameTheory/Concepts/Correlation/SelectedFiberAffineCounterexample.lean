/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.SelectedFiberBinaryGadget

/-!
# A two-context selected-fiber counterexample

This file gives a finite algebraic obstruction to exchanging the quantifiers

`forall context, exists packet`

and

`exists packet, forall context`.

The feasible packets are cut out by rational affine constraints together with
membership in two scaled copies of the correlated observation triangle.  Every
target in `[0,1]` has a feasible packet that is product-realizable at either
specified context, but no feasible packet is product-realizable at both
contexts at once.
-/

noncomputable section

namespace GameTheory
namespace Correlation
namespace SelectedFiber

open Math Math.PMFProduct

/-- The finite variables in the two-context affine counterexample. -/
structure TwoContextPacket where
  target : ℝ
  contextMass : Bool → ℝ
  observation : Bool → Bool → ℝ

namespace TwoContextPacket

/-- Correlated feasibility: the target bounds and coupling equations are
affine, while `triangle_le_mass` says that each observation lies in the scaled
correlated triangle `z * C`. -/
structure IsCorrelatedFeasible (packet : TwoContextPacket) : Prop where
  target_nonneg : 0 ≤ packet.target
  target_le_one : packet.target ≤ 1
  contextMass_nonneg : ∀ context, 0 ≤ packet.contextMass context
  observation_nonneg : ∀ context coordinate, 0 ≤ packet.observation context coordinate
  triangle_le_mass : ∀ context,
    packet.observation context false + packet.observation context true ≤
      packet.contextMass context
  false_topEdge :
    packet.observation false false + packet.observation false true = 1
  true_topEdge :
    packet.observation true false + packet.observation true true = 1
  total_contextMass : packet.contextMass false + packet.contextMass true = 2
  cross_context :
    packet.observation false true + packet.observation true false = 1 / 2

/-- Product realizability at one context, including its context-mass scaling. -/
def ProductRealizableAt (packet : TwoContextPacket) (context : Bool) : Prop :=
  ∃ productObservation ∈
      productObservationImage binaryAction binaryObservation,
    packet.observation context =
      packet.contextMass context • productObservation

theorem contextMass_eq_one {packet : TwoContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) (context : Bool) :
    packet.contextMass context = 1 := by
  have hfalse : 1 ≤ packet.contextMass false := by
    rw [← hpacket.false_topEdge]
    exact hpacket.triangle_le_mass false
  have htrue : 1 ≤ packet.contextMass true := by
    rw [← hpacket.true_topEdge]
    exact hpacket.triangle_le_mass true
  cases context <;> linarith [hpacket.total_contextMass]

theorem false_observation_eq {packet : TwoContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) :
    packet.observation false =
      binaryPair (1 - packet.observation false true)
        (packet.observation false true) := by
  funext coordinate
  cases coordinate
  · simp only [binaryPair, Bool.false_eq_true, ↓reduceIte]
    linarith [hpacket.false_topEdge]
  · simp [binaryPair]

theorem true_observation_eq {packet : TwoContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) :
    packet.observation true =
      binaryPair (1 / 2 - packet.observation false true)
        (1 / 2 + packet.observation false true) := by
  funext coordinate
  cases coordinate
  · simp only [binaryPair, Bool.false_eq_true, ↓reduceIte]
    linarith [hpacket.cross_context]
  · simp only [binaryPair, ↓reduceIte]
    linarith [hpacket.cross_context, hpacket.true_topEdge]

theorem selectedParameter_nonneg {packet : TwoContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) :
    0 ≤ packet.observation false true :=
  hpacket.observation_nonneg false true

theorem selectedParameter_le_half {packet : TwoContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) :
    packet.observation false true ≤ 1 / 2 := by
  have hnonneg := hpacket.observation_nonneg true false
  linarith [hpacket.cross_context]

/-- On the feasible fiber, the first context is product-realizable exactly at
the left endpoint of the selected parameter interval. -/
theorem productRealizableAt_false_iff {packet : TwoContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) :
    packet.ProductRealizableAt false ↔
      packet.observation false true = 0 := by
  constructor
  · rintro ⟨productObservation, hproduct, hscale⟩
    have hmass := contextMass_eq_one hpacket false
    have hobservation : packet.observation false = productObservation := by
      simpa [hmass] using hscale
    have hedge : binaryPair (1 - packet.observation false true)
        (packet.observation false true) ∈
        productObservationImage binaryAction binaryObservation := by
      rw [← false_observation_eq hpacket, hobservation]
      exact hproduct
    have hendpoints := productImage_topEdge_only_endpoints (by ring) hedge
    rcases hendpoints with hendpoints | hendpoints
    · exact hendpoints.2
    · linarith [selectedParameter_le_half hpacket]
  · intro hzero
    refine ⟨binaryPair 1 0, binaryPair_one_zero_mem_productImage, ?_⟩
    rw [contextMass_eq_one hpacket false, one_smul]
    rw [false_observation_eq hpacket, hzero]
    norm_num

/-- On the feasible fiber, the second context is product-realizable exactly at
the right endpoint of the selected parameter interval. -/
theorem productRealizableAt_true_iff {packet : TwoContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) :
    packet.ProductRealizableAt true ↔
      packet.observation false true = 1 / 2 := by
  constructor
  · rintro ⟨productObservation, hproduct, hscale⟩
    have hmass := contextMass_eq_one hpacket true
    have hobservation : packet.observation true = productObservation := by
      simpa [hmass] using hscale
    have hedge : binaryPair (1 / 2 - packet.observation false true)
        (1 / 2 + packet.observation false true) ∈
        productObservationImage binaryAction binaryObservation := by
      rw [← true_observation_eq hpacket, hobservation]
      exact hproduct
    have hendpoints := productImage_topEdge_only_endpoints (by ring) hedge
    rcases hendpoints with hendpoints | hendpoints
    · linarith [selectedParameter_nonneg hpacket]
    · linarith [hendpoints.1]
  · intro hhalf
    refine ⟨binaryPair 0 1, binaryPair_zero_one_mem_productImage, ?_⟩
    rw [contextMass_eq_one hpacket true, one_smul]
    rw [true_observation_eq hpacket, hhalf]
    norm_num

/-- The canonical point of the affine fiber with target `u` and selected
parameter `t`. -/
def canonicalPacket (u t : ℝ) : TwoContextPacket where
  target := u
  contextMass := fun _context => 1
  observation := fun context =>
    if context then
      binaryPair (1 / 2 - t) (1 / 2 + t)
    else
      binaryPair (1 - t) t

theorem canonicalPacket_isCorrelatedFeasible {u t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (canonicalPacket u t).IsCorrelatedFeasible := by
  refine
    { target_nonneg := hu0
      target_le_one := hu1
      contextMass_nonneg := ?_
      observation_nonneg := ?_
      triangle_le_mass := ?_
      false_topEdge := ?_
      true_topEdge := ?_
      total_contextMass := ?_
      cross_context := ?_ }
  · intro context
    simp [canonicalPacket]
  · intro context coordinate
    cases context <;> cases coordinate <;>
      simp [canonicalPacket, binaryPair] <;> linarith
  · intro context
    cases context <;> norm_num [canonicalPacket, binaryPair]
  · norm_num [canonicalPacket, binaryPair]
  · norm_num [canonicalPacket, binaryPair]
  · norm_num [canonicalPacket]
  · norm_num [canonicalPacket, binaryPair]

theorem canonicalPacket_productRealizableAt_false (u : ℝ) :
    (canonicalPacket u 0).ProductRealizableAt false := by
  refine ⟨binaryPair 1 0, binaryPair_one_zero_mem_productImage, ?_⟩
  funext coordinate
  cases coordinate <;> norm_num [canonicalPacket, binaryPair]

theorem canonicalPacket_productRealizableAt_true (u : ℝ) :
    (canonicalPacket u (1 / 2)).ProductRealizableAt true := by
  refine ⟨binaryPair 0 1, binaryPair_zero_one_mem_productImage, ?_⟩
  funext coordinate
  cases coordinate <;> norm_num [canonicalPacket, binaryPair]

/-- The correlated target set of the affine system is exactly `[0,1]`. -/
theorem exists_correlatedFeasible_target_iff {u : ℝ} :
    (∃ packet : TwoContextPacket,
      packet.IsCorrelatedFeasible ∧ packet.target = u) ↔
      u ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rintro ⟨packet, hpacket, rfl⟩
    exact ⟨hpacket.target_nonneg, hpacket.target_le_one⟩
  · rintro ⟨hu0, hu1⟩
    exact ⟨canonicalPacket u 0,
      canonicalPacket_isCorrelatedFeasible hu0 hu1 (by norm_num) (by norm_num), rfl⟩

/-- Every correlated-feasible target and every specified context admit some
locally product-realizable feasible packet.  The packet may depend on the
context. -/
theorem every_target_context_has_local_product_packet
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (context : Bool) :
    ∃ packet : TwoContextPacket,
      packet.IsCorrelatedFeasible ∧ packet.target = u ∧
        packet.ProductRealizableAt context := by
  rcases hu with ⟨hu0, hu1⟩
  cases context
  · exact ⟨canonicalPacket u 0,
      canonicalPacket_isCorrelatedFeasible hu0 hu1 (by norm_num) (by norm_num),
      rfl, canonicalPacket_productRealizableAt_false u⟩
  · exact ⟨canonicalPacket u (1 / 2),
      canonicalPacket_isCorrelatedFeasible hu0 hu1 (by norm_num) (by norm_num),
      rfl, canonicalPacket_productRealizableAt_true u⟩

/-- There is no single correlated-feasible packet whose observations are
product-realizable at both contexts. -/
theorem no_jointly_productRealizable_packet :
    ¬ ∃ packet : TwoContextPacket,
      packet.IsCorrelatedFeasible ∧
        ∀ context, packet.ProductRealizableAt context := by
  rintro ⟨packet, hpacket, hproduct⟩
  have hzero := (productRealizableAt_false_iff hpacket).mp (hproduct false)
  have hhalf := (productRealizableAt_true_iff hpacket).mp (hproduct true)
  linarith

end TwoContextPacket
end SelectedFiber
end Correlation
end GameTheory
