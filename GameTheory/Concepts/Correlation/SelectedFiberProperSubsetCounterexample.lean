/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.SelectedFiberBinaryGadget

/-!
# A nonvacuous proper-subset selected-fiber counterexample

Three contexts share the binary nonconvex observation gadget.  On the affine
fiber, their selected coordinates are nonnegative and sum to `1 / 2`.
Consequently every prescribed pair of contexts can simultaneously be made
product-realizable, but all three cannot.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace Correlation
namespace SelectedFiber

open Math Math.PMFProduct

/-- The finite variables in the three-context strengthening. -/
structure ThreeContextPacket where
  target : ℝ
  contextMass : Fin 3 → ℝ
  observation : Fin 3 → Bool → ℝ

namespace ThreeContextPacket

/-- The affine three-context fiber together with membership in each scaled
correlated observation triangle. -/
structure IsCorrelatedFeasible (packet : ThreeContextPacket) : Prop where
  target_nonneg : 0 ≤ packet.target
  target_le_one : packet.target ≤ 1
  contextMass_nonneg : ∀ context, 0 ≤ packet.contextMass context
  observation_nonneg : ∀ context coordinate, 0 ≤ packet.observation context coordinate
  triangle_le_mass : ∀ context,
    packet.observation context false + packet.observation context true ≤
      packet.contextMass context
  topEdge : ∀ context,
    packet.observation context false + packet.observation context true = 1
  total_contextMass : ∑ context, packet.contextMass context = 3
  selected_sum : ∑ context, packet.observation context true = 1 / 2

/-- Product realizability at one of the three contexts, including context-mass
scaling. -/
def ProductRealizableAt (packet : ThreeContextPacket) (context : Fin 3) : Prop :=
  ∃ productObservation ∈
      productObservationImage binaryAction binaryObservation,
    packet.observation context =
      packet.contextMass context • productObservation

theorem contextMass_eq_one {packet : ThreeContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) (context : Fin 3) :
    packet.contextMass context = 1 := by
  have h0 : 1 ≤ packet.contextMass 0 := by
    rw [← hpacket.topEdge 0]
    exact hpacket.triangle_le_mass 0
  have h1 : 1 ≤ packet.contextMass 1 := by
    rw [← hpacket.topEdge 1]
    exact hpacket.triangle_le_mass 1
  have h2 : 1 ≤ packet.contextMass 2 := by
    rw [← hpacket.topEdge 2]
    exact hpacket.triangle_le_mass 2
  have hsum := hpacket.total_contextMass
  rw [Fin.sum_univ_three] at hsum
  have hcontext : context = 0 ∨ context = 1 ∨ context = 2 := by
    fin_cases context <;> simp
  rcases hcontext with rfl | rfl | rfl <;> linarith

theorem observation_eq {packet : ThreeContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) (context : Fin 3) :
    packet.observation context =
      binaryPair (1 - packet.observation context true)
        (packet.observation context true) := by
  funext coordinate
  cases coordinate
  · simp only [binaryPair, Bool.false_eq_true, ↓reduceIte]
    linarith [hpacket.topEdge context]
  · simp [binaryPair]

theorem selectedCoordinate_nonneg {packet : ThreeContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) (context : Fin 3) :
    0 ≤ packet.observation context true :=
  hpacket.observation_nonneg context true

theorem selectedCoordinate_le_half {packet : ThreeContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) (context : Fin 3) :
    packet.observation context true ≤ 1 / 2 := by
  have h0 := selectedCoordinate_nonneg hpacket 0
  have h1 := selectedCoordinate_nonneg hpacket 1
  have h2 := selectedCoordinate_nonneg hpacket 2
  have hsum := hpacket.selected_sum
  rw [Fin.sum_univ_three] at hsum
  have hcontext : context = 0 ∨ context = 1 ∨ context = 2 := by
    fin_cases context <;> simp
  rcases hcontext with rfl | rfl | rfl <;> linarith

/-- At any context, product realizability is equivalent to vanishing of that
context's selected coordinate. -/
theorem productRealizableAt_iff {packet : ThreeContextPacket}
    (hpacket : packet.IsCorrelatedFeasible) (context : Fin 3) :
    packet.ProductRealizableAt context ↔
      packet.observation context true = 0 := by
  constructor
  · rintro ⟨productObservation, hproduct, hscale⟩
    have hmass := contextMass_eq_one hpacket context
    have hobservation : packet.observation context = productObservation := by
      simpa [hmass] using hscale
    have hedge : binaryPair (1 - packet.observation context true)
        (packet.observation context true) ∈
        productObservationImage binaryAction binaryObservation := by
      rw [← observation_eq hpacket context, hobservation]
      exact hproduct
    have hendpoints := productImage_topEdge_only_endpoints (by ring) hedge
    rcases hendpoints with hendpoints | hendpoints
    · exact hendpoints.2
    · linarith [selectedCoordinate_le_half hpacket context]
  · intro hzero
    refine ⟨binaryPair 1 0, binaryPair_one_zero_mem_productImage, ?_⟩
    rw [contextMass_eq_one hpacket context, one_smul]
    rw [observation_eq hpacket context, hzero]
    norm_num

/-- Put the entire selected mass on the one omitted context. -/
def properSubsetPacket (u : ℝ) (omitted : Fin 3) : ThreeContextPacket where
  target := u
  contextMass := fun _context => 1
  observation := fun context =>
    let selected : ℝ := if context = omitted then 1 / 2 else 0
    binaryPair (1 - selected) selected

theorem properSubsetPacket_isCorrelatedFeasible {u : ℝ} (omitted : Fin 3)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (properSubsetPacket u omitted).IsCorrelatedFeasible := by
  refine
    { target_nonneg := hu0
      target_le_one := hu1
      contextMass_nonneg := ?_
      observation_nonneg := ?_
      triangle_le_mass := ?_
      topEdge := ?_
      total_contextMass := ?_
      selected_sum := ?_ }
  · intro context
    simp [properSubsetPacket]
  · intro context coordinate
    by_cases hcontext : context = omitted <;> cases coordinate <;>
      norm_num [properSubsetPacket, binaryPair, hcontext]
  · intro context
    by_cases hcontext : context = omitted <;>
      norm_num [properSubsetPacket, binaryPair, hcontext]
  · intro context
    by_cases hcontext : context = omitted <;>
      norm_num [properSubsetPacket, binaryPair, hcontext]
  · norm_num [properSubsetPacket, Fin.sum_univ_three]
  · fin_cases omitted <;>
      norm_num [properSubsetPacket, binaryPair, Fin.sum_univ_three]

theorem properSubsetPacket_productRealizableAt {u : ℝ}
    {omitted context : Fin 3} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hcontext : context ≠ omitted) :
    (properSubsetPacket u omitted).ProductRealizableAt context := by
  have hpacket := properSubsetPacket_isCorrelatedFeasible omitted hu0 hu1
  rw [productRealizableAt_iff hpacket context]
  simp [properSubsetPacket, binaryPair, hcontext]

/-- At every target in `[0,1]`, every prescribed two-element subset of the
three contexts has one feasible packet that is jointly product-realizable on
that whole subset. -/
theorem every_target_twoContextSubset_has_joint_product_packet
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (contexts : Finset (Fin 3)) (hcontexts : contexts.card = 2) :
    ∃ packet : ThreeContextPacket,
      packet.IsCorrelatedFeasible ∧ packet.target = u ∧
        ∀ context ∈ contexts, packet.ProductRealizableAt context := by
  rcases hu with ⟨hu0, hu1⟩
  have hmissing : ∃ omitted : Fin 3, omitted ∉ contexts := by
    by_contra hall
    have hall' : ∀ omitted : Fin 3, omitted ∈ contexts := by
      intro omitted
      by_contra homitted
      exact hall ⟨omitted, homitted⟩
    have huniv : contexts = Finset.univ := Finset.eq_univ_iff_forall.mpr hall'
    rw [huniv] at hcontexts
    norm_num at hcontexts
  obtain ⟨omitted, homitted⟩ := hmissing
  refine ⟨properSubsetPacket u omitted,
    properSubsetPacket_isCorrelatedFeasible omitted hu0 hu1, rfl, ?_⟩
  intro context hcontext
  apply properSubsetPacket_productRealizableAt hu0 hu1
  intro heq
  subst context
  exact homitted hcontext

/-- No feasible packet is product-realizable at all three contexts. -/
theorem no_jointly_productRealizable_packet :
    ¬ ∃ packet : ThreeContextPacket,
      packet.IsCorrelatedFeasible ∧
        ∀ context, packet.ProductRealizableAt context := by
  rintro ⟨packet, hpacket, hproduct⟩
  have h0 := (productRealizableAt_iff hpacket 0).mp (hproduct 0)
  have h1 := (productRealizableAt_iff hpacket 1).mp (hproduct 1)
  have h2 := (productRealizableAt_iff hpacket 2).mp (hproduct 2)
  have hsum := hpacket.selected_sum
  rw [Fin.sum_univ_three] at hsum
  linarith

end ThreeContextPacket
end SelectedFiber
end Correlation
end GameTheory
