/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import GameTheory.Concepts.Welfare.FolkTheorem.Discounting

/-!
# Geometry of Feasible and Individually Rational Payoffs

Topological properties of finite stage-game payoff sets and compact
reservation-margin approximations to the strictly individually rational
feasible set.
-/

noncomputable section

namespace GameTheory
namespace KernelGame

variable {ι : Type}

theorem finite_purePayoffSet (G : KernelGame ι) [Finite (Profile G)] :
    G.purePayoffSet.Finite := by
  exact Set.finite_range G.payoffVector

theorem nonempty_purePayoffSet (G : KernelGame ι) [Nonempty (Profile G)] :
    G.purePayoffSet.Nonempty := by
  obtain ⟨σ⟩ := ‹Nonempty (Profile G)›
  exact ⟨G.payoffVector σ, ⟨σ, rfl⟩⟩

theorem nonempty_feasibleSet (G : KernelGame ι) [Nonempty (Profile G)] :
    G.feasibleSet.Nonempty := by
  simpa [feasibleSet] using
    (Set.Nonempty.convexHull (𝕜 := ℝ) (G.nonempty_purePayoffSet))

theorem convex_feasibleSet (G : KernelGame ι) :
    Convex ℝ G.feasibleSet := by
  exact convex_convexHull ℝ G.purePayoffSet

/-- The affine hull of feasible payoffs is already determined by pure stage
payoffs. -/
theorem affineSpan_feasibleSet (G : KernelGame ι) :
    affineSpan ℝ G.feasibleSet = affineSpan ℝ G.purePayoffSet := by
  exact affineSpan_convexHull G.purePayoffSet

/-- The feasible payoff set is full dimensional in the ambient payoff space. -/
def HasFullDimensionalFeasibleSet (G : KernelGame ι) : Prop :=
  affineSpan ℝ G.feasibleSet = ⊤

/-- For finitely many players, full dimensionality is equivalent to nonempty
ambient interior of the feasible payoff set. -/
theorem hasFullDimensionalFeasibleSet_iff_interior_nonempty
    (G : KernelGame ι) [Finite ι] :
    G.HasFullDimensionalFeasibleSet ↔ (interior G.feasibleSet).Nonempty := by
  letI := Fintype.ofFinite ι
  exact G.convex_feasibleSet.interior_nonempty_iff_affineSpan_eq_top.symm

/-- The relative, or intrinsic, interior of a finite-dimensional feasible set
is nonempty exactly when the feasible set itself is nonempty; no
full-dimensionality assumption is needed. -/
theorem intrinsicInterior_feasibleSet_nonempty_iff
    (G : KernelGame ι) [Finite ι] :
    (intrinsicInterior ℝ G.feasibleSet).Nonempty ↔ G.feasibleSet.Nonempty := by
  letI := Fintype.ofFinite ι
  exact intrinsicInterior_nonempty G.convex_feasibleSet

theorem isCompact_feasibleSet (G : KernelGame ι) [Finite (Profile G)] :
    IsCompact G.feasibleSet := by
  simpa [feasibleSet] using (G.finite_purePayoffSet.isCompact_convexHull ℝ)

theorem isClosed_feasibleSet (G : KernelGame ι) [Finite (Profile G)] :
    IsClosed G.feasibleSet := by
  simpa [feasibleSet] using (G.finite_purePayoffSet.isClosed_convexHull ℝ)

theorem convex_weakReservationSet (r : Payoff ι) :
    Convex ℝ (weakReservationSet r) := by
  rw [weakReservationSet]
  intro x hx y hy a b ha hb hab i
  calc
    r i = a * r i + b * r i := by rw [← add_mul, hab, one_mul]
    _ ≤ a * x i + b * y i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = (a • x + b • y) i := by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem convex_strictReservationSet (r : Payoff ι) :
    Convex ℝ (strictReservationSet r) := by
  rw [strictReservationSet]
  intro x hx y hy a b ha hb hab i
  have hxpos : 0 < x i - r i := sub_pos.mpr (hx i)
  have hypos : 0 < y i - r i := sub_pos.mpr (hy i)
  have hpos : 0 < a * (x i - r i) + b * (y i - r i) := by
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by simpa using hab
      simpa [hb1] using hypos
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hapos hxpos) (mul_nonneg hb hypos.le)
  have hrewrite :
      a * (x i - r i) + b * (y i - r i) = a * x i + b * y i - r i := by
    calc
      a * (x i - r i) + b * (y i - r i) =
          a * x i + b * y i - (a + b) * r i := by ring
      _ = a * x i + b * y i - r i := by rw [hab, one_mul]
  have hlt : r i < a * x i + b * y i := by
    linarith
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hlt

theorem isClosed_weakReservationSet (r : Payoff ι) :
    IsClosed (weakReservationSet r) := by
  have hclosed : IsClosed (⋂ i, {v : Payoff ι | r i ≤ v i}) := by
    refine isClosed_iInter ?_
    intro i
    change IsClosed ((fun v : Payoff ι => v i) ⁻¹' Set.Ici (r i))
    exact isClosed_Ici.preimage (continuous_apply i : Continuous fun v : Payoff ι => v i)
  have hset : weakReservationSet r = ⋂ i, {v : Payoff ι | r i ≤ v i} := by
    ext v
    simp [weakReservationSet]
  rw [hset]
  exact hclosed

theorem convex_individuallyRationalPayoffSet (G : KernelGame ι) (r : Payoff ι) :
    Convex ℝ (G.individuallyRationalPayoffSet r) :=
  (G.convex_feasibleSet).inter (convex_weakReservationSet r)

theorem convex_strictIndividuallyRationalPayoffSet (G : KernelGame ι) (r : Payoff ι) :
    Convex ℝ (G.strictIndividuallyRationalPayoffSet r) :=
  (G.convex_feasibleSet).inter (convex_strictReservationSet r)

/-- The strictly individually rational feasible region has nonempty relative
interior exactly when it is nonempty, even if feasible payoffs lie in a proper
affine subspace. -/
theorem intrinsicInterior_strictIndividuallyRationalPayoffSet_nonempty_iff
    (G : KernelGame ι) [Finite ι] (r : Payoff ι) :
    (intrinsicInterior ℝ (G.strictIndividuallyRationalPayoffSet r)).Nonempty ↔
      (G.strictIndividuallyRationalPayoffSet r).Nonempty := by
  letI := Fintype.ofFinite ι
  exact intrinsicInterior_nonempty
    (G.convex_strictIndividuallyRationalPayoffSet r)

theorem isClosed_individuallyRationalPayoffSet (G : KernelGame ι)
    [Finite (Profile G)] (r : Payoff ι) :
    IsClosed (G.individuallyRationalPayoffSet r) :=
  (G.isClosed_feasibleSet).inter (isClosed_weakReservationSet r)

theorem isCompact_individuallyRationalPayoffSet (G : KernelGame ι)
    [Finite (Profile G)] (r : Payoff ι) :
    IsCompact (G.individuallyRationalPayoffSet r) :=
  (G.isCompact_feasibleSet).inter_right (isClosed_weakReservationSet r)

/-- Payoffs weakly above a reservation vector by a fixed common margin. -/
def reservationMarginSet (r : Payoff ι) (margin : ℝ) : Set (Payoff ι) :=
  {v | ∀ i, r i + margin ≤ v i}

@[simp]
theorem reservationMarginSet_zero (r : Payoff ι) :
    reservationMarginSet r 0 = weakReservationSet r := by
  ext v
  simp [reservationMarginSet, weakReservationSet]

/-- The compact inner approximation obtained by imposing a common
reservation margin inside the feasible set. -/
def individuallyRationalInnerApproximation
    (G : KernelGame ι) (r : Payoff ι) (margin : ℝ) : Set (Payoff ι) :=
  G.feasibleSet ∩ reservationMarginSet r margin

@[simp]
theorem individuallyRationalInnerApproximation_zero
    (G : KernelGame ι) (r : Payoff ι) :
    G.individuallyRationalInnerApproximation r 0 =
      G.individuallyRationalPayoffSet r := by
  simp [individuallyRationalInnerApproximation, individuallyRationalPayoffSet]

theorem convex_reservationMarginSet (r : Payoff ι) (margin : ℝ) :
    Convex ℝ (reservationMarginSet r margin) := by
  change Convex ℝ (weakReservationSet (fun i => r i + margin))
  exact convex_weakReservationSet _

theorem isClosed_reservationMarginSet (r : Payoff ι) (margin : ℝ) :
    IsClosed (reservationMarginSet r margin) := by
  change IsClosed (weakReservationSet (fun i => r i + margin))
  exact isClosed_weakReservationSet _

theorem convex_individuallyRationalInnerApproximation
    (G : KernelGame ι) (r : Payoff ι) (margin : ℝ) :
    Convex ℝ (G.individuallyRationalInnerApproximation r margin) :=
  G.convex_feasibleSet.inter (convex_reservationMarginSet r margin)

theorem isCompact_individuallyRationalInnerApproximation
    (G : KernelGame ι) [Finite (Profile G)] (r : Payoff ι) (margin : ℝ) :
    IsCompact (G.individuallyRationalInnerApproximation r margin) :=
  G.isCompact_feasibleSet.inter_right (isClosed_reservationMarginSet r margin)

/-- Increasing the required reservation margin shrinks the approximation. -/
theorem individuallyRationalInnerApproximation_anti
    (G : KernelGame ι) (r : Payoff ι) {small large : ℝ}
    (hmargin : small ≤ large) :
    G.individuallyRationalInnerApproximation r large ⊆
      G.individuallyRationalInnerApproximation r small := by
  rintro v ⟨hv, hir⟩
  refine ⟨hv, fun i => ?_⟩
  linarith [hmargin, hir i]

/-- A positive-margin approximation lies in the strictly individually
rational feasible set. -/
theorem individuallyRationalInnerApproximation_subset_strict
    (G : KernelGame ι) (r : Payoff ι) {margin : ℝ} (hmargin : 0 < margin) :
    G.individuallyRationalInnerApproximation r margin ⊆
      G.strictIndividuallyRationalPayoffSet r := by
  rintro v ⟨hv, hir⟩
  refine ⟨hv, fun i => ?_⟩
  exact (lt_add_of_pos_right (r i) hmargin).trans_le (hir i)

/-- Over finitely many players, the positive-margin inner approximations
exhaust the strictly individually rational feasible set. -/
theorem strictIndividuallyRationalPayoffSet_eq_iUnion_innerApproximations
    (G : KernelGame ι) [Finite ι] (r : Payoff ι) :
    G.strictIndividuallyRationalPayoffSet r =
      ⋃ margin : {x : ℝ // 0 < x},
        G.individuallyRationalInnerApproximation r margin := by
  ext v
  constructor
  · intro hv
    obtain ⟨margin, hmargin, hir⟩ :=
      G.exists_pos_margin_of_mem_strictIndividuallyRationalPayoffSet hv
    exact Set.mem_iUnion.2 ⟨⟨margin, hmargin⟩, hv.1, hir⟩
  · intro hv
    obtain ⟨margin, hv⟩ := Set.mem_iUnion.1 hv
    exact G.individuallyRationalInnerApproximation_subset_strict r margin.2 hv

/-- Nonemptiness of the strict feasible region is equivalent to nonemptiness
of one positive-margin compact inner approximation. -/
theorem nonempty_strictIndividuallyRationalPayoffSet_iff_exists_innerApproximation
    (G : KernelGame ι) [Finite ι] (r : Payoff ι) :
    (G.strictIndividuallyRationalPayoffSet r).Nonempty ↔
      ∃ margin : ℝ, 0 < margin ∧
        (G.individuallyRationalInnerApproximation r margin).Nonempty := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨margin, hmargin, hir⟩ :=
      G.exists_pos_margin_of_mem_strictIndividuallyRationalPayoffSet hv
    exact ⟨margin, hmargin, v, hv.1, hir⟩
  · rintro ⟨margin, hmargin, v, hv⟩
    exact ⟨v, G.individuallyRationalInnerApproximation_subset_strict
      r hmargin hv⟩

end KernelGame
end GameTheory
