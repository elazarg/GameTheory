/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Bellman.Germ
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.Obstruction

/-!
# From analytic Bellman germs to the finite Fink obstruction hierarchy

An `AnalyticBellmanGerm` stores polynomial Bellman solutions rather than
points of Fink's compact domain.  This file gives every positive point of the
germ a canonical finite payoff bound and encodes its decoded profile and
value as a Fink-domain point.

The resulting point is an actual discounted stationary Bellman equilibrium.
For any proposed pair of hierarchy coefficients `H` and `K`, the existing
finite-dimensional alternative then returns either a supported harmonic
adjustment or a normalized signed obstruction flow.  In the obstruction
branch, one concrete supported coordinate is exposed as either an observable
transition test or a positive stage coordinate.

This is deliberately a pointwise bridge.  It does not select the hierarchy
coefficients, make the response coherent between different germ parameters,
or construct the global public-response invariant.
-/

noncomputable section

open Set

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- A finite bound containing every stage-payoff coordinate and every value
coordinate at one point of an analytic Bellman germ. -/
def finkBoundAt (germ : G.AnalyticBellmanGerm) (t : ℝ) : ℝ :=
  (∑ p : G.State × G.JointAct × ι,
      |G.stagePayoff p.1 p.2.1 p.2.2|) +
    ∑ p : G.State × ι,
      |G.bellmanDecodeValue (germ.assignment t) p.1 p.2|

private theorem abs_le_sum_abs
    {α : Type} [Fintype α] (f : α → ℝ) (a : α) :
    |f a| ≤ ∑ x, |f x| := by
  exact Finset.single_le_sum
    (fun x _ => abs_nonneg (f x)) (Finset.mem_univ a)

omit [DecidableEq G.State] in
theorem stagePayoff_abs_le_finkBoundAt
    (germ : G.AnalyticBellmanGerm) (t : ℝ)
    (s : G.State) (a : G.JointAct) (who : ι) :
    |G.stagePayoff s a who| ≤ germ.finkBoundAt t := by
  calc
    |G.stagePayoff s a who| ≤
        ∑ p : G.State × G.JointAct × ι,
          |G.stagePayoff p.1 p.2.1 p.2.2| :=
      abs_le_sum_abs
        (fun p : G.State × G.JointAct × ι =>
          G.stagePayoff p.1 p.2.1 p.2.2) (s, a, who)
    _ ≤ germ.finkBoundAt t := by
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)

omit [DecidableEq G.State] in
theorem bellmanDecodeValue_abs_le_finkBoundAt
    (germ : G.AnalyticBellmanGerm) (t : ℝ)
    (s : G.State) (who : ι) :
    |G.bellmanDecodeValue (germ.assignment t) s who| ≤
      germ.finkBoundAt t := by
  calc
    |G.bellmanDecodeValue (germ.assignment t) s who| ≤
        ∑ p : G.State × ι,
          |G.bellmanDecodeValue (germ.assignment t) p.1 p.2| :=
      abs_le_sum_abs
        (fun p : G.State × ι =>
          G.bellmanDecodeValue (germ.assignment t) p.1 p.2) (s, who)
    _ ≤ germ.finkBoundAt t := by
      exact le_add_of_nonneg_left
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The canonical Fink-domain point represented by a positive point of an
analytic Bellman germ. -/
def finkPointAt (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    G.finkDomain (germ.finkBoundAt t) :=
  G.finkPointOfProfileValue
    (G.bellmanDecodeProfile (germ.solution t ht))
    (G.bellmanDecodeValue (germ.assignment t))
    (germ.bellmanDecodeValue_abs_le_finkBoundAt t)

omit [DecidableEq G.State] in
@[simp]
theorem finkProfile_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    G.finkProfile (germ.finkPointAt ht) =
      G.bellmanDecodeProfile (germ.solution t ht) := by
  exact G.finkProfile_finkPointOfProfileValue _ _ _

omit [DecidableEq G.State] in
@[simp]
theorem finkValue_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    G.finkValue (germ.finkPointAt ht) =
      G.bellmanDecodeValue (germ.assignment t) := by
  exact G.finkValue_finkPointOfProfileValue _ _ _

omit [DecidableEq G.State] in
/-- The canonical Fink point at a positive germ parameter decodes to the
discounted stationary Bellman equilibrium carried by the germ. -/
theorem isDiscountedStationaryBellmanEq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    G.IsDiscountedStationaryBellmanEq
      (1 - t ^ germ.ramification)
      (G.finkProfile (germ.finkPointAt ht))
      (G.finkValue (germ.finkPointAt ht)) := by
  simpa using germ.isDiscountedStationaryBellmanEq ht

omit [DecidableEq G.State] in
/-- Whenever the decoded discount lies in `[0, 1]`, the canonical encoding
of a positive germ point is literally a fixed point of Fink's map. -/
theorem finkMap_finkPointAt_eq_self
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hdiscount_nonneg : 0 ≤ 1 - t ^ germ.ramification)
    (hdiscount_le_one : 1 - t ^ germ.ramification ≤ 1) :
    G.finkMap
        (1 - t ^ germ.ramification)
        (germ.finkBoundAt t)
        hdiscount_nonneg hdiscount_le_one
        (germ.stagePayoff_abs_le_finkBoundAt t)
        (germ.finkPointAt ht) =
      germ.finkPointAt ht := by
  simpa [finkPointAt] using
    G.finkMap_finkPointOfProfileValue_eq_self
      (1 - t ^ germ.ramification)
      (germ.finkBoundAt t)
      hdiscount_nonneg hdiscount_le_one
      (germ.stagePayoff_abs_le_finkBoundAt t)
      (G.bellmanDecodeProfile (germ.solution t ht))
      (G.bellmanDecodeValue (germ.assignment t))
      (germ.bellmanDecodeValue_abs_le_finkBoundAt t)
      (germ.isDiscountedStationaryBellmanEq ht)

omit [DecidableEq G.State] in
/-- Every positive germ parameter below one automatically gives an admissible
discount and hence a literal Fink fixed point. -/
theorem finkMap_finkPointAt_eq_self_of_lt_one
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (ht_one : t < 1) :
    G.finkMap
        (1 - t ^ germ.ramification)
        (germ.finkBoundAt t)
        (sub_nonneg.mpr
          (pow_le_one₀ ht.1.le ht_one.le))
        (sub_le_self 1
          (pow_nonneg ht.1.le germ.ramification))
        (germ.stagePayoff_abs_le_finkBoundAt t)
        (germ.finkPointAt ht) =
      germ.finkPointAt ht :=
  germ.finkMap_finkPointAt_eq_self ht
    (sub_nonneg.mpr (pow_le_one₀ ht.1.le ht_one.le))
    (sub_le_self 1 (pow_nonneg ht.1.le germ.ramification))

omit [DecidableEq G.State] in
/-- Pointwise entry from an analytic Bellman germ into the normalized Fink
obstruction hierarchy.

The hierarchy data `H` and `K` remain explicit.  Selecting them coherently
from successive nonzero coefficients of the analytic germ is part of the
global invariant, not a consequence of the local finite-dimensional
alternative. -/
theorem harmonicAdjustment_or_normalizedObstructionFlowAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A (germ.finkPointAt ht) = 0 ∧
        ∀ s who (d : G.Act who),
          G.finkProfile (germ.finkPointAt ht) s who d ≠ 0 →
            G.finkContinuationGain A (germ.finkPointAt ht) s who d =
              G.finkStageGain (germ.finkPointAt ht) s who d +
                G.finkContinuationGain (H - K)
                  (germ.finkPointAt ht) s who d) ∨
      Nonempty
        (G.NormalizedFinkSupportTangentObstructionFlow
          (germ.finkPointAt ht) H K) := by
  exact G.exists_harmonicAdjustment_or_normalizedObstructionFlow
    (germ.finkPointAt ht) H K

omit [DecidableEq G.State] in
/-- Operational refinement of the pointwise hierarchy branch.

If there is no supported harmonic adjustment, the returned normalized flow
exposes either a transition-visible supported coordinate and a destination
state witnessing its probability change, or a transition-invisible
supported coordinate with positive signed stage charge. -/
theorem harmonicAdjustment_or_obstructionResponseAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A (germ.finkPointAt ht) = 0 ∧
        ∀ s who (d : G.Act who),
          G.finkProfile (germ.finkPointAt ht) s who d ≠ 0 →
            G.finkContinuationGain A (germ.finkPointAt ht) s who d =
              G.finkStageGain (germ.finkPointAt ht) s who d +
                G.finkContinuationGain (H - K)
                  (germ.finkPointAt ht) s who d) ∨
      ∃ F : G.NormalizedFinkSupportTangentObstructionFlow
          (germ.finkPointAt ht) H K,
        (∃ s, ∃ who, ∃ d : G.Act who, ∃ destination,
          G.finkProfile (germ.finkPointAt ht) s who d ≠ 0 ∧
            0 < F.actionWeight s who d *
              (G.finkStageGain (germ.finkPointAt ht) s who d +
                G.finkContinuationGain (H - K)
                  (germ.finkPointAt ht) s who d) ∧
            (G.finkPureDeviationStateKernel
                (germ.finkPointAt ht) s who d destination).toReal ≠
              (G.finkStateKernel
                (germ.finkPointAt ht) s destination).toReal) ∨
          ∃ s, ∃ who, ∃ d : G.Act who,
            G.finkProfile (germ.finkPointAt ht) s who d ≠ 0 ∧
              G.finkPureDeviationStateKernel
                  (germ.finkPointAt ht) s who d =
                G.finkStateKernel (germ.finkPointAt ht) s ∧
              0 < F.actionWeight s who d *
                G.finkStageGain (germ.finkPointAt ht) s who d := by
  rcases germ.harmonicAdjustment_or_normalizedObstructionFlowAt ht H K with
    hA | hF
  · exact Or.inl hA
  · obtain ⟨F⟩ := hF
    exact Or.inr
      ⟨F, F.exists_positive_transition_test_or_positive_stage_coordinate⟩

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
