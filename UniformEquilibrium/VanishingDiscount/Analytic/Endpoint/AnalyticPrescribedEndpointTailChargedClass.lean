/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticFinkBaselineChargedClass
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticFinkTailReachableSupport
import Math.Probability.AnalyticRestrictedSourceChargeAlternative

/-!
# Tail-reachable charged classes for prescribed endpoint transport

The prescribed Fink calendar eventually has one fixed tail-reachable state
subtype.  Restricting the analytic baseline occupation columns to that
subtype prevents a charged circulation from hiding in a component unrelated
to the actual tail law.

This file supplies the positive branch of that restriction.  At every
sufficiently small valid parameter:

* the restricted raw columns are realized by genuine Fink transition rows;
* every positive row destination remains in the fixed tail subtype;
* every restricted source is support-reachable from some state carrying
  positive mass under the actual law at the tail boundary.

Consequently, an analytic positive circulation on the restricted columns
produces a positive aggregate-charge communicating class whose
representative is support-reachable from some positive-mass tail state.

The result is graph-theoretic.  It does not turn the path into a uniformly
positive calendar event, construct a legal recursive child, preserve a
whole payoff-vector target, or prove rank descent.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.OnlineLearning Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The actual state law at the complete epoch boundary from which the fixed
tail support is generated. -/
def PrescribedFinkTailReachableSupport.tailLaw
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) : PMF G.State :=
  germ.scheduledFinkStateLaw
    startEpoch valid entry tail.supportStart

/-- The fixed finite source type used by the tail-restricted occupation
alternative. -/
abbrev PrescribedFinkTailState
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) :=
  tail.states

noncomputable instance prescribedFinkTailStateFintype
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) :
    Fintype (PrescribedFinkTailState tail) :=
  Fintype.ofFinite _

/-- Restrict only the source index of the raw baseline occupation column.
Destinations remain in the ambient state space so that flow balance retains
all escape coordinates. -/
def tailRestrictedBaselineOccupationColumn
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) :
    ℝ → PrescribedFinkTailState tail → G.State → ℝ :=
  fun t source destination =>
    germ.rawBaselineOccupationColumn t source.1 destination

/-- Restrict one orientation of endpoint transport to the fixed tail source
subtype. -/
def tailRestrictedEndpointTransportCharge
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid)
    (who : ι) (forward : Bool) :
    ℝ → PrescribedFinkTailState tail → ℝ :=
  fun t source =>
    germ.endpointTransportCharge who entry forward t source.1

/-- Restricted baseline occupation coordinates remain analytic. -/
theorem analytic_tailRestrictedBaselineOccupationColumn
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) :
    ∀ source destination,
      AnalyticAt ℝ
        (fun t =>
          tailRestrictedBaselineOccupationColumn
            tail t source destination) 0 := by
  intro source destination
  exact
    germ.analytic_rawBaselineOccupationColumn
      source.1 destination

omit [DecidableEq G.State] in
/-- Restricted endpoint transport remains a constant analytic charge. -/
theorem analytic_tailRestrictedEndpointTransportCharge
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid)
    (who : ι) (forward : Bool) :
    ∀ source,
      AnalyticAt ℝ
        (fun t =>
          tailRestrictedEndpointTransportCharge
            tail who forward t source) 0 := by
  intro source
  exact germ.analytic_endpointTransportCharge
    who entry forward source.1

omit [DecidableEq G.State] in
/-- A raw punctured-support path inside the fixed tail subtype is an
available-support path for every sufficiently small semantic Fink kernel.
-/
private theorem availableReachable_of_rawReachable
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (support :
      ∀ source destination,
        0 < germ.rawStateKernelCurve t source destination ↔
          analyticPuncturedCoordinateSupport
            germ.rawStateKernelCurve source destination)
    {source destination : G.State}
    (source_mem : source ∈ tail.states)
    (reachable :
      Relation.ReflTransGen
        (analyticPuncturedCoordinateSupport
          germ.rawStateKernelCurve)
        source destination) :
    AvailableReachable
      (fun state : PrescribedFinkTailState tail =>
        G.finkStateKernel (germ.finkPointAt ht) state.1)
      (fun state : PrescribedFinkTailState tail => state.1)
      source destination := by
  let kernel :
      PrescribedFinkTailState tail → PMF G.State :=
    fun state =>
      G.finkStateKernel (germ.finkPointAt ht) state.1
  let sourceMap :
      PrescribedFinkTailState tail → G.State :=
    fun state => state.1
  have lift :
      ∀ {current next : G.State},
        current ∈ tail.states →
          Relation.ReflTransGen
              (analyticPuncturedCoordinateSupport
                germ.rawStateKernelCurve)
              current next →
            next ∈ tail.states ∧
              AvailableReachable
                kernel sourceMap current next := by
    intro current next current_mem path
    induction path with
    | refl =>
        exact ⟨current_mem, Relation.ReflTransGen.refl⟩
    | @tail middle destination hprefix step inductionHypothesis =>
        obtain ⟨middle_mem, prefix_available⟩ :=
          inductionHypothesis
        have next_mem : destination ∈ tail.states :=
          tail.states_closed middle_mem step
        have coordinate_pos :
            0 <
              (kernel
                ⟨middle, middle_mem⟩ destination).toReal := by
          change
            0 <
              (G.finkStateKernel
                (germ.finkPointAt ht) middle destination).toReal
          rw [← germ.rawStateKernelCurve_eq_finkStateKernel ht]
          exact (support middle destination).mpr step
        have kernel_ne :
            kernel ⟨middle, middle_mem⟩ destination ≠ 0 := by
          intro zero
          rw [zero] at coordinate_pos
          norm_num at coordinate_pos
        exact
          ⟨next_mem,
            prefix_available.tail
              ⟨⟨middle, middle_mem⟩, rfl, kernel_ne⟩⟩
  exact (lift source_mem reachable).2

/-- On a common punctured neighborhood, the tail-restricted raw columns
have genuine Fink semantics, are closed in the tail subtype, and every
source is support-reachable from some positive-mass tail state. -/
theorem eventually_tailRestrictedSemanticKernel
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) :
    ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
      Nonempty
        (LawSupportedRestrictedSemanticKernelAt
          (tailRestrictedBaselineOccupationColumn tail)
          (fun state : PrescribedFinkTailState tail => state.1)
          (fun parameter =>
            parameter ∈ Ioo (0 : ℝ) germ.radius)
          tail.tailLaw t) := by
  filter_upwards
    [Ioo_mem_nhdsGT germ.radius_pos,
      germ.eventually_rawStateKernelCurve_pos_iff_puncturedSupport]
      with t ht support
  let kernel :
      PrescribedFinkTailState tail → PMF G.State :=
    fun state =>
      G.finkStateKernel (germ.finkPointAt ht) state.1
  refine ⟨{
    valid := ht
    kernel := kernel
    realizes := ?_
    source_closed := ?_
    source_reachable_from_law := ?_
  }⟩
  · intro source destination
    change
      germ.rawBaselineOccupationColumn
          t source.1 destination =
        (kernel source destination).toReal -
          if destination = source.1 then 1 else 0
    unfold rawBaselineOccupationColumn kernel
    rw [germ.rawStateKernelCurve_eq_finkStateKernel ht]
  · intro source destination destination_ne
    have coordinate_pos :
        0 < germ.rawStateKernelCurve
          t source.1 destination := by
      rw [germ.rawStateKernelCurve_eq_finkStateKernel ht]
      exact ENNReal.toReal_pos destination_ne
        (PMF.apply_ne_top (kernel source) destination)
    have edge :
        analyticPuncturedCoordinateSupport
          germ.rawStateKernelCurve source.1 destination :=
      (support source.1 destination).mp coordinate_pos
    exact
      ⟨⟨destination, tail.states_closed source.2 edge⟩, rfl⟩
  · intro source
    obtain ⟨seed, seed_ne, reachable⟩ := source.2
    exact
      ⟨seed, seed_ne,
        availableReachable_of_rawReachable
          tail ht support
          (mem_analyticPuncturedTailSupport_of_initial_ne_zero
            germ.rawStateKernelCurve tail.tailLaw seed_ne)
          reachable⟩

/-- A positive analytic circulation on the tail-restricted endpoint charge
produces a positive aggregate-charge class reachable in support from some
positive-mass state of the actual tail law. -/
theorem exists_tailReachableEndpointTransportChargedClass
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid)
    (who : ι) (forward : Bool)
    (circulation :
      AnalyticPositiveChargedCirculation
        (tailRestrictedBaselineOccupationColumn tail)
        (tailRestrictedEndpointTransportCharge
          tail who forward)) :
    Nonempty
      (PuncturedLawSupportedRestrictedPositiveChargedClass
        (tailRestrictedBaselineOccupationColumn tail)
        (tailRestrictedEndpointTransportCharge tail who forward)
        (fun state : PrescribedFinkTailState tail => state.1)
        (fun parameter =>
          parameter ∈ Ioo (0 : ℝ) germ.radius)
        tail.tailLaw) := by
  exact
    exists_puncturedLawSupportedRestrictedPositiveChargedClass
      (tailRestrictedBaselineOccupationColumn tail)
      (tailRestrictedEndpointTransportCharge tail who forward)
      (fun state : PrescribedFinkTailState tail => state.1)
      (fun parameter =>
        parameter ∈ Ioo (0 : ℝ) germ.radius)
      tail.tailLaw circulation
      (eventually_tailRestrictedSemanticKernel tail)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
