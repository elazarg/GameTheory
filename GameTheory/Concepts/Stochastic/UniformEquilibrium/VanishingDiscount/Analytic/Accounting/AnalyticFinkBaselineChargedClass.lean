/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticBellmanHierarchy
import Math.Probability.AnalyticChargedOccupationFlow
import Math.Probability.PositiveChargedCirculationClass

/-!
# A punctured charged class from an analytic baseline circulation

An analytic positive charged circulation on the state-indexed baseline
occupation columns can be evaluated at one sufficiently small positive
parameter.  At that parameter the raw analytic columns are the actual
occupation columns of the decoded Fink state kernel.  Normalization and the
finite communicating-class decomposition then produce a class with positive
aggregate charge.

The representative supplied by `PositiveChargedCirculationClass` is internal
to the circulation support.  This construction does not show that a
prescribed external entry reaches the class, that the class has proper
support, that it preserves a whole payoff-vector target, or that any
game-theoretic recursion rank decreases.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The state-indexed baseline occupation column along an analytic Fink
branch. -/
def rawBaselineOccupationColumn
    (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → G.State → ℝ :=
  fun t source destination =>
    germ.rawStateKernelCurve t source destination -
      if destination = source then 1 else 0

/-- Every coordinate of the state-indexed baseline occupation column is
analytic at the endpoint. -/
theorem analytic_rawBaselineOccupationColumn
    (germ : G.AnalyticBellmanGerm) :
    ∀ source destination,
      AnalyticAt ℝ
        (fun t =>
          germ.rawBaselineOccupationColumn t source destination) 0 := by
  intro source destination
  exact
    (((analyticAt_pi_iff.mp
      ((analyticAt_pi_iff.mp
        germ.analytic_rawStateKernelCurve) source)) destination).sub
      analyticAt_const)

/-- At a valid positive parameter, the raw baseline column is the actual
occupation column of the decoded Fink state kernel. -/
theorem rawBaselineOccupationColumn_eq_actual
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (valid : t ∈ Ioo (0 : ℝ) germ.radius) :
    germ.rawBaselineOccupationColumn t =
      actualOccupationColumn
        (G.finkStateKernel (germ.finkPointAt valid))
        (fun state : G.State => state) := by
  funext source destination
  unfold rawBaselineOccupationColumn actualOccupationColumn
  rw [germ.rawStateKernelCurve_eq_finkStateKernel valid]

/-- The concrete result of evaluating an analytic baseline circulation at
one valid punctured parameter and decomposing it into communicating classes.
-/
structure PuncturedBaselinePositiveChargedClass
    (germ : G.AnalyticBellmanGerm)
    (charge : ℝ → G.State → ℝ) where
  parameter : ℝ
  valid : parameter ∈ Ioo (0 : ℝ) germ.radius
  circulation :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (G.finkStateKernel (germ.finkPointAt valid))
        (fun state : G.State => state))
      (charge parameter)
  positiveClass :
    PositiveChargedCirculationClass
      (G.finkStateKernel (germ.finkPointAt valid))
      (fun state : G.State => state)
      (charge parameter)

/-- An analytic positive charged circulation on the raw baseline columns
produces a positive-charge recurrent class at some sufficiently small valid
positive parameter. -/
theorem exists_puncturedBaselinePositiveChargedClass
    (germ : G.AnalyticBellmanGerm)
    (charge : ℝ → G.State → ℝ)
    (circulation :
      AnalyticPositiveChargedCirculation
        germ.rawBaselineOccupationColumn charge) :
    Nonempty
      (PuncturedBaselinePositiveChargedClass germ charge) := by
  have eventually_valid :
      ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
        t ∈ Ioo (0 : ℝ) germ.radius :=
    Ioo_mem_nhdsGT germ.radius_pos
  obtain ⟨parameter, valid, normalized⟩ :=
    (eventually_valid.and
      circulation.eventually_hasNormalizedPositiveChargedCirculation).exists
  rw [germ.rawBaselineOccupationColumn_eq_actual valid] at normalized
  obtain ⟨positiveClass⟩ :=
    normalized.exists_positiveChargedClass
      (G.finkStateKernel (germ.finkPointAt valid))
      (fun state : G.State => state)
      (charge parameter)
  exact ⟨{
    parameter := parameter
    valid := valid
    circulation := normalized
    positiveClass := positiveClass
  }⟩

/-- Endpoint target displacement in either orientation, viewed as a constant
analytic charge family. -/
def endpointTransportCharge
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State) (forward : Bool) :
    ℝ → G.State → ℝ :=
  fun _ state =>
    if forward then
      germ.endpointValue state who - germ.endpointValue entry who
    else
      germ.endpointValue entry who - germ.endpointValue state who

omit [DecidableEq G.State] in
/-- Endpoint transport charge is constant, hence analytic, in the germ
parameter. -/
theorem analytic_endpointTransportCharge
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State) (forward : Bool) :
    ∀ state,
      AnalyticAt ℝ
        (fun t => germ.endpointTransportCharge who entry forward t state)
        0 := by
  intro state
  exact analyticAt_const

/-- Specialization of the punctured class extraction to endpoint target
transport in either orientation. -/
theorem exists_puncturedEndpointTransportChargedClass
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State) (forward : Bool)
    (circulation :
      AnalyticPositiveChargedCirculation
        germ.rawBaselineOccupationColumn
        (germ.endpointTransportCharge who entry forward)) :
    Nonempty
      (PuncturedBaselinePositiveChargedClass germ
        (germ.endpointTransportCharge who entry forward)) :=
  exists_puncturedBaselinePositiveChargedClass
    germ (germ.endpointTransportCharge who entry forward)
    circulation

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
