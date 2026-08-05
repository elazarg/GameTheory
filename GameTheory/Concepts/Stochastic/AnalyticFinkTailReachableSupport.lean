/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ScheduledFinkMarginalRecurrence
import Math.Probability.AnalyticPuncturedTailSupport

/-!
# Tail-reachable support of the prescribed analytic Fink calendar

The raw analytic Fink state-kernel curve need not be a stochastic kernel
outside its valid positive interval.  Nevertheless its coordinate support
stabilizes on a punctured neighborhood because the coordinates are analytic
and are nonnegative wherever they decode to the actual Fink kernel.

This file applies the raw-coordinate tail-support construction to the exact
prescribed Fink state law.  After a finite number of complete quadratic
epochs it produces one fixed subtype:

* generated from the support of the actual prescribed marginal at the
  selected epoch boundary;
* closed under the stabilized raw punctured support;
* containing the support of every later prescribed marginal.

The finite prefix is retained explicitly through `supportEpoch` and
`supportStart`.  No charged-class, legal-child, or payoff-transport claim is
made.
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

omit [DecidableEq G.State] in
/-- The raw analytic Fink state coordinates have one fixed positive support
on a sufficiently small valid punctured interval. -/
theorem eventually_rawStateKernelCurve_pos_iff_puncturedSupport
    (germ : G.AnalyticBellmanGerm) :
    ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
      ∀ source destination,
        0 < germ.rawStateKernelCurve t source destination ↔
          analyticPuncturedCoordinateSupport
            germ.rawStateKernelCurve source destination := by
  have eventuallyValid :
      ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
        t ∈ Ioo (0 : ℝ) germ.radius :=
    Ioo_mem_nhdsGT germ.radius_pos
  have eventuallyNonnegative :
      ∀ source destination,
        ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
          0 ≤ germ.rawStateKernelCurve t source destination := by
    intro source destination
    filter_upwards [eventuallyValid] with t valid
    rw [germ.rawStateKernelCurve_eq_finkStateKernel valid]
    exact ENNReal.toReal_nonneg
  exact
    eventually_coordinate_pos_iff_puncturedSupport
      germ.rawStateKernelCurve
      (fun source destination =>
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawStateKernelCurve source)
          destination))
      eventuallyNonnegative

/-- One fixed tail-support package for the prescribed Fink calendar. -/
structure PrescribedFinkTailReachableSupport
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius) where
  /-- First epoch whose scheduled kernels all use stabilized raw edges. -/
  supportEpoch : ℕ
  /-- Exact tail-support condition from the corresponding epoch boundary. -/
  uses :
    UsesAnalyticPuncturedSupportAfter
      germ.rawStateKernelCurve
      (fun stage =>
        germ.scheduledFinkEpochStateKernel startEpoch valid
          (anytimeEpochIndex stage))
      (epochStart anytimeEpochLength supportEpoch)

namespace PrescribedFinkTailReachableSupport

/-- Calendar stage at which the fixed tail support is sampled. -/
def supportStart
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) : ℕ :=
  epochStart anytimeEpochLength tail.supportEpoch

/-- The fixed state set: punctured forward closure of the actual prescribed
law at the selected complete epoch boundary. -/
def states
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) : Set G.State :=
  analyticPuncturedTailSupport
    germ.rawStateKernelCurve
    (germ.scheduledFinkStateLaw
      startEpoch valid entry tail.supportStart)

omit [DecidableEq G.State] in
/-- The fixed tail state set is nonempty. -/
theorem states_nonempty
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
    tail.states.Nonempty := by
  exact
    analyticPuncturedTailSupport_nonempty
      germ.rawStateKernelCurve
      (germ.scheduledFinkStateLaw
        startEpoch valid entry tail.supportStart)

omit [DecidableEq G.State] in
/-- The fixed tail state set is closed under every retained raw analytic
edge, independently of calendar time. -/
theorem states_closed
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
    {source destination : G.State}
    (source_mem : source ∈ tail.states)
    (step :
      analyticPuncturedCoordinateSupport
        germ.rawStateKernelCurve source destination) :
    destination ∈ tail.states := by
  exact
    analyticPuncturedTailSupport_closed
      germ.rawStateKernelCurve
      (germ.scheduledFinkStateLaw
        startEpoch valid entry tail.supportStart)
      source_mem step

omit [DecidableEq G.State] in
/-- Every positive transition of every scheduled kernel after the selected
boundary stays inside the fixed tail state set. -/
theorem scheduledFinkKernel_supportStep_mem_states
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
    {stage : ℕ} (start_le : tail.supportStart ≤ stage)
    {source destination : G.State}
    (source_mem : source ∈ tail.states)
    (step :
      PMFSupportStep
        (germ.scheduledFinkEpochStateKernel startEpoch valid
          (anytimeEpochIndex stage))
        source destination) :
    destination ∈ tail.states := by
  exact
    tail.states_closed source_mem
      (tail.uses.support_step start_le step)

omit [DecidableEq G.State] in
/-- Every state with positive mass under any later prescribed marginal lies
in the one fixed tail support. -/
theorem scheduledFinkStateLaw_ne_zero_imp_mem_states
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
    {stage : ℕ} (start_le : tail.supportStart ≤ stage)
    {state : G.State}
    (state_mem :
      germ.scheduledFinkStateLaw
        startEpoch valid entry stage state ≠ 0) :
    state ∈ tail.states := by
  apply
    ne_zero_law_imp_mem_analyticPuncturedTailSupport_of_start_le
      germ.rawStateKernelCurve
      (fun currentStage =>
        germ.scheduledFinkEpochStateKernel startEpoch valid
          (anytimeEpochIndex currentStage))
      (germ.scheduledFinkStateLaw startEpoch valid entry)
      tail.supportStart
      (germ.scheduledFinkStateLaw_succ startEpoch valid entry)
      tail.uses start_le state_mem

end PrescribedFinkTailReachableSupport

omit [DecidableEq G.State] in
/-- The exact prescribed Fink calendar admits a fixed tail-reachable support
after a finite number of complete epochs. -/
theorem exists_prescribedFinkTailReachableSupport
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius) :
    Nonempty
      (PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) := by
  have scaleTendsto :
      Tendsto
        (shiftedUniversalEpochScale startEpoch)
        atTop (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_shiftedUniversalEpochScale startEpoch,
        Filter.Eventually.of_forall fun epoch =>
          shiftedUniversalEpochScale_pos startEpoch epoch⟩
  have eventuallyEpochSupport :
      ∀ᶠ epoch : ℕ in atTop,
        ∀ source destination,
          0 <
              germ.rawStateKernelCurve
                (shiftedUniversalEpochScale startEpoch epoch)
                source destination ↔
            analyticPuncturedCoordinateSupport
              germ.rawStateKernelCurve source destination := by
    exact
      scaleTendsto.eventually
        germ.eventually_rawStateKernelCurve_pos_iff_puncturedSupport
  obtain ⟨supportEpoch, supportFrom⟩ :=
    eventually_atTop.1 eventuallyEpochSupport
  refine ⟨{
    supportEpoch := supportEpoch
    uses := ?_
  }⟩
  refine ⟨?_⟩
  intro stage start_le source destination step
  have epoch_le :
      supportEpoch ≤ anytimeEpochIndex stage :=
    anytimeEpochIndex_ge_of_start_le start_le
  apply
    (supportFrom
      (anytimeEpochIndex stage) epoch_le
      source destination).mp
  rw [germ.rawStateKernelCurve_eq_finkStateKernel
    (valid (anytimeEpochIndex stage))]
  exact
    ENNReal.toReal_pos step
      (PMF.apply_ne_top
        (germ.scheduledFinkEpochStateKernel
          startEpoch valid (anytimeEpochIndex stage) source)
        destination)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
