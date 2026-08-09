/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactification.StoneCech
import UniformEquilibrium.Quitting.AbsorptionPath.MarkedAbsorptionCylinder
import UniformEquilibrium.Quitting.Boundary.Holonomy.QuantitativeAggregateTerminalAnchor

/-!
# A metrizable semantic completion of marked absorption paths

The maximal Stone--Cech envelope is useful for extending arbitrary compact
observables, but it is not a sequential decoder carrier.  This file instead
closes one explicit joint semantic encoding in a compact metric target and
exhibits it as a continuous quotient of that maximal envelope.

The encoding retains the completed absorption law, all five holonomy
coordinates, both exact-D anchors, the terminal packet, entry debt, and the
entire finite marked obstacle/deleted-clock graph.  Real coordinates in the
large graph are embedded in `EReal`; the exact-D anchors and packet scalar
coordinates use their intrinsic compact bounded boxes.

This module stops at the compact carrier and its continuous decoder-facing
projections.  Completed exact-seam composition is defined separately so that
the semantic completion does not presume a binary operation or uniqueness of
composition fibres.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 16
set_option synthInstance.maxSize 2048

noncomputable section

namespace GameTheory
namespace MetrizableMarkedAbsorptionCompletion

open Filter Set StochasticGame
open Math.Probability Math.PMFProduct
open TopologicalSpace
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/- `EReal` has a compact second-countable Hausdorff order topology.  We retain
that topology while assembling the hyperspace, then metrize the completed
joint target as a whole below. -/

/-! ## The finite carrier and its completed absorption law -/

/-- Strongly coherent source-free finite cylinders. -/
abbrev FiniteMarkedAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {cylinder : MarkedAbsorptionCylinder ι //
    cylinder.IsSemanticallyCoherent reward}

/-- Finite absorption outcomes plus the genuine `Never` outcome. -/
abbrev MarkedAbsorptionOutcome (ι : Type) [Fintype ι] :=
  Option {coalition : Finset ι // coalition.Nonempty}

/-- A probability vector on finite absorption coalitions and `Never`. -/
abbrev CompletedAbsorptionLaw (ι : Type) [Fintype ι] :=
  {mass : MarkedAbsorptionOutcome ι → Set.Icc (0 : ℝ) 1 //
    (∑ outcome, ((mass outcome : Set.Icc (0 : ℝ) 1) : ℝ)) = 1}

omit [DecidableEq ι] [Nonempty ι] in
private theorem completedAbsorptionLaw_isClosed :
    IsClosed
      {mass : MarkedAbsorptionOutcome ι → Set.Icc (0 : ℝ) 1 |
        (∑ outcome, ((mass outcome : Set.Icc (0 : ℝ) 1) : ℝ)) = 1} := by
  apply isClosed_eq
  · apply continuous_finsetSum Finset.univ
    intro outcome _
    exact continuous_subtype_val.comp (continuous_apply outcome)
  · exact continuous_const

instance : CompactSpace (CompletedAbsorptionLaw ι) :=
  isCompact_iff_compactSpace.mp completedAbsorptionLaw_isClosed.isCompact

private theorem sum_nonempty_absorbed
    (finite : FiniteMarkedAbsorptionPath reward) :
    (∑ coalition : {S : Finset ι // S.Nonempty},
        finite.1.absorbed coalition.1) = 1 - finite.1.sExit := by
  rw [← finite.2.endpoint.absorbed_total]
  exact (Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι))
    (fun coalition => by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact Finset.nonempty_iff_ne_empty.symm)
    finite.1.absorbed).symm

/-- Real mass of one outcome after closing the finite exit port by `Never`. -/
def finiteCompletedMass (finite : FiniteMarkedAbsorptionPath reward) :
    MarkedAbsorptionOutcome ι → ℝ
  | none => finite.1.sExit
  | some coalition => finite.1.absorbed coalition.1

private theorem finiteCompletedMass_nonneg
    (finite : FiniteMarkedAbsorptionPath reward)
    (outcome : MarkedAbsorptionOutcome ι) :
    0 ≤ finiteCompletedMass finite outcome := by
  cases outcome with
  | none => exact finite.2.sExit_nonneg
  | some coalition => exact finite.2.absorbed_nonneg coalition.1

private theorem finiteCompletedMass_le_one
    (finite : FiniteMarkedAbsorptionPath reward)
    (outcome : MarkedAbsorptionOutcome ι) :
    finiteCompletedMass finite outcome ≤ 1 := by
  cases outcome with
  | none => exact finite.2.sExit_le_one
  | some coalition =>
      have hmem : coalition.1 ∈
          Finset.univ.erase (∅ : Finset ι) := by
        simp [coalition.2.ne_empty]
      have hterm : finite.1.absorbed coalition.1 ≤
          ∑ terminal ∈ Finset.univ.erase (∅ : Finset ι),
            finite.1.absorbed terminal :=
        Finset.single_le_sum
          (fun terminal _ => finite.2.absorbed_nonneg terminal) hmem
      calc
        finiteCompletedMass finite (some coalition) =
            finite.1.absorbed coalition.1 := rfl
        _ ≤ ∑ terminal ∈ Finset.univ.erase (∅ : Finset ι),
              finite.1.absorbed terminal := hterm
        _ = 1 - finite.1.sExit := finite.2.endpoint.absorbed_total
        _ ≤ 1 := by linarith [finite.2.sExit_nonneg]

/-- Close the finite exit defect by the genuine `Never` atom. -/
def finiteCompletedLaw (finite : FiniteMarkedAbsorptionPath reward) :
    CompletedAbsorptionLaw ι :=
  ⟨fun outcome =>
      ⟨finiteCompletedMass finite outcome,
        finiteCompletedMass_nonneg finite outcome,
        finiteCompletedMass_le_one finite outcome⟩,
    by
      rw [Fintype.sum_option]
      change finite.1.sExit +
          (∑ coalition : {S : Finset ι // S.Nonempty},
            finite.1.absorbed coalition.1) = 1
      rw [sum_nonempty_absorbed]
      ring⟩

/-! ## Finite exact seams -/

/-- A finite seam carries literal exact-anchor composability. -/
abbrev FiniteExactSeam
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {pair : FiniteMarkedAbsorptionPath reward ×
      FiniteMarkedAbsorptionPath reward //
    MarkedAbsorptionCylinder.IsComposable pair.1.1 pair.2.1}

namespace FiniteExactSeam

def outer (seam : FiniteExactSeam reward) :
    FiniteMarkedAbsorptionPath reward := seam.1.1

def inner (seam : FiniteExactSeam reward) :
    FiniteMarkedAbsorptionPath reward := seam.1.2

def compose (seam : FiniteExactSeam reward) :
    FiniteMarkedAbsorptionPath reward :=
  ⟨seam.outer.1.compose seam.inner.1,
    seam.outer.2.compose seam.inner.2 seam.2⟩

end FiniteExactSeam

/-! ## Compact semantic coordinates -/

/-- Exact extended-real coordinates of a product root. -/
abbrev ExtendedRootCoordinates (ι : Type) := ι → Bool → EReal

/-- Exact extended-real coordinates of the five holonomy scalars. -/
abbrev ExtendedHolonomyCoordinates (ι : Type) :=
  (ι → EReal × EReal) × (ι → EReal × (EReal × EReal))

/-- A compact probability coordinate. -/
abbrev CompactProbability := Set.Icc (0 : ℝ) 1

/-- The intrinsic compact exact-D box, used without forgetting its root or
debt coordinates. -/
abbrev CompactDebtPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {point : QuittingDebtPoint ι // point ∈ quittingDebtBox reward}

instance : CompactSpace (CompactDebtPoint reward) :=
  isCompact_iff_compactSpace.mp (quittingDebtBox_isCompact reward)

/-- The bounded playerwise entry-debt coordinate. -/
abbrev CompactDebtCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {debt : Payoff ι //
    debt ∈ Set.Icc (0 : Payoff ι) (quittingPositiveSingletonDebtCap reward)}

instance : CompactSpace (CompactDebtCoordinates reward) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- Compact packet coordinates.  Owners and actions are represented by their
zero-one indicator vectors, and the kernel by its Boolean probability
coordinates.  The advantage lies in its uniform `[0, 2M]` box. -/
abbrev CompactTerminalPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  (ι → CompactProbability) ×
    ((ι → CompactProbability) ×
      ((ι → Bool → CompactProbability) ×
        (CompactProbability ×
          (CompactProbability ×
            Set.Icc (0 : ℝ) (2 * quittingRewardBound reward)))))

/-- The two playerwise clock vectors and their full/deleted products. -/
abbrev ExtendedClockCoordinates (ι : Type) :=
  ((ι → EReal) × (ι → EReal)) ×
    ((EReal × EReal) × ((ι → EReal) × (ι → EReal)))

/-- Coalition absorption immediately before and after a marked row. -/
abbrev ExtendedAbsorptionCoordinates (ι : Type) :=
  (Finset ι → EReal) × (Finset ι → EReal)

/-- Local Bellman coordinates of every player at a marked row. -/
abbrev ExtendedLocalCoordinates (ι : Type) :=
  (ι → EReal) × ((ι → EReal) × (ι → EReal))

/-- Prefix and suffix affine intercept/survival coordinates. -/
abbrev ExtendedAffineCoordinates (ι : Type) :=
  ((ι → EReal) × (ι → EReal)) × ((ι → EReal) × (ι → EReal))

/-- Literal deleted-clock obstacle and full-prefix pure-Quit payoff. -/
abbrev ExtendedObstacleCoordinates (ι : Type) :=
  (ι → EReal) × (ι → EReal)

/-- One complete source-free marked stage in a compact metric ambient type. -/
abbrev ExtendedMarkedStageCoordinates (ι : Type) :=
  ExtendedRootCoordinates ι ×
    (ExtendedClockCoordinates ι ×
      (ExtendedAbsorptionCoordinates ι ×
        (ExtendedLocalCoordinates ι ×
          (ExtendedAffineCoordinates ι × ExtendedObstacleCoordinates ι))))

/-- Compact Hausdorff graph of nonempty marked-stage coordinates. -/
abbrev CompactMarkedStageGraph (ι : Type) [Fintype ι] :=
  TopologicalSpace.NonemptyCompacts (ExtendedMarkedStageCoordinates ι)

private def realE (x : ℝ) : EReal := x

private def pmfCoordinate (μ : PMF Bool) (action : Bool) : CompactProbability :=
  ⟨(μ action).toReal, ENNReal.toReal_nonneg,
    by
      simpa using
        ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ action)⟩

private def boolCoordinate (value : Bool) : CompactProbability :=
  if value then ⟨1, by simp⟩ else ⟨0, by simp⟩

private def ownerCoordinate (owner who : ι) : CompactProbability :=
  if who = owner then ⟨1, by simp⟩ else ⟨0, by simp⟩

/-- Forget a finite holonomy to exact compact extended-real coordinates. -/
def finiteHolonomyCoordinates (finite : FiniteMarkedAbsorptionPath reward) :
    ExtendedHolonomyCoordinates ι :=
  (fun who =>
      (realE (finite.1.holonomy.prescribed who).intercept,
        realE (finite.1.holonomy.prescribed who).survival),
    fun who =>
      (realE (finite.1.holonomy.bestResponse who).early,
        (realE (finite.1.holonomy.bestResponse who).tail,
          realE (finite.1.holonomy.bestResponse who).survival)))

/-- Exact compact encoding of a source-free marked row. -/
def extendedMarkedStageCoordinates (stage : MarkedCylinderStage ι) :
    ExtendedMarkedStageCoordinates ι :=
  (fun who action => (pmfCoordinate (stage.root who) action : ℝ),
    (((fun who => realE (stage.preFactor who),
        fun who => realE (stage.postFactor who)),
      ((realE stage.preFull, realE stage.postFull),
        (fun who => realE (stage.preDeleted who),
          fun who => realE (stage.postDeleted who)))),
      ((fun coalition => realE (stage.preAbsorbed coalition),
          fun coalition => realE (stage.postAbsorbed coalition)),
        ((fun who => realE (stage.quitValue who),
            (fun who => realE (stage.continueReward who),
              fun who => realE (stage.continueMass who))),
          (((fun who => realE (stage.prefixContinue who).intercept,
              fun who => realE (stage.prefixContinue who).survival),
            (fun who => realE (stage.suffixContinue who).intercept,
              fun who => realE (stage.suffixContinue who).survival)),
            (fun who => realE (stage.obstacle who),
              fun who => realE (stage.pureQuitPayoff who)))))))

/-- The nonempty finite marked graph, regarded as a point of the compact
Hausdorff hyperspace. -/
def finiteMarkedStageGraph (finite : FiniteMarkedAbsorptionPath reward) :
    CompactMarkedStageGraph ι where
  carrier := extendedMarkedStageCoordinates '' finite.1.stages
  isCompact' :=
    (finite.1.stages_finite.image extendedMarkedStageCoordinates).isCompact
  nonempty' := finite.2.stages_nonempty.image extendedMarkedStageCoordinates

/-! ## Bounded anchors, packet, and debt -/

theorem chronology_entryAnchor_mem_box
    {cylinder : MarkedAbsorptionCylinder ι}
    (h : cylinder.IsChronologicallyGenerated reward) :
    cylinder.entryAnchor ∈ quittingDebtBox reward := by
  induction h with
  | @realized anchor source =>
      change anchor.debtPoint source.block.start ∈ quittingDebtBox reward
      exact quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
        reward (anchor.last + 1) anchor.path
        (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
          reward (anchor.last + 1)) source.block.start
  | @splice outer inner houter hinner hseam ihouter ihinner =>
      simpa using ihouter

theorem chronology_exitAnchor_mem_box
    {cylinder : MarkedAbsorptionCylinder ι}
    (h : cylinder.IsChronologicallyGenerated reward) :
    cylinder.exitAnchor ∈ quittingDebtBox reward := by
  induction h with
  | @realized anchor source =>
      change anchor.debtPoint (source.block.start + source.block.length) ∈
        quittingDebtBox reward
      exact quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
        reward (anchor.last + 1) anchor.path
        (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
          reward (anchor.last + 1))
        (source.block.start + source.block.length)
  | @splice outer inner houter hinner hseam ihouter ihinner =>
      simpa using ihinner

/-- Exact entry anchor in its intrinsic bounded box. -/
def finiteEntryAnchor (finite : FiniteMarkedAbsorptionPath reward) :
    CompactDebtPoint reward :=
  ⟨finite.1.entryAnchor, chronology_entryAnchor_mem_box finite.2.chronology⟩

/-- Exact exit anchor in its intrinsic bounded box. -/
def finiteExitAnchor (finite : FiniteMarkedAbsorptionPath reward) :
    CompactDebtPoint reward :=
  ⟨finite.1.exitAnchor, chronology_exitAnchor_mem_box finite.2.chronology⟩

/-- Entry debt in its playerwise compact interval. -/
def finiteEntryDebt (finite : FiniteMarkedAbsorptionPath reward) :
    CompactDebtCoordinates reward :=
  ⟨finite.1.entryDebt, by
    rw [finite.2.entryDebt_pin]
    exact (chronology_entryAnchor_mem_box finite.2.chronology).2⟩

private theorem finite_packet_advantage_mem
    (finite : FiniteMarkedAbsorptionPath reward) :
    finite.1.packet.advantage ∈
      Set.Icc (0 : ℝ) (2 * quittingRewardBound reward) := by
  constructor
  · exact le_of_lt finite.2.packet.advantage_pos
  · rw [finite.2.packet.advantage_pin]
    exact QuittingAggregateCalibratedTerminalAnchor.terminalOpponentAdvantage_le_two_mul_bound
      reward
      (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
      (fun terminal player => abs_reward_le_quittingRewardBound reward terminal player)
      finite.1.packet.owner finite.1.packet.action

/-- Exact bounded encoding of the terminal packet. -/
def finiteTerminalPacket (finite : FiniteMarkedAbsorptionPath reward) :
    CompactTerminalPacket reward :=
  (fun who => ownerCoordinate finite.1.packet.owner who,
    (fun who => boolCoordinate (finite.1.packet.action who),
      (fun who action => pmfCoordinate (finite.1.packet.kernel who) action,
        (⟨finite.1.packet.preterminalSurvival,
            le_of_lt finite.2.packet.preterminal_pos,
            finite.2.packet.preterminal_le_one⟩,
          (⟨finite.1.packet.terminalMass,
              le_of_lt finite.2.packet.terminalMass_pos,
              finite.2.packet.terminalMass_le_one⟩,
            ⟨finite.1.packet.advantage,
              finite_packet_advantage_mem finite⟩)))))

/-! ## The joint compact metric completion -/

/-- The concrete joint semantic target.  Its tuple order is law, holonomy,
entry anchor, exit anchor, packet, entry debt, marked graph. -/
private abbrev SemanticTail0 :=
  CompactDebtCoordinates reward × CompactMarkedStageGraph ι
private abbrev SemanticTail1 :=
  CompactTerminalPacket reward × SemanticTail0 (ι := ι) (reward := reward)
private abbrev SemanticTail2 :=
  CompactDebtPoint reward × SemanticTail1 (ι := ι) (reward := reward)
private abbrev SemanticTail3 :=
  CompactDebtPoint reward × SemanticTail2 (ι := ι) (reward := reward)
private abbrev SemanticTail4 :=
  ExtendedHolonomyCoordinates ι × SemanticTail3 (ι := ι) (reward := reward)

abbrev CompactMarkedSemanticTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  CompletedAbsorptionLaw ι ×
    SemanticTail4 (ι := ι) (reward := reward)

/- Urysohn metrization of the already-assembled joint topology avoids an
instance diamond between the Vietoris topology and a prematurely selected
Hausdorff metric on the stage hyperspace. -/
local instance : MetricSpace (CompactMarkedSemanticTarget reward) :=
  TopologicalSpace.metrizableSpaceMetric _

/-- Joint finite semantic encoding. -/
def finiteSemanticTarget (finite : FiniteMarkedAbsorptionPath reward) :
    CompactMarkedSemanticTarget reward :=
  (finiteCompletedLaw finite,
    (finiteHolonomyCoordinates finite,
      (finiteEntryAnchor finite,
        (finiteExitAnchor finite,
          (finiteTerminalPacket finite,
            (finiteEntryDebt finite, finiteMarkedStageGraph finite))))))

/-- Closure of the joint finite semantic image in a compact metric target. -/
abbrev MetrizableMarkedAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {target : CompactMarkedSemanticTarget reward //
    target ∈ closure (Set.range (finiteSemanticTarget (reward := reward)))}

instance : CompactSpace (MetrizableMarkedAbsorptionPath reward) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- Embed one finite cylinder into the compact metric semantic closure. -/
def completeMetrizable (finite : FiniteMarkedAbsorptionPath reward) :
    MetrizableMarkedAbsorptionPath reward :=
  ⟨finiteSemanticTarget finite,
    subset_closure (Set.mem_range_self finite)⟩

/-- The finite semantic points are topologically dense. -/
theorem denseRange_completeMetrizable :
    DenseRange (completeMetrizable (reward := reward)) := by
  rw [DenseRange, Subtype.dense_iff]
  intro target htarget
  have himage :
      ((fun point : MetrizableMarkedAbsorptionPath reward =>
          (point : CompactMarkedSemanticTarget reward)) ''
          Set.range (completeMetrizable (reward := reward))) =
        Set.range (finiteSemanticTarget (reward := reward)) := by
    ext point
    constructor
    · rintro ⟨_, ⟨finite, rfl⟩, rfl⟩
      exact ⟨finite, rfl⟩
    · rintro ⟨finite, rfl⟩
      exact ⟨completeMetrizable finite, ⟨finite, rfl⟩, rfl⟩
  rw [himage]
  exact htarget

/-- Every completed semantic point is the limit of a sequence of finite
cylinders, not merely of a net or ultrafilter. -/
theorem exists_finite_sequence_tendsto
    (path : MetrizableMarkedAbsorptionPath reward) :
    ∃ finite : ℕ → FiniteMarkedAbsorptionPath reward,
      Tendsto (fun n => completeMetrizable (finite n)) atTop (𝓝 path) := by
  obtain ⟨target, htarget, htendsto⟩ :=
    mem_closure_iff_seq_limit.mp path.2
  choose finite hfinite using htarget
  refine ⟨finite, tendsto_subtype_rng.mpr ?_⟩
  simpa only [completeMetrizable, hfinite] using htendsto

/-- Compactness is sequential compactness on the concrete carrier. -/
theorem exists_convergent_subsequence
    (sequence : ℕ → MetrizableMarkedAbsorptionPath reward) :
    ∃ (limit : MetrizableMarkedAbsorptionPath reward) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        Tendsto (sequence ∘ subseq) atTop (𝓝 limit) :=
  CompactSpace.tendsto_subseq sequence

/-! ## The metric carrier as a quotient of the maximal envelope -/

/-- The maximal Stone--Cech envelope, named explicitly to distinguish it from
the decoder-facing metric quotient. -/
abbrev MaximalMarkedAbsorptionEnvelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  Ultrafilter (FiniteMarkedAbsorptionPath reward)

/-- Extend the joint finite semantic target across the maximal envelope. -/
def maximalSemanticTarget :
    MaximalMarkedAbsorptionEnvelope reward → CompactMarkedSemanticTarget reward :=
  Ultrafilter.extend finiteSemanticTarget

theorem continuous_maximalSemanticTarget :
    Continuous (maximalSemanticTarget (reward := reward)) :=
  continuous_ultrafilter_extend _

@[simp] theorem maximalSemanticTarget_pure
    (finite : FiniteMarkedAbsorptionPath reward) :
    maximalSemanticTarget (pure finite) = finiteSemanticTarget finite :=
  ultrafilter_extend_pure _ finite

private theorem maximalSemanticTarget_mem_closure
    (path : MaximalMarkedAbsorptionEnvelope reward) :
    maximalSemanticTarget path ∈
      closure (Set.range (finiteSemanticTarget (reward := reward))) := by
  apply map_mem_closure continuous_maximalSemanticTarget (denseRange_pure path)
  rintro target ⟨finite, rfl⟩
  exact ⟨finite, by simp⟩

/-- Continuous semantic quotient from the maximal nonsequential envelope to
the compact metric decoder carrier. -/
def maximalToMetrizable
    (path : MaximalMarkedAbsorptionEnvelope reward) :
    MetrizableMarkedAbsorptionPath reward :=
  ⟨maximalSemanticTarget path, maximalSemanticTarget_mem_closure path⟩

theorem continuous_maximalToMetrizable :
    Continuous (maximalToMetrizable (reward := reward)) :=
  continuous_maximalSemanticTarget.subtype_mk _

/-- The semantic quotient is onto.  Thus every sequential decoder point has
at least one maximal-envelope lift, while different ultrafilters with the
same joint semantic limit are intentionally identified. -/
theorem surjective_maximalToMetrizable :
    Function.Surjective (maximalToMetrizable (reward := reward)) := by
  intro path
  have hclosed : IsClosed
      (Set.range (maximalSemanticTarget (reward := reward))) :=
    (isCompact_range continuous_maximalSemanticTarget).isClosed
  have hfinite : Set.range (finiteSemanticTarget (reward := reward)) ⊆
      Set.range (maximalSemanticTarget (reward := reward)) := by
    rintro target ⟨finite, rfl⟩
    exact ⟨pure finite, by simp⟩
  have hmem := closure_minimal hfinite hclosed path.2
  obtain ⟨lift, hlift⟩ := hmem
  refine ⟨lift, Subtype.ext ?_⟩
  exact hlift

/-! ## Continuous decoder projections and `Never` -/

def metrizableLaw (path : MetrizableMarkedAbsorptionPath reward) :
    CompletedAbsorptionLaw ι := path.1.1

def metrizableHolonomy (path : MetrizableMarkedAbsorptionPath reward) :
    ExtendedHolonomyCoordinates ι := path.1.2.1

def metrizableEntryAnchor (path : MetrizableMarkedAbsorptionPath reward) :
    CompactDebtPoint reward := path.1.2.2.1

def metrizableExitAnchor (path : MetrizableMarkedAbsorptionPath reward) :
    CompactDebtPoint reward := path.1.2.2.2.1

def metrizablePacket (path : MetrizableMarkedAbsorptionPath reward) :
    CompactTerminalPacket reward := path.1.2.2.2.2.1

def metrizableEntryDebt (path : MetrizableMarkedAbsorptionPath reward) :
    CompactDebtCoordinates reward := path.1.2.2.2.2.2.1

def metrizableStageGraph (path : MetrizableMarkedAbsorptionPath reward) :
    CompactMarkedStageGraph ι := path.1.2.2.2.2.2.2

theorem continuous_metrizableLaw :
    Continuous (metrizableLaw (reward := reward)) := by
  unfold metrizableLaw
  fun_prop

theorem continuous_metrizableHolonomy :
    Continuous (metrizableHolonomy (reward := reward)) := by
  unfold metrizableHolonomy
  fun_prop

theorem continuous_metrizableEntryAnchor :
    Continuous (metrizableEntryAnchor (reward := reward)) := by
  unfold metrizableEntryAnchor
  fun_prop

theorem continuous_metrizableExitAnchor :
    Continuous (metrizableExitAnchor (reward := reward)) := by
  unfold metrizableExitAnchor
  fun_prop

theorem continuous_metrizablePacket :
    Continuous (metrizablePacket (reward := reward)) := by
  unfold metrizablePacket
  fun_prop

theorem continuous_metrizableEntryDebt :
    Continuous (metrizableEntryDebt (reward := reward)) := by
  unfold metrizableEntryDebt
  fun_prop

theorem continuous_metrizableStageGraph :
    Continuous (metrizableStageGraph (reward := reward)) := by
  unfold metrizableStageGraph
  fun_prop

@[simp] theorem metrizableLaw_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableLaw (completeMetrizable finite) = finiteCompletedLaw finite := rfl

@[simp] theorem metrizableHolonomy_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableHolonomy (completeMetrizable finite) =
      finiteHolonomyCoordinates finite := rfl

@[simp] theorem metrizableEntryAnchor_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableEntryAnchor (completeMetrizable finite) = finiteEntryAnchor finite := rfl

@[simp] theorem metrizableExitAnchor_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableExitAnchor (completeMetrizable finite) = finiteExitAnchor finite := rfl

@[simp] theorem metrizablePacket_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizablePacket (completeMetrizable finite) = finiteTerminalPacket finite := rfl

@[simp] theorem metrizableEntryDebt_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableEntryDebt (completeMetrizable finite) = finiteEntryDebt finite := rfl

@[simp] theorem metrizableStageGraph_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableStageGraph (completeMetrizable finite) = finiteMarkedStageGraph finite := rfl

/-- Genuine `Never` mass in the sequential semantic completion. -/
def metrizableNeverMass (path : MetrizableMarkedAbsorptionPath reward) : ℝ :=
  (((metrizableLaw path).1 none : CompactProbability) : ℝ)

/-- Coalition absorption mass in the sequential semantic completion. -/
def metrizableCoalitionMass (path : MetrizableMarkedAbsorptionPath reward)
    (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  (((metrizableLaw path).1 (some coalition) : CompactProbability) : ℝ)

theorem continuous_metrizableNeverMass :
    Continuous (metrizableNeverMass (reward := reward)) := by
  exact continuous_subtype_val.comp
    ((continuous_apply none).comp
      (continuous_subtype_val.comp continuous_metrizableLaw))

theorem continuous_metrizableCoalitionMass
    (coalition : {S : Finset ι // S.Nonempty}) :
    Continuous (fun path : MetrizableMarkedAbsorptionPath reward =>
      metrizableCoalitionMass path coalition) := by
  exact continuous_subtype_val.comp
    ((continuous_apply (some coalition)).comp
      (continuous_subtype_val.comp continuous_metrizableLaw))

@[simp] theorem metrizableNeverMass_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableNeverMass (completeMetrizable finite) = finite.1.sExit := by
  simp [metrizableNeverMass, finiteCompletedLaw, finiteCompletedMass]

/-- Absorption plus `Never` has total mass one at every boundary point. -/
theorem metrizableNever_add_sum_coalitionMass
    (path : MetrizableMarkedAbsorptionPath reward) :
    metrizableNeverMass path +
        ∑ coalition : {S : Finset ι // S.Nonempty},
          metrizableCoalitionMass path coalition = 1 := by
  simpa [metrizableNeverMass, metrizableCoalitionMass, Fintype.sum_option] using
    (metrizableLaw path).2



end MetrizableMarkedAbsorptionCompletion
end GameTheory
