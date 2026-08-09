/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.MarkedObstacleRecord

/-!
# Source-forgetting finite marked absorption cylinders

This module implements a finite, source-free semantic graph for a quitting
block.  It deliberately separates the finite carrier from its future
compactification: a cylinder contains a finite `Set` of joint stage records,
but no source block, calendar index, horizon, or literal length.

The stage coordinates jointly retain coalition absorption, all playerwise
survival clocks, the current product root, local Bellman data, and an affine
suffix-continuation mark.  The suffix mark is the division-free coordinate
needed to transport outer stages when another cylinder is appended.

There is no `Never` field.  Missing mass is an exit port; a completed infinite
path must be a different type.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Source-free stage and packet coordinates -/

/-- Product of all playerwise continue factors. -/
def fullFactor (factor : ι → ℝ) : ℝ := ∏ who, factor who

/-- Product of all continue factors except the displayed player. -/
def deletedFactor (factor : ι → ℝ) (who : ι) : ℝ :=
  ∏ other ∈ Finset.univ.erase who, factor other

omit [DecidableEq ι] in
theorem fullFactor_mul (left right : ι → ℝ) :
    fullFactor (fun who => left who * right who) =
      fullFactor left * fullFactor right := by
  exact Finset.prod_mul_distrib

theorem deletedFactor_mul (left right : ι → ℝ) (who : ι) :
    deletedFactor (fun other => left other * right other) who =
      deletedFactor left who * deletedFactor right who := by
  exact Finset.prod_mul_distrib

/-- Independent marked terminal-packet data. -/
@[ext] structure TerminalPacket (ι : Type) [Fintype ι] where
  owner : ι
  action : ι → Bool
  kernel : ι → PMF Bool
  preterminalSurvival : ℝ
  terminalMass : ℝ
  advantage : ℝ

/--
One joint chronological edge of a finite cylinder.

`preAbsorbed` and `postAbsorbed` retain the coalition path, while
`preFactor` and `postFactor` retain every player clock.  `prefixContinue` is
the affine always-continue map from the block entry to immediately before this
row, and `suffixContinue` is the corresponding map from immediately after the
row to the exit port.  Both are stored so obstacle evaluation and tail
transport never require division by a possibly-zero endpoint factor.
-/
@[ext] structure MarkedCylinderStage (ι : Type) [Fintype ι] where
  root : ι → PMF Bool
  preFactor : ι → ℝ
  postFactor : ι → ℝ
  preAbsorbed : Finset ι → ℝ
  postAbsorbed : Finset ι → ℝ
  quitValue : ι → ℝ
  continueReward : ι → ℝ
  continueMass : ι → ℝ
  prefixContinue : ι → QuittingAffineSummary
  suffixContinue : ι → QuittingAffineSummary

namespace MarkedCylinderStage

def preFull (stage : MarkedCylinderStage ι) : ℝ :=
  fullFactor stage.preFactor

def postFull (stage : MarkedCylinderStage ι) : ℝ :=
  fullFactor stage.postFactor

def preDeleted (stage : MarkedCylinderStage ι) (who : ι) : ℝ :=
  deletedFactor stage.preFactor who

def postDeleted (stage : MarkedCylinderStage ι) (who : ι) : ℝ :=
  deletedFactor stage.postFactor who

/-- Literal obstacle ordinate at this chronological record. -/
def obstacle (stage : MarkedCylinderStage ι) (who : ι) : ℝ :=
  stage.preDeleted who * stage.quitValue who

/-- Full-prefix payoff of deterministically quitting at this stage.  Unlike
`obstacle`, this includes all earlier Continue rewards. -/
def pureQuitPayoff (stage : MarkedCylinderStage ι) (who : ι) : ℝ :=
  (stage.prefixContinue who).eval (stage.quitValue who)

/-- Root-induced one-row Continue map, bundled independently of the raw local
coordinates so coherence can pin those coordinates back to the root. -/
def rootContinueSummary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (stage : MarkedCylinderStage ι) (who : ι) : QuittingAffineSummary where
  intercept := quittingFixedOpponentsContinueReward reward
    (fun _ => stage.root) who 0
  survival := quittingFixedOpponentsContinueMass (fun _ => stage.root) who 0
  survival_nonneg := quittingStationaryContinueMass_nonneg
    (Function.update stage.root who (PMF.pure false))

/-- Recover the production one-row source-free record from a joint stage. -/
def toObstacleRecord (stage : MarkedCylinderStage ι) (who : ι) :
    MarkedObstacleRecord ι where
  player := who
  root := stage.root
  preFactor := stage.preFactor
  postFactor := stage.postFactor
  preFull := stage.preFull
  postFull := stage.postFull
  preDeleted := stage.preDeleted who
  postDeleted := stage.postDeleted who
  quitValue := stage.quitValue who
  continueReward := stage.continueReward who
  continueMass := stage.continueMass who
  continuation := (stage.suffixContinue who).intercept
  obstacle := stage.obstacle who
  obstacle_pin := rfl

/-- Append an affine tail to every suffix mark of an outer stage. -/
def appendTail (tail : ι → QuittingAffineSummary)
    (stage : MarkedCylinderStage ι) : MarkedCylinderStage ι :=
  { stage with
    suffixContinue := fun who => stage.suffixContinue who * tail who }

/-- Translate and scale a stage placed after a source-free prefix. -/
def shiftPrefix (absorbed : Finset ι → ℝ) (factor : ι → ℝ)
    (prefixSummary : ι → QuittingAffineSummary)
    (stage : MarkedCylinderStage ι) : MarkedCylinderStage ι :=
  { stage with
    preFactor := fun who => factor who * stage.preFactor who
    postFactor := fun who => factor who * stage.postFactor who
    preAbsorbed := fun coalition =>
      absorbed coalition + fullFactor factor * stage.preAbsorbed coalition
    postAbsorbed := fun coalition =>
      absorbed coalition + fullFactor factor * stage.postAbsorbed coalition
    prefixContinue := fun who => prefixSummary who * stage.prefixContinue who }

omit [DecidableEq ι] in
@[simp] theorem pureQuitPayoff_appendTail
    (tail : ι → QuittingAffineSummary) (stage : MarkedCylinderStage ι)
    (who : ι) :
    (stage.appendTail tail).pureQuitPayoff who = stage.pureQuitPayoff who := rfl

omit [DecidableEq ι] in
@[simp] theorem pureQuitPayoff_shiftPrefix
    (absorbed : Finset ι → ℝ) (factor : ι → ℝ)
    (prefixSummary : ι → QuittingAffineSummary)
    (stage : MarkedCylinderStage ι) (who : ι) :
    (stage.shiftPrefix absorbed factor prefixSummary).pureQuitPayoff who =
      (prefixSummary who).eval (stage.pureQuitPayoff who) := by
  exact QuittingAffineSummary.eval_mul _ _ _

omit [DecidableEq ι] in
theorem appendTail_assoc (first second : ι → QuittingAffineSummary)
    (stage : MarkedCylinderStage ι) :
    (stage.appendTail first).appendTail second =
      stage.appendTail (fun who => first who * second who) := by
  apply MarkedCylinderStage.ext
  all_goals try rfl
  funext who
  exact mul_assoc _ _ _

omit [DecidableEq ι] in
theorem appendTail_shiftPrefix (tail : ι → QuittingAffineSummary)
    (absorbed : Finset ι → ℝ) (factor : ι → ℝ)
    (prefixSummary : ι → QuittingAffineSummary)
    (stage : MarkedCylinderStage ι) :
    (stage.appendTail tail).shiftPrefix absorbed factor prefixSummary =
      (stage.shiftPrefix absorbed factor prefixSummary).appendTail tail := rfl

omit [DecidableEq ι] in
theorem shiftPrefix_assoc
    (firstAbsorbed secondAbsorbed : Finset ι → ℝ)
    (firstFactor secondFactor : ι → ℝ)
    (firstPrefix secondPrefix : ι → QuittingAffineSummary)
    (stage : MarkedCylinderStage ι) :
    (stage.shiftPrefix secondAbsorbed secondFactor secondPrefix).shiftPrefix
        firstAbsorbed firstFactor firstPrefix =
      stage.shiftPrefix
        (fun coalition => firstAbsorbed coalition +
          fullFactor firstFactor * secondAbsorbed coalition)
        (fun who => firstFactor who * secondFactor who)
        (fun who => firstPrefix who * secondPrefix who) := by
  apply MarkedCylinderStage.ext
  · rfl
  · funext who
    simp only [shiftPrefix]
    ring_nf
  · funext who
    simp only [shiftPrefix]
    ring_nf
  · funext coalition
    simp only [shiftPrefix, fullFactor_mul]
    ring_nf
  · funext coalition
    simp only [shiftPrefix, fullFactor_mul]
    ring_nf
  all_goals try rfl
  funext who
  simp only [shiftPrefix]
  exact (mul_assoc (firstPrefix who) (secondPrefix who)
    (stage.prefixContinue who)).symm

end MarkedCylinderStage

/-! ## The finite source-free cylinder -/

/--
A finite marked absorption cylinder.

The finite graph is extensional and has no length field.  Repeated-mass stages
with different marks remain distinct points.  Exact duplicate points collapse;
a future compact provenance coordinate is required if their multiplicity is
observable.
-/
@[ext] structure MarkedAbsorptionCylinder (ι : Type)
    [Fintype ι] [DecidableEq ι] where
  stages : Set (MarkedCylinderStage ι)
  stages_finite : stages.Finite
  absorbed : Finset ι → ℝ
  exitFactor : ι → ℝ
  holonomy : QuittingBoundaryHolonomy ι
  packet : TerminalPacket ι
  entryDebt : Payoff ι
  entryAnchor : QuittingDebtPoint ι
  exitAnchor : QuittingDebtPoint ι

namespace MarkedAbsorptionCylinder

/-- Full survival to the exit port. -/
def sExit (cylinder : MarkedAbsorptionCylinder ι) : ℝ :=
  fullFactor cylinder.exitFactor

/-- Opponent-only survival to the exit port. -/
def chi (cylinder : MarkedAbsorptionCylinder ι) (who : ι) : ℝ :=
  deletedFactor cylinder.exitFactor who

/-- The affine continue-through coordinate of the max-affine holonomy. -/
def continueSummary (cylinder : MarkedAbsorptionCylinder ι) (who : ι) :
    QuittingAffineSummary where
  intercept := (cylinder.holonomy.bestResponse who).tail
  survival := (cylinder.holonomy.bestResponse who).survival
  survival_nonneg :=
    (cylinder.holonomy.bestResponse who).survival_nonneg

/-- The production holonomy is the cylinder's semantic forgetful map. -/
def forgetful (cylinder : MarkedAbsorptionCylinder ι) :
    QuittingBoundaryHolonomy ι := cylinder.holonomy

/-- Exact anchor equality required for a legal semantic splice. -/
def IsComposable (outer inner : MarkedAbsorptionCylinder ι) : Prop :=
  outer.exitAnchor = inner.entryAnchor

/-- Chronological composition of finite source-free cylinders. -/
def compose (outer inner : MarkedAbsorptionCylinder ι) :
    MarkedAbsorptionCylinder ι where
  stages :=
    MarkedCylinderStage.appendTail inner.continueSummary '' outer.stages ∪
      MarkedCylinderStage.shiftPrefix outer.absorbed outer.exitFactor
        outer.continueSummary '' inner.stages
  stages_finite :=
    (outer.stages_finite.image
      (MarkedCylinderStage.appendTail inner.continueSummary)).union
      (inner.stages_finite.image
        (MarkedCylinderStage.shiftPrefix outer.absorbed outer.exitFactor
          outer.continueSummary))
  absorbed := fun coalition =>
    outer.absorbed coalition + outer.sExit * inner.absorbed coalition
  exitFactor := fun who => outer.exitFactor who * inner.exitFactor who
  holonomy := outer.holonomy * inner.holonomy
  packet := inner.packet
  entryDebt := outer.entryDebt
  entryAnchor := outer.entryAnchor
  exitAnchor := inner.exitAnchor

@[simp] theorem sExit_compose (outer inner : MarkedAbsorptionCylinder ι) :
    (outer.compose inner).sExit = outer.sExit * inner.sExit := by
  exact fullFactor_mul outer.exitFactor inner.exitFactor

@[simp] theorem chi_compose (outer inner : MarkedAbsorptionCylinder ι)
    (who : ι) :
    (outer.compose inner).chi who = outer.chi who * inner.chi who := by
  exact deletedFactor_mul outer.exitFactor inner.exitFactor who

@[simp] theorem forgetful_compose
    (outer inner : MarkedAbsorptionCylinder ι) :
    (outer.compose inner).forgetful = outer.forgetful * inner.forgetful := rfl

@[simp] theorem continueSummary_compose
    (outer inner : MarkedAbsorptionCylinder ι) (who : ι) :
    (outer.compose inner).continueSummary who =
      outer.continueSummary who * inner.continueSummary who := by
  apply QuittingAffineSummary.ext <;> rfl

@[simp] theorem absorbed_compose
    (outer inner : MarkedAbsorptionCylinder ι) (coalition : Finset ι) :
    (outer.compose inner).absorbed coalition =
      outer.absorbed coalition + outer.sExit * inner.absorbed coalition := rfl

@[simp] theorem packet_compose
    (outer inner : MarkedAbsorptionCylinder ι) :
    (outer.compose inner).packet = inner.packet := rfl

@[simp] theorem entryAnchor_compose
    (outer inner : MarkedAbsorptionCylinder ι) :
    (outer.compose inner).entryAnchor = outer.entryAnchor := rfl

@[simp] theorem exitAnchor_compose
    (outer inner : MarkedAbsorptionCylinder ι) :
    (outer.compose inner).exitAnchor = inner.exitAnchor := rfl

theorem appendTail_compose
    (second third : MarkedAbsorptionCylinder ι)
    (stage : MarkedCylinderStage ι) :
    (stage.appendTail second.continueSummary).appendTail
        third.continueSummary =
      stage.appendTail (second.compose third).continueSummary := by
  rw [MarkedCylinderStage.appendTail_assoc]
  congr 1

theorem appendTail_shiftPrefix_commute
    (first third : MarkedAbsorptionCylinder ι)
    (stage : MarkedCylinderStage ι) :
    (stage.shiftPrefix first.absorbed first.exitFactor
        first.continueSummary).appendTail
        third.continueSummary =
      (stage.appendTail third.continueSummary).shiftPrefix first.absorbed
        first.exitFactor first.continueSummary := by
  exact (MarkedCylinderStage.appendTail_shiftPrefix
    third.continueSummary first.absorbed first.exitFactor
      first.continueSummary stage).symm

theorem shiftPrefix_compose
    (first second : MarkedAbsorptionCylinder ι)
    (stage : MarkedCylinderStage ι) :
    (stage.shiftPrefix second.absorbed second.exitFactor
        second.continueSummary).shiftPrefix first.absorbed first.exitFactor
          first.continueSummary =
      stage.shiftPrefix (first.compose second).absorbed
        (first.compose second).exitFactor
        (first.compose second).continueSummary := by
  rw [MarkedCylinderStage.shiftPrefix_assoc]
  rfl

/-- The source-free chronological graph obeys exact splice associativity. -/
theorem stages_compose_assoc
    (first second third : MarkedAbsorptionCylinder ι) :
    ((first.compose second).compose third).stages =
      (first.compose (second.compose third)).stages := by
  have hfirst :
      MarkedCylinderStage.appendTail third.continueSummary ''
          (MarkedCylinderStage.appendTail second.continueSummary ''
            first.stages) =
        MarkedCylinderStage.appendTail
            (second.compose third).continueSummary '' first.stages := by
    ext stage
    constructor
    · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source, hsource, (appendTail_compose second third source).symm⟩
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨source.appendTail second.continueSummary,
        ⟨source, hsource, rfl⟩, appendTail_compose second third source⟩
  have hmiddle :
      MarkedCylinderStage.appendTail third.continueSummary ''
          (MarkedCylinderStage.shiftPrefix first.absorbed first.exitFactor
            first.continueSummary '' second.stages) =
        MarkedCylinderStage.shiftPrefix first.absorbed first.exitFactor
          first.continueSummary ''
          (MarkedCylinderStage.appendTail third.continueSummary ''
            second.stages) := by
    ext stage
    constructor
    · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source.appendTail third.continueSummary,
        ⟨source, hsource, rfl⟩,
        appendTail_shiftPrefix_commute first third source⟩
    · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source.shiftPrefix first.absorbed first.exitFactor
          first.continueSummary,
        ⟨source, hsource, rfl⟩,
        (appendTail_shiftPrefix_commute first third source).symm⟩
  have hthird :
      MarkedCylinderStage.shiftPrefix (first.compose second).absorbed
          (first.compose second).exitFactor
          (first.compose second).continueSummary '' third.stages =
        MarkedCylinderStage.shiftPrefix first.absorbed first.exitFactor
          first.continueSummary ''
          (MarkedCylinderStage.shiftPrefix second.absorbed second.exitFactor
            second.continueSummary ''
            third.stages) := by
    ext stage
    constructor
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨source.shiftPrefix second.absorbed second.exitFactor
          second.continueSummary,
        ⟨source, hsource, rfl⟩,
        shiftPrefix_compose first second source⟩
    · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source, hsource, (shiftPrefix_compose first second source).symm⟩
  change
    MarkedCylinderStage.appendTail third.continueSummary ''
          (MarkedCylinderStage.appendTail second.continueSummary '' first.stages ∪
            MarkedCylinderStage.shiftPrefix first.absorbed first.exitFactor
              first.continueSummary ''
              second.stages) ∪
        MarkedCylinderStage.shiftPrefix (first.compose second).absorbed
          (first.compose second).exitFactor
          (first.compose second).continueSummary '' third.stages =
      MarkedCylinderStage.appendTail
            (second.compose third).continueSummary '' first.stages ∪
        MarkedCylinderStage.shiftPrefix first.absorbed first.exitFactor
          first.continueSummary ''
          (MarkedCylinderStage.appendTail third.continueSummary '' second.stages ∪
            MarkedCylinderStage.shiftPrefix second.absorbed second.exitFactor
              second.continueSummary ''
              third.stages)
  rw [Set.image_union, Set.image_union, hfirst, hmiddle, hthird,
    Set.union_assoc]

/-- Composition is an associative operation on the complete finite carrier. -/
theorem compose_assoc
    (first second third : MarkedAbsorptionCylinder ι) :
    (first.compose second).compose third =
      first.compose (second.compose third) := by
  apply MarkedAbsorptionCylinder.ext
  · exact stages_compose_assoc first second third
  · funext coalition
    change
      first.absorbed coalition + first.sExit * second.absorbed coalition +
          (first.compose second).sExit * third.absorbed coalition =
        first.absorbed coalition + first.sExit *
          (second.absorbed coalition + second.sExit * third.absorbed coalition)
    rw [sExit_compose]
    ring_nf
  · funext who
    simp only [compose]
    ring_nf
  · exact mul_assoc _ _ _
  · rfl
  · rfl
  · rfl
  · rfl

instance : Semigroup (MarkedAbsorptionCylinder ι) where
  mul := compose
  mul_assoc := compose_assoc

/-- Endpoint identities required of a semantic cylinder.  The chronological
graph has richer local coherence; this predicate isolates the three global
equalities needed by the holonomy and absorption projections. -/
structure IsEndpointCoherent (cylinder : MarkedAbsorptionCylinder ι) : Prop where
  prescribed_survival : ∀ who,
    (cylinder.holonomy.prescribed who).survival = cylinder.sExit
  bestResponse_survival : ∀ who,
    (cylinder.holonomy.bestResponse who).survival = cylinder.chi who
  absorbed_total :
    (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
      cylinder.absorbed coalition) = 1 - cylinder.sExit

/-- Endpoint coherence is closed under chronological composition. -/
theorem IsEndpointCoherent.compose
    {outer inner : MarkedAbsorptionCylinder ι}
    (houter : outer.IsEndpointCoherent)
    (hinner : inner.IsEndpointCoherent) :
    (outer.compose inner).IsEndpointCoherent where
  prescribed_survival who := by
    change (outer.holonomy.prescribed who).survival *
        (inner.holonomy.prescribed who).survival =
      (outer.compose inner).sExit
    rw [houter.prescribed_survival, hinner.prescribed_survival,
      sExit_compose]
  bestResponse_survival who := by
    change (outer.holonomy.bestResponse who).survival *
        (inner.holonomy.bestResponse who).survival =
      (outer.compose inner).chi who
    rw [houter.bestResponse_survival, hinner.bestResponse_survival,
      chi_compose]
  absorbed_total := by
    let coalitions := Finset.univ.erase (∅ : Finset ι)
    calc
      (∑ coalition ∈ coalitions,
          (outer.compose inner).absorbed coalition) =
          (∑ coalition ∈ coalitions, outer.absorbed coalition) +
            outer.sExit *
              (∑ coalition ∈ coalitions, inner.absorbed coalition) := by
        simp only [absorbed_compose, Finset.sum_add_distrib]
        rw [← Finset.mul_sum]
      _ = (1 - outer.sExit) + outer.sExit * (1 - inner.sExit) := by
        rw [houter.absorbed_total, hinner.absorbed_total]
      _ = 1 - (outer.compose inner).sExit := by
        rw [sExit_compose]
        ring_nf

/-- Direct row semantics of the finite graph.  Each stored local coefficient
is induced by its root, cumulative coordinates advance by that root's mass,
the prefix clock is the deleted player clock, and prefix/local/suffix affine
maps reconstruct the cylinder's complete Continue-through map. -/
structure HasRootInducedStages
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cylinder : MarkedAbsorptionCylinder ι) : Prop where
  factor_step : ∀ stage ∈ cylinder.stages, ∀ who,
    stage.postFactor who =
      stage.preFactor who * (stage.root who false).toReal
  absorption_step : ∀ stage ∈ cylinder.stages, ∀ coalition,
    stage.postAbsorbed coalition =
      stage.preAbsorbed coalition + stage.preFull *
        quittingRootCoalitionMass stage.root coalition
  quitValue_pin : ∀ stage ∈ cylinder.stages, ∀ who,
    stage.quitValue who =
      quittingFixedOpponentsQuitValue reward (fun _ => stage.root) who 0
  continueReward_pin : ∀ stage ∈ cylinder.stages, ∀ who,
    stage.continueReward who = (stage.rootContinueSummary reward who).intercept
  continueMass_pin : ∀ stage ∈ cylinder.stages, ∀ who,
    stage.continueMass who = (stage.rootContinueSummary reward who).survival
  prefix_clock : ∀ stage ∈ cylinder.stages, ∀ who,
    (stage.prefixContinue who).survival = stage.preDeleted who
  whole_continue : ∀ stage ∈ cylinder.stages, ∀ who,
    cylinder.continueSummary who =
      stage.prefixContinue who * stage.rootContinueSummary reward who *
        stage.suffixContinue who

/-- Root-induced row semantics is stable under composition.  The outer
endpoint pin is exactly what identifies its affine survival with the factor
used to translate inner prefix clocks. -/
theorem HasRootInducedStages.compose
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {outer inner : MarkedAbsorptionCylinder ι}
    (houter : outer.HasRootInducedStages reward)
    (hinner : inner.HasRootInducedStages reward)
    (houterEndpoint : outer.IsEndpointCoherent) :
    (outer.compose inner).HasRootInducedStages reward where
  factor_step stage hstage who := by
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact houter.factor_step source hsource who
    · rcases hstage with ⟨source, hsource, rfl⟩
      change outer.exitFactor who * source.postFactor who =
        outer.exitFactor who * source.preFactor who *
          (source.root who false).toReal
      rw [hinner.factor_step source hsource who]
      ring_nf
  absorption_step stage hstage coalition := by
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact houter.absorption_step source hsource coalition
    · rcases hstage with ⟨source, hsource, rfl⟩
      change
        outer.absorbed coalition + outer.sExit * source.postAbsorbed coalition =
          outer.absorbed coalition + outer.sExit * source.preAbsorbed coalition +
            fullFactor (fun who =>
              outer.exitFactor who * source.preFactor who) *
                quittingRootCoalitionMass source.root coalition
      rw [hinner.absorption_step source hsource coalition, fullFactor_mul]
      simp only [sExit, MarkedCylinderStage.preFull]
      ring_nf
  quitValue_pin stage hstage who := by
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact houter.quitValue_pin source hsource who
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact hinner.quitValue_pin source hsource who
  continueReward_pin stage hstage who := by
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact houter.continueReward_pin source hsource who
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact hinner.continueReward_pin source hsource who
  continueMass_pin stage hstage who := by
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact houter.continueMass_pin source hsource who
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact hinner.continueMass_pin source hsource who
  prefix_clock stage hstage who := by
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨source, hsource, rfl⟩
      exact houter.prefix_clock source hsource who
    · rcases hstage with ⟨source, hsource, rfl⟩
      change
        (outer.continueSummary who).survival *
            (source.prefixContinue who).survival =
          deletedFactor (fun other =>
            outer.exitFactor other * source.preFactor other) who
      rw [deletedFactor_mul, hinner.prefix_clock source hsource who]
      change
        (outer.holonomy.bestResponse who).survival *
            source.preDeleted who = outer.chi who * source.preDeleted who
      rw [houterEndpoint.bestResponse_survival]
  whole_continue stage hstage who := by
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨source, hsource, rfl⟩
      rw [continueSummary_compose,
        houter.whole_continue source hsource who]
      change
        (source.prefixContinue who * source.rootContinueSummary reward who *
            source.suffixContinue who) * inner.continueSummary who =
          source.prefixContinue who * source.rootContinueSummary reward who *
            (source.suffixContinue who * inner.continueSummary who)
      exact mul_assoc _ _ _
    · rcases hstage with ⟨source, hsource, rfl⟩
      rw [continueSummary_compose,
        hinner.whole_continue source hsource who]
      change
        outer.continueSummary who *
            (source.prefixContinue who * source.rootContinueSummary reward who *
              source.suffixContinue who) =
          (outer.continueSummary who * source.prefixContinue who) *
            source.rootContinueSummary reward who * source.suffixContinue who
      simp only [mul_assoc]

/-- The unilateral `early` coordinate is exactly the maximum of the finitely
many full-prefix deterministic quit payoffs carried by the stage graph.  The
attainment clause avoids any order-topological supremum machinery. -/
structure HasExactObstacleCap
    (cylinder : MarkedAbsorptionCylinder ι) : Prop where
  upper : ∀ who stage, stage ∈ cylinder.stages →
    stage.pureQuitPayoff who ≤ (cylinder.holonomy.bestResponse who).early
  attained : ∀ who, ∃ stage ∈ cylinder.stages,
    stage.pureQuitPayoff who = (cylinder.holonomy.bestResponse who).early

/-- Exact finite obstacle caps are stable under chronological composition. -/
theorem HasExactObstacleCap.compose
    {outer inner : MarkedAbsorptionCylinder ι}
    (houter : outer.HasExactObstacleCap)
    (hinner : inner.HasExactObstacleCap) :
    (outer.compose inner).HasExactObstacleCap where
  upper who stage hstage := by
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨source, hsource, rfl⟩
      have hvalue := houter.upper who source hsource
      rw [MarkedCylinderStage.pureQuitPayoff_appendTail]
      change source.pureQuitPayoff who ≤
        max (outer.holonomy.bestResponse who).early
          ((outer.holonomy.bestResponse who).tail +
            (outer.holonomy.bestResponse who).survival *
              (inner.holonomy.bestResponse who).early)
      exact hvalue.trans (le_max_left _ _)
    · rcases hstage with ⟨source, hsource, rfl⟩
      have hvalue := hinner.upper who source hsource
      have hscaled := mul_le_mul_of_nonneg_left hvalue
        (outer.holonomy.bestResponse who).survival_nonneg
      have hcontinue :
          (outer.holonomy.bestResponse who).tail +
                (outer.holonomy.bestResponse who).survival *
                  source.pureQuitPayoff who ≤
            (outer.holonomy.bestResponse who).tail +
              (outer.holonomy.bestResponse who).survival *
                (inner.holonomy.bestResponse who).early :=
        by linarith
      rw [MarkedCylinderStage.pureQuitPayoff_shiftPrefix]
      change
        (outer.holonomy.bestResponse who).tail +
            (outer.holonomy.bestResponse who).survival *
              source.pureQuitPayoff who ≤
          max (outer.holonomy.bestResponse who).early
            ((outer.holonomy.bestResponse who).tail +
              (outer.holonomy.bestResponse who).survival *
                (inner.holonomy.bestResponse who).early)
      exact hcontinue.trans (le_max_right _ _)
  attained who := by
    rcases le_total (outer.holonomy.bestResponse who).early
        ((outer.holonomy.bestResponse who).tail +
          (outer.holonomy.bestResponse who).survival *
            (inner.holonomy.bestResponse who).early) with hright | hleft
    · obtain ⟨source, hsource, hvalue⟩ := hinner.attained who
      refine ⟨source.shiftPrefix outer.absorbed outer.exitFactor
          outer.continueSummary, ?_, ?_⟩
      · exact Set.mem_union_right _ ⟨source, hsource, rfl⟩
      · rw [MarkedCylinderStage.pureQuitPayoff_shiftPrefix, hvalue]
        change
          (outer.holonomy.bestResponse who).tail +
              (outer.holonomy.bestResponse who).survival *
                (inner.holonomy.bestResponse who).early =
            max (outer.holonomy.bestResponse who).early
              ((outer.holonomy.bestResponse who).tail +
                (outer.holonomy.bestResponse who).survival *
                  (inner.holonomy.bestResponse who).early)
        exact (max_eq_right hright).symm
    · obtain ⟨source, hsource, hvalue⟩ := houter.attained who
      refine ⟨source.appendTail inner.continueSummary, ?_, ?_⟩
      · exact Set.mem_union_left _ ⟨source, hsource, rfl⟩
      · rw [MarkedCylinderStage.pureQuitPayoff_appendTail, hvalue]
        change
          (outer.holonomy.bestResponse who).early =
            max (outer.holonomy.bestResponse who).early
              ((outer.holonomy.bestResponse who).tail +
                (outer.holonomy.bestResponse who).survival *
                  (inner.holonomy.bestResponse who).early)
        exact (max_eq_left hleft).symm

/-- Prescribed evaluation at an arbitrary exit payoff. -/
def prescribedValue (cylinder : MarkedAbsorptionCylinder ι)
    (who : ι) (terminalValue : ℝ) : ℝ :=
  (cylinder.holonomy.prescribed who).eval terminalValue

/-- Unilateral best-response evaluation at an arbitrary exit payoff. -/
def unilateralValue (cylinder : MarkedAbsorptionCylinder ι)
    (who : ι) (terminalValue : ℝ) : ℝ :=
  (cylinder.holonomy.bestResponse who).eval terminalValue

theorem prescribedValue_compose
    (outer inner : MarkedAbsorptionCylinder ι)
    (who : ι) (terminalValue : ℝ) :
    (outer.compose inner).prescribedValue who terminalValue =
      outer.prescribedValue who
        (inner.prescribedValue who terminalValue) := by
  exact QuittingAffineSummary.eval_mul _ _ _

theorem unilateralValue_compose
    (outer inner : MarkedAbsorptionCylinder ι)
    (who : ι) (terminalValue : ℝ) :
    (outer.compose inner).unilateralValue who terminalValue =
      outer.unilateralValue who
        (inner.unilateralValue who terminalValue) := by
  exact QuittingMaxAffineSummary.eval_mul _ _ _

/-! ## Encoding the production realized adapter -/

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Source-free coalition absorption accumulated over a root segment. -/
def finiteAbsorptionValue (roots : ℕ → ι → PMF Bool)
    (start fuel : ℕ) (coalition : Finset ι) : ℝ :=
  ∑ offset : Fin fuel,
    Math.survivalProduct
        (fun time => quittingStationaryContinueMass (roots time))
        start offset.val *
      quittingRootCoalitionMass (roots (start + offset.val)) coalition

theorem quittingRootCoalitionMass_nonneg
    (root : ι → PMF Bool) (coalition : Finset ι) :
    0 ≤ quittingRootCoalitionMass root coalition := by
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  apply mul_nonneg
  · exact Finset.prod_nonneg fun who _ => ENNReal.toReal_nonneg
  · exact Finset.prod_nonneg fun who _ => sub_nonneg.mpr (by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (root who) true))

theorem finiteAbsorptionValue_nonneg
    (roots : ℕ → ι → PMF Bool) (start fuel : ℕ)
    (coalition : Finset ι) :
    0 ≤ finiteAbsorptionValue roots start fuel coalition := by
  exact Finset.sum_nonneg fun offset _ =>
    mul_nonneg
      (Math.survivalProduct_nonneg _
        (fun _ => quittingStationaryContinueMass_nonneg _) _ _)
      (quittingRootCoalitionMass_nonneg _ _)

omit [Fintype ι] [DecidableEq ι] in
theorem playerContinueFactor_nonneg
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    0 ≤ MarkedObstacleRecord.playerContinueFactor roots who start fuel := by
  exact Math.survivalProduct_nonneg _
    (fun _ => ENNReal.toReal_nonneg) start fuel

omit [Fintype ι] [DecidableEq ι] in
theorem playerContinueFactor_le_one
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    MarkedObstacleRecord.playerContinueFactor roots who start fuel ≤ 1 := by
  exact Math.survivalProduct_le_one _
    (fun _ => ENNReal.toReal_nonneg)
    (fun time => by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (roots time who) false)) start fuel

/-- Coalition absorption splits affinely at every chronological cut. -/
theorem finiteAbsorptionValue_add
    (roots : ℕ → ι → PMF Bool) (start first second : ℕ)
    (coalition : Finset ι) :
    finiteAbsorptionValue roots start (first + second) coalition =
      finiteAbsorptionValue roots start first coalition +
        Math.survivalProduct
            (fun time => quittingStationaryContinueMass (roots time))
            start first *
          finiteAbsorptionValue roots (start + first) second coalition := by
  unfold finiteAbsorptionValue
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro offset _
  change
    Math.survivalProduct
          (fun time => quittingStationaryContinueMass (roots time))
          start (first + offset.val) *
        quittingRootCoalitionMass
          (roots (start + (first + offset.val))) coalition =
      Math.survivalProduct
            (fun time => quittingStationaryContinueMass (roots time))
            start first *
          (Math.survivalProduct
              (fun time => quittingStationaryContinueMass (roots time))
              (start + first) offset.val *
            quittingRootCoalitionMass
              (roots ((start + first) + offset.val)) coalition)
  rw [Math.survivalProduct_add]
  ring_nf

/-- Always-Continue boundary evaluation splits without dividing by survival. -/
theorem quittingFiniteContinueToBoundaryValue_append
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start first second : ℕ) :
    quittingFiniteContinueToBoundaryValue reward roots who 0 start
        (first + second) =
      quittingFiniteContinueToBoundaryValue reward roots who 0 start first +
        quittingOpponentSurvivalWeight roots who start first *
          quittingFiniteContinueToBoundaryValue reward roots who 0
            (start + first) second := by
  induction first generalizing start with
  | zero =>
      simp [quittingFiniteContinueToBoundaryValue,
        quittingOpponentSurvivalWeight]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [quittingFiniteContinueToBoundaryValue]
      rw [ih (start + 1), quittingOpponentSurvivalWeight_succ_front]
      have hindex : start + 1 + first = start + (first + 1) := by omega
      rw [hindex]
      ring_nf

/-- Division-free affine Continue-through summary of an arbitrary root
segment, including the empty segment. -/
def continueSegmentSummary (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) : QuittingAffineSummary where
  intercept := quittingFiniteContinueToBoundaryValue reward roots who 0
    start fuel
  survival := quittingOpponentSurvivalWeight roots who start fuel
  survival_nonneg := quittingOpponentSurvivalWeight_nonneg roots who start fuel

/-- Continue-through summaries compose under chronological segment splitting. -/
theorem continueSegmentSummary_add
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start first second : ℕ) :
    continueSegmentSummary (reward := reward) roots who start
        (first + second) =
      continueSegmentSummary (reward := reward) roots who start first *
        continueSegmentSummary (reward := reward) roots who
          (start + first) second := by
  apply QuittingAffineSummary.ext
  · exact quittingFiniteContinueToBoundaryValue_append
      roots who start first second
  · exact quittingOpponentSurvivalWeight_add
      roots who start first second

/-- Payoff of continuing through `offset` rows and then quitting.  This is the
literal obstacle ordinate represented by a stage's affine prefix mark. -/
def finitePrefixQuitValue (roots : ℕ → ι → PMF Bool) (who : ι)
    (start offset : ℕ) : ℝ :=
  quittingFiniteContinueToBoundaryValue reward roots who 0 start offset +
    quittingOpponentSurvivalWeight roots who start offset *
      quittingFixedOpponentsQuitValue reward roots who (start + offset)

@[simp] theorem finitePrefixQuitValue_zero
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    finitePrefixQuitValue (reward := reward) roots who start 0 =
      quittingFixedOpponentsQuitValue reward roots who start := by
  simp [finitePrefixQuitValue, quittingFiniteContinueToBoundaryValue,
    quittingOpponentSurvivalWeight]

theorem finitePrefixQuitValue_succ
    (roots : ℕ → ι → PMF Bool) (who : ι) (start offset : ℕ) :
    finitePrefixQuitValue (reward := reward) roots who start (offset + 1) =
      quittingFixedOpponentsContinueReward reward roots who start +
        quittingFixedOpponentsContinueMass roots who start *
          finitePrefixQuitValue (reward := reward) roots who
            (start + 1) offset := by
  unfold finitePrefixQuitValue
  rw [quittingFiniteContinueToBoundaryValue,
    quittingOpponentSurvivalWeight_succ_front]
  have htime : start + 1 + offset = start + (offset + 1) := by omega
  rw [htime]
  ring_nf

/-- Every displayed deterministic quit date lies below the finite Bellman
early-stop value. -/
theorem finitePrefixQuitValue_le_early
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ (start extra : ℕ) (offset : Fin (extra + 1)),
      finitePrefixQuitValue (reward := reward) roots who start offset.val ≤
        quittingFiniteEarlyBestResponseValue reward roots who start extra := by
  intro start extra
  induction extra generalizing start with
  | zero =>
      intro offset
      have hoffset : offset = 0 := Fin.eq_zero offset
      subst offset
      change finitePrefixQuitValue (reward := reward) roots who start 0 ≤
        quittingFiniteEarlyBestResponseValue reward roots who start 0
      rw [finitePrefixQuitValue_zero,
        quittingFiniteEarlyBestResponseValue]
  | succ extra ih =>
      intro offset
      refine Fin.cases ?_ (fun later => ?_) offset
      · change finitePrefixQuitValue (reward := reward) roots who start 0 ≤ _
        rw [finitePrefixQuitValue_zero,
          quittingFiniteEarlyBestResponseValue]
        exact le_max_left _ _
      · change finitePrefixQuitValue (reward := reward) roots who start
          (later.val + 1) ≤ _
        rw [finitePrefixQuitValue_succ,
          quittingFiniteEarlyBestResponseValue]
        have hlater := ih (start + 1) later
        have hmass :
            0 ≤ quittingFixedOpponentsContinueMass roots who start :=
          quittingStationaryContinueMass_nonneg
            (Function.update (roots start) who (PMF.pure false))
        have hscaled := mul_le_mul_of_nonneg_left hlater hmass
        have hcontinue :
            quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    finitePrefixQuitValue (reward := reward) roots who
                      (start + 1) later.val ≤
              quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteEarlyBestResponseValue reward roots who
                    (start + 1) extra := by
          linarith
        exact hcontinue.trans (le_max_right _ _)

/-- The finite early-stop value is attained by one displayed deterministic
quit date; there is no zero-boundary `never` sentinel in this witness. -/
theorem exists_finitePrefixQuitValue_eq_early
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ (start extra : ℕ), ∃ offset : Fin (extra + 1),
      finitePrefixQuitValue (reward := reward) roots who start offset.val =
        quittingFiniteEarlyBestResponseValue reward roots who start extra := by
  intro start extra
  induction extra generalizing start with
  | zero =>
      refine ⟨0, ?_⟩
      change finitePrefixQuitValue (reward := reward) roots who start 0 = _
      rw [finitePrefixQuitValue_zero,
        quittingFiniteEarlyBestResponseValue]
  | succ extra ih =>
      obtain ⟨later, hlater⟩ := ih (start + 1)
      by_cases hcontinue :
          quittingFixedOpponentsQuitValue reward roots who start ≤
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteEarlyBestResponseValue reward roots who
                  (start + 1) extra
      · refine ⟨Fin.succ later, ?_⟩
        change finitePrefixQuitValue (reward := reward) roots who start
          (later.val + 1) = _
        rw [finitePrefixQuitValue_succ, hlater,
          quittingFiniteEarlyBestResponseValue, max_eq_right hcontinue]
      · refine ⟨0, ?_⟩
        change finitePrefixQuitValue (reward := reward) roots who start 0 = _
        rw [finitePrefixQuitValue_zero,
          quittingFiniteEarlyBestResponseValue,
          max_eq_left (le_of_not_ge hcontinue)]

omit [Fintype ι] [DecidableEq ι] in
/-- Playerwise continue factors split at every chronological cut. -/
theorem playerContinueFactor_add
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start first second : ℕ) :
    MarkedObstacleRecord.playerContinueFactor roots who start
        (first + second) =
      MarkedObstacleRecord.playerContinueFactor roots who start first *
        MarkedObstacleRecord.playerContinueFactor roots who
          (start + first) second := by
  exact Math.survivalProduct_add _ start first second

theorem absorptionPathValue_succ [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : Fin realized.block.length) (coalition : Finset ι) :
    realized.absorptionPathValue (offset.val + 1) (by omega) coalition =
      realized.absorptionPathValue offset.val (by omega) coalition +
        realizedBlockFullSurvival realized.block offset.val (by omega) *
          realized.absorptionAtom offset.val (by omega) coalition := by
  unfold RealizedMarkedAbsorptionCylinder.absorptionPathValue
  rw [Fin.sum_univ_castSucc]
  rfl

/-- The source-free joint record of one realized stage. -/
def stageOfRealized [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (cylinder : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : Fin cylinder.block.length) : MarkedCylinderStage ι :=
  let time := cylinder.block.start + offset.val
  let remaining := cylinder.block.extra - offset.val
  { root := anchor.roots time
    preFactor := fun who =>
      MarkedObstacleRecord.playerContinueFactor anchor.roots who
        cylinder.block.start offset.val
    postFactor := fun who =>
      MarkedObstacleRecord.playerContinueFactor anchor.roots who
        cylinder.block.start (offset.val + 1)
    preAbsorbed := fun coalition =>
      cylinder.absorptionPathValue offset.val (by omega) coalition
    postAbsorbed := fun coalition =>
      cylinder.absorptionPathValue (offset.val + 1) (by omega) coalition
    quitValue := fun who =>
      quittingFixedOpponentsQuitValue reward anchor.roots who time
    continueReward := fun who =>
      quittingFixedOpponentsContinueReward reward anchor.roots who time
    continueMass := fun who =>
      quittingFixedOpponentsContinueMass anchor.roots who time
    prefixContinue := fun who =>
      continueSegmentSummary (reward := reward) anchor.roots who
        cylinder.block.start offset.val
    suffixContinue := fun who =>
      continueSegmentSummary (reward := reward) anchor.roots who
        (time + 1) remaining }

theorem stageOfRealized_postFactor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : Fin realized.block.length) (who : ι) :
    (stageOfRealized realized offset).postFactor who =
      (stageOfRealized realized offset).preFactor who *
        ((stageOfRealized realized offset).root who false).toReal := by
  exact MarkedObstacleRecord.playerContinueFactor_succ
    anchor.roots who realized.block.start offset.val

theorem stageOfRealized_postAbsorbed [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : Fin realized.block.length) (coalition : Finset ι) :
    (stageOfRealized realized offset).postAbsorbed coalition =
      (stageOfRealized realized offset).preAbsorbed coalition +
        (stageOfRealized realized offset).preFull *
          realized.absorptionAtom offset.val (by omega) coalition := by
  change
    realized.absorptionPathValue (offset.val + 1) (by omega) coalition =
      realized.absorptionPathValue offset.val (by omega) coalition +
        fullFactor (fun who =>
          MarkedObstacleRecord.playerContinueFactor anchor.roots who
            realized.block.start offset.val) *
          realized.absorptionAtom offset.val (by omega) coalition
  have hfactor :
      fullFactor (fun who =>
          MarkedObstacleRecord.playerContinueFactor anchor.roots who
            realized.block.start offset.val) =
        realizedBlockFullSurvival realized.block offset.val (by omega) := by
    simpa [fullFactor, realizedBlockFullSurvival] using
      (MarkedObstacleRecord.prod_playerContinueFactor_eq_survival
        anchor.roots realized.block.start offset.val)
  rw [absorptionPathValue_succ]
  rw [hfactor]

theorem stageOfRealized_rootContinueSummary [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : Fin realized.block.length) (who : ι) :
    (stageOfRealized realized offset).rootContinueSummary reward who =
      continueSegmentSummary (reward := reward) anchor.roots who
        (realized.block.start + offset.val) 1 := by
  apply QuittingAffineSummary.ext
  · change
      quittingFixedOpponentsContinueReward reward anchor.roots who
          (realized.block.start + offset.val) =
        quittingFiniteContinueToBoundaryValue reward anchor.roots who 0
          (realized.block.start + offset.val) 1
    simp [quittingFiniteContinueToBoundaryValue]
  · change
      quittingFixedOpponentsContinueMass anchor.roots who
          (realized.block.start + offset.val) =
        quittingOpponentSurvivalWeight anchor.roots who
          (realized.block.start + offset.val) 1
    rw [quittingOpponentSurvivalWeight_succ_front]
    simp [quittingOpponentSurvivalWeight]

/-- Every player projection of a joint stage is exactly the landed one-row
source-free record. -/
theorem stageOfRealized_toObstacleRecord [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : Fin realized.block.length) (who : ι) :
    (stageOfRealized realized offset).toObstacleRecord who =
      MarkedObstacleRecord.ofRealizedStage realized who offset := by
  simp [MarkedCylinderStage.toObstacleRecord, stageOfRealized,
    MarkedCylinderStage.preFull, MarkedCylinderStage.postFull,
    MarkedCylinderStage.preDeleted, MarkedCylinderStage.postDeleted,
    MarkedCylinderStage.obstacle, fullFactor, deletedFactor,
    continueSegmentSummary,
    MarkedObstacleRecord.ofRealizedStage,
    MarkedObstacleRecord.prod_playerContinueFactor_eq_survival,
    MarkedObstacleRecord.prod_playerContinueFactor_erase_eq_opponentSurvivalWeight,
    realizedBlockFullSurvival]

/-- Encode a realized block and then forget its source and literal horizon. -/
def ofRealized [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    MarkedAbsorptionCylinder ι where
  stages := Set.range (stageOfRealized realized)
  stages_finite := Set.finite_range _
  absorbed := fun coalition =>
    realized.absorptionPathValue realized.block.length le_rfl coalition
  exitFactor := fun who =>
    MarkedObstacleRecord.playerContinueFactor anchor.roots who
      realized.block.start realized.block.length
  holonomy := realized.block.holonomy
  packet :=
    { owner := anchor.owner
      action := anchor.action
      kernel := Function.update (anchor.roots anchor.last) anchor.owner
        (PMF.pure false)
      preterminalSurvival := realized.preterminalSurvival
      terminalMass := realized.terminalMass
      advantage := realized.advantage }
  entryDebt := realized.entryDebt
  entryAnchor := realized.entryAnchor
  exitAnchor := realized.exitAnchor

/-- Continue-through holonomy of an encoded realized block, in literal source
coordinates. -/
theorem ofRealized_continueSummary [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) :
    (ofRealized realized).continueSummary who =
      continueSegmentSummary (reward := reward) anchor.roots who
        realized.block.start realized.block.length := by
  apply QuittingAffineSummary.ext
  · exact quittingFiniteBoundaryHolonomy_bestResponse_tail
      reward anchor.roots realized.block.start realized.block.extra who
  · exact quittingFiniteBoundaryHolonomy_bestResponse_survival
      reward anchor.roots realized.block.start realized.block.extra who

/-- Every realized encoder has root-induced row transitions and an exact
prefix/local/suffix factorization of its Continue-through map. -/
theorem ofRealized_hasRootInducedStages [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).HasRootInducedStages reward where
  factor_step stage hstage who := by
    rcases hstage with ⟨offset, rfl⟩
    exact stageOfRealized_postFactor realized offset who
  absorption_step stage hstage coalition := by
    rcases hstage with ⟨offset, rfl⟩
    change
      (stageOfRealized realized offset).postAbsorbed coalition =
        (stageOfRealized realized offset).preAbsorbed coalition +
          (stageOfRealized realized offset).preFull *
            quittingRootCoalitionMass
              (anchor.roots (realized.block.start + offset.val)) coalition
    exact stageOfRealized_postAbsorbed realized offset coalition
  quitValue_pin stage hstage who := by
    rcases hstage with ⟨offset, rfl⟩
    rfl
  continueReward_pin stage hstage who := by
    rcases hstage with ⟨offset, rfl⟩
    rfl
  continueMass_pin stage hstage who := by
    rcases hstage with ⟨offset, rfl⟩
    rfl
  prefix_clock stage hstage who := by
    rcases hstage with ⟨offset, rfl⟩
    change
      quittingOpponentSurvivalWeight anchor.roots who
          realized.block.start offset.val =
        deletedFactor (fun player =>
          MarkedObstacleRecord.playerContinueFactor anchor.roots player
            realized.block.start offset.val) who
    exact (MarkedObstacleRecord.prod_playerContinueFactor_erase_eq_opponentSurvivalWeight
      anchor.roots who realized.block.start offset.val).symm
  whole_continue stage hstage who := by
    rcases hstage with ⟨offset, rfl⟩
    have hoffset : offset.val ≤ realized.block.extra := by
      have hoff := offset.isLt
      change offset.val < realized.block.extra + 1 at hoff
      omega
    let remaining := realized.block.extra - offset.val
    have hlength : realized.block.length =
        offset.val + (1 + remaining) := by
      change realized.block.extra + 1 =
        offset.val + (1 + (realized.block.extra - offset.val))
      omega
    rw [ofRealized_continueSummary,
      stageOfRealized_rootContinueSummary]
    change
      continueSegmentSummary (reward := reward) anchor.roots who
          realized.block.start realized.block.length =
        continueSegmentSummary (reward := reward) anchor.roots who
            realized.block.start offset.val *
          continueSegmentSummary (reward := reward) anchor.roots who
              (realized.block.start + offset.val) 1 *
            continueSegmentSummary (reward := reward) anchor.roots who
              (realized.block.start + offset.val + 1) remaining
    calc
      continueSegmentSummary (reward := reward) anchor.roots who
          realized.block.start realized.block.length =
        continueSegmentSummary (reward := reward) anchor.roots who
          realized.block.start (offset.val + (1 + remaining)) :=
        congrArg (fun fuel =>
          continueSegmentSummary (reward := reward) anchor.roots who
            realized.block.start fuel) hlength
      _ = continueSegmentSummary (reward := reward) anchor.roots who
              realized.block.start offset.val *
            continueSegmentSummary (reward := reward) anchor.roots who
                (realized.block.start + offset.val) 1 *
              continueSegmentSummary (reward := reward) anchor.roots who
                (realized.block.start + offset.val + 1) remaining := by
        rw [continueSegmentSummary_add, continueSegmentSummary_add]
        exact (mul_assoc _ _ _).symm

/-- Embed an outer-block offset into the concatenated block. -/
def concatLeftOffset [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (offset : Fin outer.block.length) :
    Fin (outer.concat inner hadjacent).block.length :=
  ⟨offset.val, by
    rw [RealizedMarkedAbsorptionCylinder.length_concat]
    omega⟩

/-- Embed an inner-block offset after the outer block. -/
def concatRightOffset [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (offset : Fin inner.block.length) :
    Fin (outer.concat inner hadjacent).block.length :=
  ⟨outer.block.length + offset.val, by
    rw [RealizedMarkedAbsorptionCylinder.length_concat]
    omega⟩

theorem stageOfRealized_concat_left_suffixContinue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (offset : Fin outer.block.length) (who : ι) :
    (stageOfRealized (outer.concat inner hadjacent)
        (concatLeftOffset outer inner hadjacent offset)).suffixContinue who =
      (stageOfRealized outer offset).suffixContinue who *
        (ofRealized inner).continueSummary who := by
  have hoffset : offset.val ≤ outer.block.extra := by
    have hoff := offset.isLt
    change offset.val < outer.block.extra + 1 at hoff
    omega
  have hremaining :
      (outer.block.extra + inner.block.extra + 1) - offset.val =
        (outer.block.extra - offset.val) + inner.block.length := by
    simp only [QuittingAnchoredBoundaryBlock.length]
    omega
  have hseam :
      outer.block.start + offset.val + 1 +
          (outer.block.extra - offset.val) = inner.block.start := by
    rw [hadjacent]
    simp only [QuittingAnchoredBoundaryBlock.length]
    omega
  rw [ofRealized_continueSummary]
  change
    continueSegmentSummary (reward := reward) anchor.roots who
        (outer.block.start + offset.val + 1)
        ((outer.block.extra + inner.block.extra + 1) - offset.val) =
      continueSegmentSummary (reward := reward) anchor.roots who
          (outer.block.start + offset.val + 1)
          (outer.block.extra - offset.val) *
        continueSegmentSummary (reward := reward) anchor.roots who
          inner.block.start inner.block.length
  rw [hremaining, continueSegmentSummary_add, hseam]

/-- An outer stage embeds exactly into the concatenated source-free graph; its
only transported coordinate is the appended affine suffix. -/
theorem stageOfRealized_concat_left [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (offset : Fin outer.block.length) :
    stageOfRealized (outer.concat inner hadjacent)
        (concatLeftOffset outer inner hadjacent offset) =
      (stageOfRealized outer offset).appendTail
        (ofRealized inner).continueSummary := by
  apply MarkedCylinderStage.ext
  · change anchor.roots (outer.block.start + offset.val) =
      anchor.roots (outer.block.start + offset.val)
    rfl
  · change
      (fun who => MarkedObstacleRecord.playerContinueFactor anchor.roots who
        outer.block.start offset.val) = _
    rfl
  · change
      (fun who => MarkedObstacleRecord.playerContinueFactor anchor.roots who
        outer.block.start (offset.val + 1)) = _
    rfl
  · funext coalition
    change finiteAbsorptionValue anchor.roots outer.block.start offset.val
        coalition =
      finiteAbsorptionValue anchor.roots outer.block.start offset.val coalition
    rfl
  · funext coalition
    change finiteAbsorptionValue anchor.roots outer.block.start
        (offset.val + 1) coalition =
      finiteAbsorptionValue anchor.roots outer.block.start
        (offset.val + 1) coalition
    rfl
  · change
      (fun who => quittingFixedOpponentsQuitValue reward anchor.roots who
        (outer.block.start + offset.val)) = _
    rfl
  · change
      (fun who => quittingFixedOpponentsContinueReward reward anchor.roots who
        (outer.block.start + offset.val)) = _
    rfl
  · change
      (fun who => quittingFixedOpponentsContinueMass anchor.roots who
        (outer.block.start + offset.val)) = _
    rfl
  · rfl
  · funext who
    exact stageOfRealized_concat_left_suffixContinue
      outer inner hadjacent offset who

theorem stageOfRealized_concat_right_suffixContinue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (offset : Fin inner.block.length) (who : ι) :
    (stageOfRealized (outer.concat inner hadjacent)
        (concatRightOffset outer inner hadjacent offset)).suffixContinue who =
      (stageOfRealized inner offset).suffixContinue who := by
  have hoffset : offset.val ≤ inner.block.extra := by
    have hoff := offset.isLt
    change offset.val < inner.block.extra + 1 at hoff
    omega
  have htime :
      outer.block.start + (outer.block.length + offset.val) =
        inner.block.start + offset.val := by
    omega
  have hremaining :
      (outer.block.extra + inner.block.extra + 1) -
          (outer.block.length + offset.val) =
        inner.block.extra - offset.val := by
    simp only [QuittingAnchoredBoundaryBlock.length]
    omega
  change
    continueSegmentSummary (reward := reward) anchor.roots who
        (outer.block.start + (outer.block.length + offset.val) + 1)
        ((outer.block.extra + inner.block.extra + 1) -
          (outer.block.length + offset.val)) =
      continueSegmentSummary (reward := reward) anchor.roots who
        (inner.block.start + offset.val + 1)
        (inner.block.extra - offset.val)
  rw [htime, hremaining]

theorem stageOfRealized_concat_right_prefixContinue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (offset : Fin inner.block.length) (who : ι) :
    (stageOfRealized (outer.concat inner hadjacent)
        (concatRightOffset outer inner hadjacent offset)).prefixContinue who =
      (ofRealized outer).continueSummary who *
        (stageOfRealized inner offset).prefixContinue who := by
  have hseam : outer.block.start + outer.block.length = inner.block.start :=
    hadjacent.symm
  rw [ofRealized_continueSummary]
  change
    continueSegmentSummary (reward := reward) anchor.roots who
        outer.block.start (outer.block.length + offset.val) =
      continueSegmentSummary (reward := reward) anchor.roots who
          outer.block.start outer.block.length *
        continueSegmentSummary (reward := reward) anchor.roots who
          inner.block.start offset.val
  rw [continueSegmentSummary_add, hseam]

/-- An inner stage embeds exactly after translating its cumulative absorption
and player-factor clocks by the outer endpoint. -/
theorem stageOfRealized_concat_right [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (offset : Fin inner.block.length) :
    stageOfRealized (outer.concat inner hadjacent)
        (concatRightOffset outer inner hadjacent offset) =
      (stageOfRealized inner offset).shiftPrefix
        (ofRealized outer).absorbed (ofRealized outer).exitFactor
          (ofRealized outer).continueSummary := by
  have hseam : outer.block.start + outer.block.length = inner.block.start :=
    hadjacent.symm
  have htime :
      outer.block.start + (outer.block.length + offset.val) =
        inner.block.start + offset.val := by
    omega
  have hfull :
      fullFactor (fun who =>
          MarkedObstacleRecord.playerContinueFactor anchor.roots who
            outer.block.start outer.block.length) =
        Math.survivalProduct
          (fun time => quittingStationaryContinueMass (anchor.roots time))
          outer.block.start outer.block.length := by
    exact MarkedObstacleRecord.prod_playerContinueFactor_eq_survival
      anchor.roots outer.block.start outer.block.length
  apply MarkedCylinderStage.ext
  · change anchor.roots
      (outer.block.start + (outer.block.length + offset.val)) =
        anchor.roots (inner.block.start + offset.val)
    rw [htime]
  · funext who
    change
      MarkedObstacleRecord.playerContinueFactor anchor.roots who
          outer.block.start (outer.block.length + offset.val) =
        MarkedObstacleRecord.playerContinueFactor anchor.roots who
            outer.block.start outer.block.length *
          MarkedObstacleRecord.playerContinueFactor anchor.roots who
            inner.block.start offset.val
    rw [playerContinueFactor_add, hseam]
  · funext who
    change
      MarkedObstacleRecord.playerContinueFactor anchor.roots who
          outer.block.start (outer.block.length + (offset.val + 1)) =
        MarkedObstacleRecord.playerContinueFactor anchor.roots who
            outer.block.start outer.block.length *
          MarkedObstacleRecord.playerContinueFactor anchor.roots who
            inner.block.start (offset.val + 1)
    rw [playerContinueFactor_add, hseam]
  · funext coalition
    change finiteAbsorptionValue anchor.roots outer.block.start
        (outer.block.length + offset.val) coalition =
      finiteAbsorptionValue anchor.roots outer.block.start
          outer.block.length coalition +
        fullFactor (fun who =>
          MarkedObstacleRecord.playerContinueFactor anchor.roots who
            outer.block.start outer.block.length) *
          finiteAbsorptionValue anchor.roots inner.block.start offset.val
            coalition
    rw [finiteAbsorptionValue_add, hfull, hseam]
  · funext coalition
    change finiteAbsorptionValue anchor.roots outer.block.start
        (outer.block.length + (offset.val + 1)) coalition =
      finiteAbsorptionValue anchor.roots outer.block.start
          outer.block.length coalition +
        fullFactor (fun who =>
          MarkedObstacleRecord.playerContinueFactor anchor.roots who
            outer.block.start outer.block.length) *
          finiteAbsorptionValue anchor.roots inner.block.start
            (offset.val + 1) coalition
    rw [finiteAbsorptionValue_add, hfull, hseam]
  · change
      (fun who => quittingFixedOpponentsQuitValue reward anchor.roots who
        (outer.block.start + (outer.block.length + offset.val))) =
      (fun who => quittingFixedOpponentsQuitValue reward anchor.roots who
        (inner.block.start + offset.val))
    rw [htime]
  · change
      (fun who => quittingFixedOpponentsContinueReward reward anchor.roots who
        (outer.block.start + (outer.block.length + offset.val))) =
      (fun who => quittingFixedOpponentsContinueReward reward anchor.roots who
        (inner.block.start + offset.val))
    rw [htime]
  · change
      (fun who => quittingFixedOpponentsContinueMass anchor.roots who
        (outer.block.start + (outer.block.length + offset.val))) =
      (fun who => quittingFixedOpponentsContinueMass anchor.roots who
        (inner.block.start + offset.val))
    rw [htime]
  · funext who
    exact stageOfRealized_concat_right_prefixContinue
      outer inner hadjacent offset who
  · funext who
    exact stageOfRealized_concat_right_suffixContinue
      outer inner hadjacent offset who

@[simp] theorem stageOfRealized_mem [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : Fin realized.block.length) :
    stageOfRealized realized offset ∈ (ofRealized realized).stages :=
  ⟨offset, rfl⟩

theorem stageOfRealized_pureQuitPayoff [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : Fin realized.block.length) (who : ι) :
    (stageOfRealized realized offset).pureQuitPayoff who =
      finitePrefixQuitValue (reward := reward) anchor.roots who
        realized.block.start offset.val := by
  change
    (continueSegmentSummary (reward := reward) anchor.roots who
      realized.block.start offset.val).eval
        (quittingFixedOpponentsQuitValue reward anchor.roots who
          (realized.block.start + offset.val)) = _
  rfl

/-- The realized encoder carries the exact finite obstacle cap, including an
actual maximizing chronological stage. -/
theorem ofRealized_hasExactObstacleCap [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).HasExactObstacleCap where
  upper who stage hstage := by
    rcases hstage with ⟨offset, rfl⟩
    rw [stageOfRealized_pureQuitPayoff]
    change
      finitePrefixQuitValue (reward := reward) anchor.roots who
          realized.block.start offset.val ≤
        ((quittingFiniteBoundaryHolonomy reward anchor.roots
          realized.block.start realized.block.extra).bestResponse who).early
    rw [quittingFiniteBoundaryHolonomy_bestResponse_early]
    exact finitePrefixQuitValue_le_early anchor.roots who
      realized.block.start realized.block.extra offset
  attained who := by
    obtain ⟨offset, hvalue⟩ :=
      exists_finitePrefixQuitValue_eq_early
        (reward := reward) anchor.roots who
          realized.block.start realized.block.extra
    refine ⟨stageOfRealized realized offset,
      stageOfRealized_mem realized offset, ?_⟩
    rw [stageOfRealized_pureQuitPayoff]
    change
      finitePrefixQuitValue (reward := reward) anchor.roots who
          realized.block.start offset.val =
        ((quittingFiniteBoundaryHolonomy reward anchor.roots
          realized.block.start realized.block.extra).bestResponse who).early
    rw [quittingFiniteBoundaryHolonomy_bestResponse_early]
    exact hvalue

/-- The entire encoded stage graph, not only its scalar projections, commutes
with adjacent realized concatenation. -/
theorem ofRealized_concat_stages [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (ofRealized (outer.concat inner hadjacent)).stages =
      ((ofRealized outer).compose (ofRealized inner)).stages := by
  ext stage
  constructor
  · rintro ⟨offset, rfl⟩
    have hlength :=
      RealizedMarkedAbsorptionCylinder.length_concat outer inner hadjacent
    have hbound : offset.val < outer.block.length + inner.block.length := by
      calc
        offset.val < (outer.concat inner hadjacent).block.length := offset.isLt
        _ = outer.block.length + inner.block.length := hlength
    by_cases hleft : offset.val < outer.block.length
    · let leftOffset : Fin outer.block.length := ⟨offset.val, hleft⟩
      have hoffset : offset =
          concatLeftOffset outer inner hadjacent leftOffset := by
        apply Fin.ext
        rfl
      rw [hoffset, stageOfRealized_concat_left]
      apply Set.mem_union_left
      exact ⟨stageOfRealized outer leftOffset, ⟨leftOffset, rfl⟩, rfl⟩
    · have hright : offset.val - outer.block.length <
          inner.block.length := by omega
      let rightOffset : Fin inner.block.length :=
        ⟨offset.val - outer.block.length, hright⟩
      have hoffset : offset =
          concatRightOffset outer inner hadjacent rightOffset := by
        apply Fin.ext
        change offset.val = outer.block.length +
          (offset.val - outer.block.length)
        omega
      rw [hoffset, stageOfRealized_concat_right]
      apply Set.mem_union_right
      exact ⟨stageOfRealized inner rightOffset, ⟨rightOffset, rfl⟩, rfl⟩
  · intro hstage
    rcases hstage with hstage | hstage
    · rcases hstage with ⟨outerStage, ⟨offset, rfl⟩, rfl⟩
      exact ⟨concatLeftOffset outer inner hadjacent offset,
        stageOfRealized_concat_left outer inner hadjacent offset⟩
    · rcases hstage with ⟨innerStage, ⟨offset, rfl⟩, rfl⟩
      exact ⟨concatRightOffset outer inner hadjacent offset,
        stageOfRealized_concat_right outer inner hadjacent offset⟩

@[simp] theorem ofRealized_forgetful [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).forgetful = realized.block.holonomy := rfl

theorem ofRealized_sExit [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).sExit = realized.sExit := by
  rw [realized.sExit_pin]
  exact MarkedObstacleRecord.prod_playerContinueFactor_eq_survival
    anchor.roots realized.block.start realized.block.length

theorem ofRealized_chi [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) :
    (ofRealized realized).chi who = realized.chi who := by
  rw [realized.chi_pin]
  exact MarkedObstacleRecord.prod_playerContinueFactor_erase_eq_opponentSurvivalWeight
    anchor.roots who realized.block.start realized.block.length

theorem ofRealized_absorbed_total [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
      (ofRealized realized).absorbed coalition) =
        1 - (ofRealized realized).sExit := by
  rw [ofRealized_sExit]
  rw [realized.sExit_pin]
  exact realized.absorptionPath_total_eq_one_sub_survival
    realized.block.length le_rfl

theorem ofRealized_prescribedValue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (terminalValue : ℝ) :
    (ofRealized realized).prescribedValue who terminalValue =
      quittingFiniteTerminalHazardValue reward anchor.roots who
        (fun time => anchor.roots time who) terminalValue
        realized.block.start realized.block.length := by
  exact realized.prescribedValue_eq_literal who terminalValue

theorem ofRealized_unilateralValue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (terminalValue : ℝ) :
    (ofRealized realized).unilateralValue who terminalValue =
      quittingFiniteTerminalBestResponseValue reward anchor.roots who
        terminalValue realized.block.start realized.block.length := by
  exact realized.unilateralValue_eq_literal who terminalValue

@[simp] theorem ofRealized_entryAnchor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).entryAnchor = realized.entryAnchor := rfl

@[simp] theorem ofRealized_exitAnchor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).exitAnchor = realized.exitAnchor := rfl

@[simp] theorem ofRealized_entryDebt [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).entryDebt = realized.entryDebt := rfl

theorem ofRealized_packet [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).packet.owner = anchor.owner ∧
      (ofRealized realized).packet.action = anchor.action ∧
      (ofRealized realized).packet.kernel =
        Function.update (anchor.roots anchor.last) anchor.owner
          (PMF.pure false) ∧
      (ofRealized realized).packet.preterminalSurvival =
        anchor.preterminalSurvival ∧
      (ofRealized realized).packet.terminalMass = anchor.terminalMass ∧
      (ofRealized realized).packet.advantage =
        quittingTerminalOpponentAdvantage reward anchor.owner anchor.action := by
  exact ⟨rfl, rfl, rfl, realized.preterminalSurvival_pin,
    realized.terminalMass_pin, realized.advantage_pin⟩

/-- Every production realization lands in the endpoint-coherent part of the
source-free carrier. -/
theorem ofRealized_isEndpointCoherent [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).IsEndpointCoherent where
  prescribed_survival who :=
    (realized.sExit_eq_holonomy_survival who).symm.trans
      (ofRealized_sExit realized).symm
  bestResponse_survival who :=
    (realized.chi_eq_holonomy_survival who).symm.trans
      (ofRealized_chi realized who).symm
  absorbed_total := ofRealized_absorbed_total realized

/-- Adjacent realized blocks become legally composable after source
forgetting. -/
theorem ofRealized_isComposable_of_adjacent [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    IsComposable (ofRealized outer) (ofRealized inner) := by
  exact outer.seam_eq inner hadjacent

/-- The encoder and source-free composition agree on the load-bearing
holonomy projection for adjacent realized blocks. -/
theorem ofRealized_concat_forgetful [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (ofRealized (outer.concat inner hadjacent)).forgetful =
      ((ofRealized outer).compose (ofRealized inner)).forgetful := by
  rw [ofRealized_forgetful, forgetful_compose,
    ofRealized_forgetful, ofRealized_forgetful]
  exact outer.holonomy_concat inner hadjacent

/-- The encoded full exit clock agrees with source-free composition. -/
theorem ofRealized_concat_sExit [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (ofRealized (outer.concat inner hadjacent)).sExit =
      ((ofRealized outer).compose (ofRealized inner)).sExit := by
  calc
    (ofRealized (outer.concat inner hadjacent)).sExit =
        (outer.concat inner hadjacent).sExit :=
      ofRealized_sExit (outer.concat inner hadjacent)
    _ = outer.sExit * inner.sExit := by
      rw [(outer.concat inner hadjacent).sExit_pin,
        outer.sExit_pin, inner.sExit_pin]
      change realizedBlockFullSurvival
          (outer.block.concat inner.block hadjacent)
          (outer.block.concat inner.block hadjacent).length le_rfl =
        realizedBlockFullSurvival outer.block outer.block.length le_rfl *
          realizedBlockFullSurvival inner.block inner.block.length le_rfl
      simpa only [QuittingAnchoredBoundaryBlock.length_concat] using
        (outer.fullSurvival_concat inner hadjacent)
    _ = (ofRealized outer).sExit * (ofRealized inner).sExit := by
      rw [ofRealized_sExit, ofRealized_sExit]
    _ = ((ofRealized outer).compose (ofRealized inner)).sExit :=
      (sExit_compose _ _).symm

/-- Every encoded deleted clock agrees with source-free composition. -/
theorem ofRealized_concat_chi [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) (who : ι) :
    (ofRealized (outer.concat inner hadjacent)).chi who =
      ((ofRealized outer).compose (ofRealized inner)).chi who := by
  calc
    (ofRealized (outer.concat inner hadjacent)).chi who =
        (outer.concat inner hadjacent).chi who :=
      ofRealized_chi (outer.concat inner hadjacent) who
    _ = outer.chi who * inner.chi who :=
      outer.chi_concat inner hadjacent who
    _ = (ofRealized outer).chi who * (ofRealized inner).chi who := by
      rw [ofRealized_chi, ofRealized_chi]
    _ = ((ofRealized outer).compose (ofRealized inner)).chi who :=
      (chi_compose _ _ who).symm

theorem ofRealized_concat_absorbed [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (coalition : Finset ι) :
    (ofRealized (outer.concat inner hadjacent)).absorbed coalition =
      ((ofRealized outer).compose (ofRealized inner)).absorbed coalition := by
  have hseam : outer.block.start + outer.block.length = inner.block.start :=
    hadjacent.symm
  have hfull :
      fullFactor (fun who =>
          MarkedObstacleRecord.playerContinueFactor anchor.roots who
            outer.block.start outer.block.length) =
        Math.survivalProduct
          (fun time => quittingStationaryContinueMass (anchor.roots time))
          outer.block.start outer.block.length :=
    MarkedObstacleRecord.prod_playerContinueFactor_eq_survival
      anchor.roots outer.block.start outer.block.length
  change finiteAbsorptionValue anchor.roots outer.block.start
      (outer.concat inner hadjacent).block.length coalition =
    finiteAbsorptionValue anchor.roots outer.block.start outer.block.length
        coalition +
      fullFactor (fun who =>
        MarkedObstacleRecord.playerContinueFactor anchor.roots who
          outer.block.start outer.block.length) *
        finiteAbsorptionValue anchor.roots inner.block.start inner.block.length
          coalition
  rw [RealizedMarkedAbsorptionCylinder.length_concat,
    finiteAbsorptionValue_add, hfull, hseam]

theorem ofRealized_concat_exitFactor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length)
    (who : ι) :
    (ofRealized (outer.concat inner hadjacent)).exitFactor who =
      ((ofRealized outer).compose (ofRealized inner)).exitFactor who := by
  have hseam : outer.block.start + outer.block.length = inner.block.start :=
    hadjacent.symm
  change MarkedObstacleRecord.playerContinueFactor anchor.roots who
      outer.block.start (outer.concat inner hadjacent).block.length =
    MarkedObstacleRecord.playerContinueFactor anchor.roots who
        outer.block.start outer.block.length *
      MarkedObstacleRecord.playerContinueFactor anchor.roots who
        inner.block.start inner.block.length
  rw [RealizedMarkedAbsorptionCylinder.length_concat,
    playerContinueFactor_add, hseam]

theorem ofRealized_concat_packet [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (ofRealized (outer.concat inner hadjacent)).packet =
      ((ofRealized outer).compose (ofRealized inner)).packet := by
  rw [packet_compose]
  apply TerminalPacket.ext
  · rfl
  · rfl
  · rfl
  · change (outer.concat inner hadjacent).preterminalSurvival =
      inner.preterminalSurvival
    rw [(outer.concat inner hadjacent).preterminalSurvival_pin,
      inner.preterminalSurvival_pin]
  · change (outer.concat inner hadjacent).terminalMass = inner.terminalMass
    rw [(outer.concat inner hadjacent).terminalMass_pin,
      inner.terminalMass_pin]
  · change (outer.concat inner hadjacent).advantage = inner.advantage
    rw [(outer.concat inner hadjacent).advantage_pin, inner.advantage_pin]

theorem ofRealized_concat_entryDebt [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (ofRealized (outer.concat inner hadjacent)).entryDebt =
      ((ofRealized outer).compose (ofRealized inner)).entryDebt := by
  change (outer.concat inner hadjacent).entryDebt = outer.entryDebt
  rw [(outer.concat inner hadjacent).entryDebt_pin, outer.entryDebt_pin]
  rfl

theorem ofRealized_concat_entryAnchor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (ofRealized (outer.concat inner hadjacent)).entryAnchor =
      ((ofRealized outer).compose (ofRealized inner)).entryAnchor := by
  rfl

theorem ofRealized_concat_exitAnchor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (ofRealized (outer.concat inner hadjacent)).exitAnchor =
      ((ofRealized outer).compose (ofRealized inner)).exitAnchor := by
  change anchor.debtPoint
      (outer.block.start + (outer.concat inner hadjacent).block.length) =
    anchor.debtPoint (inner.block.start + inner.block.length)
  rw [RealizedMarkedAbsorptionCylinder.length_concat]
  congr 1
  omega

/-- Full finite exactness boundary: source forgetting is a homomorphism from
adjacent realized block concatenation into the source-free cylinder semigroup. -/
theorem ofRealized_concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    ofRealized (outer.concat inner hadjacent) =
      (ofRealized outer).compose (ofRealized inner) := by
  apply MarkedAbsorptionCylinder.ext
  · exact ofRealized_concat_stages outer inner hadjacent
  · funext coalition
    exact ofRealized_concat_absorbed outer inner hadjacent coalition
  · funext who
    exact ofRealized_concat_exitFactor outer inner hadjacent who
  · exact outer.holonomy_concat inner hadjacent
  · exact ofRealized_concat_packet outer inner hadjacent
  · exact ofRealized_concat_entryDebt outer inner hadjacent
  · exact ofRealized_concat_entryAnchor outer inner hadjacent
  · exact ofRealized_concat_exitAnchor outer inner hadjacent

/-! ## Strong finite semantic coherence -/

/-- Source-free chronological provenance in `Prop`: finite semantic cylinders
are generated by realized blocks and legal exact-anchor splices.  The witness
is erased from the data and therefore does not reintroduce a horizon or source
word into `MarkedAbsorptionCylinder`. -/
inductive IsChronologicallyGenerated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) [Nonempty ι] :
    MarkedAbsorptionCylinder ι → Prop
  | realized {anchor : QuittingCalibratedTerminalAnchor reward}
      (source : RealizedMarkedAbsorptionCylinder reward anchor) :
      IsChronologicallyGenerated reward (ofRealized source)
  | splice {outer inner : MarkedAbsorptionCylinder ι}
      (houter : IsChronologicallyGenerated reward outer)
      (hinner : IsChronologicallyGenerated reward inner)
      (hseam : IsComposable outer inner) :
      IsChronologicallyGenerated reward (outer.compose inner)

/-- Intrinsic incidence and bounds for the right-biased marked terminal
packet. -/
structure IsPacketCoherent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cylinder : MarkedAbsorptionCylinder ι) : Prop where
  preterminal_pos : 0 < cylinder.packet.preterminalSurvival
  preterminal_le_one : cylinder.packet.preterminalSurvival ≤ 1
  terminalMass_pos : 0 < cylinder.packet.terminalMass
  terminalMass_le_one : cylinder.packet.terminalMass ≤ 1
  owner_continues : cylinder.packet.action cylinder.packet.owner = false
  quitters_nonempty : (quittingQuitters cylinder.packet.action).Nonempty
  kernel_owner : cylinder.packet.kernel cylinder.packet.owner = PMF.pure false
  terminalMass_pin : cylinder.packet.terminalMass =
    ((pmfPi cylinder.packet.kernel) cylinder.packet.action).toReal
  advantage_pin : cylinder.packet.advantage =
    quittingTerminalOpponentAdvantage reward cylinder.packet.owner
      cylinder.packet.action
  advantage_pos : 0 < cylinder.packet.advantage

theorem IsPacketCoherent.compose
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {outer inner : MarkedAbsorptionCylinder ι}
    (hinner : inner.IsPacketCoherent reward) :
    (outer.compose inner).IsPacketCoherent reward where
  preterminal_pos := hinner.preterminal_pos
  preterminal_le_one := hinner.preterminal_le_one
  terminalMass_pos := hinner.terminalMass_pos
  terminalMass_le_one := hinner.terminalMass_le_one
  owner_continues := hinner.owner_continues
  quitters_nonempty := hinner.quitters_nonempty
  kernel_owner := hinner.kernel_owner
  terminalMass_pin := hinner.terminalMass_pin
  advantage_pin := hinner.advantage_pin
  advantage_pos := hinner.advantage_pos

/-- Promotion-gate predicate for the finite layer.  It combines a genuine
chronological-generation certificate with all direct decoder-facing laws:
endpoint mass, root-induced rows, suffix/Bellman factorization, exact obstacle
cap, coordinate bounds, entry debt, and terminal packet incidence. -/
structure IsSemanticallyCoherent [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cylinder : MarkedAbsorptionCylinder ι) : Prop where
  chronology : IsChronologicallyGenerated reward cylinder
  endpoint : cylinder.IsEndpointCoherent
  root_induced : cylinder.HasRootInducedStages reward
  obstacle_cap : cylinder.HasExactObstacleCap
  exitFactor_nonneg : ∀ who, 0 ≤ cylinder.exitFactor who
  exitFactor_le_one : ∀ who, cylinder.exitFactor who ≤ 1
  absorbed_nonneg : ∀ coalition, 0 ≤ cylinder.absorbed coalition
  entryDebt_pin : cylinder.entryDebt = cylinder.entryAnchor.2
  packet : cylinder.IsPacketCoherent reward

/-- Every source realization lands in the strongly coherent finite carrier. -/
theorem ofRealized_isSemanticallyCoherent [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (realized : RealizedMarkedAbsorptionCylinder reward anchor) :
    (ofRealized realized).IsSemanticallyCoherent reward where
  chronology := IsChronologicallyGenerated.realized realized
  endpoint := ofRealized_isEndpointCoherent realized
  root_induced := ofRealized_hasRootInducedStages realized
  obstacle_cap := ofRealized_hasExactObstacleCap realized
  exitFactor_nonneg who := by
    exact playerContinueFactor_nonneg anchor.roots who
      realized.block.start realized.block.length
  exitFactor_le_one who := by
    exact playerContinueFactor_le_one anchor.roots who
      realized.block.start realized.block.length
  absorbed_nonneg coalition := by
    change 0 ≤ finiteAbsorptionValue anchor.roots realized.block.start
      realized.block.length coalition
    exact finiteAbsorptionValue_nonneg _ _ _ _
  entryDebt_pin := by
    change realized.entryDebt = realized.entryAnchor.2
    exact realized.entryDebt_eq
  packet := by
    constructor
    · change 0 < realized.preterminalSurvival
      rw [realized.preterminalSurvival_pin]
      exact anchor.preterminalSurvival_pos
    · change realized.preterminalSurvival ≤ 1
      rw [realized.preterminalSurvival_pin]
      exact anchor.preterminalSurvival_le_one
    · change 0 < realized.terminalMass
      rw [realized.terminalMass_pin]
      exact anchor.terminalMass_pos
    · change realized.terminalMass ≤ 1
      rw [realized.terminalMass_pin]
      exact anchor.terminalMass_le_one
    · exact anchor.owner_continues
    · exact anchor.terminalQuitters_nonempty
    · change Function.update (anchor.roots anchor.last) anchor.owner
          (PMF.pure false) anchor.owner = PMF.pure false
      exact Function.update_self anchor.owner (PMF.pure false)
        (anchor.roots anchor.last)
    · change realized.terminalMass =
        ((pmfPi (Function.update (anchor.roots anchor.last) anchor.owner
          (PMF.pure false))) anchor.action).toReal
      exact realized.terminalMass_pin
    · change realized.advantage =
        quittingTerminalOpponentAdvantage reward anchor.owner anchor.action
      exact realized.advantage_pin
    · change 0 < realized.advantage
      rw [realized.advantage_pin]
      exact anchor.terminalAdvantage_pos

/-- Strong semantic coherence is closed under legal exact-anchor splicing. -/
theorem IsSemanticallyCoherent.compose [Nonempty ι]
    {outer inner : MarkedAbsorptionCylinder ι}
    (houter : outer.IsSemanticallyCoherent reward)
    (hinner : inner.IsSemanticallyCoherent reward)
    (hseam : IsComposable outer inner) :
    (outer.compose inner).IsSemanticallyCoherent reward where
  chronology := IsChronologicallyGenerated.splice
    houter.chronology hinner.chronology hseam
  endpoint := houter.endpoint.compose hinner.endpoint
  root_induced := houter.root_induced.compose hinner.root_induced houter.endpoint
  obstacle_cap := houter.obstacle_cap.compose hinner.obstacle_cap
  exitFactor_nonneg who :=
    mul_nonneg (houter.exitFactor_nonneg who) (hinner.exitFactor_nonneg who)
  exitFactor_le_one who := by
    change outer.exitFactor who * inner.exitFactor who ≤ 1
    nlinarith [houter.exitFactor_nonneg who, houter.exitFactor_le_one who,
      hinner.exitFactor_nonneg who, hinner.exitFactor_le_one who]
  absorbed_nonneg coalition := by
    rw [absorbed_compose]
    exact add_nonneg (houter.absorbed_nonneg coalition)
      (mul_nonneg
        (Finset.prod_nonneg fun who _ => houter.exitFactor_nonneg who)
        (hinner.absorbed_nonneg coalition))
  entryDebt_pin := houter.entryDebt_pin
  packet := hinner.packet.compose

theorem IsSemanticallyCoherent.sExit_nonneg [Nonempty ι]
    {cylinder : MarkedAbsorptionCylinder ι}
    (h : cylinder.IsSemanticallyCoherent reward) :
    0 ≤ cylinder.sExit :=
  Finset.prod_nonneg fun who _ => h.exitFactor_nonneg who

theorem IsSemanticallyCoherent.sExit_le_one [Nonempty ι]
    {cylinder : MarkedAbsorptionCylinder ι}
    (h : cylinder.IsSemanticallyCoherent reward) :
    cylinder.sExit ≤ 1 :=
  Finset.prod_le_one
    (fun who _ => h.exitFactor_nonneg who)
    (fun who _ => h.exitFactor_le_one who)

theorem IsSemanticallyCoherent.stages_nonempty [Nonempty ι]
    {cylinder : MarkedAbsorptionCylinder ι}
    (h : cylinder.IsSemanticallyCoherent reward) :
    cylinder.stages.Nonempty := by
  let who : ι := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨stage, hstage, _⟩ := h.obstacle_cap.attained who
  exact ⟨stage, hstage⟩

end MarkedAbsorptionCylinder

end GameTheory
