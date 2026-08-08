/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.Atlas
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Examples.PureExternality.CycleGerm

/-!
# Leaf-returning analytic endpoint classification

`AnalyticEndpointAtlas.lean` classifies an analytic Bellman germ into one
`AnalyticEndpointAtlasLeaf`, but only through
`AnalyticEndpointAtlasLeaf.ofFirstHierarchyResponse`, whose conclusion is
`Nonempty (germ.AnalyticEndpointAtlasLeaf span entry)`.  That statement
destructs the underlying finite-bias disjunction *inside* a `Prop`, so a
concrete germ can never read off **which** leaf it landed in: the information
is discarded by `Nonempty`.  Downstream modules such as
`PureExternalityCycleGerm.lean` therefore have to re-exhibit their
`semanticClose` leaf by hand.

This file is the missing adapter.  It adds, without touching any existing
file:

* a decidable constructor label `AnalyticEndpointLeafLabel` together with
  `AnalyticEndpointAtlasLeaf.label`, and the two soundness lemmas that read a
  `semanticClose` label back as the semantic theorem it carries;
* a genuine leaf-returning classification `finiteBiasSeedLeaf` /
  `firstHierarchyResponseLeaf`, packaged with a discriminating specification
  `IsFiniteBiasSeedClassification` that pins the label down to the four
  finite-bias labels and forces the `semanticClose` label whenever the
  endpoint value really is a uniform equilibrium payoff at the entry;
* conditional selectors, both the choice-free ones (data in hand gives a leaf
  with a known label, by `rfl`) and the ones that can only be stated
  existentially because the underlying disjunct is a `Prop`;
* an acceptance test re-deriving the `semanticClose` conclusion of
  `PureExternalityCycleGerm.lean` through the adapter, for both of its germs.

## Where choice enters

`FiniteBiasSeed.uniformPayoff_or_publicResponse_or_processedObstruction_or_rankDecrease`
is a `Prop`-valued four-way disjunction whose last three disjuncts are
existentials over data (`G.State → Payoff ι`, a player, a continuation-neutral
action).  Leaves are `Type`-valued, so no choice-free function can turn that
disjunction into a leaf.  Consequently `finiteBiasSeedLeaf` is `noncomputable`
and defined by `Classical.choice` on a nonempty subtype whose predicate is the
full discrimination we can prove.  The other three branches of
`FirstHierarchyResponse` (`processedJet`, `lowerRank`, `transitionMonitor`)
carry their data in `Type` and are classified **choice-free**, with their label
known by `rfl`.

The `semanticClose` branch is nevertheless discriminated *sharply*:
`finiteBiasSeedLeaf_label_eq_semanticClose_iff` states that the produced leaf
is labelled `semanticClose` if and only if
`G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)` holds, and
`finiteBiasSeedLeaf_eq_semanticClose` upgrades that to an equation between the
produced leaf and the by-hand `semanticClose` leaf.  When the endpoint is not
a uniform equilibrium payoff the label is pinned to the remaining three
finite-bias labels
(`finiteBiasSeedLeaf_label_of_not_isUniformEquilibriumPayoff`).
-/

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

/-- The constructor labels of `AnalyticEndpointAtlasLeaf`.

This is the discriminating datum that `Nonempty` destroys: it is a decidable
enumeration, so a concrete germ can compare its classification against a
specific branch. -/
inductive AnalyticEndpointLeafLabel : Type
  | semanticClose
  | publicResponseCredibility
  | playerOwnedAnalyticResponseCredibility
  | playerOwnedCommonPotentialAccount
  | finiteBiasProcessedAccount
  | processedJetAccount
  | harmonicRankDecrease
  | transitionMonitorCredibility
  | playerNeutralProperSupportEntryTarget
  | playerNeutralFullSupport
  | playerNeutralBoundedPotentialAccount
  | playerNeutralProcessedAccount
  | terminalAnalyticCirculationEntryTarget
  | terminalZeroPairing
  deriving DecidableEq, Repr

namespace AnalyticEndpointLeafLabel

/-- The four labels a finite-bias seed can produce, matching the four
disjuncts of
`FiniteBiasSeed.uniformPayoff_or_publicResponse_or_processedObstruction_or_rankDecrease`. -/
def isFiniteBiasReachable : AnalyticEndpointLeafLabel → Bool
  | .semanticClose => true
  | .publicResponseCredibility => true
  | .finiteBiasProcessedAccount => true
  | .harmonicRankDecrease => true
  | _ => false

/-- The six labels a first hierarchy response can produce. -/
def isFirstHierarchyReachable : AnalyticEndpointLeafLabel → Bool
  | .semanticClose => true
  | .publicResponseCredibility => true
  | .finiteBiasProcessedAccount => true
  | .processedJetAccount => true
  | .harmonicRankDecrease => true
  | .transitionMonitorCredibility => true
  | _ => false

theorem isFiniteBiasReachable_iff (label : AnalyticEndpointLeafLabel) :
    label.isFiniteBiasReachable = true ↔
      label = .semanticClose ∨ label = .publicResponseCredibility ∨
        label = .finiteBiasProcessedAccount ∨ label = .harmonicRankDecrease := by
  cases label <;> simp [isFiniteBiasReachable]

theorem isFirstHierarchyReachable_of_isFiniteBiasReachable
    {label : AnalyticEndpointLeafLabel}
    (h : label.isFiniteBiasReachable = true) :
    label.isFirstHierarchyReachable = true := by
  cases label <;> simp_all [isFiniteBiasReachable, isFirstHierarchyReachable]

end AnalyticEndpointLeafLabel

end AnalyticBellmanGerm

noncomputable section

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

namespace AnalyticBellmanGerm
namespace FiniteBiasSeed

/-! ## The finite-bias disjuncts, named

The three nonsemantic disjuncts of
`uniformPayoff_or_publicResponse_or_processedObstruction_or_rankDecrease` are
`Prop`-valued existentials over `Type`-valued data.  Naming them makes the
selectors below readable and marks exactly which hypotheses can only be
consumed by choice. -/

/-- The second disjunct: a Poisson-corrected operational public response at
some fixed continuation-neutral action. -/
def HasPublicResponseObstruction (seed : germ.FiniteBiasSeed) : Prop :=
  ∃ correction : G.State → Payoff ι,
    ∃ who, ∃ response : germ.ContinuationNeutralAction who,
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint ∧
      Nonempty
        (G.FinkPublicConstraintResponse
          germ.endpointFinkPoint (seed.H - correction)
          response.source who response.1.2)

/-- The third disjunct: a nonzero harmonic obstruction already inside the
processed span. -/
def HasProcessedObstruction (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) : Prop :=
  ∃ obstruction correction : G.State → Payoff ι,
    obstruction ≠ 0 ∧
    obstruction ∈ span.carrier ∧
    G.finkContinuationResidualVector
        obstruction germ.endpointFinkPoint = 0 ∧
    G.finkBellmanForcingVector
        germ.endpointValue seed.H germ.endpointFinkPoint =
      obstruction -
        G.finkContinuationResidualVector
          correction germ.endpointFinkPoint

/-- The fourth disjunct: a new nonzero harmonic obstruction strictly
decreasing the remaining harmonic rank. -/
def HasHarmonicRankDecrease (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) : Prop :=
  ∃ obstruction correction : G.State → Payoff ι,
    ∃ harmonic : obstruction ∈ germ.endpointHarmonicSubmodule,
      obstruction ≠ 0 ∧
      obstruction ∉ span.carrier ∧
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        obstruction -
          G.finkContinuationResidualVector
            correction germ.endpointFinkPoint ∧
      (span.extend obstruction harmonic).rank < span.rank

/-- The existing four-way finite-bias alternative, restated with its three
nonsemantic disjuncts named. -/
theorem isUniformEquilibriumPayoff_or_named_obstruction
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry) ∨
      seed.HasPublicResponseObstruction ∨
      seed.HasProcessedObstruction span ∨
      seed.HasHarmonicRankDecrease span :=
  seed.uniformPayoff_or_publicResponse_or_processedObstruction_or_rankDecrease
    span entry

end FiniteBiasSeed

namespace AnalyticEndpointAtlasLeaf

/-! ## Labels -/

/-- The constructor label of an endpoint atlas leaf. -/
def label {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (leaf : germ.AnalyticEndpointAtlasLeaf span entry) :
    AnalyticEndpointLeafLabel :=
  match leaf with
  | .semanticClose _ => .semanticClose
  | .publicResponseCredibility _ => .publicResponseCredibility
  | .playerOwnedAnalyticResponseCredibility _ =>
      .playerOwnedAnalyticResponseCredibility
  | .playerOwnedCommonPotentialAccount _ => .playerOwnedCommonPotentialAccount
  | .finiteBiasProcessedAccount _ => .finiteBiasProcessedAccount
  | .processedJetAccount _ => .processedJetAccount
  | .harmonicRankDecrease _ => .harmonicRankDecrease
  | .transitionMonitorCredibility _ => .transitionMonitorCredibility
  | .playerNeutralProperSupportEntryTarget _ =>
      .playerNeutralProperSupportEntryTarget
  | .playerNeutralFullSupport _ => .playerNeutralFullSupport
  | .playerNeutralBoundedPotentialAccount _ =>
      .playerNeutralBoundedPotentialAccount
  | .playerNeutralProcessedAccount _ => .playerNeutralProcessedAccount
  | .terminalAnalyticCirculationEntryTarget _ =>
      .terminalAnalyticCirculationEntryTarget
  | .terminalZeroPairing _ => .terminalZeroPairing

@[simp] theorem label_semanticClose
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (uniform : G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)) :
    (AnalyticEndpointAtlasLeaf.semanticClose (span := span) uniform).label =
      .semanticClose :=
  rfl

/-- **Label soundness.**  A `semanticClose` label is not a name: it carries
the uniform-equilibrium-payoff theorem, which can be read back off the label
alone. -/
theorem isUniformEquilibriumPayoff_of_label_eq_semanticClose
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {leaf : germ.AnalyticEndpointAtlasLeaf span entry}
    (h : leaf.label = .semanticClose) :
    G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry) := by
  revert h
  cases leaf
  case semanticClose => exact fun _ => by assumption
  all_goals exact fun h => by simp [label] at h

/-- A leaf labelled `semanticClose` *is* the by-hand semantic leaf, for any
proof of the semantic statement (proof irrelevance). -/
theorem eq_semanticClose_of_label_eq_semanticClose
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {leaf : germ.AnalyticEndpointAtlasLeaf span entry}
    (h : leaf.label = .semanticClose)
    (uniform : G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)) :
    leaf = .semanticClose uniform := by
  revert h
  cases leaf
  case semanticClose => exact fun _ => rfl
  all_goals exact fun h => by simp [label] at h

/-! ## Choice-free conditional selectors

Each of these takes the branch data in hand and returns the leaf with its
label known by `rfl`.  They are the sufficient conditions that do not need
choice. -/

/-- Sufficient condition for the semantic leaf: the endpoint value is a
uniform equilibrium payoff at the entry. -/
def semanticCloseLeafOf {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (uniform : G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)) :
    germ.AnalyticEndpointAtlasLeaf span entry :=
  .semanticClose uniform

@[simp] theorem semanticCloseLeafOf_label
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (uniform : G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)) :
    (semanticCloseLeafOf (span := span) uniform).label = .semanticClose :=
  rfl

/-- Sufficient condition for the public-response credibility leaf. -/
def publicResponseCredibilityLeafOf
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {seed : germ.FiniteBiasSeed}
    (data : FiniteBiasPublicResponseData germ seed) :
    germ.AnalyticEndpointAtlasLeaf span entry :=
  .publicResponseCredibility data

@[simp] theorem publicResponseCredibilityLeafOf_label
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {seed : germ.FiniteBiasSeed}
    (data : FiniteBiasPublicResponseData germ seed) :
    (publicResponseCredibilityLeafOf (span := span) (entry := entry)
        data).label =
      .publicResponseCredibility :=
  rfl

/-- Sufficient condition for the processed finite-bias account leaf. -/
def finiteBiasProcessedAccountLeafOf
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {seed : germ.FiniteBiasSeed}
    (data : FiniteBiasProcessedObstructionData germ seed span) :
    germ.AnalyticEndpointAtlasLeaf span entry :=
  .finiteBiasProcessedAccount data

@[simp] theorem finiteBiasProcessedAccountLeafOf_label
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {seed : germ.FiniteBiasSeed}
    (data : FiniteBiasProcessedObstructionData germ seed span) :
    (finiteBiasProcessedAccountLeafOf (entry := entry) data).label =
      .finiteBiasProcessedAccount :=
  rfl

/-- Sufficient condition for the harmonic-rank-decrease leaf. -/
def harmonicRankDecreaseLeafOf
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (data : HarmonicRankDecreaseData germ span) :
    germ.AnalyticEndpointAtlasLeaf span entry :=
  .harmonicRankDecrease data

@[simp] theorem harmonicRankDecreaseLeafOf_label
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (data : HarmonicRankDecreaseData germ span) :
    (harmonicRankDecreaseLeafOf (entry := entry) data).label =
      .harmonicRankDecrease :=
  rfl

/-- Sufficient condition for the processed lower-value-jet account leaf. -/
def processedJetAccountLeafOf
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (data : ProcessedLowerValueJetData germ span) :
    germ.AnalyticEndpointAtlasLeaf span entry :=
  .processedJetAccount data

@[simp] theorem processedJetAccountLeafOf_label
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (data : ProcessedLowerValueJetData germ span) :
    (processedJetAccountLeafOf (entry := entry) data).label =
      .processedJetAccount :=
  rfl

/-- Sufficient condition for the transition-monitor credibility leaf. -/
def transitionMonitorCredibilityLeafOf
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (charge : germ.StateKernelMonitorPowerCharge) :
    germ.AnalyticEndpointAtlasLeaf span entry :=
  .transitionMonitorCredibility charge

@[simp] theorem transitionMonitorCredibilityLeafOf_label
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    (charge : germ.StateKernelMonitorPowerCharge) :
    (transitionMonitorCredibilityLeafOf (span := span) (entry := entry)
        charge).label =
      .transitionMonitorCredibility :=
  rfl

/-! ## Existential selectors from the `Prop`-valued disjuncts

The three nonsemantic finite-bias disjuncts only assert the *existence* of
their data, so the strongest choice-free conclusion is an existential over
leaves with a known label. -/

theorem exists_label_eq_publicResponseCredibility
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {seed : germ.FiniteBiasSeed}
    (h : seed.HasPublicResponseObstruction) :
    ∃ leaf : germ.AnalyticEndpointAtlasLeaf span entry,
      leaf.label = .publicResponseCredibility := by
  obtain ⟨correction, who, response, forcing, publicResponse⟩ := h
  exact ⟨publicResponseCredibilityLeafOf
    { correction := correction
      who := who
      response := response
      forcing := forcing
      publicResponse := publicResponse }, rfl⟩

theorem exists_label_eq_finiteBiasProcessedAccount
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {seed : germ.FiniteBiasSeed}
    (h : seed.HasProcessedObstruction span) :
    ∃ leaf : germ.AnalyticEndpointAtlasLeaf span entry,
      leaf.label = .finiteBiasProcessedAccount := by
  obtain ⟨obstruction, correction, nonzero, membership, harmonic, forcing⟩ := h
  exact ⟨finiteBiasProcessedAccountLeafOf (seed := seed)
    { obstruction := obstruction
      correction := correction
      obstruction_ne_zero := nonzero
      processed := membership
      harmonic := harmonic
      forcing := forcing }, rfl⟩

theorem exists_label_eq_harmonicRankDecrease
    {span : germ.EndpointHarmonicJetSpan} {entry : G.State}
    {seed : germ.FiniteBiasSeed}
    (h : seed.HasHarmonicRankDecrease span) :
    ∃ leaf : germ.AnalyticEndpointAtlasLeaf span entry,
      leaf.label = .harmonicRankDecrease := by
  obtain ⟨obstruction, correction, harmonic, _nonzero, _fresh, _forcing,
    decrease⟩ := h
  exact ⟨harmonicRankDecreaseLeafOf
    { direction := obstruction
      harmonic := harmonic
      decrease := decrease }, rfl⟩

/-! ## The leaf-returning finite-bias classification -/

/-- The discrimination a leaf-returning finite-bias classification must
carry: its label is one of the four finite-bias labels, and it is the
semantic label whenever the endpoint value really is a uniform equilibrium
payoff at the entry. -/
structure IsFiniteBiasSeedClassification
    (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State)
    (leaf : germ.AnalyticEndpointAtlasLeaf span entry) : Prop where
  /-- The label is reachable from a finite-bias seed. -/
  label_reachable : leaf.label.isFiniteBiasReachable = true
  /-- A uniform equilibrium payoff at the entry forces the semantic label. -/
  label_eq_semanticClose :
    G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry) →
      leaf.label = .semanticClose

/-- Every finite-bias seed admits a leaf satisfying the full discrimination.

This is the `Prop`-level content of the adapter; `finiteBiasSeedLeaf` is the
`Type`-level function extracted from it by choice. -/
theorem nonempty_isFiniteBiasSeedClassification
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    Nonempty { leaf : germ.AnalyticEndpointAtlasLeaf span entry //
      IsFiniteBiasSeedClassification germ span entry leaf } := by
  by_cases huniform :
      G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)
  · exact ⟨⟨semanticCloseLeafOf huniform, ⟨rfl, fun _ => rfl⟩⟩⟩
  · rcases seed.isUniformEquilibriumPayoff_or_named_obstruction span entry with
      uniform | response | processed | decrease
    · exact absurd uniform huniform
    · obtain ⟨leaf, hleaf⟩ :=
        exists_label_eq_publicResponseCredibility (span := span)
          (entry := entry) response
      exact ⟨⟨leaf, ⟨by rw [hleaf]; rfl, fun h => absurd h huniform⟩⟩⟩
    · obtain ⟨leaf, hleaf⟩ :=
        exists_label_eq_finiteBiasProcessedAccount (entry := entry) processed
      exact ⟨⟨leaf, ⟨by rw [hleaf]; rfl, fun h => absurd h huniform⟩⟩⟩
    · obtain ⟨leaf, hleaf⟩ :=
        exists_label_eq_harmonicRankDecrease (entry := entry) decrease
      exact ⟨⟨leaf, ⟨by rw [hleaf]; rfl, fun h => absurd h huniform⟩⟩⟩

/-- **The classified finite-bias leaf**: a leaf bundled with its
discrimination.  This is the Σ-type the existing `Nonempty`-valued
`ofFiniteBiasSeed` cannot produce.

It is `noncomputable`: the underlying alternative is a `Prop`-valued
disjunction of existentials over `Type`-valued data. -/
def classifiedFiniteBiasSeedLeaf (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    { leaf : germ.AnalyticEndpointAtlasLeaf span entry //
      IsFiniteBiasSeedClassification germ span entry leaf } :=
  Classical.choice (nonempty_isFiniteBiasSeedClassification seed span entry)

/-- **The leaf-returning finite-bias classification.**  Unlike
`ofFiniteBiasSeed`, this returns an actual leaf, not merely `Nonempty`. -/
def finiteBiasSeedLeaf (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    germ.AnalyticEndpointAtlasLeaf span entry :=
  (classifiedFiniteBiasSeedLeaf seed span entry).1

/-- The produced leaf satisfies the full discrimination. -/
theorem finiteBiasSeedLeaf_isFiniteBiasSeedClassification
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    IsFiniteBiasSeedClassification germ span entry
      (finiteBiasSeedLeaf seed span entry) :=
  (classifiedFiniteBiasSeedLeaf seed span entry).2

theorem finiteBiasSeedLeaf_label_isFiniteBiasReachable
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    (finiteBiasSeedLeaf seed span entry).label.isFiniteBiasReachable = true :=
  (finiteBiasSeedLeaf_isFiniteBiasSeedClassification seed span
    entry).label_reachable

/-- **Conditional selector.**  If the endpoint value is a uniform equilibrium
payoff at the entry, the classification lands in the semantic leaf. -/
theorem finiteBiasSeedLeaf_label_eq_semanticClose
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State)
    (uniform : G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)) :
    (finiteBiasSeedLeaf seed span entry).label = .semanticClose :=
  (finiteBiasSeedLeaf_isFiniteBiasSeedClassification seed span
    entry).label_eq_semanticClose uniform

/-- The same selector, upgraded to an equation with the by-hand semantic
leaf: the classification returns exactly `semanticClose uniform`. -/
theorem finiteBiasSeedLeaf_eq_semanticClose
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State)
    (uniform : G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)) :
    finiteBiasSeedLeaf seed span entry = .semanticClose uniform :=
  eq_semanticClose_of_label_eq_semanticClose
    (finiteBiasSeedLeaf_label_eq_semanticClose seed span entry uniform) uniform

/-- **Sharp discrimination of the semantic branch.**  The finite-bias
classification is labelled `semanticClose` exactly when the endpoint value is
a uniform equilibrium payoff at the entry. -/
theorem finiteBiasSeedLeaf_label_eq_semanticClose_iff
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    (finiteBiasSeedLeaf seed span entry).label = .semanticClose ↔
      G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry) :=
  ⟨isUniformEquilibriumPayoff_of_label_eq_semanticClose,
    finiteBiasSeedLeaf_label_eq_semanticClose seed span entry⟩

/-- The residual trichotomy: without a uniform equilibrium payoff at the
entry the finite-bias classification is one of the three named obstruction
leaves. -/
theorem finiteBiasSeedLeaf_label_of_not_isUniformEquilibriumPayoff
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State)
    (huniform :
      ¬ G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)) :
    (finiteBiasSeedLeaf seed span entry).label = .publicResponseCredibility ∨
      (finiteBiasSeedLeaf seed span entry).label =
        .finiteBiasProcessedAccount ∨
      (finiteBiasSeedLeaf seed span entry).label = .harmonicRankDecrease := by
  rcases
      (AnalyticEndpointLeafLabel.isFiniteBiasReachable_iff _).mp
        (finiteBiasSeedLeaf_label_isFiniteBiasReachable seed span entry) with
    hsem | hpublic | hprocessed | hrank
  · exact absurd (isUniformEquilibriumPayoff_of_label_eq_semanticClose hsem)
      huniform
  · exact Or.inl hpublic
  · exact Or.inr (Or.inl hprocessed)
  · exact Or.inr (Or.inr hrank)

/-! ## The leaf-returning first-hierarchy classification -/

/-- **The adapter.**  The leaf-returning form of `ofFirstHierarchyResponse`:
it returns the leaf itself, so a concrete germ can identify its branch.

Only the `finiteBias` branch needs choice; the other three branches are
classified structurally and their labels are known by `rfl`. -/
def firstHierarchyResponseLeaf {span : germ.EndpointHarmonicJetSpan}
    (response : germ.FirstHierarchyResponse span) (entry : G.State) :
    germ.AnalyticEndpointAtlasLeaf span entry :=
  match response with
  | .finiteBias seed => finiteBiasSeedLeaf seed span entry
  | .processedJet jet processed =>
      .processedJetAccount
        { jet := jet
          processed := processed
          rank_stagnates := jet.processed_extend_rank_eq span processed }
  | .lowerRank jet harmonic decreases =>
      .harmonicRankDecrease
        { direction := jet.factor 0
          harmonic := harmonic
          decrease := decreases }
  | .transitionMonitor charge => .transitionMonitorCredibility charge

@[simp] theorem firstHierarchyResponseLeaf_finiteBias
    {span : germ.EndpointHarmonicJetSpan} (seed : germ.FiniteBiasSeed)
    (entry : G.State) :
    firstHierarchyResponseLeaf (.finiteBias seed) entry =
      finiteBiasSeedLeaf seed span entry :=
  rfl

@[simp] theorem firstHierarchyResponseLeaf_processedJet_label
    {span : germ.EndpointHarmonicJetSpan} (jet : germ.LowerValueJet)
    (processed : jet.factor 0 ∈ span.carrier) (entry : G.State) :
    (firstHierarchyResponseLeaf (.processedJet jet processed) entry).label =
      .processedJetAccount :=
  rfl

@[simp] theorem firstHierarchyResponseLeaf_lowerRank_label
    {span : germ.EndpointHarmonicJetSpan} (jet : germ.LowerValueJet)
    (harmonic : jet.factor 0 ∈ germ.endpointHarmonicSubmodule)
    (decreases : (span.extend (jet.factor 0) harmonic).rank < span.rank)
    (entry : G.State) :
    (firstHierarchyResponseLeaf (.lowerRank jet harmonic decreases)
        entry).label =
      .harmonicRankDecrease :=
  rfl

@[simp] theorem firstHierarchyResponseLeaf_transitionMonitor_label
    {span : germ.EndpointHarmonicJetSpan}
    (charge : germ.StateKernelMonitorPowerCharge) (entry : G.State) :
    (firstHierarchyResponseLeaf (span := span) (.transitionMonitor charge)
        entry).label =
      .transitionMonitorCredibility :=
  rfl

/-- The adapter's label always lies in the six first-hierarchy labels. -/
theorem firstHierarchyResponseLeaf_label_isFirstHierarchyReachable
    {span : germ.EndpointHarmonicJetSpan}
    (response : germ.FirstHierarchyResponse span) (entry : G.State) :
    (firstHierarchyResponseLeaf response
      entry).label.isFirstHierarchyReachable = true := by
  cases response with
  | finiteBias seed =>
      exact
        AnalyticEndpointLeafLabel.isFirstHierarchyReachable_of_isFiniteBiasReachable
          (finiteBiasSeedLeaf_label_isFiniteBiasReachable seed span entry)
  | processedJet jet processed => rfl
  | lowerRank jet harmonic decreases => rfl
  | transitionMonitor charge => rfl

/-- **Conditional selector at the top level.**  A uniform equilibrium payoff
at the entry sends the adapter to the semantic leaf, for every finite-bias
response. -/
theorem firstHierarchyResponseLeaf_finiteBias_eq_semanticClose
    (seed : germ.FiniteBiasSeed) (span : germ.EndpointHarmonicJetSpan)
    (entry : G.State)
    (uniform : G.IsUniformEquilibriumPayoff entry (germ.endpointValue entry)) :
    firstHierarchyResponseLeaf (span := span) (.finiteBias seed) entry =
      .semanticClose uniform :=
  finiteBiasSeedLeaf_eq_semanticClose seed span entry uniform

/-- The adapter subsumes the existing existence statement
`ofFirstHierarchyResponse`. -/
theorem nonempty_of_firstHierarchyResponseLeaf
    {span : germ.EndpointHarmonicJetSpan}
    (response : germ.FirstHierarchyResponse span) (entry : G.State) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) :=
  ⟨firstHierarchyResponseLeaf response entry⟩

end AnalyticEndpointAtlasLeaf
end AnalyticBellmanGerm

/-! ## Acceptance test: the pure-externality cycle through the adapter

`PureExternalityCycleGerm.lean` had to exhibit its `semanticClose` leaves by
hand, because `ofFirstHierarchyResponse` only returns `Nonempty`.  The adapter
removes that: running it on the explicit first hierarchy responses of both
germs *returns* the by-hand leaves, and the semantic theorem can be read back
off the resulting label. -/

namespace PureExternalityCycle

open AnalyticBellmanGerm AnalyticBellmanGerm.AnalyticEndpointAtlasLeaf

/-- The adapter, run on the explicit constant-`1` first hierarchy response,
returns exactly the by-hand semantic leaf of `PureExternalityCycleGerm`. -/
theorem firstHierarchyResponseLeaf_oneFirstHierarchyResponse (entry : Bool) :
    firstHierarchyResponseLeaf oneFirstHierarchyResponse entry =
      oneEndpointLeaf entry :=
  firstHierarchyResponseLeaf_finiteBias_eq_semanticClose oneFiniteBiasSeed _
    entry (oneGerm_isUniformEquilibriumPayoff entry)

/-- The adapter identifies the constant-`1` leaf as the semantic one. -/
theorem firstHierarchyResponseLeaf_oneFirstHierarchyResponse_label
    (entry : Bool) :
    (firstHierarchyResponseLeaf oneFirstHierarchyResponse entry).label =
      .semanticClose :=
  finiteBiasSeedLeaf_label_eq_semanticClose oneFiniteBiasSeed _ entry
    (oneGerm_isUniformEquilibriumPayoff entry)

/-- The adapter, run on the explicit prescribed first hierarchy response,
returns exactly the by-hand semantic leaf — despite the nonzero finite
relative bias `prescribedFiniteBiasSeed_H_ne_zero`. -/
theorem firstHierarchyResponseLeaf_prescribedFirstHierarchyResponse
    (entry : Bool) :
    firstHierarchyResponseLeaf prescribedFirstHierarchyResponse entry =
      prescribedEndpointLeaf entry :=
  firstHierarchyResponseLeaf_finiteBias_eq_semanticClose
    prescribedFiniteBiasSeed _ entry
    (prescribedGerm_isUniformEquilibriumPayoff entry)

/-- The adapter identifies the prescribed leaf as the semantic one. -/
theorem firstHierarchyResponseLeaf_prescribedFirstHierarchyResponse_label
    (entry : Bool) :
    (firstHierarchyResponseLeaf prescribedFirstHierarchyResponse entry).label =
      .semanticClose :=
  finiteBiasSeedLeaf_label_eq_semanticClose prescribedFiniteBiasSeed _ entry
    (prescribedGerm_isUniformEquilibriumPayoff entry)

/-- **Acceptance capstone.**  For both explicit germs of the pure-externality
cycle the adapter *selects* the leaf rather than merely asserting that one
exists: the returned leaf equals the by-hand `semanticClose` leaf, its label
is `semanticClose`, and the uniform-equilibrium-payoff theorem is recovered
from that label alone. -/
theorem adapter_selects_semanticClose (entry : Bool) :
    (firstHierarchyResponseLeaf oneFirstHierarchyResponse entry =
        oneEndpointLeaf entry ∧
      (firstHierarchyResponseLeaf oneFirstHierarchyResponse entry).label =
        .semanticClose ∧
      game.IsUniformEquilibriumPayoff entry (oneGerm.endpointValue entry)) ∧
    (firstHierarchyResponseLeaf prescribedFirstHierarchyResponse entry =
        prescribedEndpointLeaf entry ∧
      (firstHierarchyResponseLeaf prescribedFirstHierarchyResponse
          entry).label =
        .semanticClose ∧
      game.IsUniformEquilibriumPayoff entry
        (prescribedGerm.endpointValue entry)) :=
  ⟨⟨firstHierarchyResponseLeaf_oneFirstHierarchyResponse entry,
      firstHierarchyResponseLeaf_oneFirstHierarchyResponse_label entry,
      isUniformEquilibriumPayoff_of_label_eq_semanticClose
        (firstHierarchyResponseLeaf_oneFirstHierarchyResponse_label entry)⟩,
    ⟨firstHierarchyResponseLeaf_prescribedFirstHierarchyResponse entry,
      firstHierarchyResponseLeaf_prescribedFirstHierarchyResponse_label entry,
      isUniformEquilibriumPayoff_of_label_eq_semanticClose
        (firstHierarchyResponseLeaf_prescribedFirstHierarchyResponse_label
          entry)⟩⟩

end PureExternalityCycle

end

end StochasticGame
end GameTheory
