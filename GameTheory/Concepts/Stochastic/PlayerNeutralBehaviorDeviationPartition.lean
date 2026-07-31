/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralPuncturedPotentialCalendarAccount

/-!
# Partitioning a behavioral deviation into strict and neutral transitions

Fix one player and one public state.  Every pure action has nonpositive
endpoint continuation gain.  We map a continuation-neutral action to its
actual player-owned occupation column, and map a continuation-strict action
to the prescribed transition from the same source.  Pushing an arbitrary
behavior distribution through this map produces a genuine PMF on the full
player-neutral occupation family.

This construction has three exact properties.

* It preserves the public source state.
* Its mixed transition is the actual transition on endpoint-neutral action
  mass and the prescribed transition on endpoint-strict action mass.
* Its moving occupation charge is exactly the moving neutral-action charge;
  strict action mass contributes zero to this secondary account.

Consequently the scaled-potential calendar account can be instantiated with
`active = Finset.univ`, without passing through analytic deflation.  The
remaining strict mass is not silently discarded: replacing it by the
prescribed transition loses exactly the negative endpoint continuation
gain.  This endpoint identity is not itself a moving shadow-to-actual law.
A global deviation proof still needs a combined moving Bellman domination,
or an equivalent segmented account, on the actual full public history.

The predictable selectors below depend on the public state history.  A
general behavior deviation may also depend on past public actions; that
full-history realization and account is a separate interface.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability Math.PMFProduct
open Math.Probability.AnalyticScaledChargedOccupationPotential
open AnalyticBellmanGerm.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

variable (germ : G.AnalyticBellmanGerm)

/-- Replace an endpoint-strict action by the prescribed occupation column
at the same source, while retaining every endpoint-neutral action as its
actual player-owned occupation column. -/
def endpointNeutralShadowIndex
    (source : G.State) (who : ι) (action : G.Act who) :
    germ.PlayerNeutralOccupationIndex who :=
  if neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0 then
    .inr ⟨(source, action), neutral⟩
  else
    .inl source

omit [DecidableEq G.State] in
/-- The neutral shadow index always declares the actual public source,
including on the strict branch which falls back to the prescribed row. -/
@[simp]
theorem playerNeutralOccupationSource_endpointNeutralShadowIndex
    (source : G.State) (who : ι) (action : G.Act who) :
    germ.playerNeutralOccupationSource who
        (germ.endpointNeutralShadowIndex source who action) =
      source := by
  simp only [endpointNeutralShadowIndex]
  split_ifs <;>
    rfl

omit [DecidableEq G.State] in
/-- Endpoint-neutral actions are represented by their genuine operational
neutral-action index. -/
theorem endpointNeutralShadowIndex_eq_neutral
    (source : G.State) (who : ι) (action : G.Act who)
    (neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0) :
    germ.endpointNeutralShadowIndex source who action =
      .inr ⟨(source, action), neutral⟩ := by
  simp only [endpointNeutralShadowIndex, dif_pos neutral]

omit [DecidableEq G.State] in
/-- Every nonneutral endpoint action is represented by the prescribed
fallback row at its source. -/
theorem endpointNeutralShadowIndex_eq_baseline
    (source : G.State) (who : ι) (action : G.Act who)
    (strict :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action ≠ 0) :
    germ.endpointNeutralShadowIndex source who action =
      .inl source := by
  simp only [endpointNeutralShadowIndex, dif_neg strict]

omit [DecidableEq G.State] in
/-- Endpoint excessiveness makes the two branches exhaustive in the
oriented form needed by the primary account. -/
theorem endpointContinuationGain_eq_zero_or_neg
    (source : G.State) (who : ι) (action : G.Act who) :
    G.finkContinuationGain germ.endpointValue
          germ.endpointFinkPoint source who action = 0 ∨
      G.finkContinuationGain germ.endpointValue
          germ.endpointFinkPoint source who action < 0 := by
  by_cases gain_zero :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0
  · exact Or.inl gain_zero
  · exact Or.inr
      (lt_of_le_of_ne
        (germ.finkContinuationGain_endpointValue_nonpos
          source who action)
        gain_zero)

/-- Push a behavior distribution through the strict/neutral shadow map. -/
def endpointNeutralShadowSelection
    (source : G.State) (who : ι) (deviation : PMF (G.Act who)) :
    PMF (germ.PlayerNeutralOccupationIndex who) :=
  PMF.map (germ.endpointNeutralShadowIndex source who) deviation

omit [DecidableEq G.State] in
/-- The shadow selection has no mass at an index with the wrong source. -/
theorem endpointNeutralShadowSelection_source_compatible
    (source : G.State) (who : ι) (deviation : PMF (G.Act who))
    (index : germ.PlayerNeutralOccupationIndex who)
    (index_mem :
      germ.endpointNeutralShadowSelection source who deviation index ≠ 0) :
    germ.playerNeutralOccupationSource who index = source := by
  have support_mem :
      index ∈
        (germ.endpointNeutralShadowSelection
          source who deviation).support := by
    exact (PMF.mem_support_iff
      (germ.endpointNeutralShadowSelection source who deviation)
      index).2
      index_mem
  rcases
      (PMF.mem_support_map_iff
        (germ.endpointNeutralShadowIndex source who)
        deviation index).1 support_mem with
    ⟨action, _, index_eq⟩
  rw [← index_eq]
  exact
    germ.playerNeutralOccupationSource_endpointNeutralShadowIndex
      source who action

/-- Lift the full shadow PMF to the subtype expected by an active-family
calendar account instantiated with `Finset.univ`. -/
def fullEndpointNeutralShadowSelection
    (source : G.State) (who : ι) (deviation : PMF (G.Act who)) :
    PMF
      {index : germ.PlayerNeutralOccupationIndex who //
        index ∈ (Finset.univ :
          Finset (germ.PlayerNeutralOccupationIndex who))} :=
  PMF.map
    (fun index => ⟨index, Finset.mem_univ index⟩)
    (germ.endpointNeutralShadowSelection source who deviation)

omit [DecidableEq G.State] in
/-- The lifted full-family selector is source compatible. -/
theorem fullEndpointNeutralShadowSelection_source_compatible
    (source : G.State) (who : ι) (deviation : PMF (G.Act who))
    (index :
      {index : germ.PlayerNeutralOccupationIndex who //
        index ∈ (Finset.univ :
          Finset (germ.PlayerNeutralOccupationIndex who))})
    (index_mem :
      germ.fullEndpointNeutralShadowSelection
          source who deviation index ≠ 0) :
    germ.playerNeutralOccupationSource who index.1 = source := by
  have support_mem :
      index ∈
        (germ.fullEndpointNeutralShadowSelection
          source who deviation).support := by
    exact (PMF.mem_support_iff
      (germ.fullEndpointNeutralShadowSelection
        source who deviation) index).2 index_mem
  change
    index ∈
      (PMF.map
        (fun ambientIndex :
            germ.PlayerNeutralOccupationIndex who =>
          ⟨ambientIndex, Finset.mem_univ ambientIndex⟩)
        (germ.endpointNeutralShadowSelection
          source who deviation)).support
    at support_mem
  rcases
      (PMF.mem_support_map_iff
        (fun ambientIndex :
            germ.PlayerNeutralOccupationIndex who =>
          ⟨ambientIndex, Finset.mem_univ ambientIndex⟩)
        (germ.endpointNeutralShadowSelection
          source who deviation) index).1 support_mem with
    ⟨ambientIndex, ambient_mem, index_eq⟩
  have ambient_ne_zero :
      germ.endpointNeutralShadowSelection
          source who deviation ambientIndex ≠ 0 :=
    (PMF.mem_support_iff
      (germ.endpointNeutralShadowSelection
        source who deviation) ambientIndex).1 ambient_mem
  have source_eq :=
    germ.endpointNeutralShadowSelection_source_compatible
      source who deviation ambientIndex ambient_ne_zero
  have value_eq : index.1 = ambientIndex := by
    simpa only using congrArg Subtype.val index_eq.symm
  simpa only [value_eq] using source_eq

/-- Predictable full-family neutral shadow selector induced by a
state-history-dependent action distribution of one fixed player. -/
def predictableFullEndpointNeutralShadowSelection
    (who : ι)
    (deviation :
      ∀ n, (Fin (n + 1) → G.State) → PMF (G.Act who)) :
    ∀ n, (Fin (n + 1) → G.State) →
      PMF
        {index : germ.PlayerNeutralOccupationIndex who //
          index ∈ (Finset.univ :
            Finset (germ.PlayerNeutralOccupationIndex who))} :=
  fun n history =>
    germ.fullEndpointNeutralShadowSelection
      (history (Fin.last n)) who (deviation n history)

omit [DecidableEq G.State] in
/-- The predictable selector produced from any state-history-dependent
action distribution meets the exact source-compatibility hypothesis of the
full-family calendar account. -/
theorem predictableFullEndpointNeutralShadowSelection_source_compatible
    (who : ι)
    (deviation :
      ∀ n, (Fin (n + 1) → G.State) → PMF (G.Act who)) :
    ∀ n history index,
      germ.predictableFullEndpointNeutralShadowSelection
          who deviation n history index ≠ 0 →
        germ.playerNeutralOccupationSource who index.1 =
          history (Fin.last n) := by
  intro n history index index_mem
  exact
    germ.fullEndpointNeutralShadowSelection_source_compatible
      (history (Fin.last n)) who (deviation n history)
      index index_mem

/-- Semantic moving state kernel of one pure action after the endpoint
strict/neutral shadow replacement. -/
def endpointNeutralShadowStateKernelAt
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) (action : G.Act who) :
    PMF G.State :=
  if G.finkContinuationGain germ.endpointValue
      germ.endpointFinkPoint source who action = 0 then
    G.finkPureDeviationStateKernel
      (germ.finkPointAt ht) source who action
  else
    G.finkStateKernel (germ.finkPointAt ht) source

omit [DecidableEq G.State] in
/-- Looking up the pushed occupation index gives exactly the semantic
strict/neutral shadow kernel. -/
theorem finkPlayerNeutralOccupationKernelAt_endpointNeutralShadowIndex
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) (action : G.Act who) :
    germ.finkPlayerNeutralOccupationKernelAt ht who
        (germ.endpointNeutralShadowIndex source who action) =
      germ.endpointNeutralShadowStateKernelAt
        ht source who action := by
  by_cases neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0
  · simp only [endpointNeutralShadowIndex, dif_pos neutral,
      endpointNeutralShadowStateKernelAt, if_pos neutral,
      finkPlayerNeutralOccupationKernelAt,
      finkActualOccupationKernelAt, occupationKernel,
      playerNeutralOccupationIndexEmbedding,
      ContinuationNeutralAction.source]
  · simp only [endpointNeutralShadowIndex, dif_neg neutral,
      endpointNeutralShadowStateKernelAt, if_neg neutral,
      finkPlayerNeutralOccupationKernelAt,
      finkActualOccupationKernelAt, occupationKernel,
      playerNeutralOccupationIndexEmbedding]

omit [DecidableEq G.State] in
/-- The mixed transition generated by the full-family selector is exactly
the behavior deviation with endpoint-strict actions replaced by the moving
prescribed transition. -/
theorem mixedTransitionComparison_fullEndpointNeutralShadowSelection
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) (deviation : PMF (G.Act who)) :
    mixedTransitionComparison
        (fun index :
            {index : germ.PlayerNeutralOccupationIndex who //
              index ∈ (Finset.univ :
                Finset (germ.PlayerNeutralOccupationIndex who))} =>
          germ.finkPlayerNeutralOccupationKernelAt ht who index.1)
        (fun _ _ =>
          germ.fullEndpointNeutralShadowSelection
            source who deviation)
        0 (fun _ => source) =
      deviation.bind
        (germ.endpointNeutralShadowStateKernelAt ht source who) := by
  simp only [mixedTransitionComparison,
    fullEndpointNeutralShadowSelection,
    endpointNeutralShadowSelection]
  rw [PMF.bind_map, PMF.bind_map]
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro action _
  exact
    germ.finkPlayerNeutralOccupationKernelAt_endpointNeutralShadowIndex
      ht source who action

/-- Moving neutral charge of one action.  Endpoint-strict action mass is
reserved for the primary endpoint-value account and contributes zero here. -/
def endpointNeutralMovingCharge
    (B : G.State → Payoff ι) (t : ℝ)
    (source : G.State) (who : ι) (action : G.Act who) : ℝ :=
  if neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0 then
    germ.rawPlayerNeutralOccupationCharge B who t
      (.inr ⟨(source, action), neutral⟩)
  else
    0

omit [DecidableEq G.State] in
/-- Pushing a behavioral deviation to the full player-neutral family
preserves exactly its moving endpoint-neutral charge. -/
theorem expect_fullEndpointNeutralShadowSelection_charge
    (B : G.State → Payoff ι) (t : ℝ)
    (source : G.State) (who : ι) (deviation : PMF (G.Act who)) :
    expect
        (germ.fullEndpointNeutralShadowSelection
          source who deviation)
        (fun index =>
          germ.rawPlayerNeutralOccupationCharge B who t index.1) =
      expect deviation
        (germ.endpointNeutralMovingCharge
          B t source who) := by
  simp only [fullEndpointNeutralShadowSelection,
    endpointNeutralShadowSelection]
  rw [expect_map, expect_map]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro action _
  by_cases neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0
  · simp only [endpointNeutralMovingCharge, dif_pos neutral,
      endpointNeutralShadowIndex, rawPlayerNeutralOccupationCharge]
  · simp only [endpointNeutralMovingCharge, dif_neg neutral,
      endpointNeutralShadowIndex, rawPlayerNeutralOccupationCharge]

/-- Endpoint continuation loss assigned to the strict branch.  It is zero
on endpoint-neutral actions and equals minus the endpoint continuation gain
on every other action. -/
def endpointStrictContinuationLoss
    (source : G.State) (who : ι) (action : G.Act who) : ℝ :=
  if G.finkContinuationGain germ.endpointValue
      germ.endpointFinkPoint source who action = 0 then
    0
  else
    -G.finkContinuationGain germ.endpointValue
      germ.endpointFinkPoint source who action

omit [DecidableEq G.State] in
/-- Strict continuation loss is nonnegative. -/
theorem endpointStrictContinuationLoss_nonneg
    (source : G.State) (who : ι) (action : G.Act who) :
    0 ≤ germ.endpointStrictContinuationLoss source who action := by
  by_cases neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0
  · simp [endpointStrictContinuationLoss, neutral]
  · simp only [endpointStrictContinuationLoss, if_neg neutral,
      neg_nonneg]
    exact
      germ.finkContinuationGain_endpointValue_nonpos
        source who action

omit [DecidableEq G.State] in
/-- A nonneutral action has strictly positive endpoint continuation loss. -/
theorem endpointStrictContinuationLoss_pos
    (source : G.State) (who : ι) (action : G.Act who)
    (strict :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action ≠ 0) :
    0 < germ.endpointStrictContinuationLoss source who action := by
  simp only [endpointStrictContinuationLoss, if_neg strict, neg_pos]
  exact
    (germ.endpointContinuationGain_eq_zero_or_neg
      source who action).resolve_left strict

omit [DecidableEq G.State] in
/-- At the endpoint, replacing one strict action by the prescribed row
increases the owner's expected continuation value by exactly its strict
continuation loss.  Neutral actions are unchanged. -/
theorem endpointNeutralShadowKernel_value_sub_actual
    (source : G.State) (who : ι) (action : G.Act who) :
    expect
          (germ.playerNeutralOccupationKernel who
            (germ.endpointNeutralShadowIndex source who action))
          (fun state => germ.endpointValue state who) -
        expect
          (G.finkPureDeviationStateKernel
            germ.endpointFinkPoint source who action)
          (fun state => germ.endpointValue state who) =
      germ.endpointStrictContinuationLoss source who action := by
  by_cases neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0
  · simp only [endpointNeutralShadowIndex, dif_pos neutral,
      playerNeutralOccupationKernel, ContinuationNeutralAction.kernel,
      ContinuationNeutralAction.source,
      endpointStrictContinuationLoss, if_pos neutral, sub_self]
  · have gain_identity :=
      G.finkContinuationGain_eq_expect_stateKernels
        germ.endpointValue germ.endpointFinkPoint source who action
    simp only [endpointNeutralShadowIndex, dif_neg neutral,
      playerNeutralOccupationKernel, endpointStrictContinuationLoss,
      if_neg neutral]
    linarith

omit [DecidableEq G.State] in
/-- The endpoint owner-value difference between the full neutral shadow
mixture and the actual behavioral deviation is exactly the expected strict
continuation loss. -/
theorem endpointNeutralShadowSelection_value_sub_actual
    (source : G.State) (who : ι) (deviation : PMF (G.Act who)) :
    expect
          ((germ.endpointNeutralShadowSelection
            source who deviation).bind
            (germ.playerNeutralOccupationKernel who))
          (fun state => germ.endpointValue state who) -
        expect
          (deviation.bind fun action =>
            G.finkPureDeviationStateKernel
              germ.endpointFinkPoint source who action)
          (fun state => germ.endpointValue state who) =
      expect deviation
        (germ.endpointStrictContinuationLoss source who) := by
  unfold endpointNeutralShadowSelection
  rw [PMF.bind_map, expect_bind, expect_bind, ← expect_sub]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro action _
  exact
    germ.endpointNeutralShadowKernel_value_sub_actual
      source who action

/-- Total predictable mass assigned to endpoint-strict actions by one
behavior distribution. -/
def endpointStrictMass
    (source : G.State) (who : ι) (deviation : PMF (G.Act who)) : ℝ :=
  expect deviation (fun action =>
    if G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0 then
      0
    else
      1)

omit [DecidableEq G.State] in
/-- Finiteness gives one positive endpoint loss gap for every player,
source, and endpoint-strict action. -/
theorem exists_uniform_endpointStrictContinuationLoss :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ source who (action : G.Act who),
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action ≠ 0 →
          δ ≤
            germ.endpointStrictContinuationLoss
              source who action := by
  let ActionIndex := Σ agent : G.FinkAgent, G.FinkAction agent
  let strict : ActionIndex → Prop := fun index =>
    G.finkContinuationGain germ.endpointValue
      germ.endpointFinkPoint index.1.1 index.1.2 index.2 ≠ 0
  let loss : ActionIndex → ℝ := fun index =>
    germ.endpointStrictContinuationLoss
      index.1.1 index.1.2 index.2
  obtain ⟨δ, δ_pos, δ_le⟩ :=
    exists_pos_le_of_finite strict loss (by
      intro index index_strict
      exact germ.endpointStrictContinuationLoss_pos
        index.1.1 index.1.2 index.2 index_strict)
  refine ⟨δ, δ_pos, ?_⟩
  intro source who action action_strict
  exact δ_le ⟨(source, who), action⟩ action_strict

omit [DecidableEq G.State] in
/-- Uniform strict gap converts endpoint-strict behavioral mass into the
primary expected continuation-loss account. -/
theorem endpointStrictMass_mul_gap_le_expectedLoss
    {δ : ℝ}
    (gap :
      ∀ source who (action : G.Act who),
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action ≠ 0 →
          δ ≤
            germ.endpointStrictContinuationLoss source who action)
    (source : G.State) (who : ι) (deviation : PMF (G.Act who)) :
    δ * germ.endpointStrictMass source who deviation ≤
      expect deviation
        (germ.endpointStrictContinuationLoss source who) := by
  unfold endpointStrictMass
  rw [← expect_const_mul]
  apply expect_mono
  intro action
  by_cases neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0
  · simp [endpointStrictContinuationLoss, neutral]
  · simpa only [endpointStrictContinuationLoss,
      if_neg neutral, mul_one] using
      gap source who action neutral

/-- Actual moving state kernel induced by a unilateral behavior
distribution against the other players' moving Fink profile. -/
def behaviorDeviationStateKernelAt
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) (deviation : PMF (G.Act who)) :
    PMF G.State :=
  deviation.bind fun action =>
    G.finkPureDeviationStateKernel
      (germ.finkPointAt ht) source who action

/-- State-history-dependent actual moving state kernel induced by one
player's action distribution. -/
def predictableBehaviorDeviationStateKernelAt
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (deviation :
      ∀ n, (Fin (n + 1) → G.State) → PMF (G.Act who)) :
    ∀ n, (Fin (n + 1) → G.State) → PMF G.State :=
  fun n history =>
    germ.behaviorDeviationStateKernelAt ht
      (history (Fin.last n)) who (deviation n history)

omit [DecidableEq G.State] in
/-- If every action in the behavior support is endpoint-neutral, the local
neutral shadow transition is exactly the actual moving deviation
transition. -/
theorem mixedTransitionComparison_eq_behaviorDeviationStateKernelAt
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) (deviation : PMF (G.Act who))
    (support_neutral :
      ∀ action, deviation action ≠ 0 →
        G.finkContinuationGain germ.endpointValue
          germ.endpointFinkPoint source who action = 0) :
    mixedTransitionComparison
        (fun index :
            {index : germ.PlayerNeutralOccupationIndex who //
              index ∈ (Finset.univ :
                Finset (germ.PlayerNeutralOccupationIndex who))} =>
          germ.finkPlayerNeutralOccupationKernelAt ht who index.1)
        (fun _ _ =>
          germ.fullEndpointNeutralShadowSelection
            source who deviation)
        0 (fun _ => source) =
      germ.behaviorDeviationStateKernelAt
        ht source who deviation := by
  rw [
    germ.mixedTransitionComparison_fullEndpointNeutralShadowSelection
      ht source who deviation]
  unfold behaviorDeviationStateKernelAt
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro action action_mem
  have action_ne_zero : deviation action ≠ 0 :=
    (PMF.mem_support_iff deviation action).1 action_mem
  have neutral := support_neutral action action_ne_zero
  simp only [endpointNeutralShadowStateKernelAt, if_pos neutral]

omit [DecidableEq G.State] in
/-- Under predictable support-neutrality, the full neutral shadow comparison
kernel agrees at every public history with the actual moving behavior
deviation kernel. -/
theorem predictableMixedTransitionComparison_eq_behaviorDeviation
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (deviation :
      ∀ n, (Fin (n + 1) → G.State) → PMF (G.Act who))
    (support_neutral :
      ∀ n history action,
        deviation n history action ≠ 0 →
          G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint
              (history (Fin.last n)) who action = 0) :
    mixedTransitionComparison
        (fun index :
            {index : germ.PlayerNeutralOccupationIndex who //
              index ∈ (Finset.univ :
                Finset (germ.PlayerNeutralOccupationIndex who))} =>
          germ.finkPlayerNeutralOccupationKernelAt ht who index.1)
        (germ.predictableFullEndpointNeutralShadowSelection
          who deviation) =
      germ.predictableBehaviorDeviationStateKernelAt
        ht who deviation := by
  funext n history
  exact
    germ.mixedTransitionComparison_eq_behaviorDeviationStateKernelAt
      ht (history (Fin.last n)) who (deviation n history)
      (support_neutral n history)

/-- Fixed-epoch punctured-potential account on the state-history law of any
predictable endpoint-neutral action distribution.

This is the direct operational use of the full-family scaled-potential
branch: `active = Finset.univ`, so no analytic deflation or conditional
renormalization is required. -/
theorem
    AnalyticScaledChargedOccupationPotential.expected_behaviorNeutralCharge_le
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ index :
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ (Finset.univ :
              Finset (germ.PlayerNeutralOccupationIndex who))},
        germ.rawPlayerNeutralOccupationCharge B who t index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                ht who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P t)
            index)
    (initial : G.State)
    (deviation :
      ∀ n, (Fin (n + 1) → G.State) → PMF (G.Act who))
    (support_neutral :
      ∀ n history action,
        deviation n history action ≠ 0 →
          G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint
              (history (Fin.last n)) who action = 0)
    (T : ℕ) :
    expect
        (adaptiveHistoryLaw
          (adaptiveMarkovStep initial
            (germ.predictableBehaviorDeviationStateKernelAt
              ht who deviation))
          (T + 1))
        (mixedTransitionCostSum
          (germ.predictableFullEndpointNeutralShadowSelection
            who deviation)
          (fun index =>
            germ.rawPlayerNeutralOccupationCharge
              B who t index.1) T) ≤
      2 * finiteStatePotentialBound
        (germ.puncturedPlayerNeutralPotentialAt B who P t) := by
  have bound :=
    expected_activeCharge_le
      germ B who P
      (Finset.univ :
        Finset (germ.PlayerNeutralOccupationIndex who))
      ht hcharge initial
      (germ.predictableFullEndpointNeutralShadowSelection
        who deviation)
      (germ.predictableFullEndpointNeutralShadowSelection_source_compatible
        who deviation)
      T
  rw [
    germ.predictableMixedTransitionComparison_eq_behaviorDeviation
      ht who deviation support_neutral] at bound
  exact bound

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
