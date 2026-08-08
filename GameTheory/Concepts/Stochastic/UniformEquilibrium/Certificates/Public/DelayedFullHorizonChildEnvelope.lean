/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FullHorizonPublicHistoryEnvelopeRealization
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FullHorizonPublicHistoryOptimalDeviation
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.VariableStoppingPrefixLawCompiler

/-!
# Delayed full-horizon envelopes for stopped child systems

This file connects finite child adaptive-potential systems to the
full-history Bellman envelope.  A public stopping rule may select a child
strictly before a fixed fuel horizon, and the strategic dispatcher may enter
that child immediately.  For accounting, however, the prefix potential is
kept as one Bellman envelope until the common fuel horizon.  Its terminal
obstacle reads the complete public history, recovers the stopped
base/suffix decomposition, and evaluates the selected child's potential on
that suffix.

This delayed construction is compatible with the expectation-level child
interface: before `fuel`, harmonicity and unilateral superharmonicity come
from the finite full-history envelope; from `fuel` onward, the existing
stopped-suffix compiler consumes the child systems.  No pointwise
immediate-switch Bellman hypothesis is required.

The resulting alternative is explicit.  Either every player's deviation
envelope is close to its prescribed terminal value, in which case target
anchors produce a parent adaptive-potential system, or a prescribed-supported
ordinary public history carries a strict player-owned Bellman gap.  The
unsafe branch also records the canonical finite-horizon unilateral deviation
that realizes strict domination of the selected-child obstacle.

The stopping region stored below is bookkeeping required by the existing
prefix-law interface.  This module does not prove that the region constructs
the online rule, nor does it construct target anchors or rule out the unsafe
branch.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι Child : Type} {G : StochasticGame ι}

/-- Finite stopped-child data used by the delayed full-horizon compiler. -/
structure DelayedFullHorizonChildEnvelopeData
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] [Fintype Child]
    (entry : Child → G.State) (childTarget : Child → Payoff ι)
    (childError : ℝ) (fuel : ℕ) where
  family :
    G.FiniteChildAdaptivePotentialFamily
      entry childTarget childError
  rule : G.OnlineCausalBoundedStoppingRule fuel
  selection : G.BehaviorProfile
  initial : G.State
  observe : G.BoundedStoppedHistory fuel → Child
  entry_eq : ∀ base : G.BoundedStoppedHistory fuel,
    base.2.2 = entry (observe base)
  region : G.FinitePublicCoinStoppingRegion
  rank_le_fuel : region.rank initial ≤ fuel

namespace DelayedFullHorizonChildEnvelopeData

open FiniteFullHistoryControlledStoppingModel

variable
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] [Fintype Child]
    {entry : Child → G.State} {childTarget : Child → Payoff ι}
    {childError : ℝ} {fuel : ℕ}
    (data :
      G.DelayedFullHorizonChildEnvelopeData
        entry childTarget childError fuel)

/-- The actual root profile: selection until the online stopping rule fires,
and the selected child profile afterwards. -/
def dispatcher : G.BehaviorProfile :=
  G.causalTerminalChildDispatcher data.rule data.selection
    (data.family.observedStoppedProfile data.observe)

/-- Evaluate a stopped-child history potential at the stopped suffix encoded
by a complete public history at the common fuel horizon. -/
def stoppedPotentialObstacle
    (childPotential :
      G.BoundedStoppedHistory fuel → G.HistoryPotential)
    (history : G.Hist fuel) : ℝ :=
  let path :=
    G.rootStoppedPathOfHistory data.rule.selector
      (le_refl fuel) history
  childPotential path.1 (fuel - path.1.1.val) path.2

/-- The full-horizon obstacle retains the entire realized post-stop suffix.
In particular, it does not replace an early-selected child by its initial
target or its time-zero potential. -/
theorem stoppedPotentialObstacle_eq_realizedSuffix
    (childPotential :
      G.BoundedStoppedHistory fuel → G.HistoryPotential)
    (history : G.Hist fuel) :
    data.stoppedPotentialObstacle childPotential history =
      let path :=
        G.rootStoppedPathOfHistory data.rule.selector
          (le_refl fuel) history
      childPotential path.1 (fuel - path.1.1.val) path.2 :=
  rfl

/-- Terminal obstacle supplied by the selected child's lower potential. -/
def lowerObstacle (history : G.Hist fuel) (who : ι) : ℝ :=
  data.stoppedPotentialObstacle
    (data.family.stoppedLowerPotential data.observe who) history

/-- Terminal obstacle supplied by the selected child's upper potential. -/
def upperObstacle (history : G.Hist fuel) (who : ι) : ℝ :=
  data.stoppedPotentialObstacle
    (data.family.stoppedUpperPotential data.observe who) history

/-- Terminal obstacle supplied by the selected child's deviation potential. -/
def deviationObstacle (history : G.Hist fuel) (who : ι) : ℝ :=
  data.stoppedPotentialObstacle
    (data.family.stoppedDeviationPotential data.observe who) history

/-- Prescribed lower Bellman envelope before the common fuel horizon. -/
def prefixLowerPotential (who : ι) : G.HistoryPotential :=
  FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential
    data.dispatcher data.lowerObstacle who

/-- Prescribed upper Bellman envelope before the common fuel horizon. -/
def prefixUpperPotential (who : ι) : G.HistoryPotential :=
  FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential
    data.dispatcher data.upperObstacle who

/-- Worst-unilateral Bellman envelope before the common fuel horizon. -/
def prefixDeviationPotential (who : ι) : G.HistoryPotential :=
  FiniteFullHistoryControlledStoppingModel.worstUnilateralHistoryPotential
    data.dispatcher data.deviationObstacle who

/-- Parent lower potential: the delayed envelope before `fuel`, and the
stopped child potential afterwards. -/
def lowerPotential (who : ι) : G.HistoryPotential :=
  G.prefixThenStoppedChildHistoryPotential data.rule.selector
    (data.prefixLowerPotential who)
    (data.family.stoppedLowerPotential data.observe who)

/-- Parent upper potential: the delayed envelope before `fuel`, and the
stopped child potential afterwards. -/
def upperPotential (who : ι) : G.HistoryPotential :=
  G.prefixThenStoppedChildHistoryPotential data.rule.selector
    (data.prefixUpperPotential who)
    (data.family.stoppedUpperPotential data.observe who)

/-- Parent deviation potential: the delayed unilateral envelope before
`fuel`, and the stopped child deviation potential afterwards. -/
def deviationPotential (who : ι) : G.HistoryPotential :=
  G.prefixThenStoppedChildHistoryPotential data.rule.selector
    (data.prefixDeviationPotential who)
    (data.family.stoppedDeviationPotential data.observe who)

@[simp] theorem lowerPotential_at_horizon
    (who : ι) (history : G.Hist fuel) :
    data.lowerPotential who fuel history =
      data.prefixLowerPotential who fuel history := by
  unfold lowerPotential prefixLowerPotential
  simp only [prefixThenStoppedChildHistoryPotential, le_refl,
    ↓reduceDIte]
  rw [
    FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential_at_horizon
      data.dispatcher data.lowerObstacle who history
  ]
  rfl

@[simp] theorem upperPotential_at_horizon
    (who : ι) (history : G.Hist fuel) :
    data.upperPotential who fuel history =
      data.prefixUpperPotential who fuel history := by
  unfold upperPotential prefixUpperPotential
  simp only [prefixThenStoppedChildHistoryPotential, le_refl,
    ↓reduceDIte]
  rw [
    FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential_at_horizon
      data.dispatcher data.upperObstacle who history
  ]
  rfl

@[simp] theorem deviationPotential_at_horizon
    (who : ι) (history : G.Hist fuel) :
    data.deviationPotential who fuel history =
      data.prefixDeviationPotential who fuel history := by
  unfold deviationPotential prefixDeviationPotential
  simp only [prefixThenStoppedChildHistoryPotential, le_refl,
    ↓reduceDIte]
  rw [
    FiniteFullHistoryControlledStoppingModel.worstUnilateralHistoryPotential_at_horizon
      data.dispatcher data.deviationObstacle who history
  ]
  rfl

theorem lowerPotential_eq_prefix_of_le
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_le : time ≤ fuel) :
    data.lowerPotential who time history =
      data.prefixLowerPotential who time history := by
  by_cases time_eq : time = fuel
  · subst time
    exact data.lowerPotential_at_horizon who history
  · have time_lt : time < fuel := lt_of_le_of_ne time_le time_eq
    simp [lowerPotential, prefixThenStoppedChildHistoryPotential,
      Nat.not_le.mpr time_lt]

theorem upperPotential_eq_prefix_of_le
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_le : time ≤ fuel) :
    data.upperPotential who time history =
      data.prefixUpperPotential who time history := by
  by_cases time_eq : time = fuel
  · subst time
    exact data.upperPotential_at_horizon who history
  · have time_lt : time < fuel := lt_of_le_of_ne time_le time_eq
    simp [upperPotential, prefixThenStoppedChildHistoryPotential,
      Nat.not_le.mpr time_lt]

theorem deviationPotential_eq_prefix_of_le
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_le : time ≤ fuel) :
    data.deviationPotential who time history =
      data.prefixDeviationPotential who time history := by
  by_cases time_eq : time = fuel
  · subst time
    exact data.deviationPotential_at_horizon who history
  · have time_lt : time < fuel := lt_of_le_of_ne time_le time_eq
    simp [deviationPotential, prefixThenStoppedChildHistoryPotential,
      Nat.not_le.mpr time_lt]

/-- One common nonnegative bound for the three finite-horizon envelope
families. -/
def prefixPotentialBound : ℝ :=
  max
    (FiniteFullHistoryControlledStoppingModel.fullHorizonEnvelopePotentialBound
        data.dispatcher data.lowerObstacle)
    (max
      (FiniteFullHistoryControlledStoppingModel.fullHorizonEnvelopePotentialBound
          data.dispatcher data.upperObstacle)
      (FiniteFullHistoryControlledStoppingModel.fullHorizonEnvelopePotentialBound
          data.dispatcher data.deviationObstacle))

theorem prefixPotentialBound_nonneg :
    0 ≤ data.prefixPotentialBound := by
  exact le_trans
    (FiniteFullHistoryControlledStoppingModel.fullHorizonEnvelopePotentialBound_nonneg
        data.dispatcher data.lowerObstacle)
    (le_max_left _ _)

theorem abs_lowerPotential_le_prefixPotentialBound
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    |data.lowerPotential who time history| ≤
      data.prefixPotentialBound := by
  rw [data.lowerPotential_eq_prefix_of_le
    who history (Nat.le_of_lt time_lt)]
  apply le_trans
    (abs_prescribedHistoryPotential_le_fullHorizonEnvelopePotentialBound
        data.dispatcher data.lowerObstacle who history
        (Nat.le_of_lt time_lt))
  exact le_max_left _ _

theorem abs_upperPotential_le_prefixPotentialBound
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    |data.upperPotential who time history| ≤
      data.prefixPotentialBound := by
  rw [data.upperPotential_eq_prefix_of_le
    who history (Nat.le_of_lt time_lt)]
  apply le_trans
    (abs_prescribedHistoryPotential_le_fullHorizonEnvelopePotentialBound
        data.dispatcher data.upperObstacle who history
        (Nat.le_of_lt time_lt))
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem abs_deviationPotential_le_prefixPotentialBound
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    |data.deviationPotential who time history| ≤
      data.prefixPotentialBound := by
  rw [data.deviationPotential_eq_prefix_of_le
    who history (Nat.le_of_lt time_lt)]
  apply le_trans
    (abs_worstUnilateralHistoryPotential_le_fullHorizonEnvelopePotentialBound
        data.dispatcher data.deviationObstacle who history
        (Nat.le_of_lt time_lt))
  exact le_trans (le_max_right _ _) (le_max_right _ _)

omit [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
private theorem historyContinuationEU_eq_of_next_eq
    (profile : G.BehaviorProfile)
    (left right : G.HistoryPotential)
    {time : ℕ} (history : G.Hist time)
    (next_eq :
      ∀ (action : G.JointAct) (next : G.State),
        left (time + 1)
            (Fin.snoc history.1 (history.2, action), next) =
          right (time + 1)
            (Fin.snoc history.1 (history.2, action), next)) :
    G.historyContinuationEU profile left history =
      G.historyContinuationEU profile right history := by
  unfold historyContinuationEU
  apply congrArg (expect (G.stageActionDist profile history))
  funext action
  apply congrArg (expect (G.transition history.2 action))
  funext next
  exact next_eq action next

theorem lowerPotential_harmonic
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    G.historyContinuationEU data.dispatcher
        (data.lowerPotential who) history =
      data.lowerPotential who time history := by
  rw [data.lowerPotential_eq_prefix_of_le
    who history (Nat.le_of_lt time_lt)]
  rw [historyContinuationEU_eq_of_next_eq
    data.dispatcher (data.lowerPotential who)
    (data.prefixLowerPotential who) history]
  · exact
      FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential_harmonic
          data.dispatcher data.lowerObstacle who history time_lt
  · intro action next
    exact data.lowerPotential_eq_prefix_of_le
      who
      ((Fin.snoc history.1 (history.2, action), next) :
        G.Hist (time + 1))
      (Nat.succ_le_of_lt time_lt)

theorem upperPotential_harmonic
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    G.historyContinuationEU data.dispatcher
        (data.upperPotential who) history =
      data.upperPotential who time history := by
  rw [data.upperPotential_eq_prefix_of_le
    who history (Nat.le_of_lt time_lt)]
  rw [historyContinuationEU_eq_of_next_eq
    data.dispatcher (data.upperPotential who)
    (data.prefixUpperPotential who) history]
  · exact
      FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential_harmonic
          data.dispatcher data.upperObstacle who history time_lt
  · intro action next
    exact data.upperPotential_eq_prefix_of_le
      who
      ((Fin.snoc history.1 (history.2, action), next) :
        G.Hist (time + 1))
      (Nat.succ_le_of_lt time_lt)

theorem deviationPotential_superharmonic
    (who : ι) (deviation : G.BehaviorStrategy who)
    {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    G.historyContinuationEU
        (Function.update data.dispatcher who deviation)
        (data.deviationPotential who) history ≤
      data.deviationPotential who time history := by
  rw [data.deviationPotential_eq_prefix_of_le
    who history (Nat.le_of_lt time_lt)]
  rw [historyContinuationEU_eq_of_next_eq
    (Function.update data.dispatcher who deviation)
    (data.deviationPotential who)
    (data.prefixDeviationPotential who) history]
  · exact
      worstUnilateralHistoryPotential_deviation_superharmonic
          data.dispatcher data.deviationObstacle who deviation
          history time_lt
  · intro action next
    exact data.deviationPotential_eq_prefix_of_le
      who
      ((Fin.snoc history.1 (history.2, action), next) :
        G.Hist (time + 1))
      (Nat.succ_le_of_lt time_lt)

/-- The delayed envelopes provide all bounded supportwise prefix data.
Absolute-gap charges and expectation-level prefix laws are generated by the
existing bounded-prefix compiler. -/
def boundedPrefixPotentials :
    G.BoundedVariableStoppingPrefixPotentials
      data.dispatcher data.initial fuel
      data.lowerPotential data.upperPotential
      data.deviationPotential where
  region := data.region
  rank_le_fuel := data.rank_le_fuel
  payoffBound := G.finiteStagePayoffBound
  potentialBound := data.prefixPotentialBound
  payoffBound_nonneg := G.finiteStagePayoffBound_nonneg
  potentialBound_nonneg := data.prefixPotentialBound_nonneg
  payoff_abs := fun state action who =>
    G.abs_stagePayoff_le_finiteStagePayoffBound state action who
  lower_potential_abs := by
    intro who time time_lt history _
    exact data.abs_lowerPotential_le_prefixPotentialBound
      who history time_lt
  upper_potential_abs := by
    intro who time time_lt history _
    exact data.abs_upperPotential_le_prefixPotentialBound
      who history time_lt
  deviation_potential_abs := by
    intro who _ time time_lt history _
    exact data.abs_deviationPotential_le_prefixPotentialBound
      who history time_lt
  lower_drift := by
    intro who time time_lt history _
    exact (data.lowerPotential_harmonic who history time_lt).ge
  upper_drift := by
    intro who time time_lt history _
    exact (data.upperPotential_harmonic who history time_lt).le
  deviation_drift := by
    intro who deviation time time_lt history _
    exact data.deviationPotential_superharmonic
      who deviation history time_lt

/-- Positive quantitative allocation used by the delayed composition.

`prefixError` amortizes the finite prefix bill, `slack` is the signed-tail
loss added to the child error, and `deviationAnchorError` plus
`deviationGapError` pays for the deviation potential's initial target
anchor. -/
structure ErrorBudget
    (_data :
      G.DelayedFullHorizonChildEnvelopeData
        entry childTarget childError fuel) where
  prefixError : ℝ
  slack : ℝ
  deviationAnchorError : ℝ
  deviationGapError : ℝ
  childError_nonneg : 0 ≤ childError
  prefixError_pos : 0 < prefixError
  slack_pos : 0 < slack
  deviationAnchorError_nonneg : 0 ≤ deviationAnchorError
  deviationGapError_nonneg : 0 ≤ deviationGapError
  deviationInitial_le :
    deviationAnchorError + deviationGapError ≤
      prefixError + (childError + slack)

namespace ErrorBudget

variable
    {data :
      G.DelayedFullHorizonChildEnvelopeData
        entry childTarget childError fuel}

/-- Error consumed by the stopped child tail, including the arbitrarily
small signed-tail slack. -/
def suffixError (budget : data.ErrorBudget) : ℝ :=
  childError + budget.slack

/-- Total error of the compiled parent system. -/
def parentError (budget : data.ErrorBudget) : ℝ :=
  budget.prefixError + budget.suffixError

theorem suffixError_nonneg (budget : data.ErrorBudget) :
    0 ≤ budget.suffixError :=
  add_nonneg budget.childError_nonneg budget.slack_pos.le

theorem parentError_pos (budget : data.ErrorBudget) :
    0 < budget.parentError :=
  add_pos_of_pos_of_nonneg budget.prefixError_pos
    budget.suffixError_nonneg

end ErrorBudget

/-- Root value of the prescribed finite-horizon process for the deviation
obstacle. -/
def prescribedDeviationRoot (who : ι) : ℝ :=
  let model :=
    G.finiteFullHistoryControlledStoppingModel
      data.dispatcher data.deviationObstacle
  model.prescribedPotential who
    (FinitePublicHistoryControlledStoppingModel.root
      (fuel := fuel) data.initial)

/-- Root value of the worst-unilateral finite-horizon process for the
deviation obstacle. -/
def worstDeviationRoot (who : ι) : ℝ :=
  let model :=
    G.finiteFullHistoryControlledStoppingModel
      data.dispatcher data.deviationObstacle
  model.worstCasePotential who
    (FinitePublicHistoryControlledStoppingModel.root
      (fuel := fuel) data.initial)

theorem deviationPotential_root_eq_worstDeviationRoot
    (who : ι) :
    data.deviationPotential who 0 (G.emptyHist data.initial) =
      data.worstDeviationRoot who := by
  rw [data.deviationPotential_eq_prefix_of_le
    who (G.emptyHist data.initial) (Nat.zero_le fuel)]
  rfl

theorem prescribedDeviationRoot_le_worstDeviationRoot
    (who : ι) :
    data.prescribedDeviationRoot who ≤
      data.worstDeviationRoot who := by
  exact
    Math.Probability.FiniteControlledStoppingModel.prescribedPotential_le_worstCasePotential
        (G.finiteFullHistoryControlledStoppingModel
          data.dispatcher data.deviationObstacle)
        who
        (FinitePublicHistoryControlledStoppingModel.root
          (fuel := fuel) data.initial)

/-- The finite-horizon deviation obstacle is safe at the root for every
player at the allocated gap tolerance. -/
def DeviationEnvelopeSafe (budget : data.ErrorBudget) : Prop :=
  ∀ who,
    data.worstDeviationRoot who ≤
      data.prescribedDeviationRoot who +
        budget.deviationGapError

/-- Target anchors not supplied by the Bellman envelope itself.

The lower and upper anchors concern the actual compiled root potentials.
The deviation anchor concerns the prescribed value of the deviation
terminal obstacle; root safety upgrades it to the worst-unilateral root
potential. -/
structure TargetAnchors
    (budget : data.ErrorBudget) (target : Payoff ι) : Prop where
  lower : ∀ who,
    |data.lowerPotential who 0 (G.emptyHist data.initial) -
        target who| ≤
      budget.parentError
  upper : ∀ who,
    |data.upperPotential who 0 (G.emptyHist data.initial) -
        target who| ≤
      budget.parentError
  prescribedDeviation : ∀ who,
    |data.prescribedDeviationRoot who - target who| ≤
      budget.deviationAnchorError

theorem deviationInitial_of_safe
    (budget : data.ErrorBudget) (target : Payoff ι)
    (anchors : data.TargetAnchors budget target)
    (safe : data.DeviationEnvelopeSafe budget)
    (who : ι) :
    |data.deviationPotential who 0 (G.emptyHist data.initial) -
        target who| ≤
      budget.parentError := by
  rw [data.deviationPotential_root_eq_worstDeviationRoot]
  unfold ErrorBudget.parentError ErrorBudget.suffixError
  rw [abs_le]
  constructor
  · have dominates :=
      data.prescribedDeviationRoot_le_worstDeviationRoot who
    have lower :=
      (abs_le.mp (anchors.prescribedDeviation who)).1
    have allocation := budget.deviationInitial_le
    have gap_nonneg := budget.deviationGapError_nonneg
    linarith
  · have upper :=
      (abs_le.mp (anchors.prescribedDeviation who)).2
    have safe_who := safe who
    have allocation := budget.deviationInitial_le
    linarith

/-- Expectation-level finite-prefix law generated by the delayed Bellman
envelopes and canonical absolute-gap charges. -/
def prefixLaw (budget : data.ErrorBudget) :=
  data.boundedPrefixPotentials.toVariableStoppingPrefixLaw
    budget.prefixError budget.prefixError_pos

/-- Post-fuel stopped-child caps at the original child error plus the
explicit positive signed-tail slack. -/
def suffixCaps (budget : data.ErrorBudget) :=
  data.family.variableStoppingSuffixCaps
    data.rule data.selection data.initial data.observe data.entry_eq
    data.prefixLowerPotential data.prefixUpperPotential
    data.prefixDeviationPotential
    (data.family.commonRootChildChargeTailBound
      data.dispatcher data.initial data.rule.selector data.observe
      budget.slack budget.slack_pos)

/-- In the safe branch, delayed full-horizon envelopes and the
expectation-level stopped-child systems compile to one ordinary parent
adaptive-potential system.

The output error is exactly
`prefixError + (childError + slack)`.  The finite prefix is paid once,
whereas the stopped child tails retain their original signed charges. -/
def toAdaptivePotentialSystemAt
    (budget : data.ErrorBudget) (target : Payoff ι)
    (anchors : data.TargetAnchors budget target)
    (safe : data.DeviationEnvelopeSafe budget) :
    G.AdaptivePotentialSystemAt
      data.dispatcher data.initial target budget.parentError := by
  simpa only [ErrorBudget.parentError, ErrorBudget.suffixError] using
    G.adaptivePotentialSystemAt_of_variableStopping
      (data.prefixLaw budget)
      (data.suffixCaps budget)
      anchors.lower anchors.upper
      (data.deviationInitial_of_safe budget target anchors safe)

/-- Certificate-level safe-branch output. -/
theorem toIsAdaptivePotentialCertificateAt
    (budget : data.ErrorBudget) (target : Payoff ι)
    (anchors : data.TargetAnchors budget target)
    (safe : data.DeviationEnvelopeSafe budget) :
    G.IsAdaptivePotentialCertificateAt
      data.initial target budget.parentError :=
  (data.toAdaptivePotentialSystemAt
    budget target anchors safe).toIsAdaptivePotentialCertificateAt

/-- Explicit unsafe-branch evidence.

The local field is a strict controlled-versus-prescribed continuation gap at
an ordinary public history with positive prescribed probability.  The
global field states that the canonical maximizing finite-horizon unilateral
deviation strictly improves the complete selected-child obstacle by more
than the allocated gap error. -/
structure UnsafeDeviation (budget : data.ErrorBudget) where
  who : ι
  root_not_safe :
    ¬data.worstDeviationRoot who ≤
      data.prescribedDeviationRoot who +
        budget.deviationGapError
  supportedGap :
    FiniteFullHistoryControlledStoppingModel.SupportedHistoryPositiveBellmanGap
        data.dispatcher data.deviationObstacle data.initial who
  canonicalStrict :
    data.prescribedDeviationRoot who +
        budget.deviationGapError <
      expect
        (G.histDist
          (Function.update data.dispatcher who
            (FiniteFullHistoryControlledStoppingModel.optimalFiniteHorizonDeviation
                data.dispatcher data.deviationObstacle who))
          data.initial fuel)
        (fun history => data.deviationObstacle history who)

/-- For one player, root safety or an ordinary supported strict Bellman
gap. -/
theorem rootSafe_or_supportedGap
    (budget : data.ErrorBudget) (who : ι) :
    data.worstDeviationRoot who ≤
        data.prescribedDeviationRoot who +
          budget.deviationGapError ∨
      Nonempty
        (FiniteFullHistoryControlledStoppingModel.SupportedHistoryPositiveBellmanGap
            data.dispatcher data.deviationObstacle
            data.initial who) := by
  simpa [worstDeviationRoot, prescribedDeviationRoot] using
    FiniteFullHistoryControlledStoppingModel.rootGap_le_or_supportedHistoryPositiveBellmanGap
        data.dispatcher data.deviationObstacle data.initial who
        budget.deviationGapError
        budget.deviationGapError_nonneg

/-- Exhaustive delayed-envelope split.

No negated leaf is hidden: failure of the safe all-player ceiling returns a
fixed owner, a prescribed-supported history and action with strict local
continuation gain, and an actual finite-horizon behavior deviation realizing
strict obstacle improvement. -/
theorem deviationEnvelopeSafe_or_unsafeDeviation
    (budget : data.ErrorBudget) :
    data.DeviationEnvelopeSafe budget ∨
      Nonempty (data.UnsafeDeviation budget) := by
  classical
  by_cases safe : data.DeviationEnvelopeSafe budget
  · exact Or.inl safe
  · apply Or.inr
    unfold DeviationEnvelopeSafe at safe
    obtain ⟨who, root_not_safe⟩ := not_forall.mp safe
    have split := data.rootSafe_or_supportedGap budget who
    rcases split with safe_who | gap
    · exact False.elim (root_not_safe safe_who)
    · refine ⟨{
        who := who
        root_not_safe := root_not_safe
        supportedGap := Classical.choice gap
        canonicalStrict := ?_
      }⟩
      rw [
        expect_obstacle_optimalFiniteHorizonDeviation_eq_worstCasePotential
            data.dispatcher data.deviationObstacle data.initial who
      ]
      simpa [worstDeviationRoot] using
        (lt_of_not_ge root_not_safe)

/-- Final local-response form of the delayed construction.

Given the child family, online stopping data, error budget and target
anchors, the construction either produces the complete parent
adaptive-potential system or exposes the fixed unsafe deviation witness.
The theorem does not assume the root safety branch. -/
theorem adaptivePotentialSystemAt_or_unsafeDeviation
    (budget : data.ErrorBudget) (target : Payoff ι)
    (anchors : data.TargetAnchors budget target) :
    Nonempty
        (G.AdaptivePotentialSystemAt
          data.dispatcher data.initial target budget.parentError) ∨
      Nonempty (data.UnsafeDeviation budget) := by
  rcases data.deviationEnvelopeSafe_or_unsafeDeviation budget with
    safe | obstruction
  · exact Or.inl ⟨data.toAdaptivePotentialSystemAt
      budget target anchors safe⟩
  · exact Or.inr obstruction

/-- Certificate-level form of the exhaustive local response. -/
theorem isAdaptivePotentialCertificateAt_or_unsafeDeviation
    (budget : data.ErrorBudget) (target : Payoff ι)
    (anchors : data.TargetAnchors budget target) :
    G.IsAdaptivePotentialCertificateAt
        data.initial target budget.parentError ∨
      Nonempty (data.UnsafeDeviation budget) := by
  rcases data.adaptivePotentialSystemAt_or_unsafeDeviation
    budget target anchors with parent | obstruction
  · exact Or.inl
      (Classical.choice parent).toIsAdaptivePotentialCertificateAt
  · exact Or.inr obstruction

end DelayedFullHorizonChildEnvelopeData

end StochasticGame
end GameTheory
