/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Adaptive.SystemEnforcementLedger
import UniformEquilibrium.Certificates.Public.FixedDepthAdaptivePotentialSplice

/-!
# Local self-generation of a public response

This file gives a recursive public-response compiler whose premises contain
no parent adaptive-potential system and no parent deviation-payoff cap.

The local data are:

* a finite deviation-safe public selector and an arbitrary public behavior
  during its fixed-depth selection block;
* a public-response ledger at every legally entered child;
* a well-founded strict rank decrease for every such child;
* one whole-vector transport inequality from the selector's terminal law to
  the parent target;
* bounded one-stage selection cost and an explicit blockwise budget for it.

Each child ledger contains the historywise prescribed and deviation-stage
inequalities used after entry.  During selection, action-independence of the
selector makes the transported child target harmonic under every unilateral
deviation; the absolute one-stage target/payoff gap is the local charge.
Thus the only blockwise hypothesis is the displayed finite-prefix cost
bound.  In particular, no eventual payoff inequality for the parent profile
or any parent deviation is assumed.

The proof reuses the fixed-depth disintegration theorem internally.  This is
not an adaptive-potential hypothesis: the adaptive systems supplied to that
theorem are compiled here from the strictly lower-rank public ledgers.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι Child Rank : Type} {G : StochasticGame ι}

/-- Public-response certificates available only at legal, strictly
lower-rank recursive children. -/
structure LegalLowerRankPublicResponseChildFamily
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [Fintype Child]
    (entry : Child → G.State) (target : Child → Payoff ι)
    (error : ℝ) (rankLt : Rank → Rank → Prop)
    (parentRank : Rank) (childRank : Child → Rank) where
  publicProfile : Child → G.PublicPhaseProfile
  ledger : ∀ child,
    G.PublicResponseEnforcementLedgerAt
      (publicProfile child) (entry child) (target child) error
  rank_wellFounded : WellFounded rankLt
  rank_decreases : ∀ child, rankLt (childRank child) parentRank

namespace LegalLowerRankPublicResponseChildFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {childError : ℝ} {rankLt : Rank → Rank → Prop}
  {parentRank : Rank} {childRank : Child → Rank}

/-- Compile the child public ledgers, and only the child ledgers, into the
explicit family expected by the fixed-depth splice theorem. -/
def toAdaptiveFamily
    (children :
      G.LegalLowerRankPublicResponseChildFamily
        entry target childError rankLt parentRank childRank) :
    G.FiniteChildAdaptivePotentialFamily entry target childError := by
  let system : ∀ child,
      G.AdaptivePotentialSystemAt
        (children.publicProfile child).behaviorProfile
        (entry child) (target child) childError :=
    fun child =>
      (children.ledger child).toPublicPhasePunishmentSystemAt
        |>.toAdaptivePotentialSystemAt G
  let finiteMaximum : ℕ :=
    Finset.univ.sup fun child => (system child).horizon
  refine {
    profile := fun child =>
      (children.publicProfile child).behaviorProfile
    system := system
    commonHorizon := max 2 finiteMaximum
    commonHorizon_ge_two := Nat.le_max_left 2 finiteMaximum
    horizon_le_common := ?_
  }
  intro child
  exact
    (Finset.le_sup (s := Finset.univ)
      (f := fun candidate => (system candidate).horizon)
      (Finset.mem_univ child)).trans
      (Nat.le_max_right 2 finiteMaximum)

@[simp]
theorem toAdaptiveFamily_lowerTerminalTarget
    (children :
      G.LegalLowerRankPublicResponseChildFamily
        entry target childError rankLt parentRank childRank)
    (child : Child) (who : ι) :
    children.toAdaptiveFamily.lowerTerminalTarget child who =
      target child who := by
  rfl

@[simp]
theorem toAdaptiveFamily_upperTerminalTarget
    (children :
      G.LegalLowerRankPublicResponseChildFamily
        entry target childError rankLt parentRank childRank)
    (child : Child) (who : ι) :
    children.toAdaptiveFamily.upperTerminalTarget child who =
      target child who := by
  rfl

@[simp]
theorem toAdaptiveFamily_deviationTerminalTarget
    (children :
      G.LegalLowerRankPublicResponseChildFamily
        entry target childError rankLt parentRank childRank)
    (child : Child) (who : ι) :
    children.toAdaptiveFamily.deviationTerminalTarget child who =
      target child who := by
  rfl

end LegalLowerRankPublicResponseChildFamily

/-- The nonrecursive local data at the parent.

`continuation_target_transport` is the sole continuation-value hypothesis:
the selector transports the complete child payoff vector to the parent
target.  `prefix_cost` is the sole blockwise incentive-accounting
hypothesis.  The structure deliberately has no field bounding a parent's
deviation payoff. -/
structure FixedDepthPublicResponseSelfGenerationData
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [Fintype Child]
    (entry : Child → G.State) (childTarget : Child → Payoff ι)
    (childError : ℝ) (rankLt : Rank → Rank → Prop)
    (parentRank : Rank) (childRank : Child → Rank)
    (children :
      G.LegalLowerRankPublicResponseChildFamily
        entry childTarget childError rankLt parentRank childRank)
    (selector : DeviationSafePublicCoinSelector G Child)
    (selection : G.BehaviorProfile) (initial : G.State) (fuel : ℕ)
    (parentTarget : Payoff ι) (parentError prefixError : ℝ)
    (payoffBound targetBound : ℝ) (accountingHorizon : ℕ) : Prop where
  fuel_covers_rank : selector.process.rank initial ≤ fuel
  legal_terminal_entry :
    ∀ state, selector.process.terminal state →
      state = entry (selector.process.observe state)
  continuation_target_transport : ∀ who,
    |expect (selector.process.value initial)
        (fun child => childTarget child who) -
      parentTarget who| ≤ parentError
  payoff_bound : ∀ state action who,
    |G.stagePayoff state action who| ≤ payoffBound
  child_target_bound : ∀ child who,
    |childTarget child who| ≤ targetBound
  payoffBound_nonneg : 0 ≤ payoffBound
  targetBound_nonneg : 0 ≤ targetBound
  childError_nonneg : 0 ≤ childError
  prefixError_nonneg : 0 ≤ prefixError
  error_budget : childError + prefixError ≤ parentError
  accountingHorizon_pos : 0 < accountingHorizon
  fuel_le_accountingHorizon : fuel ≤ accountingHorizon
  prefix_cost :
    (fuel : ℝ) * (payoffBound + targetBound) ≤
      (accountingHorizon : ℝ) * prefixError

namespace FixedDepthPublicResponseSelfGenerationData

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)] [Fintype Child]
  {entry : Child → G.State} {childTarget : Child → Payoff ι}
  {childError : ℝ} {rankLt : Rank → Rank → Prop}
  {parentRank : Rank} {childRank : Child → Rank}
  {children :
    G.LegalLowerRankPublicResponseChildFamily
      entry childTarget childError rankLt parentRank childRank}
  {selector : DeviationSafePublicCoinSelector G Child}
  {selection : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
  {parentTarget : Payoff ι} {parentError prefixError : ℝ}
  {payoffBound targetBound : ℝ} {accountingHorizon : ℕ}

/-- The fixed-depth dispatcher determined by the local self-generation
data. -/
theorem adaptiveSplice
    (data :
      G.FixedDepthPublicResponseSelfGenerationData
        entry childTarget childError rankLt parentRank childRank
        children selector selection initial fuel parentTarget
        parentError prefixError payoffBound targetBound
        accountingHorizon) :
    G.FixedDepthAdaptivePotentialSplice
      selector children.toAdaptiveFamily selection initial fuel where
  fuel_covers_rank := data.fuel_covers_rank
  terminal_entry := data.legal_terminal_entry

/-- The single child-target transport inequality supplies all three splice
transports because a public-response ledger has the child target itself as
each terminal potential. -/
theorem adaptiveBounds
    (data :
      G.FixedDepthPublicResponseSelfGenerationData
        entry childTarget childError rankLt parentRank childRank
        children selector selection initial fuel parentTarget
        parentError prefixError payoffBound targetBound
        accountingHorizon) :
    data.adaptiveSplice.Bounds parentTarget parentError prefixError
      payoffBound targetBound accountingHorizon where
  lower_parent := by
    intro who
    simpa using data.continuation_target_transport who
  upper_parent := by
    intro who
    simpa using data.continuation_target_transport who
  deviation_parent := by
    intro who
    simpa using data.continuation_target_transport who
  payoff_bound := data.payoff_bound
  lower_target_bound := by
    intro child who
    simpa using data.child_target_bound child who
  upper_target_bound := by
    intro child who
    simpa using data.child_target_bound child who
  deviation_target_bound := by
    intro child who
    simpa using data.child_target_bound child who
  payoffBound_nonneg := data.payoffBound_nonneg
  targetBound_nonneg := data.targetBound_nonneg
  childError_nonneg := data.childError_nonneg
  prefixError_nonneg := data.prefixError_nonneg
  error_budget := data.error_budget
  accountingHorizon_pos := data.accountingHorizon_pos
  fuel_le_accountingHorizon := data.fuel_le_accountingHorizon
  prefix_cost := data.prefix_cost

/-- Local self-generation compiler.

The output profile first runs `selection` for `fuel` public steps and then
dispatches the public behavior belonging to the legally selected,
strictly-lower-rank child ledger.  The factor two is the exact-stage-gap
conversion cost: one parent-error copy for initial displacement and one for
the Cesàro charge budget. -/
def toPublicResponseEnforcementLedgerAt
    (data :
      G.FixedDepthPublicResponseSelfGenerationData
        entry childTarget childError rankLt parentRank childRank
        children selector selection initial fuel parentTarget
        parentError prefixError payoffBound targetBound
        accountingHorizon) :
    G.PublicResponseEnforcementLedgerAt
      (G.behaviorPublicPhaseProfile data.adaptiveSplice.profile)
      initial parentTarget (2 * parentError) :=
  AdaptivePotentialSystemAt.toExactStageGapPublicResponseEnforcementLedgerAt
    (data.adaptiveSplice.toAdaptivePotentialSystemAt data.adaptiveBounds)
    ((add_nonneg data.childError_nonneg data.prefixError_nonneg).trans
      data.error_budget)

/-- Existential public-phase form of the same local self-generation
result. -/
theorem toIsPublicPhasePunishmentSystemAt
    (data :
      G.FixedDepthPublicResponseSelfGenerationData
        entry childTarget childError rankLt parentRank childRank
        children selector selection initial fuel parentTarget
        parentError prefixError payoffBound targetBound
        accountingHorizon) :
    G.IsPublicPhasePunishmentSystemAt
      initial parentTarget (2 * parentError) :=
  data.toPublicResponseEnforcementLedgerAt
    |>.toIsPublicPhasePunishmentSystemAt

end FixedDepthPublicResponseSelfGenerationData

end StochasticGame
end GameTheory
