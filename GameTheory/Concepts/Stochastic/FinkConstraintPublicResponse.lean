/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ContextualFinkMonitor
import GameTheory.Concepts.Stochastic.PublicLocalResponseRecursion
import Math.LinearAlgebra.MixedCompatibilityCharge

/-!
# Public responses extracted from violated Fink constraints

A positive mixed Farkas certificate yields a violated player-owned row, but
the generic linear-algebra theorem does not know that this row is an actual
unilateral deviation. This file records the exact semantic decoder needed
for that step.

Once decoded, a positive Bellman gain has two operationally different
branches. A positive stage gain names a payoff/punishment response. Otherwise
the continuation gain is positive, so the actual forward deviation changes
the next-state law and admits a bounded, baseline-centered public coordinate
monitor. Families of transition responses give exactly the fixed contextual
monitor policies consumed by `ContextualFinkMonitor`.

The final section records the remaining strategic interface honestly. A
public monitor does not by itself construct a public-phase punishment system.
A branching local-response recursion must supply a closer for both the
compatible-continuation branch and the extracted-response branch.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.LinearAlgebra Math.Probability
open NormalizedFinkSupportTangentObstructionFlow

variable {ι : Type} {G : StochasticGame ι}

/-- An operational public monitor for one actual Fink pure deviation.

The score is centered under prescribed play, strictly positive under the
forward deviation, and bounded by one on every public successor state. -/
structure FinkPublicTransitionCharge
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U)
    (source : G.State) (owner : ι) (action : G.Act owner) where
  monitor : PMFCoordinateMonitor G.State
  baseline_centered :
    expect (G.finkStateKernel z source)
        (pmfCoordinateTestScore
          (G.finkStateKernel z source) monitor.1 monitor.2) = 0
  forward_positive :
    0 <
      expect (G.finkPureDeviationStateKernel z source owner action)
        (pmfCoordinateTestScore
          (G.finkStateKernel z source) monitor.1 monitor.2)
  score_bounded :
    ∀ destination,
      |pmfCoordinateTestScore
        (G.finkStateKernel z source)
        monitor.1 monitor.2 destination| ≤ 1

/-- Positive continuation gain forces transition visibility and therefore
produces an operational public coordinate monitor. -/
noncomputable def finkPublicTransitionChargeOfContinuationGainPos
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι)
    (source : G.State) (owner : ι) (action : G.Act owner)
    (hpositive :
      0 < G.finkContinuationGain W z source owner action) :
    G.FinkPublicTransitionCharge z source owner action := by
  have hkernel :
      G.finkPureDeviationStateKernel z source owner action ≠
        G.finkStateKernel z source := by
    intro hsame
    have hzero :=
      G.finkContinuationGain_eq_zero_of_pureDeviationStateKernel_eq
        W z source owner action hsame
    linarith
  let hexists :=
    exists_pureDeviationCoordinateMonitor_spec
      G z source owner action hkernel
  let monitor := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  exact ⟨monitor, hspec.1, hspec.2.1, hspec.2.2⟩

/-- Semantic meaning of one family of player rows in a coupled Farkas
system.

This is the indispensable bridge absent from abstract linear algebra:
each constraint must decode to an available forward action owned by the
indexed player, and its algebraic deficit must be the corresponding Bellman
stage-plus-continuation gain. -/
structure FinkDeviationConstraintSemantics
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {Constraint : ι → Type*} [∀ i, Fintype (Constraint i)]
    {n : ℕ} {U : ℝ}
    (z : G.finkDomain U) (W : G.State → Payoff ι)
    (playerNormal : ∀ i, Constraint i → Fin n → ℝ)
    (playerRhs : ∀ i, Constraint i → ℝ)
    (x : Fin n → ℝ) where
  source : ∀ i, Constraint i → G.State
  action : ∀ i, Constraint i → G.Act i
  deficit_eq_bellmanGain : ∀ i constraint,
    playerRhs i constraint -
        rowEval (playerNormal i) constraint x =
      G.finkStageGain z (source i constraint) i
          (action i constraint) +
        G.finkContinuationGain W z (source i constraint) i
          (action i constraint)

/-- The public response carried by a violated, semantically decoded Fink
constraint.

The stage branch still needs a game-specific punishment closer. The
transition branch is already an observable bounded public monitor. -/
inductive FinkPublicConstraintResponse
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι)
    (source : G.State) (owner : ι) (action : G.Act owner) : Type
  | stage
      (positive : 0 < G.finkStageGain z source owner action)
  | transition
      (charge : G.FinkPublicTransitionCharge z source owner action)

/-- A positive mixed compatibility obstruction, together with the exact
Fink row decoder, yields an actual player-owned public response.

No formal reversal of an action is used. The returned action is the forward
action named by the violated constraint. -/
theorem exists_finkPublicConstraintResponse_of_positive_coupledCertificate
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {Facet : Type*} [Fintype Facet]
    {Constraint : ι → Type*} [∀ i, Fintype (Constraint i)]
    [Nonempty (Σ i, Constraint i)]
    {n : ℕ} {U : ℝ}
    (z : G.finkDomain U) (W : G.State → Payoff ι)
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ i, Constraint i → Fin n → ℝ)
    (playerRhs : ∀ i, Constraint i → ℝ)
    (x : Fin n → ℝ)
    (semantics :
      G.FinkDeviationConstraintSemantics
        z W playerNormal playerRhs x)
    (u : CoupledRow Facet ι Constraint → ℝ)
    (hu :
      IsNonnegativeBalance
        (coupledNormal facetNormal playerNormal) u)
    (hnormalized : coupledRelaxedMultiplierMass u = 1)
    (hpositive :
      0 < ∑ row, u row *
        coupledRelaxedRhs facetRhs playerRhs 0 row)
    (hfacet :
      ∀ facet, facetRhs facet ≤
        rowEval facetNormal facet x) :
    ∃ owner, ∃ constraint,
      Nonempty
        (G.FinkPublicConstraintResponse z W
          (semantics.source owner constraint) owner
          (semantics.action owner constraint)) := by
  obtain ⟨owner, constraint, hdeficit⟩ :=
    exists_positive_playerConstraintDeficit
      facetNormal facetRhs playerNormal playerRhs
      u hu hnormalized hpositive x hfacet
  rw [semantics.deficit_eq_bellmanGain] at hdeficit
  by_cases hstage :
      0 <
        G.finkStageGain z (semantics.source owner constraint)
          owner (semantics.action owner constraint)
  · exact ⟨owner, constraint,
      ⟨FinkPublicConstraintResponse.stage hstage⟩⟩
  · have hcontinuation :
        0 <
          G.finkContinuationGain W z
            (semantics.source owner constraint) owner
            (semantics.action owner constraint) := by
      linarith
    exact ⟨owner, constraint,
      ⟨FinkPublicConstraintResponse.transition
        (finkPublicTransitionChargeOfContinuationGainPos
          z W (semantics.source owner constraint) owner
          (semantics.action owner constraint) hcontinuation)⟩⟩

section ContextualPolicy

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)]
  {U : ℝ}
  (z : Q → G.finkDomain U)
  (source : Q → G.State)
  (owner : Q → ι)
  (action : ∀ q, G.Act (owner q))
  (charge : ∀ q,
    G.FinkPublicTransitionCharge
      (z q) (source q) (owner q) (action q))

/-- The fixed context-to-monitor policy supplied by a family of extracted
transition responses. -/
def finkTransitionContextMonitorPolicy
    (q : Q) : PMFCoordinateMonitor G.State :=
  (charge q).monitor

omit [Fintype Q] [DecidableEq Q] in
/-- The extracted policy is centered under the prescribed Fink kernel in
every public context. -/
theorem expect_finkTransitionContextMonitorPolicy_baseline_eq_zero
    (q : Q) (n : ℕ) :
    expect (G.finkStateKernel (z q) (source q))
        (contextualPMFCoordinateMonitorScore
          (fun q _ => G.finkStateKernel (z q) (source q))
          q n
          (finkTransitionContextMonitorPolicy
            z source owner action charge q)) = 0 := by
  change
    expect (G.finkStateKernel (z q) (source q))
        (pmfCoordinateTestScore
          (G.finkStateKernel (z q) (source q))
          (charge q).monitor.1 (charge q).monitor.2) = 0
  exact (charge q).baseline_centered

omit [Fintype Q] [DecidableEq Q] in
/-- The same fixed contextual policy has strictly positive compensator
under the actual forward deviation in every transition-response context. -/
theorem expect_finkTransitionContextMonitorPolicy_forward_pos
    (q : Q) (n : ℕ) :
    0 <
      expect
        (G.finkPureDeviationStateKernel
          (z q) (source q) (owner q) (action q))
        (contextualPMFCoordinateMonitorScore
          (fun q _ => G.finkStateKernel (z q) (source q))
          q n
          (finkTransitionContextMonitorPolicy
            z source owner action charge q)) := by
  change
    0 <
      expect
        (G.finkPureDeviationStateKernel
          (z q) (source q) (owner q) (action q))
        (pmfCoordinateTestScore
          (G.finkStateKernel (z q) (source q))
          (charge q).monitor.1 (charge q).monitor.2)
  exact (charge q).forward_positive

omit [Fintype Q] [DecidableEq Q] in
/-- Every score selected by the fixed contextual response policy is bounded
by one, as required by contextual multiplicative weights. -/
theorem abs_finkTransitionContextMonitorPolicy_score_le_one
    (q : Q) (n : ℕ) (destination : G.State) :
    |contextualPMFCoordinateMonitorScore
      (fun q _ => G.finkStateKernel (z q) (source q))
      q n
      (finkTransitionContextMonitorPolicy
        z source owner action charge q)
      destination| ≤ 1 := by
  change
    |pmfCoordinateTestScore
      (G.finkStateKernel (z q) (source q))
      (charge q).monitor.1 (charge q).monitor.2 destination| ≤ 1
  exact (charge q).score_bounded destination

end ContextualPolicy

/-- A well-founded local-response recursion whose compatibility obligation
may close either by a compatible continuation or by an explicit public
response.

The two closers are genuinely strategic data. In particular, the mixed
Farkas extraction theorem above can populate `PublicResponse`, but cannot
prove `closeResponse` without a punishment, account, or phase construction. -/
structure PublicResponseBranchingRecursionAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ) where
  Rank : Type
  rankLt : Rank → Rank → Prop
  rank_wellFounded : WellFounded rankLt
  Node : Type
  rank : Node → Rank
  root : Node
  entry : Node → G.State
  target : Node → Payoff ι
  root_entry : entry root = s₀
  root_target : target root = v
  CompatibleContinuation : Node → Prop
  PublicResponse : Node → Prop
  LegalCoreHistoryEntryInterface : Node → Prop
  compatibilityOrPublicResponse :
    ∀ node, CompatibleContinuation node ∨ PublicResponse node
  legalCoreHistoryEntryInterface :
    ∀ node, LegalCoreHistoryEntryInterface node
  closeCompatible :
    ∀ node : Node,
      (∀ child : Node, rankLt (rank child) (rank node) →
        G.IsPublicPhasePunishmentSystemAt
          (entry child) (target child) δ) →
      CompatibleContinuation node →
      LegalCoreHistoryEntryInterface node →
      G.IsPublicPhasePunishmentSystemAt
        (entry node) (target node) δ
  closeResponse :
    ∀ node : Node,
      (∀ child : Node, rankLt (rank child) (rank node) →
        G.IsPublicPhasePunishmentSystemAt
          (entry child) (target child) δ) →
      PublicResponse node →
      LegalCoreHistoryEntryInterface node →
      G.IsPublicPhasePunishmentSystemAt
        (entry node) (target node) δ

namespace PublicResponseBranchingRecursionAt

variable [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {s₀ : G.State} {v : Payoff ι} {δ : ℝ}

/-- Package an honest compatibility-or-response recursion into the existing
public local-response API. The old abstract compatibility slot is populated
by the explicit disjunction rather than by an assumed compatibility proof. -/
def toPublicLocalResponseRecursionAt
    (C : G.PublicResponseBranchingRecursionAt s₀ v δ) :
    G.PublicLocalResponseRecursionAt s₀ v δ where
  Rank := C.Rank
  rankLt := C.rankLt
  rank_wellFounded := C.rank_wellFounded
  Node := C.Node
  rank := C.rank
  root := C.root
  entry := C.entry
  target := C.target
  root_entry := C.root_entry
  root_target := C.root_target
  MixedPlayerContinuationCompatibility := fun node =>
    C.CompatibleContinuation node ∨ C.PublicResponse node
  LegalCoreHistoryEntryInterface := C.LegalCoreHistoryEntryInterface
  mixedPlayerContinuationCompatibility :=
    C.compatibilityOrPublicResponse
  legalCoreHistoryEntryInterface :=
    C.legalCoreHistoryEntryInterface
  closeLocalResponse := fun node recurse branch legal =>
    branch.elim
      (fun compatible =>
        C.closeCompatible node recurse compatible legal)
      (fun response =>
        C.closeResponse node recurse response legal)

/-- Compile a completed branching recursion through the existing verifier. -/
theorem toIsPublicPhasePunishmentSystemAt
    (C : G.PublicResponseBranchingRecursionAt s₀ v δ) :
    G.IsPublicPhasePunishmentSystemAt s₀ v δ :=
  C.toPublicLocalResponseRecursionAt.toIsPublicPhasePunishmentSystemAt

end PublicResponseBranchingRecursionAt

end StochasticGame
end GameTheory
