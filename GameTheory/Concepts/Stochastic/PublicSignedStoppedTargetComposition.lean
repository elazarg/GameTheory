/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.OptionalTargetTransport
import Math.Probability.SignedStoppedComposition
import GameTheory.Concepts.Stochastic.Absorbing
import GameTheory.Concepts.Stochastic.AdaptivePotentialSystem

/-!
# Signed composition of child certificates at a public causal stopping time

A public selection phase runs until a bounded causal stopping time, assigns a
child to every stopped history, and hands control to that child.  This file
proves that child certificates compose to a *parent* deviation-cap/delivery
pair, and then to a parent adaptive potential certificate, from **signed and
one-sided hypotheses only**.

## The design fence

Every hypothesis about the selection phase is either

* an expectation-level two-sided bound `|E[v^J_i] - v_i| ≤ δ` (prescribed
  delivery), or
* a one-sided expectation bound `E_dev[v^J_i] ≤ v_i + δ` (deviation
  transport).

No hypothesis is a *branchwise* bound `∀ J, |v^J_i - v_i| ≤ δ`, and no
hypothesis puts an absolute value *inside* an expectation.  This is not
cosmetic: `TwoChildFence` below exhibits a fair selection between a `+1`
child and a `-1` child at which the signed hypotheses hold with `δ = 0`,
while the branchwise strengthening fails by a full unit at every branch and
its accumulated bill grows linearly in the horizon.  The composition theorem
proved here applies there; a composition theorem stated branchwise cannot.

## Layer 1: the stopped-expectation calculus

`Math.Probability.OptionalTargetTransport` supplies the transport kernel
(`ControlledTransport.stoppedExpect`, exact vector transport, the unilateral
cap).  It is *consumed* here, never reproved.  What it does not supply is the
elementary calculus needed to move from *targets* to *payoffs*: monotonicity,
constants, and additive slack.  Those are proved here
(`stoppedExpect_mono`, `stoppedExpect_const`, `stoppedExpect_add_const`,
`stoppedExpect_le_add_of_le`, `abs_stoppedExpect_sub_le_of_signed`) as
lemmas about the existing definition.

## Layer 2: the composition

* `ChildDeliveryModuli` — (H3) each child delivers its own declared target
  within `childError`, and caps its own deviator at that target plus
  `childError`.  Three signed inequalities; no absolute value.
* `SignedSelectionDelivery` — (H1) + (H2), the two expectation-level
  selection hypotheses.
* `stoppedExpect_deliveredPayoff_le` /
  `le_stoppedExpect_deliveredPayoff` /
  `abs_stoppedExpect_deliveredPayoff_sub_le` /
  `stoppedExpect_deviationPayoff_le` — the composition: the *payoff*
  functional obeys the same signed delivery and one-sided cap as the
  *target* functional, at error `selectionError + childError`.
* `signedSelectionDelivery_of_harmonic` /
  `signedSelectionDelivery_of_approxHarmonic` — (H1)+(H2) supplied by the
  transport kernel from harmonicity data, consuming
  `stoppedExpect_vector_eq_of_harmonic`,
  `stoppedExpect_current_le_of_unilateral`,
  `stoppedExpect_current_le_of_unilateral_of_error` and the two approximate
  prescribed-transport theorems.

## Layer 3: the parent

* `StochasticGame.StoppedSelectionBill` — (H4), the sublinear stopping/reset
  bill: the parent's horizon-`total` payoff *total* differs from `total`
  copies of the stopped composite value by at most a fixed boundary charge,
  signed on the prescribed side and one-sided on the deviation side.  This
  is the interface supplied by the bounded-stopping factorization files; it
  is a hypothesis here, not a claim.
* `StochasticGame.finiteAveragePayoff_le_of_signedStoppedComposition` and
  friends — **tier 1**: explicit finite-horizon parent payoff bounds
  `v i ± (selectionError + childError + boundary / total)`.
* `StochasticGame.adaptivePotentialSystemAt_of_eventualAverageBounds` —
  **tier 2**: eventual signed payoff bounds assemble an explicit
  `AdaptivePotentialSystemAt`, hence an `IsAdaptivePotentialCertificateAt`.
  The child-boundary mismatch is absorbed as the one-time bounded charge
  `boundary / total`; no exact anchoring of the child potentials at the
  parent target is assumed.
* `StochasticGame.isAdaptivePotentialCertificateAt_of_signedStoppedComposition`
  — the capstone: (H1)–(H4) give a parent certificate at any error strictly
  above `selectionError + childError`.

## Non-vacuity

`TwoChildFence` instantiates the abstract layer at a genuinely branching
selection where the branchwise hypothesis fails.  `AbsorbingAcceptance`
instantiates *all four* hypothesis bundles at once and fires the capstone,
re-deriving `exists_uniformEquilibriumPayoff_of_isAbsorbingState` through it.
Without the second the capstone could be vacuous; without the first the
signed/branchwise distinction could be empty.

## What this strengthens

`PublicFixedDepthAdaptiveCertificate.isAdaptivePotentialCertificateAt_of_fixedDepthSelector`
demands `hexact`, exact preservation of the nominal child targets by the
selector.  `signedSelectionDelivery_of_exact` shows that is the
`selectionError = 0` case of (H1); (H1) is strictly weaker, and (H2) replaces
the deviation-side exactness that
`PublicRandomStoppedAdaptiveSplice.IsDeviationStoppedTargetInvariant` states
as an *equality* by a one-sided *inequality*.  The stopping rule here is a
causal predicate on histories, so the stopping time is genuinely variable
(bounded by the selection horizon), not a fixed depth.  No sign condition on
child scalar charges (`NonnegativeChildScalarCharges`) appears anywhere.
`signedSelectionDelivery_of_branchwise` records that the branchwise
hypothesis implies the signed one, and `TwoChildFence` records that the
implication is strict.
-/

noncomputable section

namespace GameTheory

/-! ## Layer 3: the parent certificate -/

namespace StochasticGame

open Math.Probability
open Math.Probability.SignedStoppedComposition

variable {ι : Type} {G : StochasticGame ι}

/-- A constant history potential has constant expectation under every
profile. -/
theorem expectedHistoryValue_constantPotential [Fintype ι]
    (profile : G.BehaviorProfile) (initial : G.State) (constant : ℝ)
    (time : ℕ) :
    G.expectedHistoryValue profile initial (fun _ _ => constant) time =
      constant := by
  unfold expectedHistoryValue
  exact expect_const _ _

/-- **Tier 2: certificate assembly from eventual signed payoff bounds.**

Constant potentials anchored *exactly* at the target, with the residuals
carried by *signed* (never truncated, never absolute) scalar charges, turn
eventual finite-horizon payoff bounds into an explicit adaptive potential
system.  Every monotonicity clause holds with equality; every stage clause
holds with equality; the whole content sits in the three Cesàro charge
bounds, which are precisely the three payoff hypotheses.

Truncating the charges at zero (`max 0 _`) would be the branchwise/absolute
variant and is exactly what this construction avoids. -/
def adaptivePotentialSystemAt_of_eventualAverageBounds
    [Fintype ι] [DecidableEq ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State) (target : Payoff ι)
    (error : ℝ) (accountingHorizon : ℕ)
    (error_nonneg : 0 ≤ error)
    (horizon_ge_two : 2 ≤ accountingHorizon)
    (prescribed_lower : ∀ who total, accountingHorizon ≤ total →
      target who - error ≤ G.finiteAveragePayoff initial total profile who)
    (prescribed_upper : ∀ who total, accountingHorizon ≤ total →
      G.finiteAveragePayoff initial total profile who ≤ target who + error)
    (deviation_upper : ∀ who (deviation : G.BehaviorStrategy who) total,
      accountingHorizon ≤ total →
        G.finiteAveragePayoff initial total
          (Function.update profile who deviation) who ≤ target who + error) :
    G.AdaptivePotentialSystemAt profile initial target error where
  horizon := accountingHorizon
  lowerPotential := fun who _ _ => target who
  upperPotential := fun who _ _ => target who
  deviationPotential := fun who _ _ => target who
  lowerCharge := fun who time =>
    target who - G.expectedStagePayoff profile initial time who
  upperCharge := fun who time =>
    G.expectedStagePayoff profile initial time who - target who
  deviationCharge := fun who deviation time =>
    G.expectedStagePayoff (Function.update profile who deviation) initial time
      who - target who
  horizon_ge_two := horizon_ge_two
  lower_initial := by
    intro who
    simpa using error_nonneg
  upper_initial := by
    intro who
    simpa using error_nonneg
  deviation_initial := by
    intro who
    simpa using error_nonneg
  lower_submartingale := by
    intro who time
    rw [G.expectedHistoryValue_constantPotential profile initial (target who) time,
      G.expectedHistoryValue_constantPotential profile initial (target who)
        (time + 1)]
  lower_stage := by
    intro who time
    rw [G.expectedHistoryValue_constantPotential profile initial (target who) time]
    linarith
  upper_supermartingale := by
    intro who time
    rw [G.expectedHistoryValue_constantPotential profile initial (target who) time,
      G.expectedHistoryValue_constantPotential profile initial (target who)
        (time + 1)]
  upper_stage := by
    intro who time
    rw [G.expectedHistoryValue_constantPotential profile initial (target who) time]
    linarith
  deviation_supermartingale := by
    intro who deviation time
    rw [G.expectedHistoryValue_constantPotential
        (Function.update profile who deviation) initial (target who) time,
      G.expectedHistoryValue_constantPotential
        (Function.update profile who deviation) initial (target who) (time + 1)]
  deviation_stage := by
    intro who deviation time
    rw [G.expectedHistoryValue_constantPotential
      (Function.update profile who deviation) initial (target who) time]
    linarith
  lower_charge_cesaro := by
    intro who total reached
    have total_pos : 0 < total := by omega
    have positive : (0 : ℝ) < (total : ℝ) := by exact_mod_cast total_pos
    have expand :
        ∑ time ∈ Finset.range total,
            (target who - G.expectedStagePayoff profile initial time who) =
          (total : ℝ) * target who -
            ∑ time ∈ Finset.range total,
              G.expectedStagePayoff profile initial time who := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have average :=
      G.finiteAveragePayoff_eq_sum_expectedStagePayoff profile initial who total
    have shape :
        (total : ℝ)⁻¹ *
            ((total : ℝ) * target who -
              ∑ time ∈ Finset.range total,
                G.expectedStagePayoff profile initial time who) =
          target who -
            (total : ℝ)⁻¹ *
              ∑ time ∈ Finset.range total,
                G.expectedStagePayoff profile initial time who := by
      field_simp
    rw [expand, shape, ← average]
    have := prescribed_lower who total reached
    linarith
  upper_charge_cesaro := by
    intro who total reached
    have total_pos : 0 < total := by omega
    have positive : (0 : ℝ) < (total : ℝ) := by exact_mod_cast total_pos
    have expand :
        ∑ time ∈ Finset.range total,
            (G.expectedStagePayoff profile initial time who - target who) =
          (∑ time ∈ Finset.range total,
              G.expectedStagePayoff profile initial time who) -
            (total : ℝ) * target who := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have average :=
      G.finiteAveragePayoff_eq_sum_expectedStagePayoff profile initial who total
    have shape :
        (total : ℝ)⁻¹ *
            ((∑ time ∈ Finset.range total,
                G.expectedStagePayoff profile initial time who) -
              (total : ℝ) * target who) =
          (total : ℝ)⁻¹ *
              (∑ time ∈ Finset.range total,
                G.expectedStagePayoff profile initial time who) -
            target who := by
      field_simp
    rw [expand, shape, ← average]
    have := prescribed_upper who total reached
    linarith
  deviation_charge_cesaro := by
    intro who deviation total reached
    have total_pos : 0 < total := by omega
    have positive : (0 : ℝ) < (total : ℝ) := by exact_mod_cast total_pos
    have expand :
        ∑ time ∈ Finset.range total,
            (G.expectedStagePayoff (Function.update profile who deviation)
              initial time who - target who) =
          (∑ time ∈ Finset.range total,
              G.expectedStagePayoff (Function.update profile who deviation)
                initial time who) - (total : ℝ) * target who := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have average :=
      G.finiteAveragePayoff_eq_sum_expectedStagePayoff
        (Function.update profile who deviation) initial who total
    have shape :
        (total : ℝ)⁻¹ *
            ((∑ time ∈ Finset.range total,
                G.expectedStagePayoff (Function.update profile who deviation)
                  initial time who) - (total : ℝ) * target who) =
          (total : ℝ)⁻¹ *
              (∑ time ∈ Finset.range total,
                G.expectedStagePayoff (Function.update profile who deviation)
                  initial time who) - target who := by
      field_simp
    rw [expand, shape, ← average]
    have := deviation_upper who deviation total reached
    linarith

/-- The certificate form of `adaptivePotentialSystemAt_of_eventualAverageBounds`. -/
theorem isAdaptivePotentialCertificateAt_of_eventualAverageBounds
    [Fintype ι] [DecidableEq ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State) (target : Payoff ι)
    (error : ℝ) (accountingHorizon : ℕ)
    (error_nonneg : 0 ≤ error)
    (horizon_ge_two : 2 ≤ accountingHorizon)
    (prescribed_lower : ∀ who total, accountingHorizon ≤ total →
      target who - error ≤ G.finiteAveragePayoff initial total profile who)
    (prescribed_upper : ∀ who total, accountingHorizon ≤ total →
      G.finiteAveragePayoff initial total profile who ≤ target who + error)
    (deviation_upper : ∀ who (deviation : G.BehaviorStrategy who) total,
      accountingHorizon ≤ total →
        G.finiteAveragePayoff initial total
          (Function.update profile who deviation) who ≤ target who + error) :
    G.IsAdaptivePotentialCertificateAt initial target error :=
  (G.adaptivePotentialSystemAt_of_eventualAverageBounds profile initial target
      error accountingHorizon error_nonneg horizon_ge_two prescribed_lower
      prescribed_upper deviation_upper).toIsAdaptivePotentialCertificateAt

/-- **(H4) The stopping/reset bill.**

The parent's horizon-`total` payoff *total* is compared with `total` copies
of the stopped composite value.  The gap is a single fixed `boundary` charge
— the finite selection prefix plus the one-time child-boundary mismatch —
independent of `total`, so it is sublinear and washes out in the average.

The prescribed side is stated as two signed inequalities; the deviation side
is one-sided.  Nothing here is branchwise. -/
structure StoppedSelectionBill [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)] {S H : Type*}
    (M : ControlledTransport S H) (root : H) (selectionHorizon : ℕ)
    (deliveredPayoff deviationPayoff : H → ι → ℝ)
    (deviationControl : ∀ who, G.BehaviorStrategy who → H → PMF S)
    (profile : G.BehaviorProfile) (initial : G.State) (boundary : ℝ) :
    Prop where
  /-- Deviating during the public selection phase is a unilateral control. -/
  deviationControl_unilateral : ∀ who deviation,
    M.IsUnilateral (deviationControl who deviation)
  /-- The parent does not outrun the composite by more than the charge. -/
  prescribed_upper : ∀ who (total : ℕ),
    (total : ℝ) * G.finiteAveragePayoff initial total profile who ≤
      (total : ℝ) *
          M.stoppedExpect M.prescribed (fun past => deliveredPayoff past who)
            selectionHorizon root + boundary
  /-- The parent does not lag the composite by more than the charge. -/
  prescribed_lower : ∀ who (total : ℕ),
    (total : ℝ) *
        M.stoppedExpect M.prescribed (fun past => deliveredPayoff past who)
          selectionHorizon root ≤
      (total : ℝ) * G.finiteAveragePayoff initial total profile who + boundary
  /-- A deviator does not outrun its own stopped composite by more than the
  charge. -/
  deviation_upper : ∀ who (deviation : G.BehaviorStrategy who) (total : ℕ),
    (total : ℝ) *
        G.finiteAveragePayoff initial total
          (Function.update profile who deviation) who ≤
      (total : ℝ) *
          M.stoppedExpect (deviationControl who deviation)
            (fun past => deviationPayoff past who) selectionHorizon root +
        boundary

section ParentPayoff

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] {S H : Type*} [Finite S]
  {M : ControlledTransport S H} {root : H} {selectionHorizon : ℕ}
  {selectedTarget deliveredPayoff deviationPayoff : H → ι → ℝ}
  {deviationControl : ∀ who, G.BehaviorStrategy who → H → PMF S}
  {profile : G.BehaviorProfile} {initial : G.State} {target : Payoff ι}
  {selectionError childError boundary : ℝ}

/-- **Tier 1, prescribed upper half.**  The parent's horizon-`total` average
payoff does not exceed the target by more than the two composition moduli
plus the amortized boundary charge. -/
theorem finiteAveragePayoff_le_of_signedStoppedComposition
    (delivery : SignedSelectionDelivery M selectedTarget target root
      selectionHorizon selectionError)
    (moduli : ChildDeliveryModuli selectedTarget deliveredPayoff
      deviationPayoff childError)
    (bill : G.StoppedSelectionBill M root selectionHorizon deliveredPayoff
      deviationPayoff deviationControl profile initial boundary)
    (who : ι) (total : ℕ) (total_pos : 0 < total) :
    G.finiteAveragePayoff initial total profile who ≤
      target who + (selectionError + childError) +
        boundary / (total : ℝ) := by
  have charged :=
    average_le_of_total_le total_pos (bill.prescribed_upper who total)
  have composite := stoppedExpect_deliveredPayoff_le delivery moduli who
  linarith

/-- **Tier 1, prescribed lower half.**  The mirror image. -/
theorem le_finiteAveragePayoff_of_signedStoppedComposition
    (delivery : SignedSelectionDelivery M selectedTarget target root
      selectionHorizon selectionError)
    (moduli : ChildDeliveryModuli selectedTarget deliveredPayoff
      deviationPayoff childError)
    (bill : G.StoppedSelectionBill M root selectionHorizon deliveredPayoff
      deviationPayoff deviationControl profile initial boundary)
    (who : ι) (total : ℕ) (total_pos : 0 < total) :
    target who - (selectionError + childError) - boundary / (total : ℝ) ≤
      G.finiteAveragePayoff initial total profile who := by
  have charged :=
    le_average_of_le_total total_pos (bill.prescribed_lower who total)
  have composite := le_stoppedExpect_deliveredPayoff delivery moduli who
  linarith

/-- **Tier 1, deviation cap.**  Every unilateral behavior deviation of the
parent is capped at the target plus the two composition moduli plus the
amortized boundary charge.  One-sided throughout. -/
theorem finiteAveragePayoff_update_le_of_signedStoppedComposition
    (delivery : SignedSelectionDelivery M selectedTarget target root
      selectionHorizon selectionError)
    (moduli : ChildDeliveryModuli selectedTarget deliveredPayoff
      deviationPayoff childError)
    (bill : G.StoppedSelectionBill M root selectionHorizon deliveredPayoff
      deviationPayoff deviationControl profile initial boundary)
    (who : ι) (deviation : G.BehaviorStrategy who) (total : ℕ)
    (total_pos : 0 < total) :
    G.finiteAveragePayoff initial total
        (Function.update profile who deviation) who ≤
      target who + (selectionError + childError) +
        boundary / (total : ℝ) := by
  have charged :=
    average_le_of_total_le total_pos
      (bill.deviation_upper who deviation total)
  have composite :=
    stoppedExpect_deviationPayoff_le delivery moduli who
      (deviationControl who deviation)
      (bill.deviationControl_unilateral who deviation)
  linarith

/-- **The capstone.**  Signed prescribed delivery, one-sided unilateral
transport, per-child moduli and a sublinear stopping bill compose to a parent
adaptive potential certificate at any error strictly above the sum of the two
moduli.

Nothing branchwise and no absolute value inside an expectation appears in any
hypothesis.  The child-boundary mismatch is carried by `boundary` and paid
once, so no exact anchoring of child potentials at the parent target is
assumed. -/
theorem isAdaptivePotentialCertificateAt_of_signedStoppedComposition
    (delivery : SignedSelectionDelivery M selectedTarget target root
      selectionHorizon selectionError)
    (moduli : ChildDeliveryModuli selectedTarget deliveredPayoff
      deviationPayoff childError)
    (bill : G.StoppedSelectionBill M root selectionHorizon deliveredPayoff
      deviationPayoff deviationControl profile initial boundary)
    (error : ℝ)
    (selectionError_nonneg : 0 ≤ selectionError)
    (childError_nonneg : 0 ≤ childError)
    (budget : selectionError + childError < error) :
    G.IsAdaptivePotentialCertificateAt initial target error := by
  have error_nonneg : 0 ≤ error := by linarith
  have slack_pos : 0 < error - (selectionError + childError) := by linarith
  obtain ⟨accountingHorizon, horizon_ge_two, spread⟩ :=
    exists_accountingHorizon boundary (error - (selectionError + childError))
      slack_pos
  refine G.isAdaptivePotentialCertificateAt_of_eventualAverageBounds profile
    initial target error accountingHorizon error_nonneg horizon_ge_two
    (fun who total reached => ?_) (fun who total reached => ?_)
    (fun who deviation total reached => ?_)
  · have total_pos : 0 < total := by omega
    have base :=
      G.le_finiteAveragePayoff_of_signedStoppedComposition delivery moduli bill
        who total total_pos
    have charge := spread total reached
    linarith
  · have total_pos : 0 < total := by omega
    have base :=
      G.finiteAveragePayoff_le_of_signedStoppedComposition delivery moduli bill
        who total total_pos
    have charge := spread total reached
    linarith
  · have total_pos : 0 < total := by omega
    have base :=
      G.finiteAveragePayoff_update_le_of_signedStoppedComposition delivery
        moduli bill who deviation total total_pos
    have charge := spread total reached
    linarith

end ParentPayoff

end StochasticGame


/-! ## Acceptance test: the hypothesis bundle is satisfiable

A composition theorem whose hypotheses are jointly unsatisfiable proves
nothing.  This section instantiates *all four* hypothesis bundles at once —
`SignedSelectionDelivery`, `ChildDeliveryModuli`, `StoppedSelectionBill`,
and the error budget — and fires the capstone, re-deriving the known
absorbing-state uniform equilibrium payoff
(`exists_uniformEquilibriumPayoff_of_isAbsorbingState`) through the new
interface.  The selection phase used is the empty one, which is the honest
minimal witness: the interface must not secretly demand a nontrivial
selection. -/

namespace AbsorbingAcceptance

open Math.Probability
open Math.Probability.SignedStoppedComposition

/-- The empty selection transport: one history, stopped at once, no allowed
deviation. -/
def trivialTransport : ControlledTransport Unit Unit where
  extend := fun _ _ => ()
  current := fun _ => ()
  current_extend := fun _ _ => rfl
  stop := fun _ => True
  prescribed := fun _ => PMF.pure ()
  allowed := fun _ _ => False

variable {ι : Type}

/-- **Acceptance test.**  At an absorbing initial state the whole signed
composition bundle is satisfiable, and the capstone returns the parent
certificate at every positive error. -/
theorem isAdaptivePotentialEquilibriumCertificate_of_isAbsorbingState_via_composition
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)] [∀ who, Nonempty (G.Act who)]
    {initial : G.State} (absorbing : G.IsAbsorbingState initial) :
    ∃ target : Payoff ι, G.IsAdaptivePotentialEquilibriumCertificate initial target := by
  obtain ⟨mixed, stageNash⟩ := G.exists_isMixedStageNash
  refine ⟨fun who => G.mixedStageEU initial (mixed initial) who,
    fun error error_pos => ?_⟩
  have scaled_on : ∀ (who : ι) (total : ℕ),
      (total : ℝ) *
          G.finiteAveragePayoff initial total
            (G.stationaryBehaviorProfile (mixed initial)) who =
        (total : ℝ) * G.mixedStageEU initial (mixed initial) who := by
    intro who total
    rcases Nat.eq_zero_or_pos total with vanishes | positive
    · subst vanishes
      simp
    · have nonzero : (total : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
        Finset.sum_congr rfl fun time _ =>
          G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
            absorbing (mixed initial) time who,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
  have scaled_off : ∀ (who : ι) (deviation : G.BehaviorStrategy who) (total : ℕ),
      (total : ℝ) *
          G.finiteAveragePayoff initial total
            (Function.update (G.stationaryBehaviorProfile (mixed initial)) who
              deviation) who ≤
        (total : ℝ) * G.mixedStageEU initial (mixed initial) who := by
    intro who deviation total
    rcases Nat.eq_zero_or_pos total with vanishes | positive
    · subst vanishes
      simp
    · have nonzero : (total : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have nonneg : (0 : ℝ) ≤ (total : ℝ) := Nat.cast_nonneg total
      rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      have stagewise :
          ∑ time ∈ Finset.range total,
              G.expectedStagePayoff
                (Function.update (G.stationaryBehaviorProfile (mixed initial))
                  who deviation) initial time who ≤
            (total : ℝ) * G.mixedStageEU initial (mixed initial) who := by
        calc
          ∑ time ∈ Finset.range total,
              G.expectedStagePayoff
                (Function.update (G.stationaryBehaviorProfile (mixed initial))
                  who deviation) initial time who ≤
              ∑ _time ∈ Finset.range total,
                G.mixedStageEU initial (mixed initial) who :=
            Finset.sum_le_sum fun time _ =>
              G.expectedStagePayoff_update_stationaryBehaviorProfile_le_of_isAbsorbingState
                absorbing (fun d => stageNash initial who d) deviation time
          _ = (total : ℝ) * G.mixedStageEU initial (mixed initial) who := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]
      exact stagewise
  refine G.isAdaptivePotentialCertificateAt_of_signedStoppedComposition
    (M := trivialTransport) (root := ()) (selectionHorizon := 0)
    (selectedTarget := fun _ who => G.mixedStageEU initial (mixed initial) who)
    (deliveredPayoff := fun _ who => G.mixedStageEU initial (mixed initial) who)
    (deviationPayoff := fun _ who => G.mixedStageEU initial (mixed initial) who)
    (deviationControl := fun _ _ => trivialTransport.prescribed)
    (profile := G.stationaryBehaviorProfile (mixed initial))
    (initial := initial)
    (target := fun who => G.mixedStageEU initial (mixed initial) who)
    (selectionError := 0) (childError := 0) (boundary := 0)
    (signedSelectionDelivery_of_branchwise trivialTransport _ _ () 0 0
      (fun _ _ => by simp))
    ⟨fun _ _ => by linarith, fun _ _ => by linarith, fun _ _ => by linarith⟩
    ?_ error le_rfl le_rfl (by linarith)
  refine ⟨fun _ _ => trivialTransport.isUnilateral_prescribed,
    fun who total => ?_, fun who total => ?_, fun who deviation total => ?_⟩
  · simpa using (scaled_on who total).le
  · simpa using (scaled_on who total).ge
  · simpa using scaled_off who deviation total

/-- **Acceptance test, verified end to end.**  The certificate produced by the
composition capstone passes the existing uniform-equilibrium verifier. -/
theorem exists_uniformEquilibriumPayoff_of_isAbsorbingState_via_composition
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)] [∀ who, Nonempty (G.Act who)]
    {initial : G.State} (absorbing : G.IsAbsorbingState initial) :
    ∃ target : Payoff ι, G.IsUniformEquilibriumPayoff initial target := by
  obtain ⟨target, certificate⟩ :=
    isAdaptivePotentialEquilibriumCertificate_of_isAbsorbingState_via_composition
      G absorbing
  exact ⟨target,
    G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
      initial target certificate⟩

end AbsorbingAcceptance

end GameTheory



