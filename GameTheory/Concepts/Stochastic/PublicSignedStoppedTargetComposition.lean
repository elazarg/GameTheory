/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.OptionalTargetTransport
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

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace SignedStoppedComposition

open Math.Probability

/-! ## Layer 1: elementary calculus of the stopped expectation -/

section StoppedCalculus

variable {S H : Type*} [Finite S] (M : ControlledTransport S H) (K : H → PMF S)

/-- The stopped expectation is monotone in its payoff. -/
theorem stoppedExpect_mono (payoff bound : H → ℝ)
    (pointwise : ∀ history, payoff history ≤ bound history) :
    ∀ (horizon : ℕ) (history : H),
      M.stoppedExpect K payoff horizon history ≤
        M.stoppedExpect K bound horizon history := by
  intro horizon
  induction horizon with
  | zero => intro history; exact pointwise history
  | succ horizon ih =>
      intro history
      by_cases stopped : M.stop history
      · rw [M.stoppedExpect_of_stop K payoff _ history stopped,
          M.stoppedExpect_of_stop K bound _ history stopped]
        exact pointwise history
      · rw [M.stoppedExpect_succ_of_not_stop K payoff horizon history stopped,
          M.stoppedExpect_succ_of_not_stop K bound horizon history stopped]
        exact expect_mono _ _ _ fun next => ih (M.extend history next)

omit [Finite S] in
/-- A constant payoff is transported unchanged. -/
theorem stoppedExpect_const (constant : ℝ) :
    ∀ (horizon : ℕ) (history : H),
      M.stoppedExpect K (fun _ => constant) horizon history = constant := by
  intro horizon
  induction horizon with
  | zero => intro history; rfl
  | succ horizon ih =>
      intro history
      by_cases stopped : M.stop history
      · rw [M.stoppedExpect_of_stop K _ _ history stopped]
      · rw [M.stoppedExpect_succ_of_not_stop K _ horizon history stopped]
        have laws :
            (fun next =>
              M.stoppedExpect K (fun _ => constant) horizon
                (M.extend history next)) = fun _ : S => constant := by
          funext next
          exact ih (M.extend history next)
        rw [laws, expect_const]

/-- Adding a constant to the payoff adds it to the stopped expectation. -/
theorem stoppedExpect_add_const (payoff : H → ℝ) (constant : ℝ) :
    ∀ (horizon : ℕ) (history : H),
      M.stoppedExpect K (fun past => payoff past + constant) horizon history =
        M.stoppedExpect K payoff horizon history + constant := by
  intro horizon
  induction horizon with
  | zero => intro history; rfl
  | succ horizon ih =>
      intro history
      by_cases stopped : M.stop history
      · rw [M.stoppedExpect_of_stop K _ _ history stopped,
          M.stoppedExpect_of_stop K payoff _ history stopped]
      · rw [M.stoppedExpect_succ_of_not_stop K _ horizon history stopped,
          M.stoppedExpect_succ_of_not_stop K payoff horizon history stopped]
        have laws :
            (fun next =>
              M.stoppedExpect K (fun past => payoff past + constant) horizon
                (M.extend history next)) =
              fun next =>
                M.stoppedExpect K payoff horizon (M.extend history next) +
                  constant := by
          funext next
          exact ih (M.extend history next)
        rw [laws, expect_add, expect_const]

/-- One-sided comparison up to an additive slack: the signed workhorse. -/
theorem stoppedExpect_le_add_of_le (payoff bound : H → ℝ) (slack : ℝ)
    (pointwise : ∀ history, payoff history ≤ bound history + slack)
    (horizon : ℕ) (history : H) :
    M.stoppedExpect K payoff horizon history ≤
      M.stoppedExpect K bound horizon history + slack := by
  have step :=
    stoppedExpect_mono M K payoff (fun past => bound past + slack) pointwise
      horizon history
  rwa [stoppedExpect_add_const M K bound slack horizon history] at step

/-- Two signed one-sided comparisons give an expectation-level two-sided
bound.  The absolute value appears only *outside* the expectations. -/
theorem abs_stoppedExpect_sub_le_of_signed (payoff bound : H → ℝ) (slack : ℝ)
    (upper : ∀ history, payoff history ≤ bound history + slack)
    (lower : ∀ history, bound history ≤ payoff history + slack)
    (horizon : ℕ) (history : H) :
    |M.stoppedExpect K payoff horizon history -
        M.stoppedExpect K bound horizon history| ≤ slack := by
  have hup :=
    stoppedExpect_le_add_of_le M K payoff bound slack upper horizon history
  have hlo :=
    stoppedExpect_le_add_of_le M K bound payoff slack lower horizon history
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- A uniformly capped per-step error accumulates to at most the horizon
times the cap. -/
theorem stoppedErrorExpect_le_horizon_mul (perStep : H → ℝ) (cap : ℝ)
    (cap_nonneg : 0 ≤ cap) (bounded : ∀ history, perStep history ≤ cap) :
    ∀ (horizon : ℕ) (history : H),
      M.stoppedErrorExpect K perStep horizon history ≤ (horizon : ℝ) * cap := by
  intro horizon
  induction horizon with
  | zero => intro history; simp
  | succ horizon ih =>
      intro history
      have expand : ((horizon + 1 : ℕ) : ℝ) * cap = (horizon : ℝ) * cap + cap := by
        push_cast
        ring
      by_cases stopped : M.stop history
      · rw [M.stoppedErrorExpect_of_stop K perStep _ history stopped, expand]
        have base : (0 : ℝ) ≤ (horizon : ℝ) * cap :=
          mul_nonneg (Nat.cast_nonneg horizon) cap_nonneg
        linarith
      · rw [M.stoppedErrorExpect_succ_of_not_stop K perStep horizon history
          stopped, expand]
        have inner :
            expect (K history)
                (fun next =>
                  M.stoppedErrorExpect K perStep horizon
                    (M.extend history next)) ≤ (horizon : ℝ) * cap := by
          calc
            expect (K history)
                (fun next =>
                  M.stoppedErrorExpect K perStep horizon
                    (M.extend history next)) ≤
                expect (K history) (fun _ => (horizon : ℝ) * cap) :=
              expect_mono _ _ _ fun next => ih (M.extend history next)
            _ = (horizon : ℝ) * cap := expect_const _ _
        linarith [bounded history]

end StoppedCalculus

/-! ## Layer 2: the signed composition hypotheses -/

section Composition

variable {S H ι : Type*}

/-- **(H3) Child delivery moduli.**  Every child delivers its own declared
target within `childError` and caps its own unilateral deviator at that
target plus `childError`.

All three clauses are signed inequalities between the *child's own* payoff
and the *child's own* target, evaluated at the stopped history.  None of them
compares a branch value to the *parent* target, which is exactly the
comparison the fence forbids. -/
structure ChildDeliveryModuli
    (selectedTarget deliveredPayoff deviationPayoff : H → ι → ℝ)
    (childError : ℝ) : Prop where
  /-- The child's on-path delivery does not overshoot its own target. -/
  delivered_upper : ∀ history who,
    deliveredPayoff history who ≤ selectedTarget history who + childError
  /-- The child's on-path delivery does not undershoot its own target. -/
  delivered_lower : ∀ history who,
    selectedTarget history who ≤ deliveredPayoff history who + childError
  /-- The child caps its own unilateral deviator at its own target. -/
  deviation_upper : ∀ history who,
    deviationPayoff history who ≤ selectedTarget history who + childError

/-- **(H1) + (H2) Signed selection delivery.**  The selection phase, run to
the bounded causal stopping time, delivers the parent target in expectation
within `selectionError`, and caps every unilateral control at the parent
target plus `selectionError`.

Both clauses are expectation-level.  Nothing is asserted branchwise, and no
absolute value occurs inside a `stoppedExpect`. -/
structure SignedSelectionDelivery (M : ControlledTransport S H)
    (selectedTarget : H → ι → ℝ) (parentTarget : ι → ℝ)
    (root : H) (selectionHorizon : ℕ) (selectionError : ℝ) : Prop where
  /-- Prescribed selection does not oversell the parent target. -/
  prescribed_upper : ∀ who,
    M.stoppedExpect M.prescribed (fun past => selectedTarget past who)
        selectionHorizon root ≤ parentTarget who + selectionError
  /-- Prescribed selection does not undersell the parent target. -/
  prescribed_lower : ∀ who,
    parentTarget who ≤
      M.stoppedExpect M.prescribed (fun past => selectedTarget past who)
        selectionHorizon root + selectionError
  /-- Every unilateral control during selection is capped. -/
  deviation_cap : ∀ who (control : H → PMF S), M.IsUnilateral control →
    M.stoppedExpect control (fun past => selectedTarget past who)
        selectionHorizon root ≤ parentTarget who + selectionError

variable [Finite S] {M : ControlledTransport S H}
  {selectedTarget deliveredPayoff deviationPayoff : H → ι → ℝ}
  {parentTarget : ι → ℝ} {root : H} {selectionHorizon : ℕ}
  {selectionError childError : ℝ}

/-- **Composition, upper half.**  The prescribed *payoff* functional does not
oversell the parent target by more than the two moduli combined. -/
theorem stoppedExpect_deliveredPayoff_le
    (delivery : SignedSelectionDelivery M selectedTarget parentTarget root
      selectionHorizon selectionError)
    (moduli : ChildDeliveryModuli selectedTarget deliveredPayoff
      deviationPayoff childError)
    (who : ι) :
    M.stoppedExpect M.prescribed (fun past => deliveredPayoff past who)
        selectionHorizon root ≤
      parentTarget who + (selectionError + childError) := by
  have step :=
    stoppedExpect_le_add_of_le M M.prescribed
      (fun past => deliveredPayoff past who)
      (fun past => selectedTarget past who) childError
      (fun history => moduli.delivered_upper history who) selectionHorizon root
  have base := delivery.prescribed_upper who
  linarith

/-- **Composition, lower half.**  The prescribed *payoff* functional does not
undersell the parent target by more than the two moduli combined. -/
theorem le_stoppedExpect_deliveredPayoff
    (delivery : SignedSelectionDelivery M selectedTarget parentTarget root
      selectionHorizon selectionError)
    (moduli : ChildDeliveryModuli selectedTarget deliveredPayoff
      deviationPayoff childError)
    (who : ι) :
    parentTarget who - (selectionError + childError) ≤
      M.stoppedExpect M.prescribed (fun past => deliveredPayoff past who)
        selectionHorizon root := by
  have step :=
    stoppedExpect_le_add_of_le M M.prescribed
      (fun past => selectedTarget past who)
      (fun past => deliveredPayoff past who) childError
      (fun history => moduli.delivered_lower history who) selectionHorizon root
  have base := delivery.prescribed_lower who
  linarith

/-- **Parent prescribed delivery.**  The two signed halves, packaged as the
expectation-level two-sided bound the parent interface consumes. -/
theorem abs_stoppedExpect_deliveredPayoff_sub_le
    (delivery : SignedSelectionDelivery M selectedTarget parentTarget root
      selectionHorizon selectionError)
    (moduli : ChildDeliveryModuli selectedTarget deliveredPayoff
      deviationPayoff childError)
    (who : ι) :
    |M.stoppedExpect M.prescribed (fun past => deliveredPayoff past who)
          selectionHorizon root - parentTarget who| ≤
      selectionError + childError := by
  have hup := stoppedExpect_deliveredPayoff_le delivery moduli who
  have hlo := le_stoppedExpect_deliveredPayoff delivery moduli who
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **Parent deviation cap.**  Every unilateral control during selection,
followed by the selected child's own deviation payoff, is capped at the
parent target plus the two moduli combined.  Strictly one-sided. -/
theorem stoppedExpect_deviationPayoff_le
    (delivery : SignedSelectionDelivery M selectedTarget parentTarget root
      selectionHorizon selectionError)
    (moduli : ChildDeliveryModuli selectedTarget deliveredPayoff
      deviationPayoff childError)
    (who : ι) (control : H → PMF S) (unilateral : M.IsUnilateral control) :
    M.stoppedExpect control (fun past => deviationPayoff past who)
        selectionHorizon root ≤
      parentTarget who + (selectionError + childError) := by
  have step :=
    stoppedExpect_le_add_of_le M control
      (fun past => deviationPayoff past who)
      (fun past => selectedTarget past who) childError
      (fun history => moduli.deviation_upper history who) selectionHorizon root
  have base := delivery.deviation_cap who control unilateral
  linarith

end Composition

/-! ### (H1) + (H2) supplied by the transport kernel -/

section TransportInput

variable {S H ι : Type*} [Finite S]

/-- **Exact transport constructor.**  A coordinatewise harmonic state target
that is superharmonic under every allowed deviation supplies the signed
selection data at any nonnegative `selectionError`.  This is the direct
consumption of `stoppedExpect_vector_eq_of_harmonic` and
`stoppedExpect_current_le_of_unilateral`. -/
theorem signedSelectionDelivery_of_harmonic (M : ControlledTransport S H)
    (V : S → ι → ℝ) (root : H) (selectionHorizon : ℕ) (selectionError : ℝ)
    (error_nonneg : 0 ≤ selectionError)
    (harmonic : ∀ history, ¬ M.stop history → ∀ who,
      expect (M.prescribed history) (fun next => V next who) =
        V (M.current history) who)
    (allowed_super : ∀ history law, ¬ M.stop history → M.allowed history law →
      ∀ who, expect law (fun next => V next who) ≤ V (M.current history) who) :
    SignedSelectionDelivery M (fun past who => V (M.current past) who)
      (fun who => V (M.current root) who) root selectionHorizon
      selectionError := by
  have exact_delivery :
      ∀ who,
        M.stoppedExpect M.prescribed (fun past => V (M.current past) who)
            selectionHorizon root = V (M.current root) who := by
    intro who
    have vector :=
      M.stoppedExpect_vector_eq_of_harmonic V harmonic selectionHorizon root
    exact congrFun vector who
  refine ⟨fun who => ?_, fun who => ?_, fun who control unilateral => ?_⟩
  · rw [exact_delivery who]
    linarith
  · rw [exact_delivery who]
    linarith
  · refine le_trans ?_ (by linarith : V (M.current root) who ≤
      V (M.current root) who + selectionError)
    exact M.stoppedExpect_current_le_of_unilateral (fun state => V state who)
      (fun history running => le_of_eq (harmonic history running who))
      (fun history law running deviated =>
        allowed_super history law running deviated who)
      control unilateral selectionHorizon root

/-- **Approximate transport constructor.**  A state target that is
approximately harmonic under the prescribed law and approximately
superharmonic under every allowed deviation, with per-step error capped by
`cap`, supplies the signed selection data at
`selectionError = selectionHorizon * cap`.  This consumes the three
`_of_error` / `_of_approx_harmonic` theorems of the transport kernel. -/
theorem signedSelectionDelivery_of_approxHarmonic
    (M : ControlledTransport S H) (V : S → ι → ℝ) (perStep : H → ℝ) (cap : ℝ)
    (root : H) (selectionHorizon : ℕ)
    (cap_nonneg : 0 ≤ cap) (perStep_le : ∀ history, perStep history ≤ cap)
    (prescribed_upper : ∀ history, ¬ M.stop history → ∀ who,
      expect (M.prescribed history) (fun next => V next who) ≤
        V (M.current history) who + perStep history)
    (prescribed_lower : ∀ history, ¬ M.stop history → ∀ who,
      V (M.current history) who ≤
        expect (M.prescribed history) (fun next => V next who) + perStep history)
    (allowed_upper : ∀ history law, ¬ M.stop history → M.allowed history law →
      ∀ who, expect law (fun next => V next who) ≤
        V (M.current history) who + perStep history) :
    SignedSelectionDelivery M (fun past who => V (M.current past) who)
      (fun who => V (M.current root) who) root selectionHorizon
      ((selectionHorizon : ℝ) * cap) := by
  refine ⟨fun who => ?_, fun who => ?_, fun who control unilateral => ?_⟩
  · have step :=
      M.stoppedExpect_current_le_of_approx_harmonic (fun state => V state who)
        perStep (fun history running => prescribed_upper history running who)
        selectionHorizon root
    have budget :=
      stoppedErrorExpect_le_horizon_mul M M.prescribed perStep cap cap_nonneg
        perStep_le selectionHorizon root
    linarith
  · have step :=
      M.le_stoppedExpect_current_of_approx_harmonic (fun state => V state who)
        perStep (fun history running => prescribed_lower history running who)
        selectionHorizon root
    have budget :=
      stoppedErrorExpect_le_horizon_mul M M.prescribed perStep cap cap_nonneg
        perStep_le selectionHorizon root
    linarith
  · have step :=
      M.stoppedExpect_current_le_of_unilateral_of_error (fun state => V state who)
        perStep (fun history running => prescribed_upper history running who)
        (fun history law running deviated =>
          allowed_upper history law running deviated who)
        control unilateral selectionHorizon root
    have budget :=
      stoppedErrorExpect_le_horizon_mul M control perStep cap cap_nonneg
        perStep_le selectionHorizon root
    linarith

omit [Finite S] in
/-- **Exact preservation is the `selectionError = 0` case.**  This is the
hypothesis `hexact` of the fixed-depth splice, read inside the signed
interface. -/
theorem signedSelectionDelivery_of_exact (M : ControlledTransport S H)
    (selectedTarget : H → ι → ℝ) (parentTarget : ι → ℝ)
    (root : H) (selectionHorizon : ℕ)
    (exact_delivery : ∀ who,
      M.stoppedExpect M.prescribed (fun past => selectedTarget past who)
        selectionHorizon root = parentTarget who)
    (exact_cap : ∀ who (control : H → PMF S), M.IsUnilateral control →
      M.stoppedExpect control (fun past => selectedTarget past who)
        selectionHorizon root ≤ parentTarget who) :
    SignedSelectionDelivery M selectedTarget parentTarget root
      selectionHorizon 0 :=
  ⟨fun who => by rw [exact_delivery who]; linarith,
    fun who => by rw [exact_delivery who]; linarith,
    fun who control unilateral => by
      have := exact_cap who control unilateral
      linarith⟩

/-- **The branchwise hypothesis implies the signed one.**  If every history
carries a selected target within `selectionError` of the parent target, then
(H1) and (H2) hold at that same modulus, for *every* control at once.

`TwoChildFence` shows the converse fails: the signed hypotheses can hold at
`selectionError = 0` while this branchwise premise fails by a unit. -/
theorem signedSelectionDelivery_of_branchwise (M : ControlledTransport S H)
    (selectedTarget : H → ι → ℝ) (parentTarget : ι → ℝ)
    (root : H) (selectionHorizon : ℕ) (selectionError : ℝ)
    (branchwise : ∀ history who,
      |selectedTarget history who - parentTarget who| ≤ selectionError) :
    SignedSelectionDelivery M selectedTarget parentTarget root
      selectionHorizon selectionError := by
  have general :
      ∀ (control : H → PMF S) (who : ι),
        |M.stoppedExpect control (fun past => selectedTarget past who)
            selectionHorizon root - parentTarget who| ≤ selectionError := by
    intro control who
    have signed :=
      abs_stoppedExpect_sub_le_of_signed M control
        (fun past => selectedTarget past who) (fun _ => parentTarget who)
        selectionError
        (fun history => by
          have := abs_le.mp (branchwise history who)
          linarith [this.2])
        (fun history => by
          have := abs_le.mp (branchwise history who)
          linarith [this.1])
        selectionHorizon root
    rwa [stoppedExpect_const M control (parentTarget who) selectionHorizon root]
      at signed
  refine ⟨fun who => ?_, fun who => ?_, fun who control _ => ?_⟩
  · have := abs_le.mp (general M.prescribed who)
    linarith [this.2]
  · have := abs_le.mp (general M.prescribed who)
    linarith [this.1]
  · have := abs_le.mp (general control who)
    linarith [this.2]

end TransportInput

/-! ### The boundary charge arithmetic -/

section BoundaryCharge

/-- Dividing a charged horizon total by the horizon. -/
theorem average_le_of_total_le {average composite boundary : ℝ} {total : ℕ}
    (total_pos : 0 < total)
    (charged : (total : ℝ) * average ≤ (total : ℝ) * composite + boundary) :
    average ≤ composite + boundary / (total : ℝ) := by
  have positive : (0 : ℝ) < (total : ℝ) := by exact_mod_cast total_pos
  have key : average ≤ ((total : ℝ) * composite + boundary) / (total : ℝ) := by
    rw [le_div_iff₀ positive, mul_comm average ((total : ℝ))]
    exact charged
  have split : ((total : ℝ) * composite + boundary) / (total : ℝ) =
      composite + boundary / (total : ℝ) := by
    field_simp
  linarith [key, split.le, split.ge]

/-- The mirror image of `average_le_of_total_le`. -/
theorem le_average_of_le_total {average composite boundary : ℝ} {total : ℕ}
    (total_pos : 0 < total)
    (charged : (total : ℝ) * composite ≤ (total : ℝ) * average + boundary) :
    composite - boundary / (total : ℝ) ≤ average := by
  have positive : (0 : ℝ) < (total : ℝ) := by exact_mod_cast total_pos
  have key : ((total : ℝ) * composite - boundary) / (total : ℝ) ≤ average := by
    rw [div_le_iff₀ positive, mul_comm average ((total : ℝ))]
    linarith
  have split : ((total : ℝ) * composite - boundary) / (total : ℝ) =
      composite - boundary / (total : ℝ) := by
    field_simp
  linarith [key, split.le, split.ge]

/-- **The sublinear stopping bill.**  A fixed nonnegative boundary charge is
eventually spread below any positive slack.  This is where the one-time
child-boundary mismatch is absorbed.  No sign condition on the charge is
needed: a negative charge is spread below any positive slack outright. -/
theorem exists_accountingHorizon (boundary slack : ℝ) (slack_pos : 0 < slack) :
    ∃ accountingHorizon : ℕ, 2 ≤ accountingHorizon ∧
      ∀ total : ℕ, accountingHorizon ≤ total →
        boundary / (total : ℝ) ≤ slack := by
  obtain ⟨raw, raw_gt⟩ := exists_nat_gt (boundary / slack)
  refine ⟨max 2 raw, le_max_left 2 raw, ?_⟩
  intro total reached
  have two_le : 2 ≤ total := le_trans (le_max_left 2 raw) reached
  have raw_le : (raw : ℝ) ≤ (total : ℝ) := by
    exact_mod_cast le_trans (le_max_right 2 raw) reached
  have positive : (0 : ℝ) < (total : ℝ) := by
    have : 0 < total := by omega
    exact_mod_cast this
  rw [div_le_iff₀ positive]
  have chained : boundary / slack < (total : ℝ) := lt_of_lt_of_le raw_gt raw_le
  rw [div_lt_iff₀ slack_pos] at chained
  linarith [mul_comm ((total : ℝ)) slack]

end BoundaryCharge

end SignedStoppedComposition

/-! ## Layer 3: the parent certificate -/

namespace StochasticGame

open Math.Probability
open GameTheory.SignedStoppedComposition

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

/-! ## The two-child fence

A fair public coin selects between a `+1` child and a `-1` child.  The parent
target is `0`.  The signed hypotheses (H1) and (H2) hold with
`selectionError = 0`; the branchwise strengthening fails by a full unit at
each of the two positive-probability branches, and its accumulated bill is
exactly the horizon.  The composition theorem of this file applies.

The underlying process is `Math.Probability.TwoBranchProbe`, the minimal
witness (a root plus a two-point branch; two states provably cannot exhibit
the phenomenon). -/

namespace SignedStoppedComposition
namespace TwoChildFence

open Math.Probability
open Math.Probability.TwoBranchProbe

/-- The fence has a single player. -/
abbrev Seat : Type := Unit

/-- The selected child's target, read off the stopped probe state:
`+1` on the high leaf, `-1` on the low leaf, `0` at the root. -/
def selectedTarget : Probe → Seat → ℝ := fun state _ => value state

/-- The parent target of the fence. -/
def parentTarget : Seat → ℝ := fun _ => 0

/-- The selected target is harmonic at every running history. -/
theorem harmonic_running (history : Probe) (running : ¬ model.stop history)
    (who : Seat) :
    expect (model.prescribed history) (fun next => selectedTarget next who) =
      selectedTarget (model.current history) who := by
  have root : history = none := by
    by_contra leaf
    exact running leaf
  subst root
  simpa [selectedTarget] using harmonic_root

/-- Every allowed deviation is superharmonic for the selected target. -/
theorem allowed_super_running (history : Probe) (law : PMF Probe)
    (running : ¬ model.stop history) (deviated : model.allowed history law)
    (who : Seat) :
    expect law (fun next => selectedTarget next who) ≤
      selectedTarget (model.current history) who := by
  simpa [selectedTarget] using
    allowed_superharmonic history law running deviated

/-- **(H1) + (H2) hold at zero selection error.**  Both come from the
transport kernel through `signedSelectionDelivery_of_harmonic`. -/
theorem delivery :
    SignedSelectionDelivery model selectedTarget parentTarget none 1 0 :=
  signedSelectionDelivery_of_harmonic model
    (fun state (who : Seat) => selectedTarget state who) none 1 0 le_rfl
    harmonic_running
    (fun history law running deviated who =>
      allowed_super_running history law running deviated who)

/-- **(H3) holds at zero child error**: each child is its own target. -/
theorem moduli :
    ChildDeliveryModuli selectedTarget selectedTarget selectedTarget 0 :=
  ⟨fun _ _ => by linarith, fun _ _ => by linarith, fun _ _ => by linarith⟩

/-- **The branchwise strengthening fails.**  The high leaf is a stopped
history reached with positive probability whose selected target is a full
unit away from the parent target, so no branchwise hypothesis at modulus `0`
— and none at any modulus below `1` — can hold. -/
theorem branchwise_fails :
    model.stop (some true) ∧ kernel none (some true) ≠ 0 ∧
      |selectedTarget (some true) () - parentTarget ()| = 1 := by
  refine ⟨by simp, branch_ne_zero, ?_⟩
  simp [selectedTarget, parentTarget, value]

/-- **The composition theorem applies.**  Parent delivery and parent
deviation cap, both at error `0`, obtained from the general theorems of this
file and not by hand. -/
theorem composition_applies (who : Seat) :
    |model.stoppedExpect model.prescribed
          (fun past => selectedTarget past who) 1 none -
        parentTarget who| ≤ 0 + 0 ∧
      ∀ control : Probe → PMF Probe, model.IsUnilateral control →
        model.stoppedExpect control (fun past => selectedTarget past who) 1
            none ≤ parentTarget who + (0 + 0) :=
  ⟨abs_stoppedExpect_deliveredPayoff_sub_le delivery moduli who,
    fun control unilateral =>
      stoppedExpect_deviationPayoff_le delivery moduli who control unilateral⟩

/-- The fair selection weights of the fence. -/
def fairWeight : Fin 2 → ℝ := fun _ => 1 / 2

/-- The two branch errors against the parent target. -/
def branchError : Fin 2 → ℝ
  | 0 => 1
  | 1 => -1

/-- **The fence's numbers are the probe's own.**  The two branch errors are
the leaf offsets from the parent target and the two fair weights are the
prescribed branch masses, so the linear separation below is a statement about
this process rather than a detached arithmetic illustration. -/
theorem fence_numbers_are_the_probe :
    branchError 0 = selectedTarget (some true) () - parentTarget () ∧
      branchError 1 = selectedTarget (some false) () - parentTarget () ∧
      (kernel none (some true)).toReal = fairWeight 0 ∧
      (kernel none (some false)).toReal = fairWeight 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [branchError, selectedTarget, parentTarget, value]
  · simp [branchError, selectedTarget, parentTarget, value]
  · change
      (PMF.ofFintype branchWeights branchWeights_sum (some true)).toReal =
        fairWeight 0
    rw [PMF.ofFintype_apply]
    simp [branchWeights, fairWeight]
  · change
      (PMF.ofFintype branchWeights branchWeights_sum (some false)).toReal =
        fairWeight 1
    rw [PMF.ofFintype_apply]
    simp [branchWeights, fairWeight]

/-- The signed selection bill of the fence is zero. -/
theorem signed_bill_zero :
    ∑ child : Fin 2, fairWeight child * branchError child = 0 := by
  norm_num [Fin.sum_univ_two, fairWeight, branchError]

/-- The absolute (branchwise) selection bill of the fence is one per step. -/
theorem absolute_bill_one :
    ∑ child : Fin 2, fairWeight child * |branchError child| = 1 := by
  norm_num [Fin.sum_univ_two, fairWeight, branchError, abs_of_nonneg,
    abs_of_nonpos]

/-- **The bill separates linearly.**  Over `total` selection rounds the signed
bill stays at zero while the branchwise bill is exactly `total`. -/
theorem bills_separate_linearly (total : ℕ) :
    (∑ _step ∈ Finset.range total,
        ∑ child : Fin 2, fairWeight child * branchError child) = 0 ∧
      (∑ _step ∈ Finset.range total,
          ∑ child : Fin 2, fairWeight child * |branchError child|) =
        (total : ℝ) := by
  constructor
  · rw [Finset.sum_const, Finset.card_range, signed_bill_zero, smul_zero]
  · rw [Finset.sum_const, Finset.card_range, absolute_bill_one, nsmul_eq_mul,
      mul_one]

end TwoChildFence
end SignedStoppedComposition

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
open SignedStoppedComposition

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



