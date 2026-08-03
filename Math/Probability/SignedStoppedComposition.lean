/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.OptionalTargetTransport

/-!
# Signed stopped composition

The elementary calculus of the stopped expectation for a
`ControlledTransport`, the composition of a signed selection phase with
child deliveries, the transport input bundle, and the boundary charge.

Everything here is stated for abstract state, history and index types: no
game, profile or Bellman datum appears.  The parent certificate that
consumes this layer lives with the stochastic-game development.

`TwoChildFence` is the separating witness: a fair public coin between a `+1`
child and a `-1` child satisfies the signed hypotheses with zero selection
error while the branchwise strengthening fails by a full unit at each
positive-probability branch.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

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

end Probability
end Math
