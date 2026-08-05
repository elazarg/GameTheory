/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingWeightedContinueMassBound

/-!
# The survival-window landing against the bounded granted predicate

`QuittingSurvivalWindowLanding.lean` states its no-large-jump step against
`IsQuittingGrantedContinueMassBound`, a predicate quantified over *all*
continuation vectors dominating the reservation level.  What
`QuittingWeightedContinueMassBound.lean` actually proves is the weaker
`IsQuittingBoundedGrantedContinueMassBound`, carrying one extra clause: the
continuation vector is uniformly bounded.  The gap between the two is the
only thing separating the landing chain from an unconditional consumer of
the weighted continue-mass theorem.

This file closes it.  The continuation the landing feeds to the granted
predicate is the *lift*

> `quittingLiftedContinuation _ = max (plan's continuation value) (reservation)`,

a coordinatewise maximum of two bounded quantities: the plan's own terminal
value is bounded by the reward bound
(`abs_quittingRootSequenceTerminalValue_le`), and the reservation vector is a
parameter, bounded by assumption.  So the lift is bounded, the bounded
predicate applies verbatim, and every theorem of the landing chain is
re-proved against it.

## The reservation bound is not an artefact

`|reservation| ≤ bound` costs nothing where the chain is used: the
reservation level is a punishment level of a game whose rewards are bounded
by `bound`, and the two hypotheses that mention it pin it from both sides --
`IsStationaryPunishment` caps each player there from above, and
`IsQuittingConditionalReservation` says each player can secure it from
below.  Both are compatible with `|reservation| ≤ bound`; neither implies it,
so it is stated.

## Main results

* `abs_quittingLiftedContinuation_le` -- the lift is bounded
* `le_quittingStationaryContinueMass_of_le_jointSurvivalWeight_of_bounded` --
  the no-large-jump lemma, against the bounded predicate
* `exists_jointSurvivalWeight_mem_survivalWindow_of_bounded` -- the landing
* `exists_pos_ratio_forall_exists_jointSurvivalWeight_mem_survivalWindow` --
  the composition with the weighted continue-mass theorem: no instant
  approximate equilibria plus a stationary punishment plus bounded rewards
  give a positive ratio at which every global `ε`-equilibrium plan's
  survival sequence visits the window, with no unproved predicate left in
  the hypothesis list
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The lift is bounded -/

omit [DecidableEq ι] in
/-- **The lifted continuation is bounded.**  It is a coordinatewise maximum
of the plan's own terminal value -- bounded by the reward bound -- and the
reservation vector, bounded by assumption. -/
theorem abs_quittingLiftedContinuation_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (reservation : Payoff ι) (start : ℕ) (who : ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hreservation : ∀ player, |reservation player| ≤ bound) :
    |quittingLiftedContinuation reward roots reservation start who| ≤ bound := by
  have hvalue : |quittingRootSequenceTerminalValue reward roots who start| ≤ bound :=
    abs_quittingRootSequenceTerminalValue_le reward roots who start hbound hreward
  have hres := hreservation who
  rw [abs_le] at hvalue hres ⊢
  rw [quittingLiftedContinuation]
  exact ⟨le_max_of_le_left hvalue.1, max_le hvalue.2 hres.2⟩

/-! ## The landing chain, re-proved against the bounded predicate -/

/-- **The no-large-jump lemma, bounded form.**  Granted only the *bounded*
per-stage continue-mass bound, a globally `ε`-optimal plan still cannot lose
more than the factor `ratio` at a stage whose joint survival is at least
`ε / ratio`.

The lift supplies the missing clause for free: it dominates the reservation
level by construction and is bounded because both of the quantities it
maximises are. -/
theorem le_quittingStationaryContinueMass_of_le_jointSurvivalWeight_of_bounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι} {ε ratio bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hreservation : ∀ player, |reservation player| ≤ bound)
    (hε : 0 < ε) (hratio : 0 < ratio)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (hgranted : IsQuittingBoundedGrantedContinueMassBound reward reservation bound ratio)
    (stage : ℕ) (hstage : ε / ratio ≤ quittingJointSurvivalWeight roots 0 stage) :
    ratio ≤ quittingStationaryContinueMass (roots stage) := by
  have hpos : 0 < ε / ratio := div_pos hε hratio
  have hsurvival : 0 < quittingJointSurvivalWeight roots 0 stage :=
    lt_of_lt_of_le hpos hstage
  have htolerance : ε / quittingJointSurvivalWeight roots 0 stage ≤ ratio := by
    rw [div_le_iff₀ hsurvival, mul_comm]
    exact (div_le_iff₀ hratio).mp hstage
  have hlift := isεQuittingRootNash_quittingLiftedContinuation reward roots hnash
    hreserve stage hsurvival
  have hratioNash : IsεQuittingRootNash reward
      (quittingLiftedContinuation reward roots reservation (stage + 1)) ratio
      (roots stage) := by
    intro player deviation
    have := hlift player deviation
    linarith
  refine hgranted _ (roots stage)
    (fun player => abs_quittingLiftedContinuation_le reward roots reservation
      (stage + 1) player hbound hreward hreservation)
    (fun player => ?_)
    ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward _ _ _).mpr hratioNash)
  have hdominates := le_quittingLiftedContinuation reward roots reservation (stage + 1) player
  linarith

/-- **The survival-window landing, bounded form.**  Granted the bounded
per-stage bound, a globally `ε`-optimal plan whose joint survival ever drops
to `window` -- with accuracy `ε ≤ ratio * window` and `ratio * window ≤ 1` --
has some stage whose joint survival lies in the closed window
`[ratio * window, window]`. -/
theorem exists_jointSurvivalWeight_mem_survivalWindow_of_bounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι} {ε ratio window bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hreservation : ∀ player, |reservation player| ≤ bound)
    (hε : 0 < ε) (hratio : 0 < ratio)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (hgranted : IsQuittingBoundedGrantedContinueMassBound reward reservation bound ratio)
    (hwindow : ratio * window ≤ 1) (haccuracy : ε ≤ ratio * window)
    {below : ℕ} (hbelow : quittingJointSurvivalWeight roots 0 below ≤ window) :
    ∃ stage, ratio * window ≤ quittingJointSurvivalWeight roots 0 stage ∧
      quittingJointSurvivalWeight roots 0 stage ≤ window := by
  refine exists_mem_survivalWindow_of_ratio_ge hratio ?_ (fun stage hstage => ?_) hbelow
  · rw [quittingJointSurvivalWeight_zero_fuel]
    exact hwindow
  · have hthreshold : ε / ratio ≤ quittingJointSurvivalWeight roots 0 stage := by
      rw [div_le_iff₀ hratio]
      nlinarith [hstage, haccuracy]
    have hmass := le_quittingStationaryContinueMass_of_le_jointSurvivalWeight_of_bounded
      reward roots hbound hreward hreservation hε hratio hnash hreserve hgranted stage
      hthreshold
    have hsucc := quittingJointSurvivalWeight_succ roots 0 stage
    rw [Nat.zero_add] at hsucc
    have hnonneg := quittingJointSurvivalWeight_nonneg roots 0 stage
    rw [hsucc]
    nlinarith [hmass, hnonneg]

/-- **The landing from a vanishing survival limit, bounded form.** -/
theorem exists_jointSurvivalWeight_mem_survivalWindow_of_bounded_of_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {reservation : Payoff ι}
    {ε ratio window bound limit : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hreservation : ∀ player, |reservation player| ≤ bound)
    (hε : 0 < ε) (hratio : 0 < ratio)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hreserve : IsQuittingConditionalReservation reward roots reservation)
    (hgranted : IsQuittingBoundedGrantedContinueMassBound reward reservation bound ratio)
    (hwindow : ratio * window ≤ 1) (haccuracy : ε ≤ ratio * window)
    (hlimit : Tendsto (quittingJointSurvivalWeight roots 0) atTop (nhds limit))
    (hbelow : limit < window) :
    ∃ stage, ratio * window ≤ quittingJointSurvivalWeight roots 0 stage ∧
      quittingJointSurvivalWeight roots 0 stage ≤ window := by
  obtain ⟨below, hbelowStage⟩ := ((tendsto_order.1 hlimit).2 window hbelow).exists
  exact exists_jointSurvivalWeight_mem_survivalWindow_of_bounded reward roots hbound
    hreward hreservation hε hratio hnash hreserve hgranted hwindow haccuracy
    hbelowStage.le

/-! ## The composition with the weighted continue-mass theorem -/

/-- **The landing with no unproved predicate left.**  A reward with no
instant approximate equilibria and a stationary punishment at every player
admits a positive `ratio` such that *every* globally `ε`-optimal plan whose
continuation vector is secured by the reservation level, and whose joint
survival ever drops to `window`, has a stage in the closed window
`[ratio * window, window]`.

The granted per-stage bound is no longer a hypothesis: it is supplied by
`exists_pos_isQuittingBoundedGrantedContinueMassBound`, and the bounded form
is exactly what the landing chain consumes above.  What remains in the
hypothesis list is the input data -- the plan, its global accuracy, and the
reservation level's two sides -- and nothing that is merely granted. -/
theorem exists_pos_ratio_forall_exists_jointSurvivalWeight_mem_survivalWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (reservation : Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hreservation : ∀ player, |reservation player| ≤ bound)
    (hnoInstant : HasNoInstantApproxEquilibria (weightOfReward reward))
    (hpunish : IsStationaryPunishment (weightOfReward reward) reservation) :
    ∃ ratio > 0, ∀ (roots : ℕ → ι → PMF Bool) (ε window : ℝ) (below : ℕ),
      0 < ε → IsεQuittingRootSequenceNash reward ε roots →
        IsQuittingConditionalReservation reward roots reservation →
        ratio * window ≤ 1 → ε ≤ ratio * window →
        quittingJointSurvivalWeight roots 0 below ≤ window →
        ∃ stage, ratio * window ≤ quittingJointSurvivalWeight roots 0 stage ∧
          quittingJointSurvivalWeight roots 0 stage ≤ window := by
  obtain ⟨ratio, hratio, hgranted⟩ :=
    exists_pos_isQuittingBoundedGrantedContinueMassBound reward reservation bound
      hnoInstant hpunish
  refine ⟨ratio, hratio, fun roots ε window below hε hnash hreserve hwindow
    haccuracy hbelow => ?_⟩
  exact exists_jointSurvivalWeight_mem_survivalWindow_of_bounded reward roots hbound
    hreward hreservation hε hratio hnash hreserve hgranted hwindow haccuracy hbelow

end GameTheory
