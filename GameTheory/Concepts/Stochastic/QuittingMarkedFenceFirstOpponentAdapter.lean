/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingMarkedFencePacket
import GameTheory.Concepts.Stochastic.QuittingBellmanTelescope
import GameTheory.Concepts.Stochastic.QuittingOpponentActionMass
import GameTheory.Concepts.Stochastic.QuittingExceptionalTailLimits

/-!
# Actual first-opponent packets for finite quitting chains

This file instantiates `QuittingMarkedFencePacket` with the genuine
owner-deleted first-opponent law of a finite quitting root sequence.  A mark
is an actual suffix date together with a joint Boolean action.  Its raw
weight is the owner's preceding opponent-survival probability times the
product-law mass of that action after forcing the owner to Continue; actions
with no quitting opponent receive zero weight.

The raw weights sum to the exact probability of an opponent fence before the
cutoff.  Their owner-reward moment is the finite payoff from Always Continue.
For an exact boundary-zero Nash--Bellman chain, that Never payoff is below
the declared current value.  A sufficiently negative current value therefore
makes the fence mass positive and normalizes the actual marks into the
abstract packet dichotomy, yielding a quantitative good boundary or an
actual negative-player transfer.

This is a one-step suffix theorem.  It does not identify repeated player
names with recurrent payoff states or compile a repeated flag into a path.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite marked dates and their displayed joint actions. -/
abbrev QuittingFirstOpponentMark (ι : Type) (fuel : ℕ) :=
  Fin fuel × (ι → Bool)

/-- The genuine unnormalized first-opponent weight. -/
def quittingFirstOpponentRawWeight
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ)
    (mark : QuittingFirstOpponentMark ι fuel) : ℝ :=
  quittingOpponentSurvivalWeight roots owner start mark.1 *
    if quittingOpponentQuitFlag owner mark.2 = true then
      ((pmfPi (Function.update (roots (start + mark.1)) owner
        (PMF.pure false))) mark.2).toReal
    else 0

/-- Probability of seeing an opponent fence before the finite cutoff. -/
def quittingFirstOpponentMass
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (start fuel : ℕ) : ℝ :=
  1 - quittingOpponentSurvivalWeight roots owner start fuel

/-- The actual owner-deleted quitter set at a mark.  Erasing the owner makes
the packet's owner-exclusion property unconditional, including on zero-mass
actions outside the forced-Continue support. -/
def quittingFirstOpponentQuitters
    (owner : ι) {fuel : ℕ}
    (mark : QuittingFirstOpponentMark ι fuel) : Finset ι :=
  (quittingQuitters mark.2).erase owner

/-- Owner reward displayed by a marked action.  It is zero on all-Continue. -/
def quittingFirstOpponentOwnerReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {fuel : ℕ}
    (mark : QuittingFirstOpponentMark ι fuel) : ℝ :=
  quittingRootPayoff reward (0 : Payoff ι) mark.2 owner

/-- Current declared payoff at the actual marked suffix date. -/
def quittingFirstOpponentValue
    (value : ℕ → Payoff ι) (start : ℕ) {fuel : ℕ}
    (mark : QuittingFirstOpponentMark ι fuel) : Payoff ι :=
  value (start + mark.1)

/-- Normalized actual first-opponent weight. -/
def quittingFirstOpponentWeight
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ)
    (mark : QuittingFirstOpponentMark ι fuel) : ℝ :=
  quittingFirstOpponentRawWeight roots owner start fuel mark /
    quittingFirstOpponentMass roots owner start fuel

theorem quittingFirstOpponent_owner_not_quitter
    (owner : ι) {fuel : ℕ} (mark : QuittingFirstOpponentMark ι fuel) :
    owner ∉ quittingFirstOpponentQuitters owner mark := by
  simp [quittingFirstOpponentQuitters]

/-- At one root, summing the marked opponent actions gives exactly one minus
the owner-deleted all-Continue mass. -/
theorem sum_opponentActionMass_eq_one_sub_continueMass
    (root : ι → PMF Bool) (owner : ι) :
    (∑ action : ι → Bool,
        if quittingOpponentQuitFlag owner action = true then
          ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal
        else 0) =
      1 - quittingStationaryContinueMass
        (Function.update root owner (PMF.pure false)) := by
  have hmass := expect_pmfPi_someOpponentQuits_eq_one_sub_continueMass
    root owner (PMF.pure false)
  rw [expect_eq_sum] at hmass
  unfold quittingSomeOpponentQuitsIndicator at hmass
  simp_rw [mul_ite, mul_one, mul_zero] at hmass
  exact hmass

/-- The raw actual mark weights sum to the exact finite opponent-fence
probability. -/
theorem sum_quittingFirstOpponentRawWeight
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    (∑ mark : QuittingFirstOpponentMark ι fuel,
        quittingFirstOpponentRawWeight roots owner start fuel mark) =
      quittingFirstOpponentMass roots owner start fuel := by
  rw [Fintype.sum_prod_type]
  change (∑ offset : Fin fuel, ∑ action : ι → Bool,
      quittingOpponentSurvivalWeight roots owner start (offset : ℕ) *
        (if quittingOpponentQuitFlag owner action = true then
          ((pmfPi (Function.update (roots (start + (offset : ℕ))) owner
            (PMF.pure false))) action).toReal
        else 0)) = quittingFirstOpponentMass roots owner start fuel
  let stageWeight : ℕ → ℝ := fun offset ↦ ∑ action : ι → Bool,
    quittingOpponentSurvivalWeight roots owner start offset *
      (if quittingOpponentQuitFlag owner action = true then
        ((pmfPi (Function.update (roots (start + offset)) owner
          (PMF.pure false))) action).toReal
      else 0)
  change (∑ offset : Fin fuel, stageWeight offset) =
    quittingFirstOpponentMass roots owner start fuel
  rw [Fin.sum_univ_eq_sum_range stageWeight fuel]
  dsimp only [stageWeight]
  simp_rw [← Finset.mul_sum,
    sum_opponentActionMass_eq_one_sub_continueMass]
  exact sum_quittingOpponentSurvivalWeight_mul_one_sub_continueMass
    roots owner start fuel

/-- Raw first-opponent weights are nonnegative. -/
theorem quittingFirstOpponentRawWeight_nonneg
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ)
    (mark : QuittingFirstOpponentMark ι fuel) :
    0 ≤ quittingFirstOpponentRawWeight roots owner start fuel mark := by
  unfold quittingFirstOpponentRawWeight
  apply mul_nonneg
  · exact quittingOpponentSurvivalWeight_nonneg roots owner start mark.1
  · by_cases hflag : quittingOpponentQuitFlag owner mark.2 = true
    · rw [if_pos hflag]
      exact ENNReal.toReal_nonneg
    · rw [if_neg hflag]

/-- The finite opponent-fence mass lies in `[0,1]`. -/
theorem quittingFirstOpponentMass_nonneg
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    0 ≤ quittingFirstOpponentMass roots owner start fuel := by
  rw [← sum_quittingFirstOpponentRawWeight]
  exact Finset.sum_nonneg fun mark _ ↦
    quittingFirstOpponentRawWeight_nonneg roots owner start fuel mark

theorem quittingFirstOpponentMass_le_one
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    quittingFirstOpponentMass roots owner start fuel ≤ 1 := by
  unfold quittingFirstOpponentMass
  linarith [quittingOpponentSurvivalWeight_nonneg roots owner start fuel]

/-! ## Owner reward moment -/

/-- Outside the opponent-quit event, the forced-owner product mass times the
zero-boundary root reward vanishes. -/
theorem opponentEventMass_mul_ownerReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (action : ι → Bool) :
    (if quittingOpponentQuitFlag owner action = true then
        ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal
      else 0) *
        quittingRootPayoff reward (0 : Payoff ι) action owner =
      ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal *
        quittingRootPayoff reward (0 : Payoff ι) action owner := by
  let distribution := pmfPi (Function.update root owner (PMF.pure false))
  by_cases hflag : quittingOpponentQuitFlag owner action = true
  · rw [if_pos hflag]
  · rw [if_neg hflag]
    by_cases hmass : (distribution action).toReal = 0
    · change 0 * quittingRootPayoff reward (0 : Payoff ι) action owner =
        (distribution action).toReal *
          quittingRootPayoff reward (0 : Payoff ι) action owner
      rw [hmass]
    · have hmassENN : distribution action ≠ 0 := by
        intro hzero
        rw [hzero, ENNReal.toReal_zero] at hmass
        exact hmass rfl
      have hsupport : action ∈ distribution.support :=
        (PMF.mem_support_iff distribution action).2 hmassENN
      have hnoOpponent : ¬quittingSomeOpponentQuits owner action := by
        intro hopponent
        exact hflag
          ((quittingOpponentQuitFlag_eq_true_iff owner action).2 hopponent)
      have hallContinue :=
        eq_allContinue_of_not_someOpponentQuits_of_mem_support
          root owner action hsupport hnoOpponent
      subst action
      simp [quittingRootPayoff]

/-- At a fixed date, the owner-reward moment of actual marked opponent
actions is the standard fixed-opponents Continue reward. -/
theorem sum_opponentActionMass_mul_ownerReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    (∑ action : ι → Bool,
        (if quittingOpponentQuitFlag owner action = true then
            ((pmfPi (Function.update root owner
              (PMF.pure false))) action).toReal
          else 0) *
          quittingRootPayoff reward (0 : Payoff ι) action owner) =
      quittingRootAbsorbingContribution reward
        (Function.update root owner (PMF.pure false)) owner := by
  calc
    (∑ action : ι → Bool,
        (if quittingOpponentQuitFlag owner action = true then
            ((pmfPi (Function.update root owner
              (PMF.pure false))) action).toReal
          else 0) *
          quittingRootPayoff reward (0 : Payoff ι) action owner) =
        ∑ action : ι → Bool,
          ((pmfPi (Function.update root owner
            (PMF.pure false))) action).toReal *
            quittingRootPayoff reward (0 : Payoff ι) action owner := by
      apply Finset.sum_congr rfl
      intro action _
      exact opponentEventMass_mul_ownerReward reward root owner action
    _ = expect (pmfPi (Function.update root owner (PMF.pure false)))
          (fun action ↦
            quittingRootPayoff reward (0 : Payoff ι) action owner) := by
      rw [expect_eq_sum]
    _ = quittingRootAbsorbingContribution reward
          (Function.update root owner (PMF.pure false)) owner := rfl

/-- The owner-reward moment of the genuine first-opponent marks. -/
def quittingFirstOpponentRawMean
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) : ℝ :=
  ∑ mark : QuittingFirstOpponentMark ι fuel,
    quittingFirstOpponentRawWeight roots owner start fuel mark *
      quittingFirstOpponentOwnerReward reward owner mark

/-- The raw owner moment is the finite opponent-survival-weighted Continue
reward, i.e. the finite Never payoff. -/
theorem quittingFirstOpponentRawMean_eq_sum_continueReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    quittingFirstOpponentRawMean reward roots owner start fuel =
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots owner start offset *
          quittingFixedOpponentsContinueReward reward roots owner
            (start + offset) := by
  unfold quittingFirstOpponentRawMean
  rw [Fintype.sum_prod_type]
  let stageMean : ℕ → ℝ := fun offset ↦ ∑ action : ι → Bool,
    (quittingOpponentSurvivalWeight roots owner start offset *
      (if quittingOpponentQuitFlag owner action = true then
        ((pmfPi (Function.update (roots (start + offset)) owner
          (PMF.pure false))) action).toReal
      else 0)) *
      quittingRootPayoff reward (0 : Payoff ι) action owner
  change (∑ offset : Fin fuel, stageMean offset) = _
  rw [Fin.sum_univ_eq_sum_range stageMean fuel]
  dsimp only [stageMean]
  apply Finset.sum_congr rfl
  intro offset hoffset
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change quittingOpponentSurvivalWeight roots owner start offset *
      (∑ action : ι → Bool,
        (if quittingOpponentQuitFlag owner action = true then
            ((pmfPi (Function.update (roots (start + offset)) owner
              (PMF.pure false))) action).toReal
          else 0) *
          quittingRootPayoff reward (0 : Payoff ι) action owner) = _
  rw [sum_opponentActionMass_mul_ownerReward]
  rfl

/-- Peeling the first live date gives the ordinary finite Never recursion. -/
theorem quittingFirstOpponentRawMean_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    quittingFirstOpponentRawMean reward roots owner start (fuel + 1) =
      quittingFixedOpponentsContinueReward reward roots owner start +
        quittingFixedOpponentsContinueMass roots owner start *
          quittingFirstOpponentRawMean reward roots owner (start + 1) fuel := by
  rw [quittingFirstOpponentRawMean_eq_sum_continueReward,
    Finset.sum_range_succ']
  simp only [quittingOpponentSurvivalWeight, Finset.range_zero,
    Finset.prod_empty, one_mul, Nat.add_zero]
  rw [quittingFirstOpponentRawMean_eq_sum_continueReward, Finset.mul_sum]
  let currentReward :=
    quittingFixedOpponentsContinueReward reward roots owner start
  let leftTail := ∑ offset ∈ Finset.range fuel,
    quittingOpponentSurvivalWeight roots owner start (offset + 1) *
      quittingFixedOpponentsContinueReward reward roots owner
        (start + (offset + 1))
  let rightTail := ∑ offset ∈ Finset.range fuel,
    quittingFixedOpponentsContinueMass roots owner start *
      (quittingOpponentSurvivalWeight roots owner (start + 1) offset *
        quittingFixedOpponentsContinueReward reward roots owner
          ((start + 1) + offset))
  change leftTail + currentReward = currentReward + rightTail
  rw [add_comm leftTail currentReward]
  apply congrArg (fun tail : ℝ ↦ currentReward + tail)
  dsimp only [leftTail, rightTail]
  apply Finset.sum_congr rfl
  intro offset hoffset
  have hweight := quittingOpponentSurvivalWeight_add
    roots owner start 1 offset
  have hone : quittingOpponentSurvivalWeight roots owner start 1 =
      quittingFixedOpponentsContinueMass roots owner start := by
    simp [quittingOpponentSurvivalWeight]
  rw [hone] at hweight
  calc
    quittingOpponentSurvivalWeight roots owner start (offset + 1) *
          quittingFixedOpponentsContinueReward reward roots owner
            (start + (offset + 1)) =
        (quittingFixedOpponentsContinueMass roots owner start *
            quittingOpponentSurvivalWeight roots owner (start + 1) offset) *
          quittingFixedOpponentsContinueReward reward roots owner
            ((start + 1) + offset) := by
      rw [show offset + 1 = 1 + offset by omega, hweight]
      congr 2; omega
    _ = quittingFixedOpponentsContinueMass roots owner start *
        (quittingOpponentSurvivalWeight roots owner (start + 1) offset *
          quittingFixedOpponentsContinueReward reward roots owner
            ((start + 1) + offset)) := by ring

/-- On an exact finite Nash--Bellman chain with zero terminal boundary, the
actual finite Never payoff is no larger than the declared current value.

The proof uses only the pure-Continue test from local root Nash.  It peels
the concrete first-opponent moment one date at a time, so there is no
separate strategic `Never` hypothesis hidden in the marked-fence adapter. -/
theorem quittingFirstOpponentRawMean_le_value_of_finiteExactChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (owner : ι) (start fuel : ℕ)
    (hterminal : value (start + fuel) = 0)
    (hpolicy : ∀ offset, offset < fuel →
      value (start + offset) =
        quittingRootSuccessorPayoff reward
          (value (start + offset + 1)) (roots (start + offset)))
    (hnash : ∀ offset, offset < fuel →
      IsεQuittingRootNash reward (value (start + offset + 1)) 0
        (roots (start + offset))) :
    quittingFirstOpponentRawMean reward roots owner start fuel ≤
      value start owner := by
  induction fuel generalizing start with
  | zero =>
      have hterminal' : value start = 0 := by
        simpa using hterminal
      rw [hterminal']
      simp [quittingFirstOpponentRawMean]
  | succ fuel ih =>
      have htailTerminal : value ((start + 1) + fuel) = 0 := by
        rw [show (start + 1) + fuel = start + Nat.succ fuel by omega]
        exact hterminal
      have htailPolicy : ∀ offset, offset < fuel →
          value ((start + 1) + offset) =
            quittingRootSuccessorPayoff reward
              (value ((start + 1) + offset + 1))
              (roots ((start + 1) + offset)) := by
        intro offset hoffset
        simpa only [Nat.add_assoc, Nat.one_add] using
          hpolicy (offset + 1) (by omega)
      have htailNash : ∀ offset, offset < fuel →
          IsεQuittingRootNash reward
            (value ((start + 1) + offset + 1)) 0
            (roots ((start + 1) + offset)) := by
        intro offset hoffset
        simpa only [Nat.add_assoc, Nat.one_add] using
          hnash (offset + 1) (by omega)
      have htail := ih (start + 1) htailTerminal htailPolicy htailNash
      have hpolicyZero : value start owner =
          quittingRootSuccessorPayoff reward (value (start + 1))
            (roots start) owner := by
        simpa using congrFun (hpolicy 0 (by omega)) owner
      have hcontinue := (hnash 0 (by omega)) owner (PMF.pure false)
      have hrootContinue :
          quittingFixedOpponentsContinueReward reward roots owner start +
              quittingFixedOpponentsContinueMass roots owner start *
                value (start + 1) owner ≤
            value start owner := by
        rw [← quittingRootContinuePayoff_eq_fixedOpponents
          reward roots owner (value (start + 1)) start]
        change quittingRootContinuePayoff reward (value (start + 1))
            (roots start) owner ≤
          quittingRootSuccessorPayoff reward (value (start + 1))
            (roots start) owner + 0 at hcontinue
        rw [← hpolicyZero] at hcontinue
        simpa only [add_zero] using hcontinue
      rw [quittingFirstOpponentRawMean_succ]
      calc
        quittingFixedOpponentsContinueReward reward roots owner start +
              quittingFixedOpponentsContinueMass roots owner start *
                quittingFirstOpponentRawMean reward roots owner
                  (start + 1) fuel ≤
            quittingFixedOpponentsContinueReward reward roots owner start +
              quittingFixedOpponentsContinueMass roots owner start *
                value (start + 1) owner := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left htail
              (quittingStationaryContinueMass_nonneg
                (Function.update (roots start) owner (PMF.pure false)))) _
        _ ≤ value start owner := hrootContinue

/-! ## Bounds and normalization -/

omit [DecidableEq ι] in
/-- The displayed owner reward inherits the common lower reward bound. -/
theorem quittingFirstOpponentOwnerReward_lower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {fuel : ℕ} (mark : QuittingFirstOpponentMark ι fuel)
    (M : ℝ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    -M ≤ quittingFirstOpponentOwnerReward reward owner mark := by
  unfold quittingFirstOpponentOwnerReward
  by_cases hquit : (quittingQuitters mark.2).Nonempty
  · simp only [quittingRootPayoff, dif_pos hquit]
    exact (abs_le.mp (hreward ⟨quittingQuitters mark.2, hquit⟩ owner)).1
  · simp only [quittingRootPayoff, dif_neg hquit, Pi.zero_apply]
    linarith

/-- The raw owner moment is bounded below by `-M` times the actual fence
mass. -/
theorem neg_M_mul_quittingFirstOpponentMass_le_rawMean
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ)
    (M : ℝ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    -M * quittingFirstOpponentMass roots owner start fuel ≤
      quittingFirstOpponentRawMean reward roots owner start fuel := by
  rw [← sum_quittingFirstOpponentRawWeight]
  unfold quittingFirstOpponentRawMean
  calc
    -M * (∑ mark : QuittingFirstOpponentMark ι fuel,
        quittingFirstOpponentRawWeight roots owner start fuel mark) =
        ∑ mark : QuittingFirstOpponentMark ι fuel,
          quittingFirstOpponentRawWeight roots owner start fuel mark * (-M) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mark _
      ring
    _ ≤ ∑ mark : QuittingFirstOpponentMark ι fuel,
        quittingFirstOpponentRawWeight roots owner start fuel mark *
          quittingFirstOpponentOwnerReward reward owner mark := by
      apply Finset.sum_le_sum
      intro mark _
      exact mul_le_mul_of_nonneg_left
        (quittingFirstOpponentOwnerReward_lower reward owner mark M hM hreward)
        (quittingFirstOpponentRawWeight_nonneg roots owner start fuel mark)

/-- A Never inequality at a negative suffix forces a quantitative amount of
actual opponent-fence mass.  This is a division-free fence bound. -/
theorem theta_le_M_mul_quittingFirstOpponentMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (owner : ι) (start fuel : ℕ) (θ M : ℝ)
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnever : quittingFirstOpponentRawMean reward roots owner start fuel ≤
      value start owner)
    (hnegative : value start owner ≤ -θ) :
    θ ≤ M * quittingFirstOpponentMass roots owner start fuel := by
  have hlower := neg_M_mul_quittingFirstOpponentMass_le_rawMean
    reward roots owner start fuel M hM hreward
  linarith

/-- A positive threshold makes the actual opponent-fence mass strictly
positive. -/
theorem quittingFirstOpponentMass_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (owner : ι) (start fuel : ℕ) (θ M : ℝ)
    (hθ : 0 < θ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnever : quittingFirstOpponentRawMean reward roots owner start fuel ≤
      value start owner)
    (hnegative : value start owner ≤ -θ) :
    0 < quittingFirstOpponentMass roots owner start fuel := by
  have hfence := theta_le_M_mul_quittingFirstOpponentMass
    reward roots value owner start fuel θ M hM hreward hnever hnegative
  have hmass0 := quittingFirstOpponentMass_nonneg roots owner start fuel
  nlinarith

/-- Positive actual fence mass normalizes the concrete weights to one. -/
theorem sum_quittingFirstOpponentWeight
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ)
    (hmass : 0 < quittingFirstOpponentMass roots owner start fuel) :
    (∑ mark : QuittingFirstOpponentMark ι fuel,
      quittingFirstOpponentWeight roots owner start fuel mark) = 1 := by
  unfold quittingFirstOpponentWeight
  rw [← Finset.sum_div, sum_quittingFirstOpponentRawWeight]
  exact div_self (ne_of_gt hmass)

/-- Normalized actual first-opponent weights are nonnegative. -/
theorem quittingFirstOpponentWeight_nonneg
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ)
    (hmass : 0 < quittingFirstOpponentMass roots owner start fuel)
    (mark : QuittingFirstOpponentMark ι fuel) :
    0 ≤ quittingFirstOpponentWeight roots owner start fuel mark := by
  exact div_nonneg
    (quittingFirstOpponentRawWeight_nonneg roots owner start fuel mark)
    hmass.le

/-- Normalization divides the raw owner moment by the actual fence mass. -/
theorem sum_quittingFirstOpponentWeight_mul_ownerReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start fuel : ℕ) :
    (∑ mark : QuittingFirstOpponentMark ι fuel,
      quittingFirstOpponentWeight roots owner start fuel mark *
        quittingFirstOpponentOwnerReward reward owner mark) =
      quittingFirstOpponentRawMean reward roots owner start fuel /
        quittingFirstOpponentMass roots owner start fuel := by
  unfold quittingFirstOpponentWeight quittingFirstOpponentRawMean
  calc
    (∑ mark : QuittingFirstOpponentMark ι fuel,
        quittingFirstOpponentRawWeight roots owner start fuel mark /
            quittingFirstOpponentMass roots owner start fuel *
          quittingFirstOpponentOwnerReward reward owner mark) =
        ∑ mark : QuittingFirstOpponentMark ι fuel,
          (quittingFirstOpponentRawWeight roots owner start fuel mark *
            quittingFirstOpponentOwnerReward reward owner mark) /
              quittingFirstOpponentMass roots owner start fuel := by
      apply Finset.sum_congr rfl
      intro mark _
      ring
    _ = (∑ mark : QuittingFirstOpponentMark ι fuel,
          quittingFirstOpponentRawWeight roots owner start fuel mark *
            quittingFirstOpponentOwnerReward reward owner mark) /
              quittingFirstOpponentMass roots owner start fuel := by
      rw [Finset.sum_div]

/-- The normalized actual owner moment is at most the same negative threshold
as the suffix value. -/
theorem sum_normalizedOwnerReward_le_neg_theta
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (owner : ι) (start fuel : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ)
    (hmass : 0 < quittingFirstOpponentMass roots owner start fuel)
    (hnever : quittingFirstOpponentRawMean reward roots owner start fuel ≤
      value start owner)
    (hnegative : value start owner ≤ -θ) :
    (∑ mark : QuittingFirstOpponentMark ι fuel,
      quittingFirstOpponentWeight roots owner start fuel mark *
        quittingFirstOpponentOwnerReward reward owner mark) ≤ -θ := by
  rw [sum_quittingFirstOpponentWeight_mul_ownerReward]
  apply (div_le_iff₀ hmass).2
  have hmass1 := quittingFirstOpponentMass_le_one roots owner start fuel
  have hraw : quittingFirstOpponentRawMean reward roots owner start fuel ≤ -θ :=
    hnever.trans hnegative
  nlinarith [mul_nonneg hθ
    (sub_nonneg.mpr hmass1)]

/-- **Concrete marked-fence adapter.**  An actual finite suffix whose Never
moment is below a negative declared value satisfies the abstract packet
dichotomy with the genuine first-opponent weights, actual quitter sets, and
actual suffix values. -/
theorem quittingFirstOpponent_markedFenceDichotomy
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (owner : ι) (start fuel : ℕ) (θ M : ℝ)
    (hθ : 0 < θ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnever : quittingFirstOpponentRawMean reward roots owner start fuel ≤
      value start owner)
    (hnegative : value start owner ≤ -θ) :
    θ ≤ 4 * M * QuittingMarkedFencePacket.packetMass
        (quittingFirstOpponentWeight roots owner start fuel)
        (QuittingMarkedFencePacket.IsGoodBoundary θ
          (quittingFirstOpponentOwnerReward reward owner)
          (quittingFirstOpponentQuitters owner)
          (quittingFirstOpponentValue value start)) ∨
      ∃ j ∈ (Finset.univ.erase owner : Finset ι),
        θ ≤ 4 * M * ((Finset.univ.erase owner : Finset ι).card : ℝ) *
          QuittingMarkedFencePacket.packetMass
            (quittingFirstOpponentWeight roots owner start fuel)
            (QuittingMarkedFencePacket.IsNewNegativeOwner θ
              (quittingFirstOpponentOwnerReward reward owner)
              (quittingFirstOpponentQuitters owner)
              (quittingFirstOpponentValue value start) j) := by
  have hmass := quittingFirstOpponentMass_pos reward roots value owner
    start fuel θ M hθ hM hreward hnever hnegative
  apply QuittingMarkedFencePacket.marked_packet_dichotomy
    owner
    (quittingFirstOpponentWeight roots owner start fuel)
    (quittingFirstOpponentOwnerReward reward owner)
    (quittingFirstOpponentQuitters owner)
    (quittingFirstOpponentValue value start) θ M
  · exact quittingFirstOpponentWeight_nonneg roots owner start fuel hmass
  · exact sum_quittingFirstOpponentWeight roots owner start fuel hmass
  · exact hθ.le
  · exact hM
  · intro mark
    exact quittingFirstOpponentOwnerReward_lower reward owner mark M hM hreward
  · exact sum_normalizedOwnerReward_le_neg_theta reward roots value owner
      start fuel θ hθ.le hmass hnever hnegative
  · exact quittingFirstOpponent_owner_not_quitter owner

/-- **Exact-chain marked-fence theorem.**  A negative coordinate on a
finite, zero-boundary Nash--Bellman chain directly yields the concrete
first-opponent packet dichotomy.  Unlike
`quittingFirstOpponent_markedFenceDichotomy`, this statement does not assume
the strategic Never inequality: local exact root Nash proves it by backward
induction through the supplied policy-evaluation chain. -/
theorem quittingFiniteExactChain_firstOpponent_markedFenceDichotomy
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (owner : ι) (start fuel : ℕ) (θ M : ℝ)
    (hterminal : value (start + fuel) = 0)
    (hpolicy : ∀ offset, offset < fuel →
      value (start + offset) =
        quittingRootSuccessorPayoff reward
          (value (start + offset + 1)) (roots (start + offset)))
    (hnash : ∀ offset, offset < fuel →
      IsεQuittingRootNash reward (value (start + offset + 1)) 0
        (roots (start + offset)))
    (hθ : 0 < θ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnegative : value start owner ≤ -θ) :
    θ ≤ 4 * M * QuittingMarkedFencePacket.packetMass
        (quittingFirstOpponentWeight roots owner start fuel)
        (QuittingMarkedFencePacket.IsGoodBoundary θ
          (quittingFirstOpponentOwnerReward reward owner)
          (quittingFirstOpponentQuitters owner)
          (quittingFirstOpponentValue value start)) ∨
      ∃ j ∈ (Finset.univ.erase owner : Finset ι),
        θ ≤ 4 * M * ((Finset.univ.erase owner : Finset ι).card : ℝ) *
          QuittingMarkedFencePacket.packetMass
            (quittingFirstOpponentWeight roots owner start fuel)
            (QuittingMarkedFencePacket.IsNewNegativeOwner θ
              (quittingFirstOpponentOwnerReward reward owner)
              (quittingFirstOpponentQuitters owner)
              (quittingFirstOpponentValue value start) j) := by
  apply quittingFirstOpponent_markedFenceDichotomy reward roots value owner
    start fuel θ M hθ hM hreward
  · exact quittingFirstOpponentRawMean_le_value_of_finiteExactChain
      reward roots value owner start fuel hterminal hpolicy hnash
  · exact hnegative

end GameTheory
