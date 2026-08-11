/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectTelescope
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticWeightedAuxiliaryNashBudget

/-!
# Dynamic costates for the plateau defect charge

A nonnegative costate keeps the opponent-absorption charge and the local Nash
defect on exactly the same player coordinates.  The costate may also vary
along the actual chronology.  The resulting stopped telescope has one new,
and unavoidable, term: the loss incurred when the new costate scores the
current tail debt below the old costate.

Thus a relabeling is free precisely when it moves uphill for the displayed
tail-debt vector.  For coordinate costates, switching from `owner time` to
`owner (time + 1)` costs

`debt(owner time) - debt(owner (time + 1))`.

This identifies the exact dynamic seam in the weighted-normal-fan route.  A
fixed costate has no switching loss, while a costate which follows changing
defect labels needs an uphill debt-transfer certificate.  Merely normalizing
costates cannot remove the seam: a componentwise increasing normalized
costate is constant.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Weighted local Nash defect, retaining the player coordinate on every
summand. -/
def quittingRootWeightedNashDefect
    (theta : Payoff ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) : ℝ :=
  ∑ who, theta who *
    quittingRootCoordinateNashDefect reward tail root who

/-- Weighted opponent-absorption debt charge, with the same coordinate
weights as `quittingRootWeightedNashDefect`. -/
def quittingRootWeightedOpponentAbsorptionDebtCharge
    (theta : Payoff ι) (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) : ℝ :=
  ∑ who, theta who *
    (quittingRootOpponentAbsorptionMass root who *
      quittingTerminalSemanticDebt pair who)

/-- Coordinatewise defect-or-drift charge for an arbitrary nonnegative
costate.  This is the one-row label-matched form of the defect charge. -/
theorem quittingRootWeightedOpponentAbsorptionDebtCharge_le_drift_add_defect
    (theta : Payoff ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (htheta : ∀ who, 0 ≤ theta who)
    (hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who) :
    quittingRootWeightedOpponentAbsorptionDebtCharge theta pair root ≤
      quittingTerminalSemanticWeightedDebtSum theta pair -
        quittingTerminalSemanticWeightedDebtSum theta
          (quittingTerminalSemanticPrefix reward root pair) +
      quittingRootWeightedNashDefect theta reward pair.1 root := by
  have hcoordinate : ∀ who,
      theta who *
          (quittingRootOpponentAbsorptionMass root who *
            quittingTerminalSemanticDebt pair who) ≤
        theta who *
          (quittingTerminalSemanticDebt pair who -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPrefix reward root pair) who +
            quittingRootCoordinateNashDefect reward pair.1 root who) := by
    intro who
    exact mul_le_mul_of_nonneg_left
      (quittingRootOpponentAbsorptionMass_mul_debt_le_drift_add_nashDefect
        reward pair root who (hdebt who))
      (htheta who)
  have hsum := Finset.sum_le_sum fun who (_hwho : who ∈ Finset.univ) =>
    hcoordinate who
  unfold quittingRootWeightedOpponentAbsorptionDebtCharge
    quittingTerminalSemanticWeightedDebtSum
    quittingRootWeightedNashDefect
  calc
    _ ≤ ∑ who, theta who *
        (quittingTerminalSemanticDebt pair who -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPrefix reward root pair) who +
          quittingRootCoordinateNashDefect reward pair.1 root who) := hsum
    _ = _ := by
      simp_rw [mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- A costate concentrated on one player. -/
def quittingCoordinateCostate (owner : ι) : Payoff ι :=
  fun who => if who = owner then 1 else 0

/-- A coordinate costate reads exactly its owner's debt. -/
theorem quittingTerminalSemanticWeightedDebtSum_coordinateCostate
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) :
    quittingTerminalSemanticWeightedDebtSum
        (quittingCoordinateCostate owner) pair =
      quittingTerminalSemanticDebt pair owner := by
  unfold quittingTerminalSemanticWeightedDebtSum quittingCoordinateCostate
  simp

/-- A coordinate costate retains exactly one coordinate of the weighted Nash
defect. -/
theorem quittingRootWeightedNashDefect_coordinateCostate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner : ι) :
    quittingRootWeightedNashDefect (quittingCoordinateCostate owner)
        reward tail root =
      quittingRootCoordinateNashDefect reward tail root owner := by
  unfold quittingRootWeightedNashDefect quittingCoordinateCostate
  simp

/-- A coordinate costate retains exactly one coordinate of the weighted
opponent-absorption debt charge. -/
theorem quittingRootWeightedOpponentAbsorptionDebtCharge_coordinateCostate
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (owner : ι) :
    quittingRootWeightedOpponentAbsorptionDebtCharge
        (quittingCoordinateCostate owner) pair root =
      quittingRootOpponentAbsorptionMass root owner *
        quittingTerminalSemanticDebt pair owner := by
  unfold quittingRootWeightedOpponentAbsorptionDebtCharge
    quittingCoordinateCostate
  simp

omit [DecidableEq ι] in
/-- A nonnegative debt coordinate is bounded by maximum semantic
exploitability. -/
theorem quittingTerminalSemanticDebt_le_exploitability
    [Nonempty ι] (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who) :
    quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticExploitability pair := by
  unfold quittingTerminalSemanticExploitability
  rw [← max_eq_right hdebt]
  exact le_finitePlayerMax
    (fun player => max 0 (quittingTerminalSemanticDebt pair player)) who

omit [DecidableEq ι] in
/-- At a nonnegative debt vector, a maximizing coordinate is exactly the
maximum semantic exploitability. -/
theorem quittingTerminalSemanticExploitability_eq_debt_of_maximizer
    [Nonempty ι] (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who)
    (hmax : ∀ who, quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebt pair owner) :
    quittingTerminalSemanticExploitability pair =
      quittingTerminalSemanticDebt pair owner := by
  apply le_antisymm
  · unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    rw [max_eq_right (hdebt who)]
    exact hmax who
  · exact quittingTerminalSemanticDebt_le_exploitability
      pair owner (hdebt owner)

/-- The shifted spine admits a debt-maximizing player at every time. -/
theorem exists_quittingSpineDebtMaximizer
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ owner : ℕ → ι, ∀ time who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) who ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time))
          (owner time) := by
  have hexists : ∀ time, ∃ owner : ι, ∀ who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) who ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) owner := by
    intro time
    obtain ⟨owner, _hownerMem, howner⟩ :=
      Finset.exists_max_image Finset.univ
        (fun who => quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) who)
        Finset.univ_nonempty
    exact ⟨owner, fun who => howner who (Finset.mem_univ who)⟩
  choose owner howner using hexists
  exact ⟨owner, howner⟩

/-- Weighted semantic debt of the actual shifted spine at one time. -/
def quittingSpineCostateDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : ℕ → Payoff ι) (time : ℕ) : ℝ :=
  quittingTerminalSemanticWeightedDebtSum (theta time)
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time))

/-- The row-`time` costate applied to the next shifted tail. -/
def quittingSpineCurrentCostateTailDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : ℕ → Payoff ι) (time : ℕ) : ℝ :=
  quittingTerminalSemanticWeightedDebtSum (theta time)
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1)))

/-- Loss caused by changing the costate across a live row.  It is nonpositive
exactly when the new costate scores the current tail at least as highly as the
old one. -/
def quittingSpineCostateSwitchLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : ℕ → Payoff ι) (time : ℕ) : ℝ :=
  quittingSpineCurrentCostateTailDebt reward profile theta time -
    quittingSpineCostateDebt reward profile theta (time + 1)

/-- Weighted opponent-absorption debt charge on one actual live row. -/
def quittingSpineCostateOpponentAbsorptionDebtCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : ℕ → Payoff ι) (time : ℕ) : ℝ :=
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  quittingRootWeightedOpponentAbsorptionDebtCharge (theta time) tail
    (quittingProfileLiveRoot reward profile time)

/-- Weighted local Nash defect on one actual live row. -/
def quittingSpineCostateNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : ℕ → Payoff ι) (time : ℕ) : ℝ :=
  quittingRootWeightedNashDefect (theta time) reward
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    (quittingProfileLiveRoot reward profile time)

/-- Dynamic weighted-debt excess above a fixed reference level. -/
def quittingSpineCostateDebtExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : ℕ → Payoff ι) (reference : ℝ) (time : ℕ) : ℝ :=
  quittingSpineCostateDebt reward profile theta time - reference

/-- For coordinate costates, the switching loss is precisely old-owner debt
minus new-owner debt on the shared shifted tail. -/
theorem quittingSpineCostateSwitchLoss_coordinate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ℕ → ι) (time : ℕ) :
    quittingSpineCostateSwitchLoss reward profile
        (fun stage => quittingCoordinateCostate (owner stage)) time =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1)))
          (owner time) -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1)))
          (owner (time + 1)) := by
  unfold quittingSpineCostateSwitchLoss
    quittingSpineCurrentCostateTailDebt quittingSpineCostateDebt
  rw [quittingTerminalSemanticWeightedDebtSum_coordinateCostate,
    quittingTerminalSemanticWeightedDebtSum_coordinateCostate]

private theorem sum_mul_forwardDiff_eq_endpoint_add_drop
    (live excess : ℕ → ℝ) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        live time * (excess (time + 1) - excess time)) =
      live cutoff * excess cutoff - live 0 * excess 0 +
        ∑ time ∈ Finset.range cutoff,
          (live time - live (time + 1)) * excess (time + 1) := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring

private theorem sum_forwardDrop_eq_start_sub_endpoint
    (live : ℕ → ℝ) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        (live time - live (time + 1))) = live 0 - live cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- **Dynamic-costate stopped telescope.**  The charge and defect remain
coordinate-matched.  Changing the costate contributes exactly the displayed
switching loss; no relabeling is silently treated as free. -/
theorem sum_liveMass_mul_spineCostateCharge_le_stoppedDefectExcessSwitch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : ℕ → Payoff ι) (reference : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htheta : ∀ time who, 0 ≤ theta time who) :
    (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineCostateOpponentAbsorptionDebtCharge
            reward profile theta time) ≤
      quittingLiveMass reward profile cutoff *
          quittingSpineCostateDebtExcess
            reward profile theta reference cutoff -
        quittingSpineCostateDebtExcess reward profile theta reference 0 +
      (∑ time ∈ Finset.range cutoff,
        (quittingLiveMass reward profile time -
            quittingLiveMass reward profile (time + 1)) *
          quittingSpineCostateDebtExcess
            reward profile theta reference (time + 1)) +
      (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineCostateSwitchLoss reward profile theta time) +
      ∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineCostateNashDefect reward profile theta time := by
  have hrow : ∀ time,
      quittingSpineCostateOpponentAbsorptionDebtCharge
          reward profile theta time ≤
        quittingSpineCostateDebtExcess
            reward profile theta reference (time + 1) -
          quittingSpineCostateDebtExcess
            reward profile theta reference time +
          quittingSpineCostateSwitchLoss reward profile theta time +
          quittingSpineCostateNashDefect reward profile theta time := by
    intro time
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))
    let current := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)
    let root := quittingProfileLiveRoot reward profile time
    have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPair_mem_carrier reward _
    have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward htailCarrier
    have hcharge :=
      quittingRootWeightedOpponentAbsorptionDebtCharge_le_drift_add_defect
        (theta time) reward tail root (htheta time) htailDebt
    have hprefix : current = quittingTerminalSemanticPrefix reward root tail := by
      dsimp only [current, root, tail]
      exact quittingTerminalSemanticPair_spine_eq_prefix
        reward profile time hM hreward
    rw [← hprefix] at hcharge
    dsimp only [quittingSpineCostateOpponentAbsorptionDebtCharge,
      quittingSpineCostateNashDefect]
    dsimp only [tail, root] at hcharge ⊢
    unfold quittingSpineCostateDebtExcess
      quittingSpineCostateSwitchLoss
      quittingSpineCurrentCostateTailDebt quittingSpineCostateDebt
    linarith
  have hweighted : ∀ time,
      quittingLiveMass reward profile time *
          quittingSpineCostateOpponentAbsorptionDebtCharge
            reward profile theta time ≤
        quittingLiveMass reward profile time *
          (quittingSpineCostateDebtExcess
              reward profile theta reference (time + 1) -
            quittingSpineCostateDebtExcess
              reward profile theta reference time +
            quittingSpineCostateSwitchLoss reward profile theta time +
            quittingSpineCostateNashDefect reward profile theta time) := by
    intro time
    exact mul_le_mul_of_nonneg_left (hrow time)
      (quittingLiveMass_nonneg reward profile time)
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) => hweighted time
  have habel := sum_mul_forwardDiff_eq_endpoint_add_drop
    (quittingLiveMass reward profile)
    (quittingSpineCostateDebtExcess reward profile theta reference) cutoff
  rw [quittingLiveMass_zero] at habel
  calc
    (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineCostateOpponentAbsorptionDebtCharge
            reward profile theta time) ≤
      (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          (quittingSpineCostateDebtExcess
              reward profile theta reference (time + 1) -
            quittingSpineCostateDebtExcess
              reward profile theta reference time)) +
      (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineCostateSwitchLoss reward profile theta time) +
      ∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineCostateNashDefect reward profile theta time := by
      simpa [mul_add, Finset.sum_add_distrib, add_assoc] using hsum
    _ = _ := by rw [habel]; ring

/-- If shifted spines stay near the dynamic weighted reference and every
costate switch moves weakly uphill on the shared tail debt, excess and
switching together cost at most `epsilon`.  The sole remaining term is the
coordinate-matched weighted defect occupation. -/
theorem sum_liveMass_mul_spineCostateCharge_le_epsilon_add_defect_of_uphill
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (theta : ℕ → Payoff ι) (reference epsilon : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htheta : ∀ time who, 0 ≤ theta time who)
    (hinitial : 0 ≤ quittingSpineCostateDebtExcess
      reward profile theta reference 0)
    (hnear : ∀ time ≤ cutoff,
      quittingSpineCostateDebtExcess
        reward profile theta reference time ≤ epsilon)
    (huphill : ∀ time < cutoff,
      quittingSpineCurrentCostateTailDebt reward profile theta time ≤
        quittingSpineCostateDebt reward profile theta (time + 1)) :
    (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineCostateOpponentAbsorptionDebtCharge
            reward profile theta time) ≤
      epsilon +
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingSpineCostateNashDefect reward profile theta time := by
  have htelescope :=
    sum_liveMass_mul_spineCostateCharge_le_stoppedDefectExcessSwitch
      reward profile theta reference cutoff hM hreward htheta
  have hliveEndpointNonneg := quittingLiveMass_nonneg reward profile cutoff
  have hendpoint : quittingLiveMass reward profile cutoff *
      quittingSpineCostateDebtExcess reward profile theta reference cutoff ≤
        quittingLiveMass reward profile cutoff * epsilon :=
    mul_le_mul_of_nonneg_left (hnear cutoff le_rfl) hliveEndpointNonneg
  have hdropNonneg : ∀ time,
      0 ≤ quittingLiveMass reward profile time -
        quittingLiveMass reward profile (time + 1) := by
    intro time
    exact sub_nonneg.mpr (quittingLiveMass_succ_le reward profile time)
  have hdrop : (∑ time ∈ Finset.range cutoff,
      (quittingLiveMass reward profile time -
          quittingLiveMass reward profile (time + 1)) *
        quittingSpineCostateDebtExcess
          reward profile theta reference (time + 1)) ≤
      ∑ time ∈ Finset.range cutoff,
        (quittingLiveMass reward profile time -
          quittingLiveMass reward profile (time + 1)) * epsilon := by
    exact Finset.sum_le_sum fun time htime =>
      mul_le_mul_of_nonneg_left
        (hnear (time + 1) (by
          have := Finset.mem_range.mp htime
          omega))
        (hdropNonneg time)
  have hdropSum := sum_forwardDrop_eq_start_sub_endpoint
    (quittingLiveMass reward profile) cutoff
  rw [quittingLiveMass_zero] at hdropSum
  have hswitch : (∑ time ∈ Finset.range cutoff,
      quittingLiveMass reward profile time *
        quittingSpineCostateSwitchLoss reward profile theta time) ≤ 0 := by
    exact Finset.sum_nonpos fun time htime =>
      mul_nonpos_of_nonneg_of_nonpos
        (quittingLiveMass_nonneg reward profile time)
        (sub_nonpos.mpr (huphill time (Finset.mem_range.mp htime)))
  have hbudget :
      quittingLiveMass reward profile cutoff *
            quittingSpineCostateDebtExcess
              reward profile theta reference cutoff -
          quittingSpineCostateDebtExcess
            reward profile theta reference 0 +
        (∑ time ∈ Finset.range cutoff,
          (quittingLiveMass reward profile time -
              quittingLiveMass reward profile (time + 1)) *
            quittingSpineCostateDebtExcess
              reward profile theta reference (time + 1)) ≤
        epsilon := by
    calc
      _ ≤ quittingLiveMass reward profile cutoff * epsilon +
          (∑ time ∈ Finset.range cutoff,
            (quittingLiveMass reward profile time -
              quittingLiveMass reward profile (time + 1)) * epsilon) := by
        linarith
      _ = epsilon := by
        rw [← Finset.sum_mul, hdropSum]
        ring
  linarith

/-! ## The maximum-debt moat -/

/-- Maximum semantic exploitability attains a minimum on the compact
terminal-semantic carrier. -/
theorem exists_minimum_quittingTerminalSemanticExploitability
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticExploitability pair ≤
          quittingTerminalSemanticExploitability candidate := by
  obtain ⟨pair, hpair, hmin⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward hM hreward).exists_isMinOn
      (quittingTerminalSemanticCarrier_nonempty reward)
      continuous_quittingTerminalSemanticExploitability.continuousOn
  exact ⟨pair, hpair, fun candidate hcandidate => hmin hcandidate⟩

/-- **Robust maximum-debt auxiliary moat.**  Suppose every carrier point has
maximum debt at least `floor`, while the displayed pair has maximum debt at
most `floor + epsilon`.  If every auxiliary shift stays `rho` below the
critical maximum-debt face, an exact auxiliary Nash root has absorption mass
at most `epsilon / (rho + epsilon)`, and hence at most `epsilon / rho`.

Unlike the summed budget, this estimate is coordinatewise.  Collision needs
no separate treatment: every singleton mass is at most total absorption, and
joint survival contracts every debt coordinate. -/
theorem nearMinimumTerminalSemantic_exploitabilityAuxiliaryNash_absorptionMass_le_sharp
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool)
    (floor epsilon rho : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      floor ≤ quittingTerminalSemanticExploitability candidate)
    (hpairUpper : quittingTerminalSemanticExploitability pair ≤
      floor + epsilon)
    (hepsilon : 0 ≤ epsilon) (hrho : 0 < rho)
    (hh : ∀ who, 0 ≤ h who)
    (hshift : ∀ who, h who ≤ floor - rho)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingRootAbsorptionMass root ≤ epsilon / (rho + epsilon) := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root pair hM hreward hpair
  have hpairDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hprefixedDebt : ∀ who,
      0 ≤ quittingTerminalSemanticDebt prefixed who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hprefixed
  have hpairDebtLe : ∀ who, quittingTerminalSemanticDebt pair who ≤
      floor + epsilon := by
    intro who
    exact (quittingTerminalSemanticDebt_le_exploitability
      pair who (hpairDebt who)).trans hpairUpper
  have hsingletonLeAbsorption : ∀ who,
      quittingRootCoalitionMass root {who} ≤
        quittingRootAbsorptionMass root := by
    intro who
    exact (quittingRootCoalitionMass_le_quitProbability_of_mem
      root {who} who (by simp)).trans
        (quitProbability_le_quittingRootAbsorptionMass root who)
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt prefixed who ≤
        quittingStationaryContinueMass root * (floor + epsilon) +
          quittingRootAbsorptionMass root * (floor - rho) := by
    intro who
    have hprefix := quittingTerminalSemanticDebt_prefix_le_auxiliaryNash
      (reward := reward) pair h root who (hh who) hnash
    have hcontinue := mul_le_mul_of_nonneg_left (hpairDebtLe who)
      (quittingStationaryContinueMass_nonneg root)
    have habsorptionNonneg := quittingRootAbsorptionMass_nonneg root
    have hsingletonNonneg :=
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who}
    have hsingletonShift :
        quittingRootCoalitionMass root {who} * h who ≤
          quittingRootAbsorptionMass root * (floor - rho) := by
      exact mul_le_mul (hsingletonLeAbsorption who) (hshift who)
        (hh who) habsorptionNonneg
    linarith
  have hprefixedUpper : quittingTerminalSemanticExploitability prefixed ≤
      quittingStationaryContinueMass root * (floor + epsilon) +
        quittingRootAbsorptionMass root * (floor - rho) := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    rw [max_eq_right (hprefixedDebt who)]
    exact hcoordinate who
  have hfloorPrefixed := hfloor prefixed hprefixed
  have hcontinueNonneg := quittingStationaryContinueMass_nonneg root
  have hcontinueLe := quittingStationaryContinueMass_le_one root
  have habsorption := quittingRootAbsorptionMass_nonneg root
  have hbudget := hfloorPrefixed.trans hprefixedUpper
  unfold quittingRootAbsorptionMass at hbudget ⊢
  apply (le_div_iff₀ (by linarith : 0 < rho + epsilon)).2
  nlinarith

/-- The convenient, slightly weaker `epsilon / rho` form of the robust
maximum-debt moat. -/
theorem nearMinimumTerminalSemantic_exploitabilityAuxiliaryNash_absorptionMass_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool)
    (floor epsilon rho : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      floor ≤ quittingTerminalSemanticExploitability candidate)
    (hpairUpper : quittingTerminalSemanticExploitability pair ≤
      floor + epsilon)
    (hepsilon : 0 ≤ epsilon) (hrho : 0 < rho)
    (hh : ∀ who, 0 ≤ h who)
    (hshift : ∀ who, h who ≤ floor - rho)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingRootAbsorptionMass root ≤ epsilon / rho := by
  have hsharp :=
    nearMinimumTerminalSemantic_exploitabilityAuxiliaryNash_absorptionMass_le_sharp
      reward pair h root floor epsilon rho hM hreward hpair hfloor
        hpairUpper hepsilon hrho hh hshift hnash
  have hfraction : epsilon / (rho + epsilon) ≤ epsilon / rho := by
    exact div_le_div_of_nonneg_left hepsilon hrho (by linarith)
  exact hsharp.trans hfraction

/-- At an exact minimum of maximum semantic debt, strict separation from all
critical shift faces forces the auxiliary Nash root to be all-Continue. -/
theorem minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability pair ≤
        quittingTerminalSemanticExploitability candidate)
    (hh : ∀ who, 0 ≤ h who)
    (hstrict : ∀ who, h who <
      quittingTerminalSemanticExploitability pair)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  let shiftMaximum := finitePlayerMax h
  let rho := quittingTerminalSemanticExploitability pair - shiftMaximum
  have hshiftMaximumLt : shiftMaximum <
      quittingTerminalSemanticExploitability pair := by
    unfold shiftMaximum finitePlayerMax
    rw [Finset.sup'_lt_iff]
    intro who _hwho
    exact hstrict who
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith
  have hshift : ∀ who,
      h who ≤ quittingTerminalSemanticExploitability pair - rho := by
    intro who
    dsimp only [rho]
    linarith [le_finitePlayerMax h who]
  have habsorptionLe :=
    nearMinimumTerminalSemantic_exploitabilityAuxiliaryNash_absorptionMass_le
      reward pair h root (quittingTerminalSemanticExploitability pair) 0 rho
        hM hreward hpair hminimum (by simp) (by positivity) hrho hh hshift hnash
  rw [zero_div] at habsorptionLe
  have habsorptionZero : quittingRootAbsorptionMass root = 0 :=
    le_antisymm habsorptionLe (quittingRootAbsorptionMass_nonneg root)
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at habsorptionZero
    linarith
  funext who
  have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hcontinue who
  simpa [quittingAllContinueRoot] using hpure

/-- At a positive minimum of maximum semantic debt, every singleton gap from
the envelope is at least the full minimax debt. -/
theorem minimumTerminalSemantic_exploitabilitySingletonMargin
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability pair ≤
        quittingTerminalSemanticExploitability candidate)
    (hpositive : 0 < quittingTerminalSemanticExploitability pair)
    (who : ι) :
    quittingTerminalSemanticExploitability pair ≤
      pair.2 who - reward (quittingSingletonTerminal who) who := by
  let zeroShift : Payoff ι := fun _ => 0
  obtain ⟨zeroRoot, hzeroNash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) pair.2
  have hzeroRoot : zeroRoot =
      (quittingAllContinueRoot : ι → PMF Bool) := by
    apply minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue
      reward pair zeroShift zeroRoot hM hreward hpair hminimum
    · intro player
      simp [zeroShift]
    · intro player
      simpa [zeroShift] using hpositive
    · have htail : pair.2 - zeroShift = pair.2 := by
        funext player
        simp [zeroShift]
      rw [htail]
      exact hzeroNash
  have hnashEnvelope : IsεQuittingRootNash reward pair.2 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa [hzeroRoot] using hzeroNash
  have hsingletonLeEnvelope :
      reward (quittingSingletonTerminal who) who ≤ pair.2 who :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward pair.2).mp hnashEnvelope who
  by_contra hnot
  have hgapLt : pair.2 who -
      reward (quittingSingletonTerminal who) who <
        quittingTerminalSemanticExploitability pair := lt_of_not_ge hnot
  let shift : Payoff ι := fun player =>
    if player = who then
      ((pair.2 who - reward (quittingSingletonTerminal who) who) +
        quittingTerminalSemanticExploitability pair) / 2
    else 0
  have hshiftNonneg : ∀ player, 0 ≤ shift player := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp only [shift, if_pos]
      nlinarith
    · simp [shift, hplayer]
  have hshiftStrict : ∀ player,
      shift player < quittingTerminalSemanticExploitability pair := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp only [shift, if_pos]
      nlinarith
    · simp [shift, hplayer, hpositive]
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash
    (reward := reward) (pair.2 - shift)
  have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) :=
    minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue
      reward pair shift root hM hreward hpair hminimum hshiftNonneg
        hshiftStrict hnash
  have hnashAll : IsεQuittingRootNash reward (pair.2 - shift) 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa [hroot] using hnash
  have hsingletonAux :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward (pair.2 - shift)).mp hnashAll who
  have hshiftWho : shift who =
      ((pair.2 who - reward (quittingSingletonTerminal who) who) +
        quittingTerminalSemanticExploitability pair) / 2 := by
    simp [shift]
  rw [Pi.sub_apply, hshiftWho] at hsingletonAux
  linarith

/-- Every positive minimizer of maximum semantic debt is an exact
all-Continue Nash self-loop.  Thus the dynamically aligned minimax objective
has the same plateau reduction as the previously used total-debt objective. -/
theorem minimumTerminalSemantic_exploitabilityIs_allContinuePlateau
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability pair ≤
        quittingTerminalSemanticExploitability candidate)
    (hpositive : 0 < quittingTerminalSemanticExploitability pair) :
    IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
        pair := by
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ pair.1 who := by
    intro who
    have hmargin :=
      minimumTerminalSemantic_exploitabilitySingletonMargin
        reward pair hM hreward hpair hminimum hpositive who
    have hdebtLe := quittingTerminalSemanticDebt_le_exploitability
      pair who (hdebtNonneg who)
    unfold quittingTerminalSemanticDebt at hdebtLe
    linarith
  have hnash :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le reward pair.1).mpr
      hsingleton
  exact ⟨hnash,
    quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
      reward pair hdebtNonneg hnash⟩

/-- **Max-debt matched selector.**  Choose at every shifted state a player
whose debt is maximal.  The next state's owner automatically scores the
shared tail at least as highly as the current owner, so every costate switch
is free.  Uniformly near-minimax shifted tails therefore charge the actual
opponent killing of the current maximal-debt coordinate to the local Nash
defect of that same player, with only one `epsilon` of total excess.

This is the dynamic label alignment supplied by the max-debt objective.  It
does not identify the remaining defects with one fixed player's cumulative
regret; the selected owner may still change with time. -/
theorem exists_maxDebtSelector_sum_liveMass_mul_charge_le_epsilon_add_defect
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (reference epsilon : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticExploitability candidate)
    (hnear : ∀ time ≤ cutoff,
      quittingTerminalSemanticExploitability
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) ≤
        reference + epsilon) :
    ∃ owner : ℕ → ι,
      (∀ time who,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) who ≤
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time))
            (owner time)) ∧
      (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          (quittingRootOpponentAbsorptionMass
              (quittingProfileLiveRoot reward profile time) (owner time) *
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1)))
              (owner time))) ≤
        epsilon +
          ∑ time ∈ Finset.range cutoff,
            quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine
                    reward profile (time + 1))).1
                (quittingProfileLiveRoot reward profile time) (owner time) := by
  obtain ⟨owner, howner⟩ :=
    exists_quittingSpineDebtMaximizer reward profile
  let theta : ℕ → Payoff ι :=
    fun time => quittingCoordinateCostate (owner time)
  have hscore : ∀ time,
      quittingSpineCostateDebt reward profile theta time =
        quittingTerminalSemanticExploitability
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) := by
    intro time
    let pair := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)
    have hpairCarrier : pair ∈ quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPair_mem_carrier reward _
    have hpairDebt : ∀ who,
        0 ≤ quittingTerminalSemanticDebt pair who :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward hpairCarrier
    have hmax : ∀ who, quittingTerminalSemanticDebt pair who ≤
        quittingTerminalSemanticDebt pair (owner time) := howner time
    unfold quittingSpineCostateDebt
    rw [quittingTerminalSemanticWeightedDebtSum_coordinateCostate]
    exact (quittingTerminalSemanticExploitability_eq_debt_of_maximizer
      pair (owner time) hpairDebt hmax).symm
  have htheta : ∀ time who, 0 ≤ theta time who := by
    intro time who
    by_cases hwho : who = owner time
    · simp [theta, quittingCoordinateCostate, hwho]
    · simp [theta, quittingCoordinateCostate, hwho]
  have hinitial : 0 ≤ quittingSpineCostateDebtExcess
      reward profile theta reference 0 := by
    unfold quittingSpineCostateDebtExcess
    rw [hscore]
    exact sub_nonneg.mpr (hfloor _
      (quittingTerminalSemanticPair_mem_carrier reward _))
  have hscoreNear : ∀ time ≤ cutoff,
      quittingSpineCostateDebtExcess
        reward profile theta reference time ≤ epsilon := by
    intro time htime
    unfold quittingSpineCostateDebtExcess
    rw [hscore]
    linarith [hnear time htime]
  have huphill : ∀ time < cutoff,
      quittingSpineCurrentCostateTailDebt reward profile theta time ≤
        quittingSpineCostateDebt reward profile theta (time + 1) := by
    intro time _htime
    unfold quittingSpineCurrentCostateTailDebt quittingSpineCostateDebt
    rw [quittingTerminalSemanticWeightedDebtSum_coordinateCostate,
      quittingTerminalSemanticWeightedDebtSum_coordinateCostate]
    exact howner (time + 1) (owner time)
  have hbound :=
    sum_liveMass_mul_spineCostateCharge_le_epsilon_add_defect_of_uphill
      reward profile theta reference epsilon cutoff hM hreward htheta
        hinitial hscoreNear huphill
  refine ⟨owner, howner, ?_⟩
  simpa only [quittingSpineCostateOpponentAbsorptionDebtCharge,
    quittingSpineCostateNashDefect, theta,
    quittingRootWeightedOpponentAbsorptionDebtCharge_coordinateCostate,
    quittingRootWeightedNashDefect_coordinateCostate] using hbound

/-- A max-debt selector gives the promised matched alternative on every row.
Either the old owner still carries almost the minimax floor on the shared
tail, so opponent absorption acts on a genuinely positive debt recipient, or
the new owner has gained at least the missing amount on that same tail. -/
theorem maxDebtSelector_tailDebt_or_transfer
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ℕ → ι) (reference eta : ℝ)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticExploitability candidate)
    (howner : ∀ time who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) who ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time))
          (owner time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ) :
    reference - eta ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1)))
          (owner time) ∨
      eta <
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (time + 1)))
            (owner (time + 1)) -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (time + 1)))
            (owner time) := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier
  have hnextMax : quittingTerminalSemanticExploitability tail =
      quittingTerminalSemanticDebt tail (owner (time + 1)) :=
    quittingTerminalSemanticExploitability_eq_debt_of_maximizer
      tail (owner (time + 1)) htailDebt (howner (time + 1))
  have hnextFloor : reference ≤
      quittingTerminalSemanticDebt tail (owner (time + 1)) := by
    rw [← hnextMax]
    exact hfloor tail htailCarrier
  by_cases hretained : reference - eta ≤
      quittingTerminalSemanticDebt tail (owner time)
  · exact Or.inl hretained
  · right
    have hlost := lt_of_not_ge hretained
    dsimp only [tail] at hnextFloor hlost ⊢
    linarith

omit [DecidableEq ι] in
/-- A componentwise increasing costate with unchanged total weight cannot
change at all.  In particular, normalized costates cannot chase changing
labels merely by invoking coordinatewise monotonicity. -/
theorem costate_eq_of_pointwise_le_of_sum_eq
    (theta next : Payoff ι) (hle : ∀ who, theta who ≤ next who)
    (hsum : (∑ who, theta who) = ∑ who, next who) :
    theta = next := by
  have hterm : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ next who - theta who := by
    intro who _hwho
    exact sub_nonneg.mpr (hle who)
  have hzero : Finset.univ.sum (fun player : ι =>
      next player - theta player) = 0 := by
    rw [Finset.sum_sub_distrib, ← hsum, sub_self]
  have hcoordinate := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero
  funext who
  have := hcoordinate who (Finset.mem_univ who)
  linarith

end GameTheory
