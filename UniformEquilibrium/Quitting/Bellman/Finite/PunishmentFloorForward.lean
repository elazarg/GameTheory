/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanFactory
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction
import UniformEquilibrium.Quitting.Projective.FiniteForwardProjectiveLasso

/-!
# A punishment-floor Nash--Bellman forward producer

The arbitrary compact Nash--Bellman spine admits the vacuous all-Continue
selection at the top of the reward box.  This module anchors the serial
selection instead at the coordinatewise stationary punishment value.

The key invariant is one-stage and exact.  Suppose the declared continuation
value of player `i` is at least its punishment value.  Every exact Nash root
then has current payoff at least the same punishment value.  Indeed the
punishment value is below the stationary unilateral cap of the opponents'
row.  If the cap is attained by quitting, exact root Nash dominates that pure
endpoint.  If it is attained by waiting, the Bellman continuation endpoint
is still above the punishment value.  The degenerate row in which every
opponent surely continues is handled separately by the exact empty-row cap.

Consequently predecessor iteration from the punishment vector gives one
chronological, product-realizable forward orbit of exact one-stage Nash roots,
all of whose values are individually rational.  Its finite prefixes are
`QuittingFiniteForwardPacket`s.  Therefore unbounded cumulative absorption
on this canonical orbit already implies a uniform-equilibrium payoff through
the existing finite charged-return and single-seam compiler.

The only branch left by this producer is explicit: cumulative absorption of
the punishment-floor orbit is bounded.  That is the projective boundary
regime; it is not hidden inside a compactness or strategy-selection premise.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The coordinatewise behavioral punishment floor. -/
def quittingPunishmentFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Payoff ι :=
  fun who => quittingPunishmentValue reward who

/-- The punishment floor lies in the canonical reward box. -/
theorem abs_quittingPunishmentFloor_le_quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) :
    |quittingPunishmentFloor reward who| ≤ quittingRewardBound reward := by
  rw [abs_le]
  constructor
  · unfold quittingPunishmentFloor quittingPunishmentValue
    exact le_ciInf fun profile =>
      neg_quittingRewardBound_le_quittingBestReplyValue reward profile who
  · exact (quittingPunishmentValue_le reward who
      (quittingAlwaysContinueProfile reward)).trans
      (quittingBestReplyValue_le reward
        (quittingAlwaysContinueProfile reward) who fun deviation =>
          (le_abs_self _).trans
            (abs_quittingTerminalPayoff_le reward _ who
              (quittingRewardBound_nonneg reward)
              (abs_reward_le_quittingRewardBound reward)))

/-- Exact root Nash dominates the pure-Quit endpoint. -/
theorem quittingRootQuitPayoff_le_successor_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingRootQuitPayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  have h := hnash who (PMF.pure true)
  change quittingRootQuitPayoff reward tail root who ≤
    quittingRootSuccessorPayoff reward tail root who + 0 at h
  simpa using h

/-- Exact root Nash dominates the pure-Continue endpoint. -/
theorem quittingRootContinuePayoff_le_successor_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingRootContinuePayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  have h := hnash who (PMF.pure false)
  change quittingRootContinuePayoff reward tail root who ≤
    quittingRootSuccessorPayoff reward tail root who + 0 at h
  simpa using h

/-- **Punishment-floor invariance.**  An exact Nash predecessor of a tail
above the punishment floor remains above that floor. -/
theorem quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (htail : quittingPunishmentValue reward who ≤ tail who)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingPunishmentValue reward who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  let c := quittingStationaryFixedOpponentsContinueMass root who
  have hc0 : 0 ≤ c := quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hc1 : c ≤ 1 := quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward tail root who hnash
  have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
    reward tail root who hnash
  by_cases hdeg : c = 1
  · have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
      reward who root
    rw [quittingStationaryUnilateralCap_of_fixedOpponentsContinueMass_eq_one
      (root := root) (who := who) hdeg] at hcap
    rcases (le_max_iff.mp hcap) with hsolo | hzero
    · have hagree :=
        eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
          (root := root) (who := who) hdeg
      have hupdate : Function.update root who (PMF.pure true) =
          quittingPureSetRoot ({who} : Finset ι) := by
        funext player
        by_cases hp : player = who
        · subst player
          simp [quittingPureSetRoot]
        · simpa [Function.update_of_ne hp, quittingPureSetRoot] using
            hagree player hp
      have hquitEq :
          quittingRootQuitPayoff reward tail root who =
            quittingSetReward reward ({who} : Finset ι) who := by
        unfold quittingRootQuitPayoff
        rw [hupdate]
        simp [quittingRootExpectedPayoff, quittingPureSetRoot]
      rw [hquitEq] at hquit
      exact hsolo.trans hquit
    · have hagree :=
        eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
          (root := root) (who := who) hdeg
      have hupdate : Function.update root who (PMF.pure false) =
          (quittingAllContinueRoot : ι → PMF Bool) := by
        funext player
        by_cases hp : player = who
        · subst player
          simp [quittingAllContinueRoot]
        · simpa [Function.update_of_ne hp, quittingPureSetRoot,
            quittingAllContinueRoot] using hagree player hp
      have hcontinueEq :
          quittingRootContinuePayoff reward tail root who = tail who := by
        unfold quittingRootContinuePayoff
        rw [hupdate, quittingRootSuccessorPayoff_allContinueRoot_eq]
      rw [hcontinueEq] at hcontinue
      exact htail.trans hcontinue
  · have hc : c < 1 := lt_of_le_of_ne hc1 hdeg
    have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
      reward who root
    rw [quittingStationaryUnilateralCap_eq_max_div] at hcap
    rcases (le_max_iff.mp hcap) with hq | hw
    · have hquitEq :
          quittingRootQuitPayoff reward tail root who =
            quittingStationaryFixedOpponentsQuitValue reward root who := by
        simpa [quittingStationaryFixedOpponentsQuitValue] using
          (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
            reward (fun _ => root) who tail 0)
      rw [hquitEq] at hquit
      exact hq.trans hquit
    · have hden : 0 < 1 - c := sub_pos.mpr hc
      have hmul :
          quittingPunishmentValue reward who * (1 - c) ≤
            quittingStationaryFixedOpponentsContinueReward reward root who :=
        (le_div_iff₀ hden).mp hw
      have hctail : c * quittingPunishmentValue reward who ≤ c * tail who :=
        mul_le_mul_of_nonneg_left htail hc0
      have hbellman :
          quittingPunishmentValue reward who ≤
            quittingStationaryFixedOpponentsContinueReward reward root who +
              c * tail who := by
        nlinarith
      have hcontinueEq :
          quittingRootContinuePayoff reward tail root who =
            quittingStationaryFixedOpponentsContinueReward reward root who +
              c * tail who := by
        simpa [c, quittingStationaryFixedOpponentsContinueReward,
          quittingStationaryFixedOpponentsContinueMass] using
          (quittingRootContinuePayoff_eq_fixedOpponents
            reward (fun _ => root) who tail 0)
      rw [hcontinueEq] at hcontinue
      exact hbellman.trans hcontinue

/-- The punishment vector, with a harmless simplex coordinate, as a point of
the canonical compact Nash--Bellman box. -/
def quittingPunishmentFloorAnchor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (canonicalQuittingNashBellmanSerialRelation reward).box := by
  refine ⟨(quittingPunishmentFloor reward,
      quittingAllContinueSimplexRoot), ?_⟩
  change quittingPunishmentFloor reward ∈ Set.Icc
    (fun _ : ι => -quittingRewardBound reward)
    (fun _ : ι => quittingRewardBound reward)
  constructor
  · intro who
    exact (abs_le.mp
      (abs_quittingPunishmentFloor_le_quittingRewardBound reward who)).1
  · intro who
    exact (abs_le.mp
      (abs_quittingPunishmentFloor_le_quittingRewardBound reward who)).2

/-- The exact predecessor orbit pulled forward from the punishment floor. -/
def quittingPunishmentFloorForwardPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) : QuittingNashBellmanPoint ι :=
  compactSerialIteratedPredecessor
    (canonicalQuittingNashBellmanSerialRelation reward) time
    (quittingPunishmentFloorAnchor reward)

/-- Every point on the orbit stays in the canonical compact box. -/
theorem quittingPunishmentFloorForwardPoint_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) :
    quittingPunishmentFloorForwardPoint reward time ∈
      quittingNashBellmanBox (quittingRewardBound reward) :=
  (compactSerialIteratedPredecessor
    (canonicalQuittingNashBellmanSerialRelation reward) time
    (quittingPunishmentFloorAnchor reward)).property

/-- Consecutive forward points form one exact Nash--Bellman edge. -/
theorem quittingPunishmentFloorForwardPoint_related
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) :
    IsQuittingNashBellmanEdge reward
      (quittingPunishmentFloorForwardPoint reward (time + 1))
      (quittingPunishmentFloorForwardPoint reward time) := by
  rw [quittingPunishmentFloorForwardPoint,
    compactSerialIteratedPredecessor_succ]
  exact (canonicalQuittingNashBellmanSerialRelation reward).predecessor_related _

/-- Payoff coordinate of the punishment-floor forward orbit. -/
def quittingPunishmentFloorForwardValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) : Payoff ι :=
  (quittingPunishmentFloorForwardPoint reward time).1

/-- Product root stored on the predecessor edge from time `t` to `t+1`. -/
def quittingPunishmentFloorForwardRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) : ι → PMF Bool :=
  quittingRootOfSimplex
    (quittingPunishmentFloorForwardPoint reward (time + 1)).2

/-- Exact forward Bellman transport. -/
theorem quittingPunishmentFloorForward_policy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) :
    quittingPunishmentFloorForwardValue reward (time + 1) =
      quittingRootSuccessorPayoff reward
        (quittingPunishmentFloorForwardValue reward time)
        (quittingPunishmentFloorForwardRoot reward time) :=
  (quittingPunishmentFloorForwardPoint_related reward time).1

/-- Exact root Nash on every selected forward edge. -/
theorem quittingPunishmentFloorForward_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) :
    IsεQuittingRootNash reward
      (quittingPunishmentFloorForwardValue reward time) 0
      (quittingPunishmentFloorForwardRoot reward time) :=
  (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (quittingPunishmentFloorForwardValue reward time)
      (quittingPunishmentFloorForwardRoot reward time)).1
    (quittingPunishmentFloorForwardPoint_related reward time).2

/-- Every value on the selected forward orbit remains above the punishment
floor. -/
theorem quittingPunishmentFloor_le_forwardValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingPunishmentFloorForwardValue reward time who := by
  induction time with
  | zero => rfl
  | succ time ih =>
      rw [quittingPunishmentFloorForward_policy reward time]
      exact quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
        reward (quittingPunishmentFloorForwardValue reward time)
        (quittingPunishmentFloorForwardRoot reward time) who ih
        (quittingPunishmentFloorForward_isZeroNash reward time)

/-- Exact one-stage Nash retains both actions' support-optimality at zero
error. -/
theorem isQuittingRootSupportApproxNash_zero_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    IsQuittingRootSupportApproxNash reward tail 0 root := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).2 hnash
  intro who
  constructor
  · intro hquit
    have hweighted := (hendpoint who).2
    have hquit0 : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
    nlinarith
  · intro hcontinue
    have hweighted := (hendpoint who).1
    have hcontinue0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
    nlinarith

/-- Canonical compact payoff carrier of the punishment-floor orbit. -/
def quittingPunishmentFloorForwardCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (Payoff ι) :=
  Set.Icc (fun _ : ι => -quittingRewardBound reward)
    (fun _ : ι => quittingRewardBound reward)

/-- The canonical payoff carrier is compact. -/
theorem quittingPunishmentFloorForwardCarrier_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingPunishmentFloorForwardCarrier reward) :=
  isCompact_Icc

/-- Every forward value belongs to the canonical payoff carrier. -/
theorem quittingPunishmentFloorForwardValue_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) :
    quittingPunishmentFloorForwardValue reward time ∈
      quittingPunishmentFloorForwardCarrier reward :=
  quittingPunishmentFloorForwardPoint_mem reward time

/-- Any charged finite prefix of the exact orbit is a finite-forward packet at
an arbitrary positive local tolerance. -/
def quittingPunishmentFloorForwardPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (supportError : ℝ) (hsupportError : 0 ≤ supportError)
    (horizon : ℕ) (chargeTarget : ℝ)
    (hcharge : chargeTarget ≤
      ∑ time ∈ Finset.range horizon,
        quittingRootAbsorptionMass
          (quittingPunishmentFloorForwardRoot reward time)) :
    QuittingFiniteForwardPacket reward
      (quittingPunishmentFloorForwardCarrier reward)
      supportError chargeTarget where
  roots := quittingPunishmentFloorForwardRoot reward
  value := quittingPunishmentFloorForwardValue reward
  horizon := horizon
  value_mem := fun time _ =>
    quittingPunishmentFloorForwardValue_mem reward time
  policy := fun time _ => quittingPunishmentFloorForward_policy reward time
  support := by
    intro time _ who
    have hexact := isQuittingRootSupportApproxNash_zero_of_isZeroNash
      reward (quittingPunishmentFloorForwardValue reward time)
      (quittingPunishmentFloorForwardRoot reward time)
      (quittingPunishmentFloorForward_isZeroNash reward time)
    constructor
    · intro hquit
      have h := (hexact who).1 hquit
      linarith
    · intro hcontinue
      have h := (hexact who).2 hcontinue
      linarith
  rational := by
    intro target time _
    have hfloor := quittingPunishmentFloor_le_forwardValue reward time target
    linarith
  chargeTarget_le := hcharge

/-- **High-charge producer theorem.**  If the punishment-floor exact Nash
orbit reaches every finite cumulative absorption target, then the existing
finite-return/single-seam compiler closes the quitting-game conjecture for
this reward table. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_punishmentFloorForwardCharge
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcharge : ∀ chargeTarget : ℝ, 0 ≤ chargeTarget →
      ∃ horizon : ℕ, chargeTarget ≤
        ∑ time ∈ Finset.range horizon,
          quittingRootAbsorptionMass
            (quittingPunishmentFloorForwardRoot reward time)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets
    reward (quittingPunishmentFloorForwardCarrier reward)
      (quittingPunishmentFloorForwardCarrier_isCompact reward)
  intro supportError hsupportError chargeTarget hchargeTarget
  obtain ⟨horizon, hhorizon⟩ := hcharge chargeTarget hchargeTarget
  exact ⟨quittingPunishmentFloorForwardPacket reward supportError
    hsupportError.le horizon chargeTarget hhorizon⟩

/-- **Exact producer alternative.**  Every finite quitting game either already
gets a uniform-equilibrium payoff from the punishment-floor orbit, or that
same game-generated orbit has a fixed finite upper bound on all cumulative
absorption prefixes. -/
theorem quittingGame_uniformPayoff_or_punishmentFloorForwardChargeBound
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ chargeBound : ℝ, 0 ≤ chargeBound ∧
        ∀ horizon : ℕ,
          (∑ time ∈ Finset.range horizon,
            quittingRootAbsorptionMass
              (quittingPunishmentFloorForwardRoot reward time)) < chargeBound := by
  classical
  by_cases hcharge : ∀ chargeTarget : ℝ, 0 ≤ chargeTarget →
      ∃ horizon : ℕ, chargeTarget ≤
        ∑ time ∈ Finset.range horizon,
          quittingRootAbsorptionMass
            (quittingPunishmentFloorForwardRoot reward time)
  · exact Or.inl
      (quittingGame_exists_uniformEquilibriumPayoff_of_punishmentFloorForwardCharge
        reward hcharge)
  · push_neg at hcharge
    exact Or.inr hcharge

end GameTheory
