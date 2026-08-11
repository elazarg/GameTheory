/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalIncomingPathAlternative

/-!
# Decoding the one-owner terminal-funding Farkas branch

The canonical strict terminal-funding root has one owner quitting with hazard
`p ∈ (0,1)` and every other player continuing.  At zero Bellman target its
continuation vector is not a free variable: the Bellman rows determine it
coordinatewise.  Substitution reduces affine infeasibility to four literal
finite failures:

* the active owner's mixing equation fails;
* an outsider has a strictly positive join derivative;
* the forced continuation violates the punishment floor; or
* it violates the payoff box.

The owner's mixing residual is especially rigid: it is its singleton payoff
divided by `1-p`.  Thus the funding root chosen at a player with positive
singleton debt cap can never take the physical branch.  Its Farkas
certificate is not an unknown strategic separator; it certifies the already
visible positive sure-exit row.  Only owners with zero singleton payoff leave
the strict-joiner and continuation-face alternatives genuinely open.

This module classifies the physical infeasibility certified by arbitrary dual
multipliers.  It does not select a second hazard, prove that a strict joiner
satisfies the two-owner reciprocal compatibility equations, or compile a
punishment tail.
-/

noncomputable section

namespace GameTheory

open Finset
open Math.ProbabilityMassFunction
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The unique continuation forced by the zero-target Bellman rows of the
strict one-owner root. -/
def quittingOneOwnerZeroTargetContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) : Payoff ι :=
  fun who ↦ -(p * reward (quittingSingletonTerminal owner) who) / (1 - p)

/-- The one-owner zero-target continuation satisfies every Bellman row. -/
theorem quittingRootSuccessorPayoff_oneOwnerZeroTargetContinuation
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    quittingRootSuccessorPayoff reward
        (quittingOneOwnerZeroTargetContinuation reward owner p)
        (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) = 0 := by
  funext who
  rw [quittingRootSuccessorPayoff_apply_eq_affine,
    stationaryContinueMass_sureSetOwnerRoot_empty,
    quittingRootAbsorbingContribution_sureSetOwnerRoot reward
      (by simp : owner ∉ (∅ : Finset ι)),
    quittingSureSetOwnerValue_empty]
  simp only [quittingOneOwnerZeroTargetContinuation, Pi.zero_apply]
  have hdenom : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty owner)]
  change p * reward (quittingSingletonTerminal owner) who +
    (1 - p) * (-(p * reward (quittingSingletonTerminal owner) who) /
      (1 - p)) = 0
  field_simp
  ring

/-- Any zero-target Bellman lift at the strict one-owner root has the forced
continuation displayed above. -/
theorem continuation_eq_oneOwnerZeroTargetContinuation_of_policy
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (continuation : Payoff ι)
    (hpolicy : (0 : Payoff ι) = quittingRootSuccessorPayoff reward continuation
      (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le)) :
    continuation = quittingOneOwnerZeroTargetContinuation reward owner p := by
  funext who
  have hcoordinate := congrFun hpolicy who
  rw [quittingRootSuccessorPayoff_apply_eq_affine,
    stationaryContinueMass_sureSetOwnerRoot_empty,
    quittingRootAbsorbingContribution_sureSetOwnerRoot reward
      (by simp : owner ∉ (∅ : Finset ι)),
    quittingSureSetOwnerValue_empty,
    quittingSetReward_of_nonempty reward (Finset.singleton_nonempty owner)]
      at hcoordinate
  change (0 : ℝ) = p * reward (quittingSingletonTerminal owner) who +
    (1 - p) * continuation who at hcoordinate
  simp only [quittingOneOwnerZeroTargetContinuation]
  have hdenom : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  apply (eq_div_iff hdenom).2
  linarith

/-- The active owner's Möbius mixing derivative at the forced continuation is
its singleton payoff divided by the positive Continue probability. -/
theorem oneOwnerZeroTarget_ownerDerivative
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (quittingStageCenteredCoalGame reward
        (quittingOneOwnerZeroTargetContinuation reward owner p) owner).coordinateDerivative
          (hazardOfRoot
            (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le)) owner =
      reward (quittingSingletonTerminal owner) owner / (1 - p) := by
  rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [update_sureSetOwnerRoot_owner_true,
    update_sureSetOwnerRoot_owner_false
      (by simp : owner ∉ (∅ : Finset ι))]
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    quittingRootAbsorbingContribution_pureSetRoot]
  simp only [Finset.insert_empty]
  rw [stationaryContinueMass_pureSetRoot_of_nonempty
    (Finset.singleton_nonempty owner)]
  have hemptyMass :
      quittingStationaryContinueMass
        (quittingPureSetRoot (∅ : Finset ι)) = 1 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    simp [quittingPureSetRoot, quittingSetAction]
  rw [hemptyMass]
  simp only [zero_mul, add_zero, one_mul,
    quittingOneOwnerZeroTargetContinuation]
  have hdenom : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty owner)]
  simp only [quittingSetReward_empty, zero_add]
  change reward (quittingSingletonTerminal owner) owner -
      (-(p * reward (quittingSingletonTerminal owner) owner) / (1 - p)) =
    reward (quittingSingletonTerminal owner) owner / (1 - p)
  field_simp
  ring

/-! ## Finite physical-infeasibility classification -/

/-- The one-owner derivative evaluated at the forced zero-target
continuation. -/
def quittingOneOwnerZeroTargetDerivative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (who : ι) : ℝ :=
  (quittingStageCenteredCoalGame reward
      (quittingOneOwnerZeroTargetContinuation reward owner p) who).coordinateDerivative
      (hazardOfRoot (quittingSureSetOwnerRoot ∅ owner p hp0 hp1)) who

/-- An outsider's derivative is the literal payoff from joining the owner
hazard: singleton exit when the owner continues, and pair exit when the owner
quits.  This is the finite signed pivot passed to a two-owner search. -/
theorem oneOwnerZeroTarget_outsiderDerivative
    (owner joiner : ι) (hne : joiner ≠ owner)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    quittingOneOwnerZeroTargetDerivative reward owner p hp0.le hp1.le
        joiner =
      quittingSureSetOwnerValue reward {joiner} owner p joiner := by
  unfold quittingOneOwnerZeroTargetDerivative
  rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [update_sureSetOwnerRoot_other_true hne,
    update_sureSetOwnerRoot_other_false hne, Finset.erase_empty]
  simp only [Finset.insert_empty]
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_sureSetOwnerRoot reward
      (by simpa using hne.symm : owner ∉ ({joiner} : Finset ι)),
    stationaryContinueMass_sureSetOwnerRoot_of_nonempty
      (Finset.singleton_nonempty joiner) (by simpa using hne.symm)]
  simp only [zero_mul, add_zero]
  have htarget := congrFun
    (quittingRootSuccessorPayoff_oneOwnerZeroTargetContinuation
      (reward := reward) owner p hp0 hp1) joiner
  exact sub_eq_self.mpr (by
    simpa [quittingRootSuccessorPayoff] using htarget)

/-- The forced continuation is a physical frozen-root lift exactly when the
owner mixes, every outsider has nonpositive join derivative, and all
continuation coordinates lie in the requested floor/box interval. -/
theorem oneOwnerZeroTargetContinuation_isLift_iff
    (floor : Payoff ι) (upper : ℝ)
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsQuittingFrozenRootContinuationLift reward 0 floor upper
        (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner}
        (quittingOneOwnerZeroTargetContinuation reward owner p) ↔
      quittingOneOwnerZeroTargetDerivative reward owner p hp0.le hp1.le
          owner = 0 ∧
        (∀ who, who ≠ owner →
          quittingOneOwnerZeroTargetDerivative reward owner p hp0.le hp1.le
            who ≤ 0) ∧
        (∀ who, floor who ≤
          quittingOneOwnerZeroTargetContinuation reward owner p who) ∧
        ∀ who,
          quittingOneOwnerZeroTargetContinuation reward owner p who ≤ upper := by
  constructor
  · intro hlift
    refine ⟨?_, ?_, hlift.2.2.2.1, hlift.2.2.2.2⟩
    · exact hlift.2.1 owner (by simp)
    · intro who hne
      exact hlift.2.2.1 who (by simp [hne])
  · rintro ⟨howner, houtside, hfloor, hupper⟩
    refine ⟨?_, ?_, ?_, hfloor, hupper⟩
    · exact (quittingRootSuccessorPayoff_oneOwnerZeroTargetContinuation
        (reward := reward) owner p hp0 hp1).symm
    · intro who hwho
      have : who = owner := by simpa using hwho
      subst who
      exact howner
    · intro who hwho
      exact houtside who (by simpa using hwho)

/-- Existential physical feasibility reduces to the forced continuation. -/
theorem exists_oneOwnerZeroTargetLift_iff
    (floor : Payoff ι) (upper : ℝ)
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∃ continuation,
      IsQuittingFrozenRootContinuationLift reward 0 floor upper
        (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner}
          continuation) ↔
      IsQuittingFrozenRootContinuationLift reward 0 floor upper
        (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner}
          (quittingOneOwnerZeroTargetContinuation reward owner p) := by
  constructor
  · rintro ⟨continuation, hlift⟩
    have heq := continuation_eq_oneOwnerZeroTargetContinuation_of_policy
      (reward := reward) owner p hp0 hp1 continuation hlift.1
    simpa [heq] using hlift
  · intro hlift
    exact ⟨quittingOneOwnerZeroTargetContinuation reward owner p, hlift⟩

/-- Finite game-facing reasons why the canonical strict one-owner funding
root has no physical zero-target continuation lift. -/
inductive QuittingOneOwnerFundingObstruction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (floor : Payoff ι) (upper : ℝ)
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : Type
  /-- The selected owner's sure singleton exit is strictly positive. -/
  | ownerPositive
      (hpositive : 0 < reward (quittingSingletonTerminal owner) owner)
  /-- The selected owner's singleton row is a negative phase. -/
  | ownerNegative
      (hnegative : reward (quittingSingletonTerminal owner) owner < 0)
  /-- An outsider has a strictly profitable derivative for joining the
  one-owner root. -/
  | strictJoiner (joiner : ι) (hne : joiner ≠ owner)
      (hjoin : 0 < quittingOneOwnerZeroTargetDerivative reward owner p
        hp0.le hp1.le joiner)
  /-- The forced Bellman continuation lies strictly below punishment. -/
  | punishmentFace (who : ι)
      (hfloor : quittingOneOwnerZeroTargetContinuation reward owner p who <
        floor who)
  /-- The forced Bellman continuation lies strictly above the payoff box. -/
  | upperBoxFace (who : ι)
      (hupper : upper <
        quittingOneOwnerZeroTargetContinuation reward owner p who)

/-- **Decoded one-owner Farkas classification.**  Physical infeasibility of
the canonical strict one-owner zero-target root is equivalent to one of the
five finite game-facing obstructions above. -/
theorem not_exists_oneOwnerZeroTargetLift_iff_obstruction
    (floor : Payoff ι) (upper : ℝ)
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (¬ ∃ continuation,
      IsQuittingFrozenRootContinuationLift reward 0 floor upper
        (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner}
          continuation) ↔
      Nonempty (QuittingOneOwnerFundingObstruction reward floor upper
        owner p hp0 hp1) := by
  rw [exists_oneOwnerZeroTargetLift_iff
    (reward := reward) floor upper owner p hp0 hp1,
    oneOwnerZeroTargetContinuation_isLift_iff
      (reward := reward) floor upper owner p hp0 hp1]
  let derivative := quittingOneOwnerZeroTargetDerivative reward owner p
    hp0.le hp1.le
  let continuation := quittingOneOwnerZeroTargetContinuation reward owner p
  constructor
  · intro hnot
    by_cases hpositive : 0 < reward (quittingSingletonTerminal owner) owner
    · exact ⟨.ownerPositive hpositive⟩
    by_cases hnegative : reward (quittingSingletonTerminal owner) owner < 0
    · exact ⟨.ownerNegative hnegative⟩
    have hrewardZero : reward (quittingSingletonTerminal owner) owner = 0 :=
      le_antisymm (le_of_not_gt hpositive) (le_of_not_gt hnegative)
    have howner : derivative owner = 0 := by
      dsimp [derivative, quittingOneOwnerZeroTargetDerivative]
      rw [oneOwnerZeroTarget_ownerDerivative
        (reward := reward) owner p hp0 hp1, hrewardZero, zero_div]
    by_cases houtside : ∀ who, who ≠ owner → derivative who ≤ 0
    · by_cases hfloor : ∀ who, floor who ≤ continuation who
      · by_cases hupper : ∀ who, continuation who ≤ upper
        · exact (hnot ⟨howner, houtside, hfloor, hupper⟩).elim
        · push Not at hupper
          obtain ⟨who, hwho⟩ := hupper
          exact ⟨.upperBoxFace who hwho⟩
      · push Not at hfloor
        obtain ⟨who, hwho⟩ := hfloor
        exact ⟨.punishmentFace who hwho⟩
    · push Not at houtside
      obtain ⟨who, hne, hwho⟩ := houtside
      exact ⟨.strictJoiner who hne hwho⟩
  · rintro ⟨hobstruction⟩ hlift
    rcases hobstruction with hpositive | hnegative |
        ⟨joiner, hne, hjoin⟩ | ⟨who, hfloor⟩ | ⟨who, hupper⟩
    · have howner := hlift.1
      dsimp [derivative, quittingOneOwnerZeroTargetDerivative] at howner
      rw [oneOwnerZeroTarget_ownerDerivative
        (reward := reward) owner p hp0 hp1] at howner
      have hdenom : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
      simp only [div_eq_zero_iff, hdenom, or_false] at howner
      linarith
    · have howner := hlift.1
      dsimp [derivative, quittingOneOwnerZeroTargetDerivative] at howner
      rw [oneOwnerZeroTarget_ownerDerivative
        (reward := reward) owner p hp0 hp1] at howner
      have hdenom : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
      simp only [div_eq_zero_iff, hdenom, or_false] at howner
      linarith
    · exact (not_lt_of_ge (hlift.2.1 joiner hne)) hjoin
    · exact (not_lt_of_ge (hlift.2.2.1 who)) hfloor
    · exact (not_lt_of_ge (hlift.2.2.2 who)) hupper

omit [Fintype ι] [DecidableEq ι] in
/-- A positive singleton debt cap is exactly a positive owner singleton
reward, not merely a nonzero absolute-value row. -/
theorem singletonReward_pos_of_positiveSingletonDebtCap
    (owner : ι)
    (hcap : 0 < quittingPositiveSingletonDebtCap reward owner) :
    0 < reward (quittingSingletonTerminal owner) owner := by
  unfold quittingPositiveSingletonDebtCap at hcap
  by_contra hnot
  have hrewards : reward (quittingSingletonTerminal owner) owner ≤ 0 :=
    le_of_not_gt hnot
  rw [max_eq_left hrewards] at hcap
  exact lt_irrefl 0 hcap

/-- Any Farkas certificate for the canonical one-owner root decodes to the
finite obstruction classification; the multipliers themselves carry no
additional strategic branch. -/
theorem oneOwnerFundingObstruction_of_farkas
    (floor : Payoff ι) (upper : ℝ)
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hfarkas : HasQuittingFrozenRootLiftFarkasCertificate
      (reward := reward) 0 floor upper
        (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner}) :
    Nonempty (QuittingOneOwnerFundingObstruction reward floor upper
      owner p hp0 hp1) :=
  (not_exists_oneOwnerZeroTargetLift_iff_obstruction
    (reward := reward) floor upper owner p hp0 hp1).1 hfarkas.1

/-- At any owner with positive singleton debt cap, the canonical strict
one-owner zero-target system is necessarily in the Farkas branch.  Its
decoded obstruction is the positive owner sure-exit row. -/
theorem positiveSingletonDebtCap_oneOwnerFarkas
    (floor : Payoff ι) (upper : ℝ)
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hcap : 0 < quittingPositiveSingletonDebtCap reward owner) :
    HasQuittingFrozenRootLiftFarkasCertificate
        (reward := reward) 0 floor upper
          (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner} ∧
      Nonempty (QuittingOneOwnerFundingObstruction reward floor upper
        owner p hp0 hp1) := by
  have hpositive :=
    singletonReward_pos_of_positiveSingletonDebtCap
      (reward := reward) owner hcap
  have hobstruction : Nonempty
      (QuittingOneOwnerFundingObstruction reward floor upper
        owner p hp0 hp1) :=
    ⟨.ownerPositive hpositive⟩
  have hnoLift : ¬ ∃ continuation,
      IsQuittingFrozenRootContinuationLift reward 0 floor upper
        (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner}
          continuation :=
    (not_exists_oneOwnerZeroTargetLift_iff_obstruction
      (reward := reward) floor upper owner p hp0 hp1).2 hobstruction
  rcases quittingFrozenRootContinuationLift_or_farkas
      (reward := reward) 0 floor upper
        (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner} with
    hlift | hfarkas
  · exact (hnoLift hlift).elim
  · exact ⟨⟨hfarkas.1, hfarkas.2⟩, hobstruction⟩

namespace QuittingAggregateCalibratedTerminalAnchor

/-- **Canonical terminal-funding Farkas collapse.**  For a calibrated
positive-debt anchor, choose exactly the strict one-owner hazard used by the
terminal-funding construction at the marked owner.  That hazard funds the
aggregate terminal cap, but the owner's positive singleton debt cap forces
the affine continuation problem into the Farkas branch.

Thus this canonical choice cannot supply the physical incoming edge.  Its
dual certificate decodes to `ownerPositive`; a different funding owner with
zero singleton payoff, or a genuinely enlarged support, is required to reach
the other branches of the finite classification. -/
theorem exists_canonicalOwnerFundingFarkas
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    ∃ p : ℝ, ∃ hp0 : 0 < p, ∃ hp1 : p < 1,
      (Fintype.card ι : ℝ) * quittingRewardBound reward * p =
          ∑ who, quittingPositiveSingletonDebtCap reward who ∧
        HasQuittingFrozenRootLiftFarkasCertificate
          (reward := reward) 0 (quittingPunishmentValue reward)
            (quittingRewardBound reward)
            (quittingSureSetOwnerRoot ∅ anchor.owner p hp0.le hp1.le)
            {anchor.owner} ∧
        Nonempty (QuittingOneOwnerFundingObstruction reward
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          anchor.owner p hp0 hp1) := by
  let terminalDebt :=
    ∑ who, quittingPositiveSingletonDebtCap reward who
  let scale := (Fintype.card ι : ℝ) * quittingRewardBound reward
  have hdebtPos : 0 < terminalDebt := by
    exact anchor.terminalAggregateDebt_pos
  have hdebtLt : terminalDebt < scale := by
    exact anchor.terminalAggregateDebt_lt_card_mul_rewardBound regime
  have hscale : 0 < scale := hdebtPos.trans hdebtLt
  let p := terminalDebt / scale
  have hp0 : 0 < p := div_pos hdebtPos hscale
  have hp1 : p < 1 := (div_lt_one hscale).2 hdebtLt
  have hfunds : scale * p = terminalDebt := by
    dsimp [p]
    field_simp
  have hownerCap :
      quittingFiniteNashBellmanPathDynamicDebt
          reward (anchor.last + 1) anchor.path anchor.owner 0 ≤
        quittingPositiveSingletonDebtCap reward anchor.owner :=
    quittingFiniteNashBellmanPathDynamicDebt_le_cap
      reward (anchor.last + 1) anchor.path anchor.path_mem anchor.owner 0
        (by omega)
  have hcap : 0 < quittingPositiveSingletonDebtCap reward anchor.owner :=
    anchor.ownerDebt_pos.trans_le hownerCap
  have hfarkas := positiveSingletonDebtCap_oneOwnerFarkas
    (reward := reward) (quittingPunishmentValue reward)
      (quittingRewardBound reward) anchor.owner p hp0 hp1 hcap
  exact ⟨p, hp0, hp1, by simpa [scale, terminalDebt] using hfunds,
    hfarkas⟩

end QuittingAggregateCalibratedTerminalAnchor

end GameTheory
