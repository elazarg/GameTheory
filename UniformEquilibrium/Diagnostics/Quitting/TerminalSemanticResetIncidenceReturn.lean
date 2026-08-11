/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetExcursionReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence

/-!
# Incidence-preserving compactification of reset excursions

The ordinary terminal-semantic carrier remembers only prescribed payoffs and
best-response envelopes.  A reset sequence, however, also carries a literal
finite terminal-outcome law.  Projecting away that law before minimizing on
the reset face loses the same-law incidence used by the transfer argument.

This file keeps exactly one additional finite-dimensional coordinate: the
complete terminal-outcome law of the realizing profile.  The closure of these
joint points is compact.  Every point in it still satisfies the exact reward-
moment identity, and a joint reset cluster can be minimized on the slice with
its law fixed.  The resulting reset point has no larger total debt, retains
the whole law (hence every incidence coordinate) literally, and keeps the
exact opposite-face transfer account.

This does not make the fixed-law minimizer invariant under cap prefixing.
Prefixing changes the law by inserting first-stage absorption and transporting
the old law only on the all-Continue event.  Therefore the result below is an
incidence-preserving constrained return, not an assertion that its minimizer
has an all-Continue cap--Nash correspondence.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A terminal semantic pair together with one complete terminal-outcome law. -/
abbrev QuittingTerminalSemanticLawPoint (ι : Type) [Fintype ι] :=
  QuittingTerminalSemanticPair ι × (QuittingTerminalOutcome ι → ℝ)

/-- Joint semantic/law points literally realized by executable profiles. -/
def quittingAttainableTerminalSemanticLawPoints
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingTerminalSemanticLawPoint ι) :=
  Set.range fun profile : (quittingGame reward).BehaviorProfile =>
    (quittingTerminalSemanticPair reward profile,
      quittingTerminalOutcomeMass reward profile)

/-- The smallest closed carrier retaining both terminal semantics and the
complete limiting outcome law of one realizing sequence. -/
def quittingTerminalSemanticLawCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingTerminalSemanticLawPoint ι) :=
  closure (quittingAttainableTerminalSemanticLawPoints reward)

/-- The joint semantic/law carrier is compact under the usual reward bound. -/
theorem quittingTerminalSemanticLawCarrier_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    IsCompact (quittingTerminalSemanticLawCarrier reward) := by
  let ambient : Set (QuittingTerminalSemanticLawPoint ι) :=
    quittingTerminalSemanticBox ι M ×ˢ
      stdSimplex ℝ (QuittingTerminalOutcome ι)
  have hambient : IsCompact ambient :=
    (quittingTerminalSemanticBox_isCompact (ι := ι) M).prod
      (isCompact_stdSimplex ℝ (QuittingTerminalOutcome ι))
  apply hambient.of_isClosed_subset isClosed_closure
  · apply closure_minimal
    · rintro point ⟨profile, rfl⟩
      exact ⟨quittingTerminalSemanticPair_mem_box reward profile hM hreward,
        quittingTerminalOutcomeMass_mem_stdSimplex reward profile⟩
    · exact hambient.isClosed

/-- Every literal profile supplies a point of the joint carrier. -/
theorem quittingTerminalSemanticLawPoint_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    (quittingTerminalSemanticPair reward profile,
        quittingTerminalOutcomeMass reward profile) ∈
      quittingTerminalSemanticLawCarrier reward := by
  apply subset_closure
  exact ⟨profile, rfl⟩

/-- A joint carrier point retains the exact reward moment of its displayed
law.  This is the key coupling that is lost in the semantic projection. -/
theorem terminalSemanticLawCarrier_rewardMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward) :
    quittingTerminalRewardMoment reward point.2 = point.1.1 := by
  let constraint : Set (QuittingTerminalSemanticLawPoint ι) :=
    {candidate | quittingTerminalRewardMoment reward candidate.2 =
      candidate.1.1}
  have hclosed : IsClosed constraint := by
    apply isClosed_eq
    · exact (continuous_quittingTerminalRewardMoment reward).comp continuous_snd
    · exact continuous_fst.fst
  have hsubset : quittingAttainableTerminalSemanticLawPoints reward ⊆
      constraint := by
    rintro candidate ⟨profile, rfl⟩
    exact quittingTerminalRewardMoment_outcomeMass reward profile
  exact (closure_minimal hsubset hclosed) hpoint

/-- A jointly convergent sequence of executable profiles lands in the joint
carrier. -/
theorem mem_terminalSemanticLawCarrier_of_joint_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (point : QuittingTerminalSemanticLawPoint ι)
    (htendsto : Tendsto (fun n =>
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)))
      atTop (𝓝 point)) :
    point ∈ quittingTerminalSemanticLawCarrier reward := by
  rw [quittingTerminalSemanticLawCarrier, mem_closure_iff_seq_limit]
  exact ⟨fun n =>
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)),
    fun n => ⟨profiles n, rfl⟩, htendsto⟩

/-- **Fixed-law reset-face minimizer.**

Starting from any joint reset point, minimize total debt without projecting
away its terminal law.  The returned point retains the complete law exactly,
has no larger total debt, and keeps the full opposite-face transfer account
relative to a global minimum source.

In particular every positive terminal-incidence coordinate present in the
reset law remains positive at the returned point with no quantitative loss. -/
theorem exists_fixedLaw_resetFace_minimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target who = 0) :
    ∃ returned : QuittingTerminalSemanticPair ι,
      (returned, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
      returned ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt returned who = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned ∧
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum target ∧
      quittingTerminalRewardMoment reward mass = returned.1 ∧
      (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source returned other) =
        (quittingTerminalSemanticDebtSum returned -
            quittingTerminalSemanticDebtSum source) +
          quittingTerminalSemanticDebt source who ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source returned other := by
  let fixedLawResetFace : Set (QuittingTerminalSemanticLawPoint ι) :=
    quittingTerminalSemanticLawCarrier reward ∩
      {point | quittingTerminalSemanticDebt point.1 who = 0} ∩
      {point | point.2 = mass}
  have hresetClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        quittingTerminalSemanticDebt point.1 who = 0} :=
    isClosed_eq
      ((continuous_quittingTerminalSemanticDebt who).comp continuous_fst)
      continuous_const
  have hlawClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι | point.2 = mass} :=
    isClosed_eq continuous_snd continuous_const
  have hcompact : IsCompact fixedLawResetFace :=
    ((quittingTerminalSemanticLawCarrier_isCompact reward hM hreward).inter_right
      hresetClosed).inter_right hlawClosed
  have hnonempty : fixedLawResetFace.Nonempty :=
    ⟨(target, mass), ⟨htarget, hreset⟩, rfl⟩
  obtain ⟨returnedPoint, hreturnedFace, hreturnedMin⟩ :=
    hcompact.exists_isMinOn hnonempty
      (continuous_quittingTerminalSemanticDebtSum.comp
        continuous_fst).continuousOn
  let returned : QuittingTerminalSemanticPair ι := returnedPoint.1
  have hjoint : (returned, mass) ∈
      quittingTerminalSemanticLawCarrier reward := by
    have hlaw : returnedPoint.2 = mass := hreturnedFace.2
    have hpointEq : returnedPoint = (returned, mass) := by
      apply Prod.ext
      · rfl
      · exact hlaw
    rw [← hpointEq]
    exact hreturnedFace.1.1
  have hreturnedCarrier : returned ∈
      quittingTerminalSemanticCarrier reward := by
    rw [quittingTerminalSemanticCarrier]
    apply map_mem_closure continuous_fst hreturnedFace.1.1
    rintro point ⟨profile, rfl⟩
    exact ⟨profile, rfl⟩
  have hreturnedReset : quittingTerminalSemanticDebt returned who = 0 :=
    hreturnedFace.1.2
  have hsourceLe : quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum returned :=
    hminimum returned hreturnedCarrier
  have hreturnedLe : quittingTerminalSemanticDebtSum returned ≤
      quittingTerminalSemanticDebtSum target := by
    exact hreturnedMin ⟨⟨htarget, hreset⟩, rfl⟩
  have hmoment : quittingTerminalRewardMoment reward mass = returned.1 :=
    terminalSemanticLawCarrier_rewardMoment reward (returned, mass) hjoint
  have htransfer :=
    sum_opponent_debtChange_eq_totalChange_add_sourceDebt_of_target_zero
      source returned who hreturnedReset
  have htransferLower : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source returned other := by
    rw [htransfer]
    linarith
  exact ⟨returned, hjoint, hreturnedCarrier, hreturnedReset, hsourceLe,
    hreturnedLe, hmoment, htransfer, htransferLower⟩

/-- The fixed-law minimizer preserves any displayed opponent-incidence floor
literally, since its law coordinate is unchanged. -/
theorem exists_fixedLaw_resetFace_minimizer_with_incidence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (who other : ι) (incidenceFloor : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target who = 0)
    (hincidence : incidenceFloor ≤
      quittingTerminalOpponentIncidenceMass who other mass) :
    ∃ returned : QuittingTerminalSemanticPair ι,
      (returned, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned who = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned ∧
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum target ∧
      incidenceFloor ≤
        quittingTerminalOpponentIncidenceMass who other mass ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ player ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source returned player := by
  obtain ⟨returned, hjoint, _hcarrier, hreturnedReset, hsourceLe,
      hreturnedLe, _hmoment, _hidentity, htransfer⟩ :=
    exists_fixedLaw_resetFace_minimizer reward source target mass who
      hM hreward hminimum htarget hreset
  exact ⟨returned, hjoint, hreturnedReset, hsourceLe, hreturnedLe,
    hincidence, htransfer⟩

/-! ## Exact law action of a literal prefix -/

omit [DecidableEq ι] in
/-- At time zero, the root/continuation splice has the root's joint
all-Continue probability. -/
theorem quittingJointContinueMass_rootThenContinuation_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) :
    quittingJointContinueMass reward
        (quittingRootThenContinuationProfile reward root continuation) 0 =
      quittingStationaryContinueMass root := by
  unfold quittingJointContinueMass StochasticGame.stageActionDist
    quittingStationaryContinueMass
  rfl

omit [DecidableEq ι] in
/-- After the root stage, the splice's conditional all-Continue row is the
corresponding row of the declared continuation. -/
theorem quittingJointContinueMass_rootThenContinuation_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingJointContinueMass reward
        (quittingRootThenContinuationProfile reward root continuation)
        (time + 1) =
      quittingJointContinueMass reward continuation time := by
  unfold quittingJointContinueMass StochasticGame.stageActionDist
    quittingRootThenContinuationProfile quittingLiveHist
  rfl

omit [DecidableEq ι] in
/-- Live mass after a literal root prefix is exactly root survival times the
continuation live mass. -/
theorem quittingLiveMass_rootThenContinuation_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward
        (quittingRootThenContinuationProfile reward root continuation)
        (time + 1) =
      quittingStationaryContinueMass root *
        quittingLiveMass reward continuation time := by
  induction time with
  | zero =>
      rw [quittingLiveMass_succ,
        quittingJointContinueMass_rootThenContinuation_zero,
        quittingLiveMass_zero, quittingLiveMass_zero, mul_one, one_mul]
  | succ time ih =>
      rw [show time + 1 + 1 = (time + 1) + 1 by omega,
        quittingLiveMass_succ, ih,
        quittingJointContinueMass_rootThenContinuation_succ,
        quittingLiveMass_succ]
      ring

omit [DecidableEq ι] in
/-- Never mass is transported by exactly the root all-Continue mass. -/
theorem quittingLiveMassLimit_rootThenContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) :
    quittingLiveMassLimit reward
        (quittingRootThenContinuationProfile reward root continuation) =
      quittingStationaryContinueMass root *
        quittingLiveMassLimit reward continuation := by
  let spliced := quittingRootThenContinuationProfile reward root continuation
  have hspliced : Tendsto (fun time =>
      quittingLiveMass reward spliced (time + 1)) atTop
      (𝓝 (quittingLiveMassLimit reward spliced)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_quittingLiveMass reward spliced)
  have htail : Tendsto (fun time =>
      quittingStationaryContinueMass root *
        quittingLiveMass reward continuation time) atTop
      (𝓝 (quittingStationaryContinueMass root *
        quittingLiveMassLimit reward continuation)) :=
    tendsto_const_nhds.mul (tendsto_quittingLiveMass reward continuation)
  apply tendsto_nhds_unique hspliced
  apply htail.congr'
  filter_upwards [] with time
  exact (quittingLiveMass_rootThenContinuation_succ
    reward root continuation time).symm

omit [DecidableEq ι] in
/-- The live root at the first stage of a splice is its displayed root. -/
@[simp] theorem quittingProfileLiveRoot_rootThenContinuation_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) :
    quittingProfileLiveRoot reward
        (quittingRootThenContinuationProfile reward root continuation) 0 =
      root := by
  rfl

omit [DecidableEq ι] in
/-- After the first stage, the live roots of a splice are those of its
declared continuation. -/
@[simp] theorem quittingProfileLiveRoot_rootThenContinuation_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingRootThenContinuationProfile reward root continuation)
        (time + 1) =
      quittingProfileLiveRoot reward continuation time := by
  rfl

/-- First-stage coalition mass of a splice is exactly the root coalition
mass. -/
theorem quittingStageCoalitionMass_rootThenContinuation_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingRootThenContinuationProfile reward root continuation)
        0 terminal =
      quittingRootCoalitionMass root terminal.val := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingProfileLiveRoot_rootThenContinuation_zero,
    quittingLiveMass_zero, one_mul]

/-- Every later coalition atom is the corresponding continuation atom scaled
by root survival. -/
theorem quittingStageCoalitionMass_rootThenContinuation_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingRootThenContinuationProfile reward root continuation)
        (time + 1) terminal =
      quittingStationaryContinueMass root *
        quittingStageCoalitionMass reward continuation time terminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingProfileLiveRoot_rootThenContinuation_succ,
    quittingLiveMass_rootThenContinuation_succ,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  ring

/-- Exact affine transport of one finite terminal-coalition mass under a
literal prefix. -/
theorem quittingAbsorbedMassLimit_rootThenContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMassLimit reward
        (quittingRootThenContinuationProfile reward root continuation)
        terminal =
      quittingRootCoalitionMass root terminal.val +
        quittingStationaryContinueMass root *
          quittingAbsorbedMassLimit reward continuation terminal := by
  let spliced := quittingRootThenContinuationProfile reward root continuation
  have hsummable : Summable (fun time =>
      quittingStageCoalitionMass reward spliced time terminal) :=
    (hasSum_quittingStageCoalitionMass reward spliced terminal).summable
  rw [← tsum_quittingStageCoalitionMass reward spliced terminal,
    hsummable.tsum_eq_zero_add,
    quittingStageCoalitionMass_rootThenContinuation_zero]
  have htail : (∑' time,
      quittingStageCoalitionMass reward spliced (time + 1) terminal) =
      quittingStationaryContinueMass root *
        quittingAbsorbedMassLimit reward continuation terminal := by
    dsimp only [spliced]
    simp_rw [quittingStageCoalitionMass_rootThenContinuation_succ]
    rw [tsum_mul_left,
      tsum_quittingStageCoalitionMass reward continuation terminal]
  exact congrArg
    (fun value => quittingRootCoalitionMass root terminal.val + value) htail

/-- The complete terminal law of a literal prefix: fresh root absorption is
inserted, while the old law (including Never) is transported only on the
all-Continue event. -/
theorem quittingTerminalOutcomeMass_rootThenContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation)
        outcome =
      match outcome with
      | none => quittingStationaryContinueMass root *
          quittingTerminalOutcomeMass reward continuation none
      | some terminal => quittingRootCoalitionMass root terminal.val +
          quittingStationaryContinueMass root *
            quittingTerminalOutcomeMass reward continuation (some terminal) := by
  cases outcome with
  | none =>
      exact quittingLiveMassLimit_rootThenContinuation
        reward root continuation
  | some terminal =>
      exact quittingAbsorbedMassLimit_rootThenContinuation
        reward root continuation terminal

/-- The affine action of one root prefix on a complete terminal-outcome law. -/
def quittingTerminalOutcomeLawPrefix
    (root : ι → PMF Bool)
    (mass : QuittingTerminalOutcome ι → ℝ) :
    QuittingTerminalOutcome ι → ℝ
  | none => quittingStationaryContinueMass root * mass none
  | some terminal => quittingRootCoalitionMass root terminal.val +
      quittingStationaryContinueMass root * mass (some terminal)

/-- Prefixing a law is continuous in its law coordinate. -/
theorem continuous_quittingTerminalOutcomeLawPrefix
    (root : ι → PMF Bool) :
    Continuous (quittingTerminalOutcomeLawPrefix root) := by
  apply continuous_pi
  intro outcome
  cases outcome with
  | none => exact continuous_const.mul (continuous_apply none)
  | some terminal =>
      exact continuous_const.add
        (continuous_const.mul (continuous_apply (some terminal)))

/-- The affine law prefix is exactly the law of the literal spliced profile. -/
theorem quittingTerminalOutcomeLawPrefix_outcomeMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) :
    quittingTerminalOutcomeLawPrefix root
        (quittingTerminalOutcomeMass reward continuation) =
      quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation) := by
  funext outcome
  exact (quittingTerminalOutcomeMass_rootThenContinuation
    reward root continuation outcome).symm

/-- The joint semantic/law carrier is invariant under the exact affine
prefix action.  Thus the transported law remains coupled to the returned
semantic pair, rather than being an external annotation. -/
theorem quittingTerminalSemanticLawPrefix_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (point : QuittingTerminalSemanticLawPoint ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward) :
    (quittingTerminalSemanticPrefix reward root point.1,
        quittingTerminalOutcomeLawPrefix root point.2) ∈
      quittingTerminalSemanticLawCarrier reward := by
  let prefixMap : QuittingTerminalSemanticLawPoint ι →
      QuittingTerminalSemanticLawPoint ι := fun candidate =>
    (quittingTerminalSemanticPrefix reward root candidate.1,
      quittingTerminalOutcomeLawPrefix root candidate.2)
  have hcontinuous : Continuous prefixMap :=
    ((continuous_quittingTerminalSemanticPrefix reward root).comp
      continuous_fst).prodMk
        ((continuous_quittingTerminalOutcomeLawPrefix root).comp
          continuous_snd)
  change prefixMap point ∈ quittingTerminalSemanticLawCarrier reward
  unfold quittingTerminalSemanticLawCarrier at hpoint ⊢
  apply map_mem_closure hcontinuous hpoint
  rintro candidate ⟨profile, rfl⟩
  refine ⟨quittingRootThenContinuationProfile reward root profile, ?_⟩
  apply Prod.ext
  · exact quittingTerminalSemanticPair_rootThenContinuation
      reward root profile hM hreward
  · exact (quittingTerminalOutcomeLawPrefix_outcomeMass
      reward root profile).symm

/-- First-stage root incidence for a displayed opponent label. -/
def quittingRootOpponentIncidenceMass
    (who other : ι) (root : ι → PMF Bool) : ℝ :=
  ∑ terminal ∈ Finset.univ.filter
      (fun terminal : {S : Finset ι // S.Nonempty} =>
        other ∈ terminal.val ∧ other ≠ who),
    quittingRootCoalitionMass root terminal.val

/-- **Exact incidence action of a prefix.**  New first-stage incidence is
added to the old same-law incidence transported by root survival. -/
theorem quittingTerminalOpponentIncidenceMass_lawPrefix
    (who other : ι) (root : ι → PMF Bool)
    (mass : QuittingTerminalOutcome ι → ℝ) :
    quittingTerminalOpponentIncidenceMass who other
        (quittingTerminalOutcomeLawPrefix root mass) =
      quittingRootOpponentIncidenceMass who other root +
        quittingStationaryContinueMass root *
          quittingTerminalOpponentIncidenceMass who other mass := by
  unfold quittingTerminalOpponentIncidenceMass
    quittingRootOpponentIncidenceMass
  simp_rw [quittingTerminalOutcomeLawPrefix]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- A prefix never loses more than its survival factor of any old incidence
coordinate. -/
theorem quittingStationaryContinueMass_mul_incidence_le_lawPrefix
    (who other : ι) (root : ι → PMF Bool)
    (mass : QuittingTerminalOutcome ι → ℝ) :
    quittingStationaryContinueMass root *
        quittingTerminalOpponentIncidenceMass who other mass ≤
      quittingTerminalOpponentIncidenceMass who other
        (quittingTerminalOutcomeLawPrefix root mass) := by
  rw [quittingTerminalOpponentIncidenceMass_lawPrefix]
  exact le_add_of_nonneg_left <| Finset.sum_nonneg fun terminal _ =>
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      root terminal.val

/-- Positive old incidence survives every prefix with positive all-Continue
mass.  No such conclusion is available for a sure-absorbing prefix. -/
theorem positive_incidence_lawPrefix_of_positive_continueMass
    (who other : ι) (root : ι → PMF Bool)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hcontinue : 0 < quittingStationaryContinueMass root)
    (hincidence : 0 <
      quittingTerminalOpponentIncidenceMass who other mass) :
    0 < quittingTerminalOpponentIncidenceMass who other
      (quittingTerminalOutcomeLawPrefix root mass) := by
  exact (mul_pos hcontinue hincidence).trans_le
    (quittingStationaryContinueMass_mul_incidence_le_lawPrefix
      who other root mass)

/-- **Near-minimum reset return with matched same-law incidence.**

If a cap--Nash return selection spends enough excursion debt and still has
positive survival, then the returned semantic point is within the requested
minimum-debt tolerance and its canonically transported terminal law retains
the displayed opponent incidence with the exact survival factor.  The joint
carrier membership ensures that this is a co-realized limiting law, not an
unrelated simplex annotation.

The positive-survival premise is sharp for transport of the old incidence:
a sure-absorbing prefix assigns coefficient zero to the entire old law. -/
theorem nearMinimum_resetPrefix_with_incidence_of_capNashReturnSelection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (root : ι → PMF Bool) (who other : ι) (tolerance : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hjoint : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target who = 0)
    (hselection : IsQuittingCapNashResetReturnSelection
      (reward := reward) source target root tolerance)
    (hcontinue : 0 < quittingStationaryContinueMass root)
    (hincidence : 0 <
      quittingTerminalOpponentIncidenceMass who other mass) :
    let returned := quittingTerminalSemanticPrefix reward root target
    let returnedMass := quittingTerminalOutcomeLawPrefix root mass
    (returned, returnedMass) ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned who = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned ∧
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum source + tolerance ∧
      quittingStationaryContinueMass root *
          quittingTerminalOpponentIncidenceMass who other mass ≤
        quittingTerminalOpponentIncidenceMass who other returnedMass ∧
      0 < quittingTerminalOpponentIncidenceMass who other returnedMass ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ player ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source returned player := by
  let returned := quittingTerminalSemanticPrefix reward root target
  let returnedMass := quittingTerminalOutcomeLawPrefix root mass
  have htargetCarrier : target ∈ quittingTerminalSemanticCarrier reward := by
    rw [quittingTerminalSemanticCarrier]
    apply map_mem_closure continuous_fst hjoint
    rintro point ⟨profile, rfl⟩
    exact ⟨profile, rfl⟩
  have haccount := capNashPrefix_resetExcursion_exact_account
    (reward := reward) source target root who hM hreward hminimum
      htargetCarrier hreset hselection.1
  have hreturnedJoint : (returned, returnedMass) ∈
      quittingTerminalSemanticLawCarrier reward := by
    exact quittingTerminalSemanticLawPrefix_mem_carrier
      reward root (target, mass) hM hreward hjoint
  have hnear : quittingTerminalSemanticDebtSum returned ≤
      quittingTerminalSemanticDebtSum source + tolerance := by
    dsimp only [returned]
    linarith [haccount.2.2.2.2.1, hselection.2]
  have hincidenceLower : quittingStationaryContinueMass root *
        quittingTerminalOpponentIncidenceMass who other mass ≤
      quittingTerminalOpponentIncidenceMass who other returnedMass := by
    exact quittingStationaryContinueMass_mul_incidence_le_lawPrefix
      who other root mass
  have hincidencePositive : 0 <
      quittingTerminalOpponentIncidenceMass who other returnedMass := by
    exact positive_incidence_lawPrefix_of_positive_continueMass
      who other root mass hcontinue hincidence
  exact ⟨hreturnedJoint, haccount.2.1, haccount.2.2.1, hnear,
    hincidenceLower, hincidencePositive, haccount.2.2.2.2.2.2⟩

end GameTheory
