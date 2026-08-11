/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn

/-!
# Same-account consumers for the two positive terminal reservoirs

The positive-part audit splits one limiting best-response law into harmonic
`Never` charge and finite opponent-containing charge.  At a positive minimum
debt gate, both branches retain the same reset law:

* the harmonic branch gives the quantitative negative singleton vertex,
  alongside the counterexample punishment moat;
* the finite branch puts that very law on a zero-debt reset face and feeds it
  to the fixed-law reset dispatch.

The bridge is joint convergence.  The semantic reset cluster is extracted
along a subsequence of the same deviated profiles whose outcome laws converge,
so the cluster and law form one joint carrier point.  No conditioning or
replacement by an unrelated terminal law occurs.

The finite dispatch still ends in either a positive-survival absorbing return
or an all-Continue cap face.  The theorem does not turn the latter face into a
chronological recurrence, nor does it manufacture the finite list of endpoint
moves required by the pair-to-singleton dropout theorem.
-/

noncomputable section

namespace GameTheory

open Filter Set QuittingSureSetOwnerRepair
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The game-facing data retained by the fixed-law reset dispatch. -/
structure QuittingFixedLawResetDispatch
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner other : ι) (returned : QuittingTerminalSemanticPair ι) : Prop where
  joint : (returned, mass) ∈ quittingTerminalSemanticLawCarrier reward
  reset : quittingTerminalSemanticDebt returned owner = 0
  source_le : quittingTerminalSemanticDebtSum source ≤
    quittingTerminalSemanticDebtSum returned
  target_ge : quittingTerminalSemanticDebtSum returned ≤
    quittingTerminalSemanticDebtSum target
  transfer : quittingTerminalSemanticDebt source owner ≤
    ∑ player ∈ Finset.univ.erase owner,
      quittingTerminalSemanticDebtChange source returned player
  supported_toggle : ∃ terminal : {S : Finset ι // S.Nonempty},
    other ∈ terminal.val ∧ 0 < mass (some terminal) ∧
      ((∃ member ∈ terminal.val,
          quittingSetReward reward terminal.val member <
            quittingSetReward reward (terminal.val.erase member) member) ∨
        ∃ outsider ∉ terminal.val,
          quittingSetReward reward terminal.val outsider <
            quittingSetReward reward
              (insert outsider terminal.val) outsider)
  dynamic_exit :
    (∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward returned.2 0 root ∧
      0 < quittingRootAbsorptionMass root ∧
      0 < quittingStationaryContinueMass root ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root returned) <
        quittingTerminalSemanticDebtSum returned ∧
      (quittingTerminalSemanticPrefix reward root returned,
          quittingTerminalOutcomeLawPrefix root mass) ∈
        quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root returned) owner = 0 ∧
      0 < quittingTerminalOpponentIncidenceMass owner other
        (quittingTerminalOutcomeLawPrefix root mass)) ∨
    (IsεQuittingRootNash reward returned.2 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot
        returned = returned)

/-- A semantic reset subsequence and the inherited law limit form one joint
carrier point.  This is the missing provenance bridge between pure-time debt
extraction and fixed-law reset minimization. -/
theorem mem_terminalSemanticLawCarrier_of_reset_subseq_tendsto
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (cluster : QuittingTerminalSemanticPair ι)
    (subseq : ℕ → ℕ)
    (hmass : Tendsto (fun n => quittingTerminalOutcomeMass reward (profiles n))
      atTop (nhds mass))
    (hsubseq : StrictMono subseq)
    (hcluster : Tendsto (fun n =>
      quittingTerminalSemanticPair reward (profiles (subseq n)))
      atTop (nhds cluster)) :
    (cluster, mass) ∈ quittingTerminalSemanticLawCarrier reward := by
  apply mem_terminalSemanticLawCarrier_of_joint_tendsto reward
    (fun n => profiles (subseq n)) (cluster, mass)
  exact hcluster.prodMk_nhds (hmass.comp hsubseq.tendsto_atTop)

/-- **Contamination-robust two-reservoir consumer on one reset law.**

At a positive minimum debt gate in a counterexample, either there is already
a strict singleton joiner, or there is a fixed punishment moat and one joint
reset law satisfying the exact threshold alternative:

* the harmonic share gives the quantitative negative singleton vertex;
* the finite share gives quantitative opponent-containing mass and a
  fixed-law reset dispatch for a concrete opponent incidence coordinate.

Every minimum, singleton-tightness, root-Nash, and reward-bound gate is shown
in the hypotheses.  The terminal law in the finite dispatch is literally the
law in the positive-part split. -/
theorem QuittingCounterexampleRegime.exists_twoReservoir_sameLaw_resetDispatch
    (regime : QuittingCounterexampleRegime reward)
    (source : QuittingTerminalSemanticPair ι) (owner : ι) {M theta : ℝ}
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum source)
    (hnash : IsεQuittingRootNash reward source.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (hgate : IsMinimumTerminalSemanticDebtGate reward source owner)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSingletonCollisionReward reward owner other) ∨
      quittingSoloReward reward owner owner <
          quittingPunishmentValue reward owner ∧
        ∃ (mass : QuittingTerminalOutcome ι → ℝ)
            (cluster : QuittingTerminalSemanticPair ι),
          (cluster, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
          quittingTerminalSemanticDebt cluster owner = 0 ∧
          ((source.1 owner ≤
                -theta * quittingTerminalSemanticDebtSum source ∧
              theta * quittingTerminalSemanticDebtSum source / M ≤
                mass none) ∨
            ((1 - theta) * quittingTerminalSemanticDebtSum source /
                  (2 * M) ≤
                quittingTerminalOpponentContainingMass owner mass ∧
              ∃ other returned,
                other ≠ owner ∧
                0 < quittingTerminalOpponentIncidenceMass owner other mass ∧
                QuittingFixedLawResetDispatch (reward := reward)
                  source cluster mass owner other returned)) := by
  rcases regime.strictJoiner_or_soloReward_lt_punishmentValue owner with
    hjoin | hpunishment
  · exact Or.inl hjoin
  · right
    refine ⟨hpunishment, ?_⟩
    have howner := minimumTerminalSemantic_debtGate_ownerPin_and_debt_pos
      (reward := reward) source owner hM.le hreward hsource hminimum
        hpositive hgate
    obtain ⟨profiles, quitTime, mass, baseSubseq, hprofiles, hmass,
        hbaseSubseq, hmassLimit, hmoment⟩ :=
      exists_pureTimeDeviation_terminalLaw_tendsto_semanticEnvelope
        reward source hsource owner hM.le hreward
    let resetProfile : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
      Function.update (profiles (baseSubseq rank)) owner
        (quittingPureTimeBehaviorStrategy reward owner
          (quitTime (baseSubseq rank)))
    have hpayoff : Tendsto (fun rank =>
        quittingTerminalPayoff reward (resetProfile rank) owner)
        atTop (nhds (source.2 owner)) := by
      have hmomentLimit : Tendsto (fun rank =>
          quittingTerminalRewardMoment reward
            (quittingTerminalOutcomeMass reward (resetProfile rank)) owner)
          atTop (nhds (quittingTerminalRewardMoment reward mass owner)) :=
        ((continuous_apply owner).comp
          (continuous_quittingTerminalRewardMoment reward)).tendsto mass |>.comp
            hmassLimit
      rw [hmoment] at hmomentLimit
      simpa only [quittingTerminalRewardMoment_outcomeMass] using hmomentLimit
    obtain ⟨cluster, resetSubseq, _hclusterCarrier, hresetSubseq,
        hclusterLimit, hreset, _hidentity, _htransfer⟩ :=
      exists_terminalSemanticResetCluster_quantitative_transfer
        reward source (fun rank => profiles (baseSubseq rank)) owner
        (fun rank => quittingPureTimeBehaviorStrategy reward owner
          (quitTime (baseSubseq rank))) hM.le hreward hminimum
        (hprofiles.comp hbaseSubseq.tendsto_atTop) hpayoff
    have hjoint : (cluster, mass) ∈
        quittingTerminalSemanticLawCarrier reward := by
      apply mem_terminalSemanticLawCarrier_of_reset_subseq_tendsto
        (reward := reward) resetProfile mass cluster resetSubseq hmassLimit
          hresetSubseq
      simpa only [resetProfile] using hclusterLimit
    refine ⟨mass, cluster, hjoint, hreset, ?_⟩
    have hsourceBox := quittingTerminalSemanticCarrier_mem_box
      source hM.le hreward hsource
    have hprescribed : |source.1 owner| ≤ M := by
      exact abs_le.mpr ⟨hsourceBox.1.1 owner, hsourceBox.1.2 owner⟩
    rcases negativeNever_or_opponentContainingMass
        reward source hnash owner mass hM hreward hprescribed hmass hmoment
          howner.2 htheta hthetaOne with hharmonic | hfinite
    · left
      simpa [hgate.1] using hharmonic
    · right
      refine ⟨by simpa [hgate.1] using hfinite, ?_⟩
      have hfinitePositive : 0 <
          quittingTerminalOpponentContainingMass owner mass := by
        have hcoefficient : 0 <
            (1 - theta) * quittingTerminalSemanticDebtSum source /
              (2 * M) := by
          positivity
        exact hcoefficient.trans_le (by simpa [hgate.1] using hfinite)
      obtain ⟨other, hotherNe, hotherIncidence⟩ :=
        exists_positive_opponentIncidenceMass owner mass hmass hfinitePositive
      obtain ⟨returned, hreturnedJoint, _hreturnedCarrier, hreturnedReset,
          hsourceLe, hreturnedLe, htransfer, htoggle, hdynamic⟩ :=
        regime.exists_fixedLaw_resetFace_dispatch source cluster mass owner
          other hM.le hreward hminimum hpositive hjoint hreset hotherIncidence
      exact ⟨other, returned, hotherNe, hotherIncidence,
        ⟨hreturnedJoint, hreturnedReset, hsourceLe, hreturnedLe, htransfer,
          htoggle, hdynamic⟩⟩

end GameTheory
