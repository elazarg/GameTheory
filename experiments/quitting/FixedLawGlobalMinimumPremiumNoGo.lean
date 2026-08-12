/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalEndpointReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetSurfaceTension
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticTwoReservoirConsumer

/-!
# A fixed-law premium need not charge the reset owner

The fixed-law and global reset-face selectors optimize over different compact
sets.  Their scalar value gap does not identify a unilateral direction.  This
three-player table makes that failure literal.  The fixed point has a positive
atom containing a genuine opponent of the reset owner, and that atom supports
a strict membership toggle.  Retaining its law costs one unit of total debt,
whereas another point on the same reset face has zero debt.  Nevertheless the
reset owner has no profitable behavioral deviation at the fixed point: the
whole premium belongs to a third player.

Thus `D(F) - D(G) > 0` cannot by itself supply the owner/source-matched gain
needed by the rectangle compiler.  Stopping-law convexity cannot repair this:
it controls a chosen unilateral chord, but the two compact selectors do not
provide such a chord or choose the coordinate carrying the premium.

This is a local interface regression, not a counterexample regime.  In
particular it does not challenge the positive-global-minimum hypothesis; it
shows exactly which extra provenance that hypothesis would still have to
supply.
-/

noncomputable section

namespace GameTheory
namespace FixedLawGlobalMinimumPremiumNoGo

open StochasticGame QuittingSureSetOwnerRepair

abbrev Player := Fin 3

abbrev owner : Player := 0
abbrev atomPlayer : Player := 1
abbrev debtor : Player := 2

/-- The owner always receives one.  The debtor receives one exactly when it
belongs to the quitting coalition.  The remaining player receives zero. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal player =>
    if player = owner then 1
    else if player = debtor ∧ debtor ∈ terminal.val then 1
    else 0

theorem abs_reward_le_one
    (terminal : {S : Finset Player // S.Nonempty}) (player : Player) :
    |reward terminal player| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

/-- Fixed-law point: only the atom player exits. -/
def fixedProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot {atomPlayer})

/-- Global reset-face comparison: the atom player and debtor exit together. -/
def globalProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward
    (quittingPureSetRoot {atomPlayer, debtor})

def fixed : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward fixedProfile

def global : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward globalProfile

def fixedLaw : QuittingTerminalOutcome Player → ℝ :=
  quittingTerminalOutcomeMass reward fixedProfile

def atomTerminal : {S : Finset Player // S.Nonempty} :=
  ⟨{atomPlayer}, Finset.singleton_nonempty atomPlayer⟩

theorem fixed_debt_owner :
    quittingTerminalSemanticDebt fixed owner = 0 := by
  unfold fixed fixedProfile
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward {atomPlayer} owner
    (by norm_num) abs_reward_le_one]
  norm_num [quittingSetReward, reward, owner, atomPlayer, debtor]

theorem fixed_debt_atomPlayer :
    quittingTerminalSemanticDebt fixed atomPlayer = 0 := by
  unfold fixed fixedProfile
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward {atomPlayer}
    atomPlayer (by norm_num) abs_reward_le_one]
  norm_num [quittingSetReward, reward, owner, atomPlayer, debtor]

theorem fixed_debt_debtor :
    quittingTerminalSemanticDebt fixed debtor = 1 := by
  unfold fixed fixedProfile
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward {atomPlayer} debtor
    (by norm_num) abs_reward_le_one]
  norm_num [quittingSetReward, reward, owner, atomPlayer, debtor]

theorem global_debt_owner :
    quittingTerminalSemanticDebt global owner = 0 := by
  unfold global globalProfile
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward
    {atomPlayer, debtor} owner (by norm_num) abs_reward_le_one]
  norm_num [quittingSetReward, reward, owner, atomPlayer, debtor]

theorem global_debt_atomPlayer :
    quittingTerminalSemanticDebt global atomPlayer = 0 := by
  unfold global globalProfile
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward
    {atomPlayer, debtor} atomPlayer (by norm_num) abs_reward_le_one]
  norm_num [quittingSetReward, reward, owner, atomPlayer, debtor]

theorem global_debt_debtor :
    quittingTerminalSemanticDebt global debtor = 0 := by
  unfold global globalProfile
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward
    {atomPlayer, debtor} debtor (by norm_num) abs_reward_le_one]
  norm_num [quittingSetReward, reward, owner, atomPlayer, debtor]

theorem fixed_debtSum : quittingTerminalSemanticDebtSum fixed = 1 := by
  unfold quittingTerminalSemanticDebtSum
  rw [Fin.sum_univ_three, fixed_debt_owner, fixed_debt_atomPlayer,
    fixed_debt_debtor]
  norm_num

theorem global_debtSum : quittingTerminalSemanticDebtSum global = 0 := by
  unfold quittingTerminalSemanticDebtSum
  rw [Fin.sum_univ_three, global_debt_owner, global_debt_atomPlayer,
    global_debt_debtor]
  norm_num

/-- The selector gap is positive and equals one. -/
theorem lawPremium_eq_one :
    quittingTerminalSemanticDebtSum fixed -
        quittingTerminalSemanticDebtSum global = 1 := by
  rw [fixed_debtSum, global_debtSum]
  norm_num

/-- The law-bearing atom pays the reset owner positively. -/
theorem atom_reward_owner_pos : 0 < reward atomTerminal owner := by
  norm_num [reward, atomTerminal, owner]

/-- The same atom carries a strict outsider toggle, but for the debtor rather
than the reset owner. -/
theorem atom_has_strict_debtor_toggle :
    quittingSetReward reward ({atomPlayer} : Finset Player) debtor <
      quittingSetReward reward (insert debtor {atomPlayer}) debtor := by
  norm_num [quittingSetReward, reward, owner, atomPlayer, debtor]

/-- Quitting immediately guarantees the debtor one against every opponent
profile, because every resulting terminal contains the debtor. -/
theorem quitNow_payoff_debtor_eq_one
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward
        (Function.update profile debtor
          (quittingPureTimeBehaviorStrategy reward debtor (some 0))) debtor =
      1 := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  let root := quittingProfileLiveRoot reward profile 0
  let distribution := Math.PMFProduct.pmfPi
    (Function.update root debtor (PMF.pure true))
  change Math.Probability.expect distribution
      (fun action => quittingRootPayoff reward 0 action debtor) = 1
  rw [Math.ProbabilityMassFunction.expect_congr_on_support distribution
    (fun action => quittingRootPayoff reward 0 action debtor)
    (fun _ => (1 : ℝ))]
  · exact Math.Probability.expect_const distribution 1
  · intro action haction
    have hself : action debtor = true :=
      action_eq_true_of_mem_support_pmfPi_update_pure_true
        root debtor action haction
    have hnonempty : (quittingQuitters action).Nonempty :=
      (quittingQuitters_nonempty_iff action).2 ⟨debtor, hself⟩
    have hmem : debtor ∈ quittingQuitters action := by
      simpa [quittingQuitters] using hself
    simp [quittingRootPayoff, hnonempty, reward, debtor, owner, hmem]

/-- Every executable profile gives the debtor best-response value at least
one. -/
theorem one_le_continuationBestResponseValue_debtor
    (profile : (quittingGame reward).BehaviorProfile) :
    1 ≤ quittingContinuationBestResponseValue reward profile debtor := by
  rw [← quitNow_payoff_debtor_eq_one profile]
  exact quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile debtor
      (quittingPureTimeBehaviorStrategy reward debtor (some 0))
      (by norm_num) abs_reward_le_one

/-- The uniform immediate-Quit lower bound survives passage to the compact
semantic carrier. -/
theorem one_le_cap_debtor_of_mem_carrier
    (pair : QuittingTerminalSemanticPair Player)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    1 ≤ pair.2 debtor := by
  have hclosed : IsClosed
      {candidate : QuittingTerminalSemanticPair Player |
        1 ≤ candidate.2 debtor} :=
    isClosed_Ici.preimage
      ((continuous_apply debtor).comp continuous_snd)
  have hsubset : quittingAttainableTerminalSemanticPairs reward ⊆
      {candidate : QuittingTerminalSemanticPair Player |
        1 ≤ candidate.2 debtor} := by
    rintro candidate ⟨profile, rfl⟩
    exact one_le_continuationBestResponseValue_debtor profile
  rw [quittingTerminalSemanticCarrier] at hpair
  exact closure_minimal hsubset hclosed hpair

theorem fixed_mem_lawCarrier :
    (fixed, fixedLaw) ∈ quittingTerminalSemanticLawCarrier reward := by
  exact quittingTerminalSemanticLawPoint_mem_carrier reward fixedProfile

theorem global_mem_lawCarrier :
    (global,
        quittingTerminalOutcomeMass reward globalProfile) ∈
      quittingTerminalSemanticLawCarrier reward := by
  exact quittingTerminalSemanticLawPoint_mem_carrier reward globalProfile

/-- The displayed fixed profile really minimizes total debt among all
semantic points retaining its complete outcome law. -/
theorem fixed_minimal_on_fixedLaw
    (candidate : QuittingTerminalSemanticPair Player)
    (hcandidate :
      (candidate, fixedLaw) ∈ quittingTerminalSemanticLawCarrier reward) :
    quittingTerminalSemanticDebtSum fixed ≤
      quittingTerminalSemanticDebtSum candidate := by
  have hcandidateCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier
      (candidate, fixedLaw) hcandidate
  have hcap : 1 ≤ candidate.2 debtor :=
    one_le_cap_debtor_of_mem_carrier candidate hcandidateCarrier
  have hmomentCandidate :=
    terminalSemanticLawCarrier_rewardMoment reward
      (candidate, fixedLaw) hcandidate
  have hmomentFixed :=
    terminalSemanticLawCarrier_rewardMoment reward
      (fixed, fixedLaw) fixed_mem_lawCarrier
  have hpayoff : candidate.1 debtor = 0 := by
    have heq : candidate.1 = fixed.1 := by
      rw [← hmomentCandidate, ← hmomentFixed]
    have hfixedPayoff := quittingTerminalPayoff_pureSetRoot reward
      ({atomPlayer} : Finset Player) debtor
    change fixed.1 debtor = _ at hfixedPayoff
    rw [heq, hfixedPayoff]
    norm_num [quittingSetReward, reward, owner, atomPlayer, debtor]
  have hdebt : 1 ≤ quittingTerminalSemanticDebt candidate debtor := by
    unfold quittingTerminalSemanticDebt
    rw [hpayoff]
    simpa using hcap
  have hotherNonneg : ∀ player ∈ Finset.univ,
      0 ≤ quittingTerminalSemanticDebt candidate player := by
    intro player _
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (by norm_num) abs_reward_le_one hcandidateCarrier player
  rw [fixed_debtSum]
  exact hdebt.trans (Finset.single_le_sum hotherNonneg (Finset.mem_univ debtor))

/-- The comparison point is a global total-debt minimizer, hence in
particular a global minimizer on the owner's reset face. -/
theorem global_minimal_on_resetFace
    (candidate : QuittingTerminalSemanticLawPoint Player)
    (hcandidate : candidate ∈ quittingTerminalSemanticLawCarrier reward)
    (_hcandidateReset :
      quittingTerminalSemanticDebt candidate.1 owner = 0) :
    quittingTerminalSemanticDebtSum global ≤
      quittingTerminalSemanticDebtSum candidate.1 := by
  have hcandidateCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier candidate hcandidate
  rw [global_debtSum]
  exact Finset.sum_nonneg fun player _ =>
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (by norm_num) abs_reward_le_one hcandidateCarrier player

/-- The retained fixed law has unit mass on the displayed singleton atom. -/
theorem fixedLaw_atom_eq_one : fixedLaw (some atomTerminal) = 1 := by
  unfold fixedLaw quittingTerminalOutcomeMass
  change quittingAbsorbedMassLimit reward fixedProfile atomTerminal = 1
  rw [quittingAbsorbedMassLimit_eq_absorbedMass_of_stage_zero_after
    reward fixedProfile atomTerminal 1]
  · rw [show 1 = 0 + 1 by omega,
      quittingAbsorbedMass_succ_eq_add_stageCoalitionMass,
      quittingAbsorbedMass_zero,
      quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
    rw [quittingLiveMass_zero, one_mul, zero_add]
    unfold quittingRootCoalitionMass quittingRootQuitRates
    unfold fixedProfile
    rw [quittingProfileLiveRoot_stationary]
    change Math.PMFProduct.coalitionMass
      (fun who => ((quittingPureSetRoot {atomPlayer} who) true).toReal)
        ({atomPlayer} : Finset Player) = 1
    unfold Math.PMFProduct.coalitionMass
    simp only [quittingPureSetRoot, quittingSetAction,
      Finset.mem_singleton, PMF.pure_apply]
    rw [Finset.prod_singleton]
    norm_num
    apply Finset.prod_eq_one
    intro player hplayer
    have hne : player ≠ atomPlayer := by
      simpa [Finset.mem_compl] using hplayer
    simp [hne]
  · intro time htime
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
    have htimePos : 0 < time := by omega
    have hlive : quittingLiveMass reward fixedProfile time = 0 := by
      unfold fixedProfile
      rw [quittingLiveMass_stationary_eq_pow,
        stationaryContinueMass_pureSetRoot_of_nonempty
          (Finset.singleton_nonempty atomPlayer),
        zero_pow (ne_of_gt htimePos)]
    rw [hlive, zero_mul]

/-- Consequently the atom-supported owner/opponent incidence is positive
with no loss at the fixed-law selector. -/
theorem fixedLaw_owner_atomPlayer_incidence_pos :
    0 < quittingTerminalOpponentIncidenceMass owner atomPlayer fixedLaw := by
  have hsimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
    (fixed, fixedLaw) fixed_mem_lawCarrier
  unfold quittingTerminalOpponentIncidenceMass
  have hatom : atomTerminal ∈
      Finset.univ.filter
        (fun terminal : {S : Finset Player // S.Nonempty} =>
          atomPlayer ∈ terminal.val ∧ atomPlayer ≠ owner) := by
    simp [atomTerminal, atomPlayer, owner]
  have hle := Finset.single_le_sum
    (fun terminal _ => hsimplex.1 (some terminal)) hatom
  change fixedLaw (some atomTerminal) ≤
    ∑ terminal ∈ Finset.univ.filter
      (fun terminal : {S : Finset Player // S.Nonempty} =>
        atomPlayer ∈ terminal.val ∧ atomPlayer ≠ owner),
      fixedLaw (some terminal) at hle
  rw [fixedLaw_atom_eq_one] at hle
  linarith

/-- Every behavioral deviation of the reset owner from the fixed profile has
nonpositive gain. -/
theorem fixed_owner_deviation_nonpos
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    quittingTerminalPayoff reward
          (Function.update fixedProfile owner deviation) owner -
        quittingTerminalPayoff reward fixedProfile owner ≤ 0 := by
  have hupper := quittingTerminalPayoff_update_pureSetRoot_le reward
    ({atomPlayer} : Finset Player) owner deviation
  have hcurrent := quittingTerminalPayoff_pureSetRoot reward
    ({atomPlayer} : Finset Player) owner
  change quittingTerminalPayoff reward
      (Function.update fixedProfile owner deviation) owner ≤ _ at hupper
  change quittingTerminalPayoff reward fixedProfile owner = _ at hcurrent
  rw [hcurrent]
  norm_num [quittingSetReward, reward, owner, atomPlayer, debtor] at hupper ⊢
  exact hupper

/-- The reset owner cannot receive any positive fraction of the law premium
as a source-matched legal gain. -/
theorem no_owner_gain_from_positive_lawPremium
    {c : ℝ} (hc : 0 < c) :
    ¬ ∃ deviation : (quittingGame reward).BehaviorStrategy owner,
      c * (quittingTerminalSemanticDebtSum fixed -
          quittingTerminalSemanticDebtSum global) ≤
        quittingTerminalPayoff reward
            (Function.update fixedProfile owner deviation) owner -
          quittingTerminalPayoff reward fixedProfile owner := by
  rintro ⟨deviation, hgain⟩
  have hnonpos := fixed_owner_deviation_nonpos deviation
  rw [lawPremium_eq_one, mul_one] at hgain
  linarith

end FixedLawGlobalMinimumPremiumNoGo
end GameTheory
