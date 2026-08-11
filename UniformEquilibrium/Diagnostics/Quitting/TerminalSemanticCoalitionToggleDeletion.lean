/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Root.TerminalOpponentAdvantage

/-!
# Coalition toggles and a never-quit best response

Fix a player whose payoff weakly decreases whenever that player is inserted
into an already nonempty quitting coalition.  If the player's solo reward is
strictly below the quitting punishment value and that punishment value is
nonpositive, then `Never` is a full behavioral best response against every
opponent profile.

The infinite-horizon boundary is handled by the live ledger.  At every row,
the stationary punishment bound and the insertion inequalities force the
absorption branch to finance the punishment value.  The whole `Never` tail is
therefore at least the punishment value.  Inserting the player at any finite
date is then weakly worse than continuing.  Pure-time extremality upgrades
the comparison from deterministic quit dates to arbitrary behavioral
stopping rules.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Player `owner` weakly loses by joining every already nonempty coalition
of opponents. -/
def QuittingOwnerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  ∀ (quitters : Finset ι) (hquitters : quitters.Nonempty),
    owner ∉ quitters →
      reward
          ⟨insert owner quitters, Finset.insert_nonempty owner quitters⟩ owner ≤
        reward ⟨quitters, hquitters⟩ owner

/-- If all nonempty owner-insertion increments are nonpositive, the terminal
opponent advantage is nonnegative when the owner is forced to Continue. -/
theorem quittingTerminalOpponentAdvantage_nonneg_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hjoin : QuittingOwnerJoinAntitone reward owner)
    (action : ι → Bool) (howner : action owner = false) :
    0 ≤ quittingTerminalOpponentAdvantage reward owner action := by
  unfold quittingTerminalOpponentAdvantage quittingRootPayoff
  rw [quittingQuitters_update_true_of_apply_false]
  by_cases hquitters : (quittingQuitters action).Nonempty
  · simp only [dif_pos hquitters,
      dif_pos (Finset.insert_nonempty owner (quittingQuitters action))]
    apply sub_nonneg.mpr
    apply hjoin (quittingQuitters action) hquitters
    simp [quittingQuitters, howner]
  · have hempty : quittingQuitters action = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hquitters
    simp [hempty, quittingSingletonTerminal]

/-- The owner-insertion inequalities compare the two one-stage endpoints:
quitting now is no better than continuing with the solo payoff at the
all-Continue outcome. -/
theorem quittingFixedOpponentsQuitValue_le_continueReward_add_mass_mul_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward roots owner time ≤
      quittingFixedOpponentsContinueReward reward roots owner time +
        quittingFixedOpponentsContinueMass roots owner time *
          reward (quittingSingletonTerminal owner) owner := by
  let root := roots time
  have hexpect :
      0 ≤ expect (pmfPi (Function.update root owner (PMF.pure false)))
        (quittingTerminalOpponentAdvantage reward owner) := by
    unfold expect
    apply tsum_nonneg
    intro action
    by_cases howner : action owner = false
    · exact mul_nonneg ENNReal.toReal_nonneg
        (quittingTerminalOpponentAdvantage_nonneg_of_ownerJoinAntitone
          reward owner hjoin action howner)
    · have htrue : action owner = true := by
        cases h : action owner <;> simp_all
      have hmass :
          pmfPi (Function.update root owner (PMF.pure false)) action = 0 := by
        rw [pmfPi_apply_update_family]
        simp [htrue]
      rw [hmass, ENNReal.toReal_zero, zero_mul]
  rw [expect_terminalOpponentAdvantage] at hexpect
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward roots owner (0 : Payoff ι) time
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward roots owner
      (fun _ => reward (quittingSingletonTerminal owner) owner) time
  dsimp only [root] at hexpect
  rw [hquit, hcontinue] at hexpect
  exact sub_nonneg.mp hexpect

/-- The punishment value and the antitone insertion table force the row's
opponent-absorption reward to finance the punishment value. -/
theorem quittingPunishmentValue_ride_le_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner) (time : ℕ) :
    (1 - quittingFixedOpponentsContinueMass roots owner time) *
        quittingPunishmentValue reward owner ≤
      quittingFixedOpponentsContinueReward reward roots owner time := by
  let root := roots time
  let mass := quittingFixedOpponentsContinueMass roots owner time
  let absorb := quittingFixedOpponentsContinueReward reward roots owner time
  let quitValue := quittingFixedOpponentsQuitValue reward roots owner time
  let solo := reward (quittingSingletonTerminal owner) owner
  let chi := quittingPunishmentValue reward owner
  have hmass0 : 0 ≤ mass :=
    quittingFixedOpponentsContinueMass_nonneg roots owner time
  have hmass1 : mass ≤ 1 :=
    quittingFixedOpponentsContinueMass_le_one roots owner time
  have hquit : quitValue ≤ absorb + mass * solo := by
    exact quittingFixedOpponentsQuitValue_le_continueReward_add_mass_mul_solo
      reward roots owner hjoin time
  have hcap : chi ≤ max quitValue (absorb / (1 - mass)) := by
    have h := quittingPunishmentValue_le_stationaryUnilateralCap
      reward owner root
    rw [quittingStationaryUnilateralCap_eq_max_div,
      quittingStationaryFixedOpponentsQuitValue_apply,
      quittingStationaryFixedOpponentsContinueReward_apply,
      quittingStationaryFixedOpponentsContinueMass_apply] at h
    exact h
  by_cases hone : mass = 1
  · have habsorb : absorb = 0 := by
      dsimp only [absorb, mass, root]
      exact
        quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
          reward hone
    change (1 - mass) * chi ≤ absorb
    rw [hone, habsorb]
    norm_num
  · have hmasslt : mass < 1 := lt_of_le_of_ne hmass1 hone
    have hdenom : 0 < 1 - mass := by linarith
    by_contra hnot
    have habsorbLt : absorb < (1 - mass) * chi := lt_of_not_ge hnot
    have hratio : absorb / (1 - mass) < chi := by
      rw [div_lt_iff₀ hdenom]
      simpa [mul_comm] using habsorbLt
    have hquitLt : quitValue < chi := by
      change solo < chi at hsolo
      nlinarith
    have hmaxLt : max quitValue (absorb / (1 - mass)) < chi :=
      max_lt hquitLt hratio
    exact (not_lt_of_ge hcap) hmaxLt

/-- Start-indexed live-ledger inequality. -/
theorem le_quittingLiveLedgerAccum_add_survival_mul_from
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (target : ℝ) :
    ∀ (start fuel : ℕ),
      (∀ offset < fuel,
        (1 - quittingFixedOpponentsContinueMass roots owner
            (start + offset)) * target ≤
          quittingFixedOpponentsContinueReward reward roots owner
            (start + offset)) →
      target ≤ quittingLiveLedgerAccum reward roots owner start fuel +
        quittingOpponentSurvivalWeight roots owner start fuel * target := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      intro hride
      have hstep := hride 0 (by omega)
      simp only [Nat.add_zero] at hstep
      have htail : ∀ offset < fuel,
          (1 - quittingFixedOpponentsContinueMass roots owner
              (start + 1 + offset)) * target ≤
            quittingFixedOpponentsContinueReward reward roots owner
              (start + 1 + offset) := by
        intro offset hoffset
        have htime : start + (offset + 1) = start + 1 + offset := by omega
        rw [← htime]
        exact hride (offset + 1) (by omega)
      have hih := ih (start + 1) htail
      have hmass0 :=
        quittingFixedOpponentsContinueMass_nonneg roots owner start
      have hscaled := mul_le_mul_of_nonneg_left hih hmass0
      rw [quittingLiveLedgerAccum_shift,
        quittingOpponentSurvivalWeight_shift]
      nlinarith

/-- The finite never-quit ledger from an arbitrary start converges to the
literal infinite `Never` payoff from that start. -/
theorem tendsto_quittingLiveLedgerAccum_from
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ) :
    Tendsto (fun fuel => quittingLiveLedgerAccum reward roots owner start fuel)
      atTop (nhds (quittingRootSequencePureTimeTerminalValue reward roots owner
        none start)) := by
  have hlimit := tendsto_quittingFiniteRootPayoff_terminal reward roots owner
    (quittingPureTimeHazard none) start
  simpa [quittingFiniteRootPayoff_never_eq_ledgerAccum,
    quittingRootSequencePureTimeTerminalValue,
    quittingRootSequenceHazardTerminalValue,
    quittingRootSequenceTerminalValue] using hlimit

/-- Under the gate hypotheses, every suffix `Never` payoff is at least the
punishment value. -/
theorem quittingPunishmentValue_le_neverTail_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) (start : ℕ) :
    quittingPunishmentValue reward owner ≤
      quittingRootSequencePureTimeTerminalValue reward roots owner none start := by
  let chi := quittingPunishmentValue reward owner
  have hledger : ∀ fuel,
      chi ≤ quittingLiveLedgerAccum reward roots owner start fuel := by
    intro fuel
    have haccount := le_quittingLiveLedgerAccum_add_survival_mul_from
      reward roots owner chi start fuel (fun offset _ =>
        quittingPunishmentValue_ride_le_of_ownerJoinAntitone
          reward roots owner hjoin hsolo (start + offset))
    have hsurvival0 :=
      quittingOpponentSurvivalWeight_nonneg roots owner start fuel
    have hsurvival1 :=
      quittingOpponentSurvivalWeight_le_one roots owner start fuel
    dsimp only [chi] at haccount ⊢
    nlinarith
  exact ge_of_tendsto'
    (tendsto_quittingLiveLedgerAccum_from reward roots owner start) hledger

/-- A `Never` payoff splits into its finite live ledger and the surviving
stake in the corresponding suffix `Never` payoff. -/
theorem quittingRootSequencePureTimeTerminalValue_none_eq_ledger_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) :
    ∀ (start fuel : ℕ),
      quittingRootSequencePureTimeTerminalValue reward roots owner none start =
        quittingLiveLedgerAccum reward roots owner start fuel +
          quittingOpponentSurvivalWeight roots owner start fuel *
            quittingRootSequencePureTimeTerminalValue reward roots owner none
              (start + fuel) := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      rw [quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents,
        ih (start + 1), quittingLiveLedgerAccum_shift,
        quittingOpponentSurvivalWeight_shift]
      rw [show start + (fuel + 1) = start + 1 + fuel by omega]
      ring

/-- Every deterministic finite quit date is weakly dominated by `Never`.
The `none` case is equality. -/
theorem quittingRootSequencePureTimeTerminalValue_le_never_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0)
    (quitTime : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots owner quitTime 0 ≤
      quittingRootSequencePureTimeTerminalValue reward roots owner none 0 := by
  cases quitTime with
  | none => exact le_rfl
  | some time =>
      have htail := quittingPunishmentValue_le_neverTail_of_ownerJoinAntitone
        reward roots owner hjoin hsolo hchi (time + 1)
      have hquitLocal :=
        quittingFixedOpponentsQuitValue_le_continueReward_add_mass_mul_solo
          reward roots owner hjoin time
      have hmass0 :=
        quittingFixedOpponentsContinueMass_nonneg roots owner time
      have hlocal : quittingFixedOpponentsQuitValue reward roots owner time ≤
          quittingRootSequencePureTimeTerminalValue reward roots owner none
            time := by
        rw [quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents]
        have hsoloLe : reward (quittingSingletonTerminal owner) owner ≤
            quittingRootSequencePureTimeTerminalValue reward roots owner none
              (time + 1) := hsolo.le.trans htail
        nlinarith
      rw [quittingRootSequencePureTimeTerminalValue_some_eq,
        quittingRootSequencePureTimeTerminalValue_none_eq_ledger_add_tail
          reward roots owner 0 time]
      have hscaled := mul_le_mul_of_nonneg_left hlocal
        (quittingOpponentSurvivalWeight_nonneg roots owner 0 time)
      simpa [Nat.zero_add, add_comm] using
        (add_le_add_right hscaled
          (quittingLiveLedgerAccum reward roots owner 0 time))

/-- **Coalition-toggle deletion core.**  If every nonempty owner-side
coalition increment is nonpositive and the solo reward lies strictly below a
nonpositive punishment value, then literal `Never` attains the full
behavioral best-response value against every arbitrary opponent behavior
profile. -/
theorem quittingBestReplyValue_eq_never_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    quittingBestReplyValue reward profile owner =
      quittingTerminalPayoff reward
        (Function.update profile owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner := by
  let neverPayoff := quittingTerminalPayoff reward
    (Function.update profile owner
      (quittingPureTimeBehaviorStrategy reward owner none)) owner
  have hpure : ∀ quitTime : Option ℕ,
      quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner quitTime)) owner ≤
        neverPayoff := by
    intro quitTime
    dsimp only [neverPayoff]
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    exact
      quittingRootSequencePureTimeTerminalValue_le_never_of_ownerJoinAntitone
        reward (quittingProfileLiveRoot reward profile) owner hjoin hsolo hchi
        quitTime
  apply le_antisymm
  · apply quittingBestReplyValue_le
    intro deviation
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨quitTime, htime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        reward profile owner deviation hε
    have hp := hpure quitTime
    linarith
  · exact le_quittingBestReplyValue reward profile owner
      (quittingPureTimeBehaviorStrategy reward owner none)

/-- The owner has zero behavioral best-response debt on the literal
never-quit face. -/
theorem quittingBestReplyDebt_eq_zero_on_neverFace_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    quittingBestReplyValue reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner none)) owner -
        quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner none)) owner = 0 := by
  rw [quittingBestReplyValue_eq_never_of_ownerJoinAntitone
    reward
      (Function.update profile owner
        (quittingPureTimeBehaviorStrategy reward owner none))
      owner hjoin hsolo hchi]
  simp

omit [Fintype ι] in
/-- Finite dispatcher: either a strict owner-side coalition toggle exists,
or all owner-side increments are nonpositive. -/
theorem exists_strict_owner_toggle_or_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner) ∨
      QuittingOwnerJoinAntitone reward owner := by
  classical
  by_cases h : QuittingOwnerJoinAntitone reward owner
  · exact Or.inr h
  · left
    unfold QuittingOwnerJoinAntitone at h
    push Not at h
    obtain ⟨quitters, hquitters, howner, hstrict⟩ := h
    exact ⟨quitters, hquitters, howner, hstrict⟩

/-- **Coalition-toggle-or-Never alternative.**  Under the negative singleton
gate, either a nonempty opponent coalition has a strict owner-side insertion
increment, or `Never` is the owner's full behavioral best response against
every opponent profile. -/
theorem exists_strict_owner_toggle_or_forall_bestReply_eq_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner) ∨
      ∀ profile : (quittingGame reward).BehaviorProfile,
        quittingBestReplyValue reward profile owner =
          quittingTerminalPayoff reward
            (Function.update profile owner
              (quittingPureTimeBehaviorStrategy reward owner none)) owner := by
  rcases exists_strict_owner_toggle_or_ownerJoinAntitone reward owner with
    htoggle | hjoin
  · exact Or.inl htoggle
  · exact Or.inr fun profile =>
      quittingBestReplyValue_eq_never_of_ownerJoinAntitone
        reward profile owner hjoin hsolo hchi

end GameTheory
