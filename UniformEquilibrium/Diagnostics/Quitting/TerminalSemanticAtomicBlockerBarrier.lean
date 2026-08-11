/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion

/-!
# The atomic blocker barrier

For an arbitrary product row at which `owner` Quits surely, this module
records the largest one-stage outsider deviation gain.  Since the owner's
action makes every outsider deviation absorb at date zero, this finite
quantity is also an exact bound on full behavioral deviation gains after an
arbitrary punishment tail is attached.

Combining that observation with the owner-specific punishment completion
gives the every-row blocker barrier

`η ≤ max outsiderDefect (max 0 (-blockerBalance))`.

Thus a positive owner-side coalition toggle carries an outsider deviation of
size at least the global terminal exploitability gap.  This is the
quantitative atomic handoff from failure of player deletion.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The positive part of one outsider's best pure endpoint gain at a
forced-owner row.  The owner coordinate is set to zero. -/
def quittingForcedOwnerOutsiderCoordinateDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner who : ι) : ℝ :=
  if who = owner then 0 else
    max 0
      (max (quittingStationaryFixedOpponentsQuitValue reward root who)
          (quittingStationaryFixedOpponentsContinueReward reward root who) -
        quittingRootAbsorbingContribution reward root who)

/-- Largest outsider one-stage deviation gain at a forced-owner product row.
The definition is meaningful for every row; its behavioral interpretation
uses the hypothesis `root owner = PMF.pure true`. -/
def quittingForcedOwnerOutsiderDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) : ℝ := by
  letI : Nonempty ι := ⟨owner⟩
  exact Finset.univ.sup' Finset.univ_nonempty fun who =>
    quittingForcedOwnerOutsiderCoordinateDefect reward root owner who

theorem quittingForcedOwnerOutsiderCoordinateDefect_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner who : ι) :
    0 ≤ quittingForcedOwnerOutsiderCoordinateDefect reward root owner who := by
  unfold quittingForcedOwnerOutsiderCoordinateDefect
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem quittingForcedOwnerOutsiderCoordinateDefect_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner who : ι) :
    quittingForcedOwnerOutsiderCoordinateDefect reward root owner who ≤
      quittingForcedOwnerOutsiderDefect reward root owner := by
  letI : Nonempty ι := ⟨owner⟩
  unfold quittingForcedOwnerOutsiderDefect
  exact Finset.le_sup'
    (quittingForcedOwnerOutsiderCoordinateDefect reward root owner)
    (Finset.mem_univ who)

theorem quittingForcedOwnerOutsiderDefect_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    0 ≤ quittingForcedOwnerOutsiderDefect reward root owner := by
  letI : Nonempty ι := ⟨owner⟩
  exact (quittingForcedOwnerOutsiderCoordinateDefect_nonneg
      reward root owner owner).trans
    (quittingForcedOwnerOutsiderCoordinateDefect_le
      reward root owner owner)

/-- The raw best-endpoint gain of any outsider is bounded by the finite
outsider defect. -/
theorem quittingForcedOwner_bestEndpointGain_le_outsiderDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner who : ι) (hwho : who ≠ owner) :
    max (quittingStationaryFixedOpponentsQuitValue reward root who)
          (quittingStationaryFixedOpponentsContinueReward reward root who) -
        quittingRootAbsorbingContribution reward root who ≤
      quittingForcedOwnerOutsiderDefect reward root owner := by
  calc
    max (quittingStationaryFixedOpponentsQuitValue reward root who)
          (quittingStationaryFixedOpponentsContinueReward reward root who) -
        quittingRootAbsorbingContribution reward root who ≤
      max 0
        (max (quittingStationaryFixedOpponentsQuitValue reward root who)
            (quittingStationaryFixedOpponentsContinueReward reward root who) -
          quittingRootAbsorbingContribution reward root who) :=
        le_max_right _ _
    _ = quittingForcedOwnerOutsiderCoordinateDefect reward root owner who := by
      simp [quittingForcedOwnerOutsiderCoordinateDefect, hwho]
    _ ≤ quittingForcedOwnerOutsiderDefect reward root owner :=
      quittingForcedOwnerOutsiderCoordinateDefect_le reward root owner who

omit [DecidableEq ι] in
/-- A surely quitting owner makes the product row absorb at date zero. -/
theorem quittingStationaryContinueMass_eq_zero_of_owner_eq_pure
    {root : ι → PMF Bool} {owner : ι}
    (howner : root owner = PMF.pure true) :
    quittingStationaryContinueMass root = 0 := by
  unfold quittingStationaryContinueMass
  have hzero :=
    (quittingRootHasSureQuitter_iff_allContinue_mass_zero root).mp
      ⟨owner, howner⟩
  rw [show (quittingAllContinueAction : ι → Bool) =
      (fun _ => false) by rfl, hzero]
  simp

/-- Even after an outsider is forced to Continue, the sure owner kills the
continuation mass. -/
theorem quittingStationaryFixedOpponentsContinueMass_eq_zero_of_owner_eq_pure
    {root : ι → PMF Bool} {owner who : ι}
    (howner : root owner = PMF.pure true) (hwho : who ≠ owner) :
    quittingStationaryFixedOpponentsContinueMass root who = 0 := by
  have hle := quittingStationaryContinueMass_le_ownContinueProbability
    (Function.update root who (PMF.pure false)) owner
  have howner' :
      Function.update root who (PMF.pure false) owner = PMF.pure true := by
    rw [Function.update_of_ne (Ne.symm hwho)]
    exact howner
  rw [howner'] at hle
  have hnonneg :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root who
  change quittingStationaryContinueMass
      (Function.update root who (PMF.pure false)) = 0
  change 0 ≤ quittingStationaryContinueMass
      (Function.update root who (PMF.pure false)) at hnonneg
  exact le_antisymm (by simpa using hle) hnonneg

omit [DecidableEq ι] in
/-- The arbitrary forced-owner row itself receives its absorbing
contribution under the one-stage punishment construction. -/
theorem quittingTerminalPayoff_atomicBlockerCompletion_of_owner_eq_pure
    {root punishRow : ι → PMF Bool} {owner : ι}
    (howner : root owner = PMF.pure true) (who : ι) :
    quittingTerminalPayoff reward
        (quittingOneStagePunishedProfile reward root punishRow) who =
      quittingRootAbsorbingContribution reward root who := by
  exact quittingTerminalPayoff_oneStagePunishedProfile reward root punishRow who
    (quittingStationaryContinueMass_eq_zero_of_owner_eq_pure howner)

/-- Full behavioral outsider deviations are bounded by the finite outsider
defect.  This is exact rather than a one-stage surrogate: the sure owner
absorbs every deviated history at date zero. -/
theorem quittingTerminalPayoff_update_atomicBlockerCompletion_outsider_le_defect
    {root punishRow : ι → PMF Bool} {owner who : ι}
    (howner : root owner = PMF.pure true) (hwho : who ≠ owner)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingOneStagePunishedProfile reward root punishRow)
          who deviation) who ≤
      quittingRootAbsorbingContribution reward root who +
        quittingForcedOwnerOutsiderDefect reward root owner := by
  have hcap := quittingTerminalPayoff_update_oneStagePunishedProfile_le
    reward root punishRow who deviation
  rw [quittingStationaryFixedOpponentsContinueMass_eq_zero_of_owner_eq_pure
      howner hwho,
    zero_mul, add_zero] at hcap
  have hfinite := quittingForcedOwner_bestEndpointGain_le_outsiderDefect
    reward root owner who hwho
  linarith

/-- The owner estimate in the atomic completion only needs the owner to Quit
surely; outsider Nash conditions play no role. -/
theorem quittingTerminalPayoff_update_atomicBlockerCompletion_owner_le_of_owner_eq_pure
    {root punishRow : ι → PMF Bool} {owner : ι}
    (howner : root owner = PMF.pure true) {ε : ℝ}
    (hpunish : quittingStationaryUnilateralCap reward punishRow owner ≤
      quittingPunishmentValue reward owner + ε)
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingOneStagePunishedProfile reward root punishRow)
          owner deviation) owner ≤
      quittingForcedOwnerObeyValue reward root owner +
        quittingAtomicBlockerCompletionError reward root owner ε := by
  have hcap := quittingTerminalPayoff_update_oneStagePunishedProfile_le
    reward root punishRow owner deviation
  have hupdate : Function.update root owner (PMF.pure true) = root := by
    rw [← howner, Function.update_eq_self]
  have hquit : quittingStationaryFixedOpponentsQuitValue reward root owner =
      quittingForcedOwnerObeyValue reward root owner := by
    simp only [quittingStationaryFixedOpponentsQuitValue,
      quittingFixedOpponentsQuitValue]
    rw [hupdate]
    rfl
  have hp0 : 0 ≤ quittingForcedOwnerAllOutsidersContinueMass root owner :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root owner
  have hscaled := mul_le_mul_of_nonneg_left hpunish hp0
  have herror0 : 0 ≤
      quittingAtomicBlockerCompletionError reward root owner ε :=
    le_max_left _ _
  have herrorBalance :
      -quittingAtomicBlockerBalance reward root owner +
          quittingForcedOwnerAllOutsidersContinueMass root owner * ε ≤
        quittingAtomicBlockerCompletionError reward root owner ε :=
    le_max_right _ _
  rw [hquit] at hcap
  refine hcap.trans (max_le (le_add_of_nonneg_right herror0) ?_)
  unfold quittingAtomicBlockerBalance at herrorBalance
  unfold quittingForcedOwnerRefusalCap at herrorBalance
  change quittingStationaryFixedOpponentsContinueReward reward root owner +
      quittingForcedOwnerAllOutsidersContinueMass root owner *
        quittingStationaryUnilateralCap reward punishRow owner ≤
    quittingForcedOwnerObeyValue reward root owner +
      quittingAtomicBlockerCompletionError reward root owner ε
  nlinarith

/-- **Every-row atomic blocker barrier.**  At a row where the owner Quits
surely, either an outsider has the stated finite deviation defect or the
owner's refusal advantage reaches the global exploitability floor. -/
theorem terminalExploitabilityGap_le_atomicBlockerBarrier
    {root : ι → PMF Bool} {owner : ι} {η : ℝ}
    (howner : root owner = PMF.pure true)
    (_hη : 0 < η) (hgap : HasTerminalExploitabilityGap reward η) :
    η ≤ max (quittingForcedOwnerOutsiderDefect reward root owner)
      (max 0 (-quittingAtomicBlockerBalance reward root owner)) := by
  by_contra hnot
  have hbarrier_lt :
      max (quittingForcedOwnerOutsiderDefect reward root owner)
          (max 0 (-quittingAtomicBlockerBalance reward root owner)) < η :=
    lt_of_not_ge hnot
  let barrier :=
    max (quittingForcedOwnerOutsiderDefect reward root owner)
      (max 0 (-quittingAtomicBlockerBalance reward root owner))
  let ε := (η - barrier) / 2
  have hε : 0 < ε := by
    dsimp [ε, barrier]
    linarith
  obtain ⟨punishRow, hpunish⟩ :=
    exists_quittingStationaryPunishmentRoot_lt_add reward owner hε
  let profile := quittingOneStagePunishedProfile reward root punishRow
  obtain ⟨who, deviation, hexploit⟩ := hgap profile
  have hprofile : quittingTerminalPayoff reward profile who =
      quittingRootAbsorbingContribution reward root who := by
    exact quittingTerminalPayoff_atomicBlockerCompletion_of_owner_eq_pure
      howner who
  have hp0_le :
      quittingForcedOwnerAllOutsidersContinueMass root owner ≤ 1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root owner
  have hp0_nonneg :
      0 ≤ quittingForcedOwnerAllOutsidersContinueMass root owner :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root owner
  have hrefusal_nonneg :
      0 ≤ max 0 (-quittingAtomicBlockerBalance reward root owner) :=
    le_max_left _ _
  have hrefusal_le :
      max 0 (-quittingAtomicBlockerBalance reward root owner) ≤ barrier := by
    dsimp [barrier]
    exact le_max_right _ _
  have hdefect_le :
      quittingForcedOwnerOutsiderDefect reward root owner ≤ barrier := by
    dsimp [barrier]
    exact le_max_left _ _
  have hp0ε :
      quittingForcedOwnerAllOutsidersContinueMass root owner * ε ≤ ε := by
    nlinarith
  have herror_le :
      quittingAtomicBlockerCompletionError reward root owner ε ≤
        max 0 (-quittingAtomicBlockerBalance reward root owner) + ε := by
    unfold quittingAtomicBlockerCompletionError
    apply max_le
    · linarith
    · exact add_le_add (le_max_right _ _) hp0ε
  have herror_lt :
      quittingAtomicBlockerCompletionError reward root owner ε < η := by
    dsimp [ε] at herror_le
    nlinarith
  by_cases hwho : who = owner
  · subst who
    have hupper :=
      quittingTerminalPayoff_update_atomicBlockerCompletion_owner_le_of_owner_eq_pure
        howner hpunish.le deviation
    have hprofileOwner :
        quittingTerminalPayoff reward profile owner =
          quittingForcedOwnerObeyValue reward root owner := by
      exact quittingTerminalPayoff_atomicBlockerCompletion_of_owner_eq_pure
        howner owner
    dsimp only [profile] at hexploit hupper hprofileOwner
    linarith
  · have hupper :=
      quittingTerminalPayoff_update_atomicBlockerCompletion_outsider_le_defect
        (punishRow := punishRow) howner hwho deviation
    dsimp only [profile] at hexploit hupper hprofile
    linarith

/-- Counterexample-regime form of the every-row blocker barrier. -/
theorem QuittingCounterexampleRegime.terminalGap_le_atomicBlockerBarrier
    (regime : QuittingCounterexampleRegime reward)
    {root : ι → PMF Bool} {owner : ι}
    (howner : root owner = PMF.pure true) :
    regime.terminalGap ≤
      max (quittingForcedOwnerOutsiderDefect reward root owner)
        (max 0 (-quittingAtomicBlockerBalance reward root owner)) :=
  terminalExploitabilityGap_le_atomicBlockerBarrier howner
    regime.terminalGap_pos regime.terminalExploitability

/-- If the blocker balance is positive, the barrier is paid entirely by a
literal outsider endpoint deviation.  The witness can be chosen pure because
the outsider's Boolean mixed payoff is affine between its two endpoints. -/
theorem exists_outsider_atomicDeviation_ge_of_pos_blockerBalance
    {root : ι → PMF Bool} {owner : ι} {η : ℝ}
    (howner : root owner = PMF.pure true)
    (hη : 0 < η) (hgap : HasTerminalExploitabilityGap reward η)
    (hbalance : 0 < quittingAtomicBlockerBalance reward root owner) :
    ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
      quittingRootExpectedPayoff reward 0 root who + η ≤
        quittingRootExpectedPayoff reward 0
          (Function.update root who deviation) who := by
  have hbarrier := terminalExploitabilityGap_le_atomicBlockerBarrier
    howner hη hgap
  have hrefusal :
      max 0 (-quittingAtomicBlockerBalance reward root owner) = 0 := by
    rw [max_eq_left]
    linarith
  have hdefect : η ≤ quittingForcedOwnerOutsiderDefect reward root owner := by
    rw [hrefusal,
      max_eq_left (quittingForcedOwnerOutsiderDefect_nonneg
        reward root owner)] at hbarrier
    exact hbarrier
  letI : Nonempty ι := ⟨owner⟩
  obtain ⟨who, _hwhoMem, hsup⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (quittingForcedOwnerOutsiderCoordinateDefect reward root owner)
  have hcoordinate : η ≤
      quittingForcedOwnerOutsiderCoordinateDefect reward root owner who := by
    rw [← hsup]
    exact hdefect
  have hwho : who ≠ owner := by
    intro heq
    subst who
    simp [quittingForcedOwnerOutsiderCoordinateDefect] at hcoordinate
    linarith
  let quitValue :=
    quittingStationaryFixedOpponentsQuitValue reward root who
  let continueValue :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let obeyValue := quittingRootAbsorbingContribution reward root who
  have hrawPos : 0 < max quitValue continueValue - obeyValue := by
    by_contra hnot
    have hnonpos : max quitValue continueValue - obeyValue ≤ 0 :=
      le_of_not_gt hnot
    have hzero :
        quittingForcedOwnerOutsiderCoordinateDefect reward root owner who = 0 := by
      simp [quittingForcedOwnerOutsiderCoordinateDefect, hwho,
        quitValue, continueValue, obeyValue, max_eq_left hnonpos]
    rw [hzero] at hcoordinate
    linarith
  have hraw : η ≤ max quitValue continueValue - obeyValue := by
    simpa [quittingForcedOwnerOutsiderCoordinateDefect, hwho,
      quitValue, continueValue, obeyValue, max_eq_right hrawPos.le] using
      hcoordinate
  have hgain : obeyValue + η ≤ max quitValue continueValue := by
    linarith
  have hrootPayoff :
      quittingRootExpectedPayoff reward 0 root who = obeyValue := by
    rfl
  have hquitPayoff :
      quittingRootExpectedPayoff reward 0
          (Function.update root who (PMF.pure true)) who = quitValue := by
    rfl
  have hcontinuePayoff :
      quittingRootExpectedPayoff reward 0
          (Function.update root who (PMF.pure false)) who = continueValue := by
    rfl
  rcases le_total quitValue continueValue with hquit_le | hcontinue_le
  · refine ⟨who, hwho, PMF.pure false, ?_⟩
    rw [hrootPayoff, hcontinuePayoff]
    rwa [max_eq_right hquit_le] at hgain
  · refine ⟨who, hwho, PMF.pure true, ?_⟩
    rw [hrootPayoff, hquitPayoff]
    rwa [max_eq_left hcontinue_le] at hgain

/-- A strict owner-side coalition toggle has a quantitative outsider pivot
at the corresponding pure joined-coalition row. -/
theorem exists_outsider_atomicDeviation_ge_of_strict_ownerToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {η : ℝ} (hη : 0 < η) (hgap : HasTerminalExploitabilityGap reward η)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    (howner : owner ∉ quitters)
    (htoggle : reward ⟨quitters, hquitters⟩ owner <
      reward
        ⟨insert owner quitters,
          Finset.insert_nonempty owner quitters⟩ owner) :
    ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
      quittingRootExpectedPayoff reward 0
          (QuittingSureSetOwnerRepair.quittingPureSetRoot
            (insert owner quitters)) who + η ≤
        quittingRootExpectedPayoff reward 0
          (Function.update
            (QuittingSureSetOwnerRepair.quittingPureSetRoot
              (insert owner quitters)) who deviation) who := by
  let root := QuittingSureSetOwnerRepair.quittingPureSetRoot
    (insert owner quitters)
  have hrootOwner : root owner = PMF.pure true := by
    simp [root, QuittingSureSetOwnerRepair.quittingPureSetRoot,
      QuittingSureSetOwnerRepair.quittingSetAction]
  have hbalance : 0 < quittingAtomicBlockerBalance reward root owner := by
    rw [show quittingAtomicBlockerBalance reward root owner =
      quittingAtomicBlockerBalance reward
        (QuittingSureSetOwnerRepair.quittingPureSetRoot
          (insert owner quitters)) owner by rfl,
      quittingAtomicBlockerBalance_pure_ownerToggle reward owner quitters
        hquitters howner]
    linarith
  exact exists_outsider_atomicDeviation_ge_of_pos_blockerBalance
    hrootOwner hη hgap hbalance

/-! ## A finite mountain-pass dichotomy -/

/-- Along any finite word of forced-owner rows which starts at positive
blocker balance and ends below `-η`, the first nonpositive row either lies on
the outsider defect wall or the preceding edge makes a blocker-balance drop
strictly larger than `η / 2`.

This is the discrete polygonal mountain-pass form needed by fractional reset
words.  No regularity of the chosen word is assumed: a coarse crossing is
retained explicitly rather than hidden in a continuity argument. -/
theorem exists_atomicBlockerDefect_or_balanceDrop_on_finiteWord
    (roots : ℕ → ι → PMF Bool) (owner : ι) {cutoff : ℕ} {η : ℝ}
    (howner : ∀ time, time ≤ cutoff →
      roots time owner = PMF.pure true)
    (hη : 0 < η) (hgap : HasTerminalExploitabilityGap reward η)
    (hstart : 0 < quittingAtomicBlockerBalance reward (roots 0) owner)
    (hend : quittingAtomicBlockerBalance reward (roots cutoff) owner ≤ -η) :
    ∃ time, time < cutoff ∧
      (η / 2 <
          quittingAtomicBlockerBalance reward (roots time) owner -
            quittingAtomicBlockerBalance reward (roots (time + 1)) owner ∨
        η ≤ quittingForcedOwnerOutsiderDefect reward (roots (time + 1))
          owner) := by
  let balance : ℕ → ℝ := fun time =>
    quittingAtomicBlockerBalance reward (roots time) owner
  have hcutoffNonpos : balance cutoff ≤ 0 := by
    dsimp [balance]
    linarith
  have hexists : ∃ time, time ≤ cutoff ∧ balance time ≤ 0 :=
    ⟨cutoff, le_rfl, hcutoffNonpos⟩
  let first := Nat.find hexists
  have hfirstSpec : first ≤ cutoff ∧ balance first ≤ 0 :=
    Nat.find_spec hexists
  have hfirstPos : 0 < first := by
    by_contra hnot
    have hfirstZero : first = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hfirstZero] at hfirstSpec
    linarith
  let previous := first - 1
  have hpreviousLtFirst : previous < first := by
    dsimp [previous]
    omega
  have hpreviousLeCutoff : previous ≤ cutoff :=
    hpreviousLtFirst.le.trans hfirstSpec.1
  have hpreviousPos : 0 < balance previous := by
    have hminimal := Nat.find_min hexists hpreviousLtFirst
    by_contra hnot
    exact hminimal ⟨hpreviousLeCutoff, le_of_not_gt hnot⟩
  have hpreviousSucc : previous + 1 = first := by
    dsimp [previous]
    omega
  refine ⟨previous, hpreviousLtFirst.trans_le hfirstSpec.1, ?_⟩
  by_cases hlargeDropLanding : balance first < -η / 2
  · left
    rw [hpreviousSucc]
    linarith
  · right
    have hlandingLower : -η / 2 ≤ balance first :=
      le_of_not_gt hlargeDropLanding
    have hbarrier := terminalExploitabilityGap_le_atomicBlockerBarrier
      (howner first hfirstSpec.1) hη hgap
    have hrefusal : max 0 (-balance first) = -balance first := by
      rw [max_eq_right]
      linarith
    have hrefusalLt : -balance first < η := by
      linarith
    rw [hpreviousSucc]
    change η ≤ quittingForcedOwnerOutsiderDefect reward (roots first) owner
    rw [show quittingAtomicBlockerBalance reward (roots first) owner =
      balance first by rfl, hrefusal] at hbarrier
    by_contra hnot
    have hdefectLt :
        quittingForcedOwnerOutsiderDefect reward (roots first) owner < η :=
      lt_of_not_ge hnot
    exact (not_lt_of_ge hbarrier) (max_lt hdefectLt hrefusalLt)

end GameTheory
