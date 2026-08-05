/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingOwnerSoloCertification
import Math.PMFProduct.Update

/-!
# Repair by a sure quitting set and one owner hazard

Fix a nonempty set `T` of sure quitters and a player `owner ∉ T`.  The
stationary root studied here makes every player in `T` quit surely, makes the
owner quit with probability `p`, and makes every remaining player continue.

The root has only two on-path terminal sets, `T` and `insert owner T`.  This
file computes that mixture and the exact stationary unilateral caps.  The
singleton case `T = {who}` is kept separate: if its unique sure quitter
continues, the owner hazard is the only remaining source of absorption, so
the selected `Never` value is a genuine recurrence quotient rather than a
zero-tail shortcut.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The payoff of a quitter set, extended by zero at the empty set. -/
def quittingSetReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) : ℝ :=
  if hS : S.Nonempty then reward ⟨S, hS⟩ who else 0

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingSetReward_of_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {S : Finset ι} (hS : S.Nonempty) (who : ι) :
    quittingSetReward reward S who = reward ⟨S, hS⟩ who := by
  simp [quittingSetReward, hS]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingSetReward_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingSetReward reward ∅ who = 0 := by
  simp [quittingSetReward]

/-- The pure Boolean action whose quitter set is exactly `T`. -/
def quittingSetAction (T : Finset ι) : ι → Bool :=
  fun who ↦ if who ∈ T then true else false

omit [Fintype ι] in
@[simp] theorem quittingSetAction_eq_true_iff
    (T : Finset ι) (who : ι) :
    quittingSetAction T who = true ↔ who ∈ T := by
  simp [quittingSetAction]

@[simp] theorem quittingQuitters_setAction (T : Finset ι) :
    quittingQuitters (quittingSetAction T) = T := by
  ext who
  simp [quittingQuitters]

/-- The pure product root associated with a quitter set. -/
def quittingPureSetRoot (T : Finset ι) : ι → PMF Bool :=
  fun who ↦ PMF.pure (quittingSetAction T who)

/-- Every player in `T` quits surely, and `owner` quits with hazard `p`. -/
def quittingSureSetOwnerRoot
    (T : Finset ι) (owner : ι)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ι → PMF Bool :=
  Function.update (quittingPureSetRoot T) owner
    (quittingHazardCoin p hp0 hp1)

/-- The on-path mixture between `T` and `insert owner T`. -/
def quittingSureSetOwnerValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (T : Finset ι) (owner : ι) (p : ℝ) : Payoff ι :=
  fun who ↦
    (1 - p) * quittingSetReward reward T who +
      p * quittingSetReward reward (insert owner T) who

omit [Fintype ι] in
@[simp] theorem update_quittingSetAction_owner_false
    {T : Finset ι} {owner : ι} (howner : owner ∉ T) :
    Function.update (quittingSetAction T) owner false =
      quittingSetAction T := by
  funext who
  by_cases hwho : who = owner
  · subst who
    simp [quittingSetAction, howner]
  · simp [Function.update, hwho]

omit [Fintype ι] in
@[simp] theorem update_quittingSetAction_owner_true
    {T : Finset ι} {owner : ι} :
    Function.update (quittingSetAction T) owner true =
      quittingSetAction (insert owner T) := by
  funext who
  by_cases hwho : who = owner
  · subst who
    simp [quittingSetAction]
  · simp [Function.update, quittingSetAction, hwho]

omit [Fintype ι] in
theorem update_quittingPureSetRoot_eq
    (T : Finset ι) (owner : ι) (ownerQuits : Bool) :
    Function.update (quittingPureSetRoot T) owner (PMF.pure ownerQuits) =
      fun who ↦ PMF.pure
        (Function.update (quittingSetAction T) owner ownerQuits who) := by
  funext who
  by_cases hwho : who = owner
  · subst who
    simp
  · simp [quittingPureSetRoot, Function.update, hwho]

/-- Exact two-point disintegration of the sure-set/owner product root. -/
theorem expect_pmfPi_quittingSureSetOwnerRoot
    {T : Finset ι} {owner : ι} (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) :
    expect (pmfPi (quittingSureSetOwnerRoot T owner p hp0 hp1)) f =
      (1 - p) * f (quittingSetAction T) +
        p * f (quittingSetAction (insert owner T)) := by
  unfold quittingSureSetOwnerRoot
  rw [pmfPi_update_bind, expect_bind]
  simp_rw [update_quittingPureSetRoot_eq, pmfPi_pure, expect_pure]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp only [quittingHazardCoin_false_toReal,
    quittingHazardCoin_true_toReal]
  rw [update_quittingSetAction_owner_false howner,
    update_quittingSetAction_owner_true]
  ring

omit [Fintype ι] in
/-- A member of `T` remains a sure quitter in the owner-hazard root. -/
theorem rootHasSureQuitter_quittingSureSetOwnerRoot
    {T : Finset ι} {owner sure : ι} (hsure : sure ∈ T)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuittingRootHasSureQuitter
      (quittingSureSetOwnerRoot T owner p hp0 hp1) := by
  refine ⟨sure, ?_⟩
  have hne : sure ≠ owner := by
    intro h
    subst sure
    exact howner hsure
  simp [quittingSureSetOwnerRoot, quittingPureSetRoot,
    quittingSetAction, hne, hsure]

/-! ## On-path payoff -/

@[simp] theorem quittingRootPayoff_zero_setAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingRootPayoff reward (0 : Payoff ι)
        (quittingSetAction S) who =
      quittingSetReward reward S who := by
  unfold quittingRootPayoff quittingSetReward
  rw [quittingQuitters_setAction]
  by_cases hS : S.Nonempty <;> simp [hS]

/-- The absorbing contribution of a pure set root is its extended set
reward. -/
theorem quittingRootAbsorbingContribution_pureSetRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingRootAbsorbingContribution reward
        (quittingPureSetRoot S) who =
      quittingSetReward reward S who := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    quittingPureSetRoot
  rw [pmfPi_pure, expect_pure]
  exact quittingRootPayoff_zero_setAction reward S who

/-- Exact absorbing mixture of the sure-set/owner root. -/
theorem quittingRootAbsorbingContribution_sureSetOwnerRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner : ι} (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (who : ι) :
    quittingRootAbsorbingContribution reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who =
      quittingSureSetOwnerValue reward T owner p who := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_quittingSureSetOwnerRoot howner,
    quittingRootPayoff_zero_setAction,
    quittingRootPayoff_zero_setAction]
  rfl

/-- A nonempty sure set makes the stationary profile absorb immediately, so
its terminal payoff is exactly the two-set mixture. -/
theorem terminalPayoff_sureSetOwnerRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner : ι} (hT : T.Nonempty)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (who : ι) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward
          (quittingSureSetOwnerRoot T owner p hp0 hp1)) who =
      quittingSureSetOwnerValue reward T owner p who := by
  obtain ⟨sure, hsure⟩ := hT
  let root := quittingSureSetOwnerRoot T owner p hp0 hp1
  have hsureRoot : QuittingRootHasSureQuitter root :=
    rootHasSureQuitter_quittingSureSetOwnerRoot hsure howner p hp0 hp1
  rw [quittingTerminalPayoff_stationary_eq_rootExpectedPayoff]
  rw [quittingRootExpectedPayoff_eq_of_hasSureQuitter
    reward root hsureRoot
    (fun player ↦ quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player)
    (0 : Payoff ι) who]
  exact quittingRootAbsorbingContribution_sureSetOwnerRoot
    reward howner p hp0 hp1 who

/-! ## Updating the selected coordinate -/

omit [Fintype ι] in
@[simp] theorem update_quittingPureSetRoot_true
    (T : Finset ι) (who : ι) :
    Function.update (quittingPureSetRoot T) who (PMF.pure true) =
      quittingPureSetRoot (insert who T) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingPureSetRoot, quittingSetAction]
  · simp [quittingPureSetRoot, quittingSetAction,
      Function.update, hplayer]

omit [Fintype ι] in
@[simp] theorem update_quittingPureSetRoot_false
    (T : Finset ι) (who : ι) :
    Function.update (quittingPureSetRoot T) who (PMF.pure false) =
      quittingPureSetRoot (T.erase who) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingPureSetRoot, quittingSetAction]
  · simp [quittingPureSetRoot, quittingSetAction,
      Function.update, hplayer]

omit [Fintype ι] in
theorem update_sureSetOwnerRoot_owner_true
    {T : Finset ι} {owner : ι}
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Function.update (quittingSureSetOwnerRoot T owner p hp0 hp1)
        owner (PMF.pure true) =
      quittingPureSetRoot (insert owner T) := by
  simp [quittingSureSetOwnerRoot]

omit [Fintype ι] in
theorem update_sureSetOwnerRoot_owner_false
    {T : Finset ι} {owner : ι} (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Function.update (quittingSureSetOwnerRoot T owner p hp0 hp1)
        owner (PMF.pure false) =
      quittingPureSetRoot T := by
  rw [quittingSureSetOwnerRoot, Function.update_idem]
  exact update_quittingPureSetRoot_false T owner |>.trans (by
    congr
    exact Finset.erase_eq_of_notMem howner)

omit [Fintype ι] in
theorem update_sureSetOwnerRoot_other_true
    {T : Finset ι} {owner who : ι} (hne : who ≠ owner)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Function.update (quittingSureSetOwnerRoot T owner p hp0 hp1)
        who (PMF.pure true) =
      quittingSureSetOwnerRoot (insert who T) owner p hp0 hp1 := by
  unfold quittingSureSetOwnerRoot
  rw [Function.update_comm (f := quittingPureSetRoot T)
    (a := owner) (b := who) hne.symm]
  simp

omit [Fintype ι] in
theorem update_sureSetOwnerRoot_other_false
    {T : Finset ι} {owner who : ι} (hne : who ≠ owner)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Function.update (quittingSureSetOwnerRoot T owner p hp0 hp1)
        who (PMF.pure false) =
      quittingSureSetOwnerRoot (T.erase who) owner p hp0 hp1 := by
  unfold quittingSureSetOwnerRoot
  rw [Function.update_comm (f := quittingPureSetRoot T)
    (a := owner) (b := who) hne.symm]
  simp

/-! ## Exact fixed-opponent data -/

theorem fixedOpponentsQuitValue_sureSetOwnerRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner : ι}
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) owner =
      quittingSetReward reward (insert owner T) owner := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
  rw [update_sureSetOwnerRoot_owner_true,
    quittingRootAbsorbingContribution_pureSetRoot]

theorem fixedOpponentsContinueReward_sureSetOwnerRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner : ι} (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) owner =
      quittingSetReward reward T owner := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  rw [update_sureSetOwnerRoot_owner_false howner,
    quittingRootAbsorbingContribution_pureSetRoot]

theorem fixedOpponentsQuitValue_sureSetOwnerRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner who : ι} (howner : owner ∉ T)
    (hne : who ≠ owner)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who =
      quittingSureSetOwnerValue reward (insert who T) owner p who := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
  rw [update_sureSetOwnerRoot_other_true hne]
  apply quittingRootAbsorbingContribution_sureSetOwnerRoot
  simp [howner, Ne.symm hne]

theorem fixedOpponentsContinueReward_sureSetOwnerRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner who : ι} (howner : owner ∉ T)
    (hne : who ≠ owner)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who =
      quittingSureSetOwnerValue reward (T.erase who) owner p who := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  rw [update_sureSetOwnerRoot_other_false hne]
  apply quittingRootAbsorbingContribution_sureSetOwnerRoot
  simp [howner]

theorem stationaryContinueMass_pureSetRoot_of_nonempty
    {T : Finset ι} (hT : T.Nonempty) :
    quittingStationaryContinueMass (quittingPureSetRoot T) = 0 := by
  obtain ⟨sure, hsure⟩ := hT
  have hsureRoot : QuittingRootHasSureQuitter
      (quittingPureSetRoot T) := by
    refine ⟨sure, ?_⟩
    simp [quittingPureSetRoot, quittingSetAction, hsure]
  change ((pmfPi (quittingPureSetRoot T))
    (fun _ : ι ↦ false)).toReal = 0
  rw [(quittingRootHasSureQuitter_iff_allContinue_mass_zero
    (quittingPureSetRoot T)).mp hsureRoot]
  simp

theorem stationaryContinueMass_sureSetOwnerRoot_of_nonempty
    {T : Finset ι} {owner : ι} (hT : T.Nonempty)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryContinueMass
        (quittingSureSetOwnerRoot T owner p hp0 hp1) = 0 := by
  obtain ⟨sure, hsure⟩ := hT
  have hsureRoot := rootHasSureQuitter_quittingSureSetOwnerRoot
    hsure howner p hp0 hp1
  change ((pmfPi (quittingSureSetOwnerRoot T owner p hp0 hp1))
    (fun _ : ι ↦ false)).toReal = 0
  rw [(quittingRootHasSureQuitter_iff_allContinue_mass_zero
    (quittingSureSetOwnerRoot T owner p hp0 hp1)).mp hsureRoot]
  simp

theorem stationaryContinueMass_sureSetOwnerRoot_empty
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryContinueMass
        (quittingSureSetOwnerRoot ∅ owner p hp0 hp1) = 1 - p := by
  have hroot : quittingSureSetOwnerRoot ∅ owner p hp0 hp1 =
      quittingSoloStationaryRoot owner
        (quittingHazardCoin p hp0 hp1) := by
    unfold quittingSureSetOwnerRoot quittingSoloStationaryRoot
    congr 1
  rw [hroot, quittingStationaryContinueMass_solo]
  simp

theorem fixedOpponentsContinueMass_sureSetOwnerRoot_owner
    {T : Finset ι} {owner : ι} (hT : T.Nonempty)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSureSetOwnerRoot T owner p hp0 hp1) owner = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_sureSetOwnerRoot_owner_false howner,
    stationaryContinueMass_pureSetRoot_of_nonempty hT]

theorem fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_nonempty
    {T : Finset ι} {owner who : ι} (howner : owner ∉ T)
    (hne : who ≠ owner) (herase : (T.erase who).Nonempty)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_sureSetOwnerRoot_other_false hne]
  apply stationaryContinueMass_sureSetOwnerRoot_of_nonempty herase
  simp [howner]

theorem fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_empty
    {T : Finset ι} {owner who : ι} (hne : who ≠ owner)
    (herase : T.erase who = ∅)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who = 1 - p := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_sureSetOwnerRoot_other_false hne, herase,
    stationaryContinueMass_sureSetOwnerRoot_empty]

/-! ## Exact unilateral caps -/

omit [Fintype ι] in
@[simp] theorem quittingSureSetOwnerValue_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) (p : ℝ) :
    quittingSureSetOwnerValue reward ∅ owner p who =
      p * quittingSetReward reward {owner} who := by
  simp [quittingSureSetOwnerValue]

/-- Closed form of the complete behavioral unilateral cap.  For `owner`,
the alternatives are joining `T` and leaving `T` alone.  A different player
either leaves a nonempty sure set, or is the unique member of `T`; in the
latter case its `Never` value is the reward of the owner's singleton exit. -/
def quittingSureSetOwnerExactCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (T : Finset ι) (owner : ι) (p : ℝ) (who : ι) : ℝ :=
  if who = owner then
    max (quittingSetReward reward (insert owner T) owner)
      (quittingSetReward reward T owner)
  else if (T.erase who).Nonempty then
    max (quittingSureSetOwnerValue reward (insert who T) owner p who)
      (quittingSureSetOwnerValue reward (T.erase who) owner p who)
  else
    max (quittingSureSetOwnerValue reward (insert who T) owner p who)
      (quittingSetReward reward {owner} who)

theorem unilateralCap_sureSetOwnerRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner : ι} (hT : T.Nonempty)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryUnilateralCap reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) owner =
      max (quittingSetReward reward (insert owner T) owner)
        (quittingSetReward reward T owner) := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [fixedOpponentsQuitValue_sureSetOwnerRoot_owner,
    fixedOpponentsContinueReward_sureSetOwnerRoot_owner reward howner,
    fixedOpponentsContinueMass_sureSetOwnerRoot_owner hT howner]
  simp

theorem unilateralCap_sureSetOwnerRoot_other_of_erase_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner who : ι} (howner : owner ∉ T)
    (hne : who ≠ owner) (herase : (T.erase who).Nonempty)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryUnilateralCap reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who =
      max (quittingSureSetOwnerValue reward (insert who T) owner p who)
        (quittingSureSetOwnerValue reward (T.erase who) owner p who) := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [fixedOpponentsQuitValue_sureSetOwnerRoot_other reward howner hne,
    fixedOpponentsContinueReward_sureSetOwnerRoot_other reward howner hne,
    fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_nonempty
      howner hne herase]
  simp

theorem unilateralCap_sureSetOwnerRoot_other_of_erase_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner who : ι} (howner : owner ∉ T)
    (hne : who ≠ owner) (herase : T.erase who = ∅)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p) :
    quittingStationaryUnilateralCap reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who =
      max (quittingSureSetOwnerValue reward (insert who T) owner p who)
        (quittingSetReward reward {owner} who) := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [fixedOpponentsQuitValue_sureSetOwnerRoot_other reward howner hne,
    fixedOpponentsContinueReward_sureSetOwnerRoot_other reward howner hne,
    fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_empty
      hne herase,
    herase, quittingSureSetOwnerValue_empty]
  have hpne : p ≠ 0 := ne_of_gt hp
  congr 1
  field_simp [hpne]
  ring

/-- The exact cap formula, valid at every positive hazard `p ≤ 1`. -/
theorem unilateralCap_sureSetOwnerRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner : ι} (hT : T.Nonempty)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p)
    (who : ι) :
    quittingStationaryUnilateralCap reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who =
      quittingSureSetOwnerExactCap reward T owner p who := by
  by_cases hwho : who = owner
  · subst who
    rw [unilateralCap_sureSetOwnerRoot_owner reward hT howner]
    simp [quittingSureSetOwnerExactCap]
  · by_cases herase : (T.erase who).Nonempty
    · rw [unilateralCap_sureSetOwnerRoot_other_of_erase_nonempty
        reward howner hwho herase]
      simp [quittingSureSetOwnerExactCap, hwho, herase]
    · have heraseEq : T.erase who = ∅ := Finset.not_nonempty_iff_eq_empty.mp herase
      rw [unilateralCap_sureSetOwnerRoot_other_of_erase_empty
        reward howner hwho heraseEq p hp0 hp1 hp]
      simp [quittingSureSetOwnerExactCap, hwho, herase]

/-- Every selected coordinate is strictly contracting at positive owner
hazard. -/
theorem fixedOpponentsContinueMass_sureSetOwnerRoot_lt_one
    {T : Finset ι} {owner : ι} (hT : T.Nonempty)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p)
    (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSureSetOwnerRoot T owner p hp0 hp1) who < 1 := by
  by_cases hwho : who = owner
  · subst who
    rw [fixedOpponentsContinueMass_sureSetOwnerRoot_owner hT howner]
    norm_num
  · by_cases herase : (T.erase who).Nonempty
    · rw [fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_nonempty
        howner hwho herase]
      norm_num
    · have heraseEq : T.erase who = ∅ := Finset.not_nonempty_iff_eq_empty.mp herase
      rw [fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_empty
        hwho heraseEq]
      linarith

/-- Exact full-rate sure-set repair criterion.  It deliberately retains both
endpoint mixtures: in particular the criterion can hold at `p = 1` even when
its small-`p` limiting inequalities fail. -/
theorem isεAsymptoticNash_sureSetOwnerRoot_of_exactCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner : ι} (hT : T.Nonempty)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p)
    (ε : ℝ)
    (hcap : ∀ who,
      quittingSureSetOwnerExactCap reward T owner p who ≤
        quittingSureSetOwnerValue reward T owner p who + ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingStationaryProfile reward
        (quittingSureSetOwnerRoot T owner p hp0 hp1)) := by
  apply isεAsymptoticNash_stationary_of_unilateralCap_le
  · exact fixedOpponentsContinueMass_sureSetOwnerRoot_lt_one
      hT howner p hp0 hp1 hp
  · intro who
    rw [unilateralCap_sureSetOwnerRoot reward hT howner p hp0 hp1 hp who,
      terminalPayoff_sureSetOwnerRoot reward hT howner p hp0 hp1 who]
    exact hcap who

/-- Exact semantic characterization of terminal approximate Nash for the
full-rate sure-set/owner root.  Thus a strict exact-cap gap produces an
actual deterministic-time deviation, not merely failure of a surrogate
certificate. -/
theorem isεAsymptoticNash_sureSetOwnerRoot_iff_exactCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {T : Finset ι} {owner : ι} (hT : T.Nonempty)
    (howner : owner ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p)
    (ε : ℝ) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward
          (quittingSureSetOwnerRoot T owner p hp0 hp1)) ↔
      ∀ who,
        quittingSureSetOwnerExactCap reward T owner p who ≤
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward
              (quittingSureSetOwnerRoot T owner p hp0 hp1)) who + ε := by
  rw [isεAsymptoticNash_stationary_iff_unilateralCap_le reward
    (quittingSureSetOwnerRoot T owner p hp0 hp1) ε
    (fixedOpponentsContinueMass_sureSetOwnerRoot_lt_one
      hT howner p hp0 hp1 hp)]
  constructor
  · intro hcap who
    rw [← unilateralCap_sureSetOwnerRoot
      reward hT howner p hp0 hp1 hp who]
    exact hcap who
  · intro hcap who
    rw [unilateralCap_sureSetOwnerRoot
      reward hT howner p hp0 hp1 hp who]
    exact hcap who

end QuittingSureSetOwnerRepair

end GameTheory
