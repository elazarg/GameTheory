/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.FirstLayerSimple
import UniformEquilibrium.Quitting.Cycles.ConditionedSoloExtraction

/-!
# The later-layer corrected all-abnormal branch

This file closes the part of the corrected all-abnormal regime left open by
`FirstLayerSimple.lean`.  If the corrected core is empty but its first layer
is nonempty, choose the last nonempty layer and an owner in it.  The owner's
normalized singleton column is nonnegative for every receiver, while
membership in the first layer supplies a distinct blocker whose singleton
column is nonpositive in the owner's row.

At rate `p`, let the owner quit with probability `p`, the blocker with
probability `p^2`, and every other player Continue.  The owner dominates the
conditional absorbing law; the blocker's smaller hazard makes refusing safe
for the owner.  Every unilateral cap is within
`6 * quittingRewardBound reward * p` of the stationary payoff.  Sending `p`
to zero gives terminal approximate Nash profiles at every accuracy, hence a
uniform-equilibrium payoff.

## Convention warning

The published displayed normal-layer recursion omits the condition that the
witness differ from the receiver.  With the normalized zero diagonal that
printed recursion never removes a player.  The theorem below is therefore a
theorem about this repository's corrected distinct-witness recursion, which
is the recursion used by the source proof's last-layer argument; it is not a
literal theorem about `printedNormalLayer`.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Finite corrected-layer algebra -/

/-- Membership in a later corrected layer implies membership in every
earlier layer. -/
theorem normalLayer_antitone
    (M : ι → ι → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    normalLayer M n ⊆ normalLayer M m := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact fun _ h => h
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
      · exact fun _ h => h
      · exact (normalLayer_succ_subset M n).trans
          (ih (Nat.le_of_lt_succ hlt))

/-- If a receiver can use a player surviving to layer `n` as a nonpositive
distinct witness, then the receiver itself survives to layer `n`. -/
theorem mem_normalLayer_of_persistent_witness
    (M : ι → ι → ℝ) {receiver witness : ι} (hne : witness ≠ receiver)
    (hentry : M receiver witness ≤ 0) :
    ∀ {n : ℕ}, witness ∈ normalLayer M n → receiver ∈ normalLayer M n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hwitness
      have hwitnessPrev := (mem_normalLayer_succ M n witness).mp hwitness |>.1
      have hreceiverPrev := ih hwitnessPrev
      exact (mem_normalLayer_succ M n receiver).2
        ⟨hreceiverPrev, witness, hwitnessPrev, hne, hentry⟩

/-- Empty corrected core forces one finite layer to be empty.  The proof is
the finite-witness argument: every player has a layer at which it disappears;
the sum of those finitely many witness indices is later than all of them. -/
theorem exists_normalLayer_eq_empty_of_normalCore_eq_empty
    (M : ι → ι → ℝ) (hcore : normalCore M = ∅) :
    ∃ n : ℕ, normalLayer M n = ∅ := by
  classical
  have hmissing : ∀ i : ι, ∃ n : ℕ, i ∉ normalLayer M n := by
    intro i
    by_contra h
    have hall : ∀ n : ℕ, i ∈ normalLayer M n := by
      intro n
      exact Classical.byContradiction fun hn => h ⟨n, hn⟩
    have hicore : i ∈ normalCore M := (mem_normalCore M i).2 hall
    rw [hcore] at hicore
    simp at hicore
  choose firstMissing hfirstMissing using hmissing
  let cutoff : ℕ := ∑ i : ι, firstMissing i
  refine ⟨cutoff, Finset.not_nonempty_iff_eq_empty.mp ?_⟩
  rintro ⟨i, hi⟩
  have hle : firstMissing i ≤ cutoff := by
    dsimp only [cutoff]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact hfirstMissing i (normalLayer_antitone M hle hi)

/-- If the corrected core is empty but layer one is nonempty, there is a last
nonempty layer. -/
theorem exists_last_nonempty_normalLayer
    (M : ι → ι → ℝ) (hcore : normalCore M = ∅)
    (hfirst : normalLayer M 1 ≠ ∅) :
    ∃ last : ℕ, 1 ≤ last ∧ normalLayer M last ≠ ∅ ∧
      normalLayer M (last + 1) = ∅ := by
  classical
  let emptyAt : ℕ := Nat.find (exists_normalLayer_eq_empty_of_normalCore_eq_empty M hcore)
  have hempty : normalLayer M emptyAt = ∅ := Nat.find_spec
    (exists_normalLayer_eq_empty_of_normalCore_eq_empty M hcore)
  have hone_lt : 1 < emptyAt := by
    have hzero : emptyAt ≠ 0 := by
      intro h
      have hzeroEmpty : normalLayer M 0 = ∅ := by simpa [h] using hempty
      apply hfirst
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨i, hi⟩
      have hi0 := normalLayer_succ_subset M 0 hi
      rw [hzeroEmpty] at hi0
      simp at hi0
    have hone : emptyAt ≠ 1 := by
      intro h
      exact hfirst (by simpa [h] using hempty)
    omega
  let last := emptyAt - 1
  have hlast : last + 1 = emptyAt := by
    dsimp only [last]
    omega
  have hlastNonempty : normalLayer M last ≠ ∅ := by
    intro hlastEmpty
    have hminimal := Nat.find_min'
      (exists_normalLayer_eq_empty_of_normalCore_eq_empty M hcore) hlastEmpty
    dsimp only [last] at hminimal
    omega
  refine ⟨last, ?_, hlastNonempty, ?_⟩
  · dsimp only [last]
    omega
  · rwa [hlast]

/-- At the last nonempty corrected layer, any selected owner's matrix column
is nonnegative everywhere, and strictly positive away from the diagonal. -/
theorem nonnegative_column_of_last_normalLayer
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    {last : ℕ} (hnext : normalLayer M (last + 1) = ∅)
    {owner : ι} (howner : owner ∈ normalLayer M last) :
    ∀ receiver, 0 ≤ M receiver owner := by
  intro receiver
  by_cases hsame : receiver = owner
  · subst receiver
    rw [hdiag]
  · apply le_of_not_gt
    intro hnegative
    have hreceiver := mem_normalLayer_of_persistent_witness M
      (receiver := receiver) (witness := owner) (Ne.symm hsame)
      hnegative.le howner
    have hmem : receiver ∈ normalLayer M (last + 1) :=
      (mem_normalLayer_succ M last receiver).2
        ⟨hreceiver, owner, howner, Ne.symm hsame, hnegative.le⟩
    rw [hnext] at hmem
    simp at hmem

/-- Any owner in a positive corrected layer has a distinct nonpositive
first-layer witness. -/
theorem exists_firstLayer_blocker_of_mem_normalLayer
    (M : ι → ι → ℝ) {last : ℕ} (hlast : 1 ≤ last)
    {owner : ι} (howner : owner ∈ normalLayer M last) :
    ∃ blocker, blocker ≠ owner ∧ M owner blocker ≤ 0 := by
  have hownerOne : owner ∈ normalLayer M 1 :=
    normalLayer_antitone M hlast howner
  have h := (mem_normalLayer_succ M 0 owner).mp (by simpa using hownerOne)
  rcases h.2 with ⟨blocker, _, hne, hnonpos⟩
  exact ⟨blocker, hne, hnonpos⟩

/-! ## The owner/blocker stationary row -/

/-- Owner hazard `p`, blocker hazard `p^2`, all other hazards zero. -/
def laterAbnormalRoot (owner blocker : ι) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ι → PMF Bool :=
  Function.update
    (quittingSoloStationaryRoot owner (quittingHazardCoin p hp0 hp1)) blocker
    (quittingHazardCoin (p ^ 2) (sq_nonneg p)
      (pow_le_one₀ hp0 hp1))

omit [Fintype ι] in
@[simp] theorem laterAbnormalRoot_owner
    {owner blocker : ι} (hne : blocker ≠ owner) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    laterAbnormalRoot owner blocker p hp0 hp1 owner =
      quittingHazardCoin p hp0 hp1 := by
  simp [laterAbnormalRoot, quittingSoloStationaryRoot, Ne.symm hne]

omit [Fintype ι] in
@[simp] theorem laterAbnormalRoot_blocker
    (owner blocker : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    laterAbnormalRoot owner blocker p hp0 hp1 blocker =
      quittingHazardCoin (p ^ 2) (sq_nonneg p) (pow_le_one₀ hp0 hp1) := by
  simp [laterAbnormalRoot]

omit [Fintype ι] in
theorem laterAbnormalRoot_other
    {owner blocker other : ι} (howner : other ≠ owner)
    (hblocker : other ≠ blocker) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    laterAbnormalRoot owner blocker p hp0 hp1 other = PMF.pure false := by
  simp [laterAbnormalRoot, quittingSoloStationaryRoot, howner, hblocker]

omit [Fintype ι] in
theorem update_laterAbnormalRoot_owner_continue
    {owner blocker : ι} (hne : blocker ≠ owner) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Function.update (laterAbnormalRoot owner blocker p hp0 hp1) owner
        (PMF.pure false) =
      quittingSoloStationaryRoot blocker
        (quittingHazardCoin (p ^ 2) (sq_nonneg p) (pow_le_one₀ hp0 hp1)) := by
  unfold laterAbnormalRoot quittingSoloStationaryRoot
  rw [Function.update_comm hne, Function.update_idem]
  simp

omit [Fintype ι] in
theorem update_laterAbnormalRoot_blocker_continue
    {owner blocker : ι} (hne : blocker ≠ owner) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Function.update (laterAbnormalRoot owner blocker p hp0 hp1) blocker
        (PMF.pure false) =
      quittingSoloStationaryRoot owner (quittingHazardCoin p hp0 hp1) := by
  funext who
  by_cases hwhoOwner : who = owner
  · subst who
    simp [laterAbnormalRoot, quittingSoloStationaryRoot, Ne.symm hne]
  · by_cases hwhoBlocker : who = blocker
    · subst who
      simp [laterAbnormalRoot, quittingSoloStationaryRoot, hne]
    · simp [laterAbnormalRoot, quittingSoloStationaryRoot,
        hwhoOwner, hwhoBlocker]

omit [Fintype ι] in
theorem update_laterAbnormalRoot_other_continue
    {owner blocker other : ι} (howner : other ≠ owner)
    (hblocker : other ≠ blocker) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Function.update (laterAbnormalRoot owner blocker p hp0 hp1) other
        (PMF.pure false) =
      laterAbnormalRoot owner blocker p hp0 hp1 := by
  rw [← laterAbnormalRoot_other howner hblocker p hp0 hp1]
  exact Function.update_eq_self other _

/-- The joint Continue mass of the two-scale row. -/
theorem laterAbnormalRoot_continueMass
    {owner blocker : ι} (hne : blocker ≠ owner) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryContinueMass
        (laterAbnormalRoot owner blocker p hp0 hp1) =
      (1 - p ^ 2) * (1 - p) := by
  rw [quittingStationaryContinueMass_eq_forcedContinue_mul_own
    (laterAbnormalRoot owner blocker p hp0 hp1) owner,
    update_laterAbnormalRoot_owner_continue hne,
    quittingStationaryContinueMass_solo,
    laterAbnormalRoot_owner hne,
    quittingHazardCoin_false_toReal,
    quittingHazardCoin_false_toReal]

/-- The one-stage absorption probability lies between `p` and `2p`. -/
theorem laterAbnormalRoot_absorption_bounds
    {owner blocker : ι} (hne : blocker ≠ owner) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ≤ quittingRootAbsorptionMass
        (laterAbnormalRoot owner blocker p hp0 hp1) ∧
      quittingRootAbsorptionMass
        (laterAbnormalRoot owner blocker p hp0 hp1) ≤ 2 * p := by
  rw [quittingRootAbsorptionMass, laterAbnormalRoot_continueMass hne]
  constructor <;> nlinarith [sq_nonneg p, mul_nonneg hp0 (sub_nonneg.mpr hp1)]

/-- Deleting the owner leaves precisely the blocker's `p^2` absorption
hazard. -/
theorem laterAbnormalRoot_owner_opponentAbsorption
    {owner blocker : ι} (hne : blocker ≠ owner) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootOpponentAbsorptionMass
        (laterAbnormalRoot owner blocker p hp0 hp1) owner = p ^ 2 := by
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  rw [update_laterAbnormalRoot_owner_continue hne,
    quittingStationaryContinueMass_solo,
    quittingHazardCoin_false_toReal]
  ring

/-- Every unilateral problem contracts because each player faces at least one
positive opponent hazard. -/
theorem laterAbnormalRoot_fixedOpponents_contracts
    {owner blocker : ι} (hne : blocker ≠ owner) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ who, quittingStationaryFixedOpponentsContinueMass
      (laterAbnormalRoot owner blocker p hp.le hp1) who < 1 := by
  intro who
  by_cases hwho : who = owner
  · subst who
    change quittingStationaryContinueMass
      (Function.update (laterAbnormalRoot owner blocker p hp.le hp1) owner
        (PMF.pure false)) < 1
    rw [update_laterAbnormalRoot_owner_continue hne,
      quittingStationaryContinueMass_solo,
      quittingHazardCoin_false_toReal]
    nlinarith [sq_pos_of_pos hp]
  · change quittingStationaryContinueMass
      (Function.update (laterAbnormalRoot owner blocker p hp.le hp1) who
        (PMF.pure false)) < 1
    have hle := quittingStationaryContinueMass_le_ownContinueProbability
      (Function.update (laterAbnormalRoot owner blocker p hp.le hp1) who
        (PMF.pure false)) owner
    have hvalue :
        (Function.update
          (laterAbnormalRoot owner blocker p hp.le hp1) who
          (PMF.pure false)) owner = quittingHazardCoin p hp.le hp1 := by
      rw [Function.update]
      simp only [Ne.symm hwho, ↓reduceDIte]
      exact laterAbnormalRoot_owner hne p hp.le hp1
    rw [hvalue, quittingHazardCoin_false_toReal] at hle
    linarith

/-! ## Quantitative cap estimate -/

/-- The stationary payoff is close to the owner's singleton vector. -/
theorem abs_laterAbnormal_terminalPayoff_sub_ownerSolo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner) {p M : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (who : ι) :
    |quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (laterAbnormalRoot owner blocker p hp.le hp1)) who -
        quittingSoloReward reward owner who| ≤ 2 * M * p := by
  let root := laterAbnormalRoot owner blocker p hp.le hp1
  let absorption := quittingRootAbsorptionMass root
  have habsorptionBounds := laterAbnormalRoot_absorption_bounds hne hp.le hp1
  have habsorption : 0 < absorption := lt_of_lt_of_le hp habsorptionBounds.1
  have hcontinue : quittingStationaryContinueMass root < 1 := by
    unfold absorption quittingRootAbsorptionMass at habsorption
    linarith
  have hanchor :=
    abs_quittingRootAbsorbingContribution_sub_absorption_mul_solo_le
      (reward := reward) root owner who hM hreward
  rw [laterAbnormalRoot_owner_opponentAbsorption hne] at hanchor
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward root who hcontinue]
  have hrearrange :
      quittingRootAbsorbingContribution reward root who /
            (1 - quittingStationaryContinueMass root) -
          quittingSoloReward reward owner who =
        (quittingRootAbsorbingContribution reward root who -
            absorption * quittingSoloReward reward owner who) / absorption := by
    have hdenEq : 1 - quittingStationaryContinueMass root = absorption := rfl
    rw [hdenEq]
    calc
      _ = quittingRootAbsorbingContribution reward root who / absorption -
          (absorption * quittingSoloReward reward owner who) / absorption := by
        rw [mul_div_cancel_left₀ _ habsorption.ne']
      _ = _ := (sub_div _ _ _).symm
  rw [hrearrange, abs_div, abs_of_pos habsorption]
  apply (div_le_iff₀ habsorption).2
  calc
    |quittingRootAbsorbingContribution reward root who -
          absorption * quittingSoloReward reward owner who| ≤
        2 * M * p ^ 2 := hanchor
    _ ≤ (2 * M * p) * absorption := by
      have hcoef : 0 ≤ 2 * M * p := by positivity
      calc
        2 * M * p ^ 2 = (2 * M * p) * p := by ring
        _ ≤ (2 * M * p) * absorption :=
          mul_le_mul_of_nonneg_left habsorptionBounds.1 hcoef

/-- Immediate quitting is close to the receiver's own singleton reward. -/
theorem abs_laterAbnormal_quitValue_sub_solo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner) {p M : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (who : ι) :
    |quittingStationaryFixedOpponentsQuitValue reward
          (laterAbnormalRoot owner blocker p hp0 hp1) who -
        quittingSoloReward reward who who| ≤ 4 * M * p := by
  have hbase := abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
    (reward := reward) (laterAbnormalRoot owner blocker p hp0 hp1) who hM hreward
  have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass
    (laterAbnormalRoot owner blocker p hp0 hp1) who
  have habsorption := (laterAbnormalRoot_absorption_bounds hne hp0 hp1).2
  calc
    _ ≤ 2 * M * quittingRootOpponentAbsorptionMass
        (laterAbnormalRoot owner blocker p hp0 hp1) who := hbase
    _ ≤ 2 * M * quittingRootAbsorptionMass
        (laterAbnormalRoot owner blocker p hp0 hp1) :=
      mul_le_mul_of_nonneg_left hopponent (by positivity)
    _ ≤ 2 * M * (2 * p) :=
      mul_le_mul_of_nonneg_left habsorption (by positivity)
    _ = 4 * M * p := by ring

/-- The owner/blocker hypotheses bound the complete stationary unilateral
cap, including the Never alternative. -/
theorem isεAsymptoticNash_laterAbnormalRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner) {p M : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcolumn : ∀ who,
      quittingSoloReward reward who who ≤ quittingSoloReward reward owner who)
    (hblocker : quittingSoloReward reward blocker owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (6 * M * p)
      (quittingStationaryProfile reward
        (laterAbnormalRoot owner blocker p hp.le hp1)) := by
  let root := laterAbnormalRoot owner blocker p hp.le hp1
  let payoff := fun who => quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  apply isεAsymptoticNash_stationary_of_unilateralCap_le
  · exact laterAbnormalRoot_fixedOpponents_contracts hne hp hp1
  · intro who
    unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    apply max_le
    · have hquit := abs_laterAbnormal_quitValue_sub_solo_le
        reward hne hp.le hp1 hM hreward who
      have hpayoff := abs_laterAbnormal_terminalPayoff_sub_ownerSolo_le
        reward hne hp hp1 hM hreward who
      have hquitUpper := (abs_le.mp hquit).2
      have hpayoffLower := (abs_le.mp hpayoff).1
      linarith [hcolumn who]
    · change quittingStationaryNeverValue
        (quittingRootAbsorbingContribution reward
          (Function.update root who (PMF.pure false)) who)
        (quittingStationaryContinueMass
          (Function.update root who (PMF.pure false))) ≤
        payoff who + 6 * M * p
      by_cases hwhoOwner : who = owner
      · subst who
        have hpayoff := abs_laterAbnormal_terminalPayoff_sub_ownerSolo_le
          reward hne hp hp1 hM hreward owner
        have hpayoffLower := (abs_le.mp hpayoff).1
        change quittingStationaryNeverValue
          (quittingRootAbsorbingContribution reward
            (Function.update
              (laterAbnormalRoot owner blocker p hp.le hp1) owner
              (PMF.pure false)) owner)
          (quittingStationaryContinueMass
            (Function.update
              (laterAbnormalRoot owner blocker p hp.le hp1) owner
              (PMF.pure false))) ≤ _
        rw [update_laterAbnormalRoot_owner_continue hne,
          quittingRootAbsorbingContribution_solo,
          quittingStationaryContinueMass_solo,
          quittingHazardCoin_true_toReal,
          quittingHazardCoin_false_toReal]
        unfold quittingStationaryNeverValue
        have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne'
        rw [show 1 - (1 - p ^ 2) = p ^ 2 by ring,
          mul_div_cancel_left₀ _ hp2]
        dsimp only [root, payoff]
        nlinarith [mul_nonneg hM hp.le]
      · by_cases hwhoBlocker : who = blocker
        · subst who
          have hpayoff := abs_laterAbnormal_terminalPayoff_sub_ownerSolo_le
            reward hne hp hp1 hM hreward blocker
          have hpayoffLower := (abs_le.mp hpayoff).1
          change quittingStationaryNeverValue
            (quittingRootAbsorbingContribution reward
              (Function.update
                (laterAbnormalRoot owner blocker p hp.le hp1) blocker
                (PMF.pure false)) blocker)
            (quittingStationaryContinueMass
              (Function.update
                (laterAbnormalRoot owner blocker p hp.le hp1) blocker
                (PMF.pure false))) ≤ _
          rw [update_laterAbnormalRoot_blocker_continue hne,
            quittingRootAbsorbingContribution_solo,
            quittingStationaryContinueMass_solo,
            quittingHazardCoin_true_toReal,
            quittingHazardCoin_false_toReal]
          unfold quittingStationaryNeverValue
          rw [show 1 - (1 - p) = p by ring,
            mul_div_cancel_left₀ _ hp.ne']
          dsimp only [root, payoff]
          nlinarith [mul_nonneg hM hp.le]
        · have hupdate := update_laterAbnormalRoot_other_continue
            hwhoOwner hwhoBlocker p hp.le hp1
          change quittingStationaryNeverValue
            (quittingRootAbsorbingContribution reward
              (Function.update
                (laterAbnormalRoot owner blocker p hp.le hp1) who
                (PMF.pure false)) who)
            (quittingStationaryContinueMass
              (Function.update
                (laterAbnormalRoot owner blocker p hp.le hp1) who
                (PMF.pure false))) ≤ _
          rw [hupdate]
          unfold quittingStationaryNeverValue
          have hcontinue : quittingStationaryContinueMass root < 1 := by
            have hcontracts := laterAbnormalRoot_fixedOpponents_contracts
              hne hp hp1 who
            change quittingStationaryContinueMass
              (Function.update root who (PMF.pure false)) < 1 at hcontracts
            rw [hupdate] at hcontracts
            exact hcontracts
          rw [← quittingTerminalPayoff_stationary_eq_absorbingContribution_div
            reward root who hcontinue]
          exact le_add_of_nonneg_right (by positivity)

/-! ## Strategic closure -/

/-- A nonnegative normalized singleton column and one nonpositive owner-row
witness yield terminal approximate equilibria at every accuracy. -/
theorem terminalNash_all_errors_of_nonnegative_column
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner)
    (hcolumn : ∀ who, 0 ≤ normalizedSoloMatrix reward who owner)
    (hblocker : normalizedSoloMatrix reward owner blocker ≤ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  intro ε hε
  let M := quittingRewardBound reward
  let scale := 6 * M
  let p := ε / (scale + ε)
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hden : 0 < scale + ε := by
    dsimp only [scale]
    positivity
  have hp : 0 < p := div_pos hε hden
  have hp1 : p ≤ 1 := (div_le_one hden).2 (by
    dsimp only [scale]
    nlinarith)
  have herror : 6 * M * p < ε := by
    have hscale : 6 * M < scale + ε := by
      dsimp only [scale]
      linarith
    calc
      6 * M * p < (scale + ε) * p :=
        mul_lt_mul_of_pos_right hscale hp
      _ = ε := by
        dsimp only [p]
        exact mul_div_cancel₀ ε hden.ne'
  have hcolumn' : ∀ who,
      quittingSoloReward reward who who ≤ quittingSoloReward reward owner who := by
    intro who
    have h := hcolumn who
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix] at h
    unfold quittingProjectiveLCPMatrix at h
    simpa [quittingSoloReward, quittingProjectiveSingletonTerminal] using
      sub_nonneg.mp h
  have hblocker' : quittingSoloReward reward blocker owner ≤
      quittingSoloReward reward owner owner := by
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix] at hblocker
    unfold quittingProjectiveLCPMatrix at hblocker
    simpa [quittingSoloReward, quittingProjectiveSingletonTerminal] using
      sub_nonpos.mp hblocker
  refine ⟨quittingStationaryProfile reward
      (laterAbnormalRoot owner blocker p hp.le hp1), ?_⟩
  exact (isεAsymptoticNash_laterAbnormalRoot reward hne hp hp1 hM
    (abs_reward_le_quittingRewardBound reward) hcolumn' hblocker').mono herror.le

/-- The same matrix hypotheses yield a uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_nonnegative_column
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : blocker ≠ owner)
    (hcolumn : ∀ who, 0 ≤ normalizedSoloMatrix reward who owner)
    (hblocker : normalizedSoloMatrix reward owner blocker ≤ 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  exact terminalNash_all_errors_of_nonnegative_column
    reward hne hcolumn hblocker

/-- **Later-layer all-abnormal producer.**  Empty corrected normal core always
produces a uniform-equilibrium payoff.  The empty-first-layer case uses the
exact stationary producer; the later-layer case uses the two-scale
owner/blocker row above. -/
theorem exists_uniformEquilibriumPayoff_of_allPlayersAbnormal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (habnormal : AllPlayersAbnormal (normalizedSoloMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  classical
  by_cases hfirst : normalLayer (normalizedSoloMatrix reward) 1 = ∅
  · exact exists_uniformEquilibriumPayoff_of_normalLayer_one_eq_empty
      reward hfirst
  · obtain ⟨last, hlast, hlastNonempty, hnext⟩ :=
      exists_last_nonempty_normalLayer (normalizedSoloMatrix reward)
        habnormal hfirst
    obtain ⟨owner, howner⟩ := Finset.nonempty_iff_ne_empty.mpr hlastNonempty
    obtain ⟨blocker, hne, hblocker⟩ :=
      exists_firstLayer_blocker_of_mem_normalLayer
        (normalizedSoloMatrix reward) hlast howner
    have hcolumn := nonnegative_column_of_last_normalLayer
      (normalizedSoloMatrix reward)
      (normalizedSoloMatrix_diagonal reward) hnext howner
    exact exists_uniformEquilibriumPayoff_of_nonnegative_column
      reward hne hcolumn hblocker

/-- Consequently a counterexample cannot lie in the corrected all-abnormal
matrix regime. -/
theorem hasNormalPlayers_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    HasNormalPlayers (normalizedSoloMatrix reward) := by
  by_contra hnormal
  exact hnot (exists_uniformEquilibriumPayoff_of_allPlayersAbnormal reward
    ((allPlayersAbnormal_iff_not_hasNormalPlayers
      (normalizedSoloMatrix reward)).2 hnormal))

end QuittingLCPClassification
end GameTheory
