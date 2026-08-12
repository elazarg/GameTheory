/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence

/-!
# Unconditional elementary-tail semantic reduction

The coordinatewise sure-Quit cap needs two zero-Never seeds if every
unilateral deviation is to face literal finite-horizon absorption.  This file
records the complementary unconditional reduction: compress the *whole live
root word* after a finite prefix to one of three elementary suffixes.

The suffix is either sure-joint, sure-solo, or Never.  The last alternative
keeps the cemetery state instead of pretending that it can be removed.  All
three suffixes have an exact finite-dimensional terminal semantic boundary,
so terminal payoff, the unrestricted behavioral best-response envelope, and
semantic debt can still be evaluated by finitely many backward prefix steps.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The elementary suffix grammar is equivalent to two exceptional labels
plus one owner-indexed label. -/
def quittingElementaryTailCapEquivOptionOption :
    QuittingElementaryTailCap ι ≃ Option (Option ι) where
  toFun
    | .never => none
    | .sureJoint => some none
    | .sureSolo owner => some (some owner)
  invFun
    | none => .never
    | some none => .sureJoint
    | some (some owner) => .sureSolo owner
  left_inv cap := by cases cap <;> rfl
  right_inv code := by
    cases code with
    | none => rfl
    | some code => cases code <;> rfl

noncomputable instance quittingElementaryTailCapFintype :
    Fintype (QuittingElementaryTailCap ι) :=
  Fintype.ofEquiv (Option (Option ι))
    quittingElementaryTailCapEquivOptionOption.symm

omit [DecidableEq ι] in
/-- With `n` players there are literally `n + 2` elementary boundary
labels. -/
theorem card_quittingElementaryTailCap :
    Fintype.card (QuittingElementaryTailCap ι) = Fintype.card ι + 2 := by
  rw [Fintype.card_congr
    (quittingElementaryTailCapEquivOptionOption (ι := ι))]
  simp

/-- Replace the canonical live-root tail of a behavior profile by one
elementary suffix after `cutoff`. -/
def quittingElementaryCompressedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (cutoff : ℕ) (cap : QuittingElementaryTailCap ι) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward
    (quittingElementaryTailRoots
      (quittingProfileLiveRoot reward profile) cutoff cap) 0

@[simp] theorem quittingProfileLiveRoot_elementaryCompressedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (cutoff : ℕ) (cap : QuittingElementaryTailCap ι) :
    quittingProfileLiveRoot reward
        (quittingElementaryCompressedProfile reward profile cutoff cap) =
      quittingElementaryTailRoots
        (quittingProfileLiveRoot reward profile) cutoff cap := by
  simp [quittingElementaryCompressedProfile]

/-- Compression is literally invisible on every live root before its
cutoff. -/
theorem quittingElementaryCompressedProfile_liveRoot_eq_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (cap : QuittingElementaryTailCap ι) {cutoff time : ℕ}
    (htime : time < cutoff) :
    quittingProfileLiveRoot reward
        (quittingElementaryCompressedProfile reward profile cutoff cap) time =
      quittingProfileLiveRoot reward profile time := by
  rw [quittingProfileLiveRoot_elementaryCompressedProfile]
  exact quittingElementaryTailRoots_of_lt _ cap htime

/-- The unrestricted behavioral envelope, like prescribed terminal payoff,
depends only on the canonical live-root word. -/
theorem quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingContinuationBestResponseValue reward profile who =
      quittingRootSequenceBestResponseValue reward
        (quittingProfileLiveRoot reward profile) who := by
  unfold quittingRootSequenceBestResponseValue
    quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime
      reward profile who hM hreward,
    sSup_range_quittingTerminalPayoff_update_eq_pureTime
      reward
        (quittingRootSequenceProfile reward
          (quittingProfileLiveRoot reward profile) 0)
        who hM hreward]
  have hvalues :
      (fun quitTime : Option ℕ =>
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who) =
      (fun quitTime : Option ℕ =>
        quittingTerminalPayoff reward
          (Function.update
            (quittingRootSequenceProfile reward
              (quittingProfileLiveRoot reward profile) 0)
            who (quittingPureTimeBehaviorStrategy reward who quitTime)) who) := by
    funext quitTime
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  rw [hvalues]

/-! ## A finite survival-stratum quotient -/

/-- The canonical survival stratum attached to an elementary suffix.

* `never`: positive joint survival;
* `sureJoint`: zero joint survival and every one-player-deleted clock dies;
* `sureSolo owner`: zero joint survival and `owner` is the unique player
  whose deleted-opponent clock has positive limit.

For a finite player set this has exactly `card ι + 2` syntactic labels. -/
def QuittingElementaryCapMatchesSurvivalStratum
    (roots : ℕ → ι → PMF Bool) : QuittingElementaryTailCap ι → Prop
  | .never => 0 < quittingJointSurvivalLimit roots 0
  | .sureJoint =>
      quittingJointSurvivalLimit roots 0 = 0 ∧
        ∀ who, quittingOpponentSurvivalLimit roots who 0 = 0
  | .sureSolo owner =>
      quittingJointSurvivalLimit roots 0 = 0 ∧
        0 < quittingOpponentSurvivalLimit roots owner 0 ∧
        ∀ who, 0 < quittingOpponentSurvivalLimit roots who 0 → who = owner

/-- The elementary tail-density theorem can be selected inside the unique
matching survival stratum; the three cap shapes are not an arbitrary menu. -/
theorem exists_stratifiedElementaryTailCap_terminalPair_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      QuittingElementaryCapMatchesSurvivalStratum roots cap ∧
      (∀ who, |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingElementaryTailRoots roots cutoff cap) who 0| < ε) ∧
      (∀ who, |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff cap) who| < ε) := by
  rcases quittingSurvivalLimit_trichotomy reward roots with
    hpositive | ⟨hjoint, hall | hunique⟩
  · obtain ⟨cutoff, hp, hb⟩ :=
      exists_elementaryNever_terminalPair_close_of_joint_pos
        reward roots hM hε hreward hpositive
    exact ⟨.never, cutoff, hpositive, hp, hb⟩
  · obtain ⟨cutoff, hp, hb⟩ :=
      exists_elementarySureJoint_terminalPair_close
        reward roots hM hε hreward hjoint hall
    exact ⟨.sureJoint, cutoff, ⟨hjoint, hall⟩, hp, hb⟩
  · obtain ⟨owner, howner, hownerUnique⟩ := hunique
    obtain ⟨cutoff, hp, hb⟩ :=
      exists_elementarySureSolo_terminalPair_close_of_unique
        reward roots owner hM hε hreward hjoint howner hownerUnique
    exact ⟨.sureSolo owner, cutoff,
      ⟨hjoint, howner, hownerUnique⟩, hp, hb⟩

/-- The owner label in the sure-solo stratum is unique. -/
theorem quittingSureSolo_survivalStratum_owner_unique
    (roots : ℕ → ι → PMF Bool) (first second : ι)
    (hfirst : QuittingElementaryCapMatchesSurvivalStratum roots (.sureSolo first))
    (hsecond : QuittingElementaryCapMatchesSurvivalStratum roots (.sureSolo second)) :
    first = second := by
  exact (hfirst.2.2 second hsecond.2.1).symm

/-- The stratified elementary representative may be chosen after any fixed
finite entrance block. -/
theorem exists_stratifiedElementaryTailCap_terminalPair_close_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (lowerBound : ℕ) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      lowerBound ≤ cutoff ∧
      QuittingElementaryCapMatchesSurvivalStratum roots cap ∧
      (∀ who, |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingElementaryTailRoots roots cutoff cap) who 0| < ε) ∧
      (∀ who, |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff cap) who| < ε) := by
  rcases quittingSurvivalLimit_trichotomy reward roots with
    hpositive | ⟨hjoint, hall | hunique⟩
  · have hp : ∀ᶠ cutoff : ℕ in Filter.atTop, ∀ who,
        |quittingRootSequenceTerminalValue reward roots who 0 -
          quittingRootSequenceTerminalValue reward
            (quittingElementaryTailRoots roots cutoff (.never)) who 0| < ε := by
      apply Filter.eventually_all.mpr
      intro who
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
        (tendsto_quittingRootSequenceTerminalValue_elementaryNever
          reward roots who hM hreward hpositive) ε hε
      exact Filter.eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
        simpa [Real.dist_eq, abs_sub_comm] using hN cutoff hcutoff⟩
    have hb : ∀ᶠ cutoff : ℕ in Filter.atTop, ∀ who,
        |quittingRootSequenceBestResponseValue reward roots who -
          quittingRootSequenceBestResponseValue reward
            (quittingElementaryTailRoots roots cutoff (.never)) who| < ε := by
      apply Filter.eventually_all.mpr
      intro who
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
        (tendsto_quittingRootSequenceBestResponseValue_elementaryNever
          reward roots who hM hreward
            (quittingOpponentSurvivalLimit_pos_of_joint_pos
              roots who hpositive)) ε hε
      exact Filter.eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
        simpa [Real.dist_eq, abs_sub_comm] using hN cutoff hcutoff⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hp.and hb)
    let cutoff := max lowerBound N
    exact ⟨.never, cutoff, le_max_left _ _, hpositive,
      (hN cutoff (le_max_right _ _)).1,
      (hN cutoff (le_max_right _ _)).2⟩
  · have hp : ∀ᶠ cutoff : ℕ in Filter.atTop, ∀ who,
        |quittingRootSequenceTerminalValue reward roots who 0 -
          quittingRootSequenceTerminalValue reward
            (quittingElementaryTailRoots roots cutoff (.sureJoint)) who 0| < ε := by
      apply Filter.eventually_all.mpr
      intro who
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
        (tendsto_quittingRootSequenceTerminalValue_elementarySureJoint
          reward roots who hM hreward hjoint) ε hε
      exact Filter.eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
        simpa [Real.dist_eq, abs_sub_comm] using hN cutoff hcutoff⟩
    have hb : ∀ᶠ cutoff : ℕ in Filter.atTop, ∀ who,
        |quittingRootSequenceBestResponseValue reward roots who -
          quittingRootSequenceBestResponseValue reward
            (quittingElementaryTailRoots roots cutoff (.sureJoint)) who| < ε := by
      apply Filter.eventually_all.mpr
      intro who
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
        (tendsto_quittingRootSequenceBestResponseValue_elementarySureJoint
          reward roots who hM hreward (hall who)) ε hε
      exact Filter.eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
        simpa [Real.dist_eq, abs_sub_comm] using hN cutoff hcutoff⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hp.and hb)
    let cutoff := max lowerBound N
    exact ⟨.sureJoint, cutoff, le_max_left _ _, ⟨hjoint, hall⟩,
      (hN cutoff (le_max_right _ _)).1,
      (hN cutoff (le_max_right _ _)).2⟩
  · obtain ⟨owner, howner, hownerUnique⟩ := hunique
    have hp : ∀ᶠ cutoff : ℕ in Filter.atTop, ∀ who,
        |quittingRootSequenceTerminalValue reward roots who 0 -
          quittingRootSequenceTerminalValue reward
            (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) who 0| < ε := by
      have hmajorant : Filter.Tendsto (fun cutoff =>
          2 * M * quittingJointSurvivalWeight roots 0 cutoff)
          Filter.atTop (nhds 0) := by
        simpa [hjoint] using
          (tendsto_quittingJointSurvivalLimit roots 0).const_mul (2 * M)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmajorant ε hε
      exact Filter.eventually_atTop.mpr ⟨N, fun cutoff hcutoff who => by
        have hbound :=
          abs_quittingRootSequenceTerminalValue_sub_elementarySureSolo_le
            reward roots owner who cutoff hM hreward
        have hclose := hN cutoff hcutoff
        rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hclose
        · exact lt_of_le_of_lt hbound hclose
        · exact mul_nonneg (mul_nonneg (by norm_num) hM)
            (quittingJointSurvivalWeight_nonneg roots 0 cutoff)⟩
    have hb : ∀ᶠ cutoff : ℕ in Filter.atTop, ∀ who,
        |quittingRootSequenceBestResponseValue reward roots who -
          quittingRootSequenceBestResponseValue reward
            (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) who| < ε := by
      apply Filter.eventually_all.mpr
      intro who
      by_cases hwho : who = owner
      · subst who
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
          (tendsto_quittingRootSequenceBestResponseValue_elementaryNever
            reward roots owner hM hreward howner) ε hε
        exact Filter.eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
          rw [quittingRootSequenceBestResponseValue_elementarySureSolo_owner_eq_never]
          simpa [Real.dist_eq, abs_sub_comm] using hN cutoff hcutoff⟩
      · have hzero : quittingOpponentSurvivalLimit roots who 0 = 0 := by
          apply le_antisymm _
            (quittingOpponentSurvivalLimit_nonneg roots who 0)
          by_contra hnot
          have hpos : 0 < quittingOpponentSurvivalLimit roots who 0 :=
            lt_of_not_ge hnot
          exact hwho (hownerUnique who hpos)
        have hmajorant : Filter.Tendsto (fun cutoff =>
            2 * M * quittingOpponentSurvivalWeight roots who 0 cutoff)
            Filter.atTop (nhds 0) := by
          simpa [hzero] using
            (tendsto_quittingOpponentSurvivalLimit roots who 0).const_mul (2 * M)
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmajorant ε hε
        exact Filter.eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
          have hbound :=
            abs_quittingRootSequenceBestResponseValue_sub_elementarySureSolo_le
              reward roots owner who cutoff hM hreward
          have hclose := hN cutoff hcutoff
          rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hclose
          · exact lt_of_le_of_lt hbound hclose
          · exact mul_nonneg (mul_nonneg (by norm_num) hM)
              (quittingOpponentSurvivalWeight_nonneg roots who 0 cutoff)⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hp.and hb)
    let cutoff := max lowerBound N
    exact ⟨.sureSolo owner, cutoff, le_max_left _ _,
      ⟨hjoint, howner, hownerUnique⟩,
      (hN cutoff (le_max_right _ _)).1,
      (hN cutoff (le_max_right _ _)).2⟩

/-- An elementary whole-tail compression approximates the complete terminal
semantics of an arbitrary behavior profile, without any zero-Never seed
hypothesis. -/
theorem exists_elementaryCompressedProfile_terminalSemantics_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      ∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward
              (quittingElementaryCompressedProfile reward profile cutoff cap)).1
                observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward
              (quittingElementaryCompressedProfile reward profile cutoff cap)).2
                observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingElementaryCompressedProfile reward profile cutoff cap))
              observer| < δ := by
  let η := δ / 2
  have hη : 0 < η := div_pos hδ (by norm_num)
  obtain ⟨cap, cutoff, hpayoff, henvelope⟩ :=
    exists_elementaryTailCap_terminalPair_close
      reward (quittingProfileLiveRoot reward profile) hM hη hreward
  refine ⟨cap, cutoff, fun observer => ?_⟩
  have hp := hpayoff observer
  have hb := henvelope observer
  change
    |quittingTerminalPayoff reward profile observer -
      quittingTerminalPayoff reward
        (quittingElementaryCompressedProfile reward profile cutoff cap)
        observer| < δ ∧
    |quittingContinuationBestResponseValue reward profile observer -
      quittingContinuationBestResponseValue reward
        (quittingElementaryCompressedProfile reward profile cutoff cap)
        observer| < δ ∧ _
  have hp' :
      |quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward
          (quittingElementaryCompressedProfile reward profile cutoff cap)
          observer| < η := by
    simpa [quittingElementaryCompressedProfile,
      quittingTerminalPayoff_eq_rootSequence_profileLiveRoot] using hp
  have hb' :
      |quittingContinuationBestResponseValue reward profile observer -
        quittingContinuationBestResponseValue reward
          (quittingElementaryCompressedProfile reward profile cutoff cap)
          observer| < η := by
    rw [quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
        reward profile observer hM hreward,
      quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
        reward
          (quittingElementaryCompressedProfile reward profile cutoff cap)
          observer hM hreward,
      quittingProfileLiveRoot_elementaryCompressedProfile]
    exact hb
  constructor
  · exact hp'.trans_le (by dsimp [η]; linarith)
  · constructor
    · exact hb'.trans_le (by dsimp [η]; linarith)
    · unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
      calc
        |(quittingContinuationBestResponseValue reward profile observer -
              quittingTerminalPayoff reward profile observer) -
            (quittingContinuationBestResponseValue reward
                (quittingElementaryCompressedProfile reward profile cutoff cap)
                observer -
              quittingTerminalPayoff reward
                (quittingElementaryCompressedProfile reward profile cutoff cap)
                observer)| =
            |(quittingContinuationBestResponseValue reward profile observer -
                quittingContinuationBestResponseValue reward
                  (quittingElementaryCompressedProfile reward profile cutoff cap)
                  observer) +
              (quittingTerminalPayoff reward
                  (quittingElementaryCompressedProfile reward profile cutoff cap)
                  observer -
                quittingTerminalPayoff reward profile observer)| := by ring_nf
        _ ≤ |quittingContinuationBestResponseValue reward profile observer -
                quittingContinuationBestResponseValue reward
                  (quittingElementaryCompressedProfile reward profile cutoff cap)
                  observer| +
              |quittingTerminalPayoff reward
                  (quittingElementaryCompressedProfile reward profile cutoff cap)
                  observer -
                quittingTerminalPayoff reward profile observer| := abs_add_le _ _
        _ < η + η := add_lt_add hb' (by simpa [abs_sub_comm] using hp')
        _ = δ := by dsimp [η]; ring

/-- Strong stratified form: the cutoff can be placed after any requested
finite entrance block, whose canonical live roots are then preserved
literally. -/
theorem exists_elementaryCompressedProfile_terminalSemantics_close_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (lowerBound : ℕ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      lowerBound ≤ cutoff ∧
      QuittingElementaryCapMatchesSurvivalStratum
        (quittingProfileLiveRoot reward profile) cap ∧
      (∀ time < lowerBound,
        quittingProfileLiveRoot reward
            (quittingElementaryCompressedProfile reward profile cutoff cap) time =
          quittingProfileLiveRoot reward profile time) ∧
      ∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward
              (quittingElementaryCompressedProfile reward profile cutoff cap)).1
                observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward
              (quittingElementaryCompressedProfile reward profile cutoff cap)).2
                observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingElementaryCompressedProfile reward profile cutoff cap))
              observer| < δ := by
  let η := δ / 2
  have hη : 0 < η := div_pos hδ (by norm_num)
  obtain ⟨cap, cutoff, hlate, hmatch, hpayoff, henvelope⟩ :=
    exists_stratifiedElementaryTailCap_terminalPair_close_after
      reward (quittingProfileLiveRoot reward profile) lowerBound hM hη hreward
  refine ⟨cap, cutoff, hlate, hmatch, ?_, fun observer => ?_⟩
  · intro time htime
    exact quittingElementaryCompressedProfile_liveRoot_eq_of_lt
      reward profile cap (htime.trans_le hlate)
  · have hp := hpayoff observer
    have hb := henvelope observer
    change
      |quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward
          (quittingElementaryCompressedProfile reward profile cutoff cap)
          observer| < δ ∧
      |quittingContinuationBestResponseValue reward profile observer -
        quittingContinuationBestResponseValue reward
          (quittingElementaryCompressedProfile reward profile cutoff cap)
          observer| < δ ∧ _
    have hp' :
        |quittingTerminalPayoff reward profile observer -
          quittingTerminalPayoff reward
            (quittingElementaryCompressedProfile reward profile cutoff cap)
            observer| < η := by
      simpa [quittingElementaryCompressedProfile,
        quittingTerminalPayoff_eq_rootSequence_profileLiveRoot] using hp
    have hb' :
        |quittingContinuationBestResponseValue reward profile observer -
          quittingContinuationBestResponseValue reward
            (quittingElementaryCompressedProfile reward profile cutoff cap)
            observer| < η := by
      rw [quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
          reward profile observer hM hreward,
        quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
          reward
            (quittingElementaryCompressedProfile reward profile cutoff cap)
            observer hM hreward,
        quittingProfileLiveRoot_elementaryCompressedProfile]
      exact hb
    constructor
    · exact hp'.trans_le (by dsimp [η]; linarith)
    · constructor
      · exact hb'.trans_le (by dsimp [η]; linarith)
      · unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
        calc
          |(quittingContinuationBestResponseValue reward profile observer -
                quittingTerminalPayoff reward profile observer) -
              (quittingContinuationBestResponseValue reward
                  (quittingElementaryCompressedProfile reward profile cutoff cap)
                  observer -
                quittingTerminalPayoff reward
                  (quittingElementaryCompressedProfile reward profile cutoff cap)
                  observer)| =
              |(quittingContinuationBestResponseValue reward profile observer -
                  quittingContinuationBestResponseValue reward
                    (quittingElementaryCompressedProfile reward profile cutoff cap)
                    observer) +
                (quittingTerminalPayoff reward
                    (quittingElementaryCompressedProfile reward profile cutoff cap)
                    observer -
                  quittingTerminalPayoff reward profile observer)| := by ring_nf
          _ ≤ |quittingContinuationBestResponseValue reward profile observer -
                  quittingContinuationBestResponseValue reward
                    (quittingElementaryCompressedProfile reward profile cutoff cap)
                    observer| +
                |quittingTerminalPayoff reward
                    (quittingElementaryCompressedProfile reward profile cutoff cap)
                    observer -
                  quittingTerminalPayoff reward profile observer| := abs_add_le _ _
          _ < η + η := add_lt_add hb' (by simpa [abs_sub_comm] using hp')
          _ = δ := by dsimp [η]; ring

/-- Unconditional finite-semantic approximate-Nash transport.  The target
may retain the explicit Never boundary; no two-seed hypothesis is needed. -/
theorem exists_elementaryCompressedProfile_isεAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      (∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward
              (quittingElementaryCompressedProfile reward profile cutoff cap)).1
                observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward
              (quittingElementaryCompressedProfile reward profile cutoff cap)).2
                observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingElementaryCompressedProfile reward profile cutoff cap))
              observer| < δ) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (ε + 2 * δ)
        (quittingElementaryCompressedProfile reward profile cutoff cap) := by
  obtain ⟨cap, cutoff, hclose⟩ :=
    exists_elementaryCompressedProfile_terminalSemantics_close
      reward profile hM hδ hreward
  refine ⟨cap, cutoff, hclose, ?_⟩
  let target := quittingElementaryCompressedProfile reward profile cutoff cap
  have hsourceBest : ∀ observer,
      quittingContinuationBestResponseValue reward profile observer ≤
        quittingTerminalPayoff reward profile observer + ε := by
    intro observer
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, ⟨profile observer, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      exact hnash observer deviation
  intro observer deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward target observer deviation hM hreward
  have hp := (hclose observer).1
  have hb := (hclose observer).2.1
  change
    |quittingTerminalPayoff reward profile observer -
      quittingTerminalPayoff reward target observer| < δ at hp
  change
    |quittingContinuationBestResponseValue reward profile observer -
      quittingContinuationBestResponseValue reward target observer| < δ at hb
  have hbestUpper :
      quittingContinuationBestResponseValue reward target observer <
        quittingContinuationBestResponseValue reward profile observer + δ := by
    linarith [neg_le_abs
      (quittingContinuationBestResponseValue reward profile observer -
        quittingContinuationBestResponseValue reward target observer)]
  have hpayoffUpper :
      quittingTerminalPayoff reward profile observer <
        quittingTerminalPayoff reward target observer + δ := by
    linarith [le_abs_self
      (quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward target observer)]
  dsimp [target] at hdeviation ⊢
  linarith [hsourceBest observer]

/-! ## Exact finite-dimensional boundary semantics -/

/-- Exact terminal semantic pair of the perpetual-Continue suffix. -/
def quittingNeverBoundarySemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingTerminalSemanticPair ι :=
  (fun _ => 0,
    fun who => max 0 (reward (quittingSingletonTerminal who) who))

/-- The explicit Never boundary is the literal semantic pair of the
all-Continue root word. -/
theorem quittingTerminalSemanticPair_elementaryCap_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingElementaryCapRoots
            (.never : QuittingElementaryTailCap ι)) 0) =
      quittingNeverBoundarySemanticPair reward := by
  apply Prod.ext
  · funext who
    exact quittingRootSequenceTerminalValue_elementaryCap_never reward who
  · funext who
    exact quittingRootSequenceBestResponseValue_elementaryCap_never
      reward who hM hreward

/-- Finite-dimensional boundary pair for each elementary suffix.  A sure
cap is one ordinary semantic-prefix step in front of the explicit Never
boundary. -/
def quittingElementaryBoundarySemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingElementaryTailCap ι → QuittingTerminalSemanticPair ι
  | .never => quittingNeverBoundarySemanticPair reward
  | .sureJoint =>
      quittingTerminalSemanticPrefix reward quittingSureJointRoot
        (quittingNeverBoundarySemanticPair reward)
  | .sureSolo owner =>
      quittingTerminalSemanticPrefix reward (quittingSureSoloRoot owner)
        (quittingNeverBoundarySemanticPair reward)

/-- Every elementary suffix is represented exactly by its explicit
finite-dimensional boundary pair. -/
theorem quittingTerminalSemanticPair_elementaryCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : QuittingElementaryTailCap ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingElementaryCapRoots cap) 0) =
      quittingElementaryBoundarySemanticPair reward cap := by
  cases cap with
  | never =>
      exact quittingTerminalSemanticPair_elementaryCap_never
        reward hM hreward
  | sureJoint =>
      have htail :
          quittingRootSequenceProfile reward
              (quittingElementaryCapRoots
                (.sureJoint : QuittingElementaryTailCap ι)) 1 =
            quittingRootSequenceProfile reward
              (quittingElementaryCapRoots
                (.never : QuittingElementaryTailCap ι)) 0 := by
        funext player time history
        cases time <;> rfl
      rw [quittingRootSequenceProfile_eq_rootThenContinuation,
        quittingTerminalSemanticPair_rootThenContinuation
          reward _ _ hM hreward,
        htail,
        quittingTerminalSemanticPair_elementaryCap_never reward hM hreward]
      rfl
  | sureSolo owner =>
      have htail :
          quittingRootSequenceProfile reward
              (quittingElementaryCapRoots
                (.sureSolo owner : QuittingElementaryTailCap ι)) 1 =
            quittingRootSequenceProfile reward
              (quittingElementaryCapRoots
                (.never : QuittingElementaryTailCap ι)) 0 := by
        funext player time history
        cases time <;> rfl
      rw [quittingRootSequenceProfile_eq_rootThenContinuation,
        quittingTerminalSemanticPair_rootThenContinuation
          reward _ _ hM hreward,
        htail,
        quittingTerminalSemanticPair_elementaryCap_never reward hM hreward]
      rfl

/-! ## Literal finite backward evaluation -/

/-- Apply the exact semantic-prefix action to a finite root word, starting
from a supplied finite-dimensional boundary pair. -/
def quittingFinitePrefixSemanticEval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (ℕ → ι → PMF Bool) → ℕ → QuittingTerminalSemanticPair ι →
      QuittingTerminalSemanticPair ι
  | _, 0, boundary => boundary
  | roots, fuel + 1, boundary =>
      quittingTerminalSemanticPrefix reward (roots 0)
        (quittingFinitePrefixSemanticEval reward
          (fun time => roots (time + 1)) fuel boundary)

omit [Fintype ι] in
/-- Removing the first stage of a capped word shifts both its original
prefix and its cap date by one. -/
theorem quittingElementaryTailRoots_succ_shift
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (cap : QuittingElementaryTailCap ι) :
    (fun time =>
      quittingElementaryTailRoots roots (cutoff + 1) cap (1 + time)) =
      quittingElementaryTailRoots (fun time => roots (time + 1)) cutoff cap := by
  funext time
  unfold quittingElementaryTailRoots quittingPhaseSwitchRoots
  by_cases htime : time < cutoff
  · have hsucc : 1 + time < cutoff + 1 := by omega
    rw [if_pos hsucc, if_pos htime]
    congr 1
    omega
  · have hsucc : ¬1 + time < cutoff + 1 := by omega
    rw [if_neg hsucc, if_neg htime]
    congr 1
    omega

/-- A finite prefix followed by an elementary suffix has *exactly* the pair
computed by finitely many semantic-prefix steps from the explicit elementary
boundary.  No limiting evaluation remains in this representative. -/
theorem quittingTerminalSemanticPair_elementaryTail_eq_finiteEval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (cap : QuittingElementaryTailCap ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingElementaryTailRoots roots cutoff cap) 0) =
      quittingFinitePrefixSemanticEval reward roots cutoff
        (quittingElementaryBoundarySemanticPair reward cap) := by
  induction cutoff generalizing roots with
  | zero =>
      have hroots : quittingElementaryTailRoots roots 0 cap =
          quittingElementaryCapRoots cap := by
        funext time
        simp [quittingElementaryTailRoots, quittingPhaseSwitchRoots]
      rw [hroots]
      exact quittingTerminalSemanticPair_elementaryCap
        reward cap hM hreward
  | succ cutoff ih =>
      rw [quittingRootSequenceProfile_eq_rootThenContinuation,
        quittingTerminalSemanticPair_rootThenContinuation
          reward _ _ hM hreward]
      change
        quittingTerminalSemanticPrefix reward
            (quittingElementaryTailRoots roots (cutoff + 1) cap 0)
            (quittingTerminalSemanticPair reward
              (quittingRootSequenceProfile reward
                (quittingElementaryTailRoots roots (cutoff + 1) cap) 1)) =
          quittingTerminalSemanticPrefix reward (roots 0)
            (quittingFinitePrefixSemanticEval reward
              (fun time => roots (time + 1)) cutoff
              (quittingElementaryBoundarySemanticPair reward cap))
      rw [quittingElementaryTailRoots_of_lt roots cap (by omega)]
      congr 1
      · have htail :
            quittingRootSequenceProfile reward
                (quittingElementaryTailRoots roots (cutoff + 1) cap) 1 =
              quittingRootSequenceProfile reward
                (quittingElementaryTailRoots
                  (fun time => roots (time + 1)) cutoff cap) 0 := by
          rw [quittingRootSequenceProfile_eq_shift,
            quittingElementaryTailRoots_succ_shift]
        rw [htail]
        exact ih (fun time => roots (time + 1))

/-- Profile-facing form of the exact finite evaluator theorem. -/
theorem quittingTerminalSemanticPair_elementaryCompressedProfile_eq_finiteEval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (cutoff : ℕ) (cap : QuittingElementaryTailCap ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticPair reward
        (quittingElementaryCompressedProfile reward profile cutoff cap) =
      quittingFinitePrefixSemanticEval reward
        (quittingProfileLiveRoot reward profile) cutoff
        (quittingElementaryBoundarySemanticPair reward cap) := by
  exact quittingTerminalSemanticPair_elementaryTail_eq_finiteEval
    reward (quittingProfileLiveRoot reward profile) cutoff cap hM hreward

/-! ## Compression after a marked causal date -/

/-- Terminal semantic pair of the continuation of a root word at a marked
live date. -/
def quittingRootSequenceContinuationSemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingRootSequenceProfile reward roots start)

@[simp] theorem quittingRootSequenceContinuationSemanticPair_payoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) (who : ι) :
    (quittingRootSequenceContinuationSemanticPair reward roots start).1 who =
      quittingRootSequenceTerminalValue reward roots who start :=
  rfl

theorem quittingRootSequenceContinuationSemanticPair_envelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) (who : ι) :
    (quittingRootSequenceContinuationSemanticPair reward roots start).2 who =
      quittingRootSequenceBestResponseValue reward
        (fun time => roots (start + time)) who := by
  unfold quittingRootSequenceContinuationSemanticPair
    quittingTerminalSemanticPair quittingRootSequenceBestResponseValue
  rw [quittingRootSequenceProfile_eq_shift]

omit [Fintype ι] in
/-- Shifting an elementary compression past a marked date reduces its
absolute cutoff by that date. -/
theorem quittingElementaryTailRoots_add_shift
    (roots : ℕ → ι → PMF Bool) (mark tailCutoff : ℕ)
    (cap : QuittingElementaryTailCap ι) :
    (fun time =>
      quittingElementaryTailRoots roots (mark + tailCutoff) cap
        (mark + time)) =
      quittingElementaryTailRoots
        (fun time => roots (mark + time)) tailCutoff cap := by
  funext time
  unfold quittingElementaryTailRoots quittingPhaseSwitchRoots
  by_cases htime : time < tailCutoff
  · have habsolute : mark + time < mark + tailCutoff :=
      Nat.add_lt_add_left htime mark
    rw [if_pos habsolute, if_pos htime]
  · have habsolute : ¬mark + time < mark + tailCutoff := by omega
    rw [if_neg habsolute, if_neg htime]
    congr 1
    omega

/-- Equality of a root word through a displayed date preserves the literal
unconditional terminal-coalition atom at that date. -/
theorem quittingStageCoalitionMass_rootSequence_eq_of_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ℕ → ι → PMF Bool) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hprefix : ∀ date ≤ time, first date = second date) :
    quittingStageCoalitionMass reward
        (quittingRootSequenceProfile reward first 0) time terminal =
      quittingStageCoalitionMass reward
        (quittingRootSequenceProfile reward second 0) time terminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    ← quittingJointSurvivalWeight_eq_liveMass_rootSequence reward first time,
    ← quittingJointSurvivalWeight_eq_liveMass_rootSequence reward second time,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
    hprefix time le_rfl]
  congr 1
  exact quittingJointSurvivalWeight_congr first second 0 time
    (fun offset hoffset => by
      simpa using hprefix offset (Nat.le_of_lt hoffset))

/-- **Marked-date elementary compression.**  After any finite causal date
`mark`, retain an arbitrarily long additional root block, then attach the
matching elementary boundary.  Every root before the absolute cutoff is
literal, while payoff, the unrestricted behavioral envelope, and semantic
debt of the continuation *at the mark* change by less than `δ`.

The last conjunct identifies the compressed marked continuation exactly with
a finite backward semantic evaluation.  This is the form needed after a
chronological atom has already been localized.  It asserts no Nash--Bellman
compatibility of the retained roots. -/
theorem exists_markedDate_elementaryCompression_continuationSemantics_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (mark retainedAfterMark : ℕ)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ tailCutoff,
      retainedAfterMark + 1 ≤ tailCutoff ∧
      QuittingElementaryCapMatchesSurvivalStratum
        (fun time => roots (mark + time)) cap ∧
      (∀ time < mark + tailCutoff,
        quittingElementaryTailRoots roots (mark + tailCutoff) cap time =
          roots time) ∧
      (∀ terminal,
        quittingStageCoalitionMass reward
            (quittingRootSequenceProfile reward roots 0) mark terminal =
          quittingStageCoalitionMass reward
            (quittingRootSequenceProfile reward
              (quittingElementaryTailRoots
                roots (mark + tailCutoff) cap) 0) mark terminal) ∧
      (∀ observer,
        |(quittingRootSequenceContinuationSemanticPair
              reward roots mark).1 observer -
            (quittingRootSequenceContinuationSemanticPair reward
              (quittingElementaryTailRoots roots (mark + tailCutoff) cap)
              mark).1 observer| < δ ∧
        |(quittingRootSequenceContinuationSemanticPair
              reward roots mark).2 observer -
            (quittingRootSequenceContinuationSemanticPair reward
              (quittingElementaryTailRoots roots (mark + tailCutoff) cap)
              mark).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingRootSequenceContinuationSemanticPair
                reward roots mark) observer -
            quittingTerminalSemanticDebt
              (quittingRootSequenceContinuationSemanticPair reward
                (quittingElementaryTailRoots roots (mark + tailCutoff) cap)
                mark) observer| < δ) ∧
      quittingRootSequenceContinuationSemanticPair reward
          (quittingElementaryTailRoots roots (mark + tailCutoff) cap) mark =
        quittingFinitePrefixSemanticEval reward
          (fun time => roots (mark + time)) tailCutoff
          (quittingElementaryBoundarySemanticPair reward cap) := by
  let shifted := fun time => roots (mark + time)
  let η := δ / 2
  have hη : 0 < η := div_pos hδ (by norm_num)
  obtain ⟨cap, tailCutoff, hlate, hmatch, hpayoff, henvelope⟩ :=
    exists_stratifiedElementaryTailCap_terminalPair_close_after
      reward shifted (retainedAfterMark + 1) hM hη hreward
  let capped :=
    quittingElementaryTailRoots roots (mark + tailCutoff) cap
  have hcappedShift :
      (fun time => capped (mark + time)) =
        quittingElementaryTailRoots shifted tailCutoff cap := by
    exact quittingElementaryTailRoots_add_shift
      roots mark tailCutoff cap
  refine ⟨cap, tailCutoff, hlate, hmatch, ?_, ?_, ?_, ?_⟩
  · intro time htime
    exact quittingElementaryTailRoots_of_lt roots cap htime
  · intro terminal
    apply quittingStageCoalitionMass_rootSequence_eq_of_prefix
    intro date hdate
    exact (quittingElementaryTailRoots_of_lt roots cap (by
      have htailPositive : 0 < tailCutoff := by omega
      omega)).symm
  · intro observer
    have hp := hpayoff observer
    have hb := henvelope observer
    have hp' :
        |(quittingRootSequenceContinuationSemanticPair
              reward roots mark).1 observer -
            (quittingRootSequenceContinuationSemanticPair
              reward capped mark).1 observer| < η := by
      rw [quittingRootSequenceContinuationSemanticPair_payoff,
        quittingRootSequenceContinuationSemanticPair_payoff]
      have hsource :
          quittingRootSequenceTerminalValue reward roots observer mark =
            quittingRootSequenceTerminalValue reward shifted observer 0 := by
        simpa [shifted] using
          (quittingRootSequenceTerminalValue_eq_shift
            reward roots observer mark)
      have htarget :
          quittingRootSequenceTerminalValue reward capped observer mark =
            quittingRootSequenceTerminalValue reward
              (quittingElementaryTailRoots shifted tailCutoff cap)
              observer 0 := by
        calc
          quittingRootSequenceTerminalValue reward capped observer mark =
              quittingRootSequenceTerminalValue reward
                (fun time => capped (mark + time)) observer 0 :=
            quittingRootSequenceTerminalValue_eq_shift
              reward capped observer mark
          _ = quittingRootSequenceTerminalValue reward
                (quittingElementaryTailRoots shifted tailCutoff cap)
                observer 0 := by rw [hcappedShift]
      rw [hsource, htarget]
      exact hp
    have hb' :
        |(quittingRootSequenceContinuationSemanticPair
              reward roots mark).2 observer -
            (quittingRootSequenceContinuationSemanticPair
              reward capped mark).2 observer| < η := by
      rw [quittingRootSequenceContinuationSemanticPair_envelope,
        quittingRootSequenceContinuationSemanticPair_envelope,
        hcappedShift]
      exact hb
    constructor
    · exact hp'.trans_le (by dsimp [η]; linarith)
    · constructor
      · exact hb'.trans_le (by dsimp [η]; linarith)
      · unfold quittingTerminalSemanticDebt
        calc
          |((quittingRootSequenceContinuationSemanticPair
                  reward roots mark).2 observer -
                (quittingRootSequenceContinuationSemanticPair
                  reward roots mark).1 observer) -
              ((quittingRootSequenceContinuationSemanticPair
                  reward capped mark).2 observer -
                (quittingRootSequenceContinuationSemanticPair
                  reward capped mark).1 observer)| =
              |((quittingRootSequenceContinuationSemanticPair
                    reward roots mark).2 observer -
                  (quittingRootSequenceContinuationSemanticPair
                    reward capped mark).2 observer) +
                ((quittingRootSequenceContinuationSemanticPair
                    reward capped mark).1 observer -
                  (quittingRootSequenceContinuationSemanticPair
                    reward roots mark).1 observer)| := by ring_nf
          _ ≤ |(quittingRootSequenceContinuationSemanticPair
                    reward roots mark).2 observer -
                  (quittingRootSequenceContinuationSemanticPair
                    reward capped mark).2 observer| +
                |(quittingRootSequenceContinuationSemanticPair
                    reward capped mark).1 observer -
                  (quittingRootSequenceContinuationSemanticPair
                    reward roots mark).1 observer| := abs_add_le _ _
          _ < η + η := add_lt_add hb'
            (by simpa [abs_sub_comm] using hp')
          _ = δ := by dsimp [η]; ring
  · unfold quittingRootSequenceContinuationSemanticPair
    rw [quittingRootSequenceProfile_eq_shift, hcappedShift]
    exact quittingTerminalSemanticPair_elementaryTail_eq_finiteEval
      reward shifted tailCutoff cap hM hreward

/-- A strict negative sign with margin survives any marked-continuation
compression error smaller than that margin. -/
theorem markedContinuation_negative_preserved_of_close
    {source target margin error : ℝ}
    (hsource : source ≤ -margin) (hmargin : error < margin)
    (hclose : |source - target| < error) :
    target < 0 := by
  rw [abs_lt] at hclose
  linarith

/-- An exactly vanishing source debt becomes quantitatively small under a
marked-continuation semantic perturbation.  Exact vanishing itself is not
claimed to survive. -/
theorem markedContinuation_debt_lt_of_zero_of_close
    {sourceDebt targetDebt error : ℝ}
    (hzero : sourceDebt = 0)
    (hclose : |sourceDebt - targetDebt| < error) :
    targetDebt < error := by
  subst sourceDebt
  rw [zero_sub, abs_neg, abs_lt] at hclose
  exact hclose.2

end GameTheory

#print axioms GameTheory.card_quittingElementaryTailCap
#print axioms GameTheory.quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
#print axioms GameTheory.exists_stratifiedElementaryTailCap_terminalPair_close
#print axioms GameTheory.exists_stratifiedElementaryTailCap_terminalPair_close_after
#print axioms GameTheory.exists_elementaryCompressedProfile_terminalSemantics_close
#print axioms GameTheory.exists_elementaryCompressedProfile_terminalSemantics_close_after
#print axioms GameTheory.exists_elementaryCompressedProfile_isεAsymptoticNash
#print axioms GameTheory.quittingTerminalSemanticPair_elementaryCap
#print axioms GameTheory.quittingTerminalSemanticPair_elementaryCompressedProfile_eq_finiteEval
#print axioms GameTheory.exists_markedDate_elementaryCompression_continuationSemantics_close
