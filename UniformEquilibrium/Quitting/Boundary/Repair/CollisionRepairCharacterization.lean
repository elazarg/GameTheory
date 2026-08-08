/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchDeviationCap

/-!
# The sure-blocker collision repair, characterized exactly

Fix a quitting game, an `owner`, a distinct `blocker`, and a collision rate
`rate ∈ [0,1]`.  The **one-stage sure-blocker repair mechanism** prescribes,
at the very first stage,

* the blocker quits surely,
* the owner quits with probability `rate`,
* every remaining player -- every *spectator* -- continues,

and, should the game nevertheless still be live at the next stage (which on
path never happens, the blocker quitting surely), switches to a punishment of
the blocker.  Only the blocker can produce that continuation, so the
punishment phase is a threat addressed to the blocker alone.

The mechanism **works** at `rate` when, for every tolerance `ε > 0`, *some*
behavior profile whose stage-zero row is the repair row is a terminal
`ε`-Nash equilibrium.  The continuation is left free, so shrinking tolerances
may be met by increasingly accurate punishments.

## The characterization

`quittingCollisionRepairWorks_iff` proves that the mechanism works at `rate`
if and only if three scalar conditions hold.  Writing `r(S)` for the payoff
vector at the terminal state reached when exactly `S` quits, and
`U = (1 - rate) * r({blocker}) + rate * r({owner, blocker})` for the
prescribed payoff:

1. **Owner endpoint optimality** —
   `max (r_owner({owner,blocker})) (r_owner({blocker})) ≤ U_owner`.
   Since `U_owner` is a convex combination of the two endpoints this is an
   equality; at an interior rate it forces exact owner indifference
   `r_owner({blocker}) = r_owner({owner,blocker})`, and at an endpoint rate
   it is the corresponding one-sided inequality.
2. **Spectator no-join** —
   `(1-rate) * r_s({s,blocker}) + rate * r_s({owner,s,blocker}) ≤ U_s`
   for every spectator `s`.  This is *punishment independent*: both of a
   spectator's actions absorb the game at stage zero, so no continuation
   promise can move either side of it.
3. **Blocker-floor balance** —
   `rate * r_blocker({owner}) + (1-rate) * χ ≤ U_blocker`, priced against the
   **exact min-max** `χ = quittingPunishmentValue reward blocker`.
   Equivalently `0 ≤ (1-rate) * (q - χ) + rate * (r_blocker({owner,blocker})
   - r_blocker({owner}))` with `q = r_blocker({blocker})`.

Necessity of 1 and 2 is a stage-zero argument valid against *any*
continuation; necessity of 3 uses that no opponent plan, however history
dependent, holds the blocker below `χ`.  Sufficiency builds the punishment
phase from a near-optimal constant row.

## Two consequences of the balance condition

* `quittingCollisionRate_ge_of_blockerBalance` — a sub-floor blocker, with
  gap `γ = χ - q > 0` and pair bonus
  `π = r_blocker({owner,blocker}) - r_blocker({owner}) > 0`, forces
  `rate ≥ γ / (γ + π)`;
  `not_quittingCollisionBlockerBalance_of_bonus_nonpos` rules the repair out
  entirely once the pair bonus is nonpositive.
* `quittingCollisionBlockerGain_ge_of_subFloor` — against the canonical
  reward bound `M`, the blocker's one-stage continuation gain is at least
  `γ - 4 * M * rate`, so genuine sub-floor compensation cannot survive a
  vanishing collision rate
  (`not_quittingCollisionRepairWorks_of_subFloor_of_rate_lt`).

## Method

The mechanism profile is a phase switch at stage one, so a unilateral
deviation splits exactly once:
`quittingRootSequenceHazardTerminalValue_zero_split` writes any root
sequence's deviated value as the stage-zero absorbing contribution of the
deviated row plus that row's survival times the shifted value.  Applied to
the repair row this yields the deviation caps directly, the blocker's sure
exit killing the survival factor of every other player.

All statements are at an arbitrary finite player set: one owner, one blocker,
and an arbitrary set of spectators, each carrying its own no-join inequality.
Three players is the smallest instance with a spectator.

Everything here is original to this development; the quitting-game model is
that of Solan and Vieille, *Quitting games*, Israel J. Math. 119 (2001).
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

/-! ## Two elementary hazard sequences -/

/-- The hazard that continues at stage zero and then follows `g`. -/
def quittingContinueThenHazard (g : ℕ → PMF Bool) : ℕ → PMF Bool
  | 0 => PMF.pure false
  | time + 1 => g time

@[simp] theorem quittingContinueThenHazard_zero (g : ℕ → PMF Bool) :
    quittingContinueThenHazard g 0 = PMF.pure false := rfl

@[simp] theorem quittingContinueThenHazard_succ (g : ℕ → PMF Bool) (time : ℕ) :
    quittingContinueThenHazard g (time + 1) = g time := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Splitting a deviation at the first stage -/

omit [Fintype ι] [DecidableEq ι] in
/-- Every root sequence is the phase switch that plays its own stage-zero row
once and its shift afterwards. -/
theorem quittingPhaseSwitchRoots_shift_one (roots : ℕ → ι → PMF Bool) :
    quittingPhaseSwitchRoots roots (fun time => roots (time + 1)) 1 = roots := by
  funext time
  rcases Nat.eq_zero_or_pos time with rfl | hpos
  · exact quittingPhaseSwitchRoots_of_lt roots _ Nat.one_pos
  · rw [quittingPhaseSwitchRoots_of_le roots _ hpos]
    congr 1
    omega

/-- **The stage-zero split.**  A unilateral hazard deviation against a root
sequence is worth the stage-zero absorbing contribution of the deviated row
plus the probability that that row absorbs nobody times the value of the
remaining deviation against the shifted sequence. -/
theorem quittingRootSequenceHazardTerminalValue_zero_split
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 =
      quittingRootAbsorbingContribution reward
          (Function.update (roots 0) who (hazard 0)) who +
        quittingStationaryContinueMass
            (Function.update (roots 0) who (hazard 0)) *
          quittingRootSequenceHazardTerminalValue reward
            (fun time => roots (time + 1)) who
            (fun time => hazard (time + 1)) 0 := by
  have hphase : quittingRootSequenceHazardTerminalValue reward roots who hazard 0 =
      quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots roots (fun time => roots (time + 1)) 1) who
        hazard 0 := by
    rw [quittingPhaseSwitchRoots_shift_one]
  have htrunc : quittingRootSequenceHazardTerminalValue reward
      (quittingTruncatedRoots roots 1) who
      (quittingTruncatedHazard hazard 1) 0 =
      quittingRootAbsorbingContribution reward
        (Function.update (roots 0) who (hazard 0)) who := by
    unfold quittingRootSequenceHazardTerminalValue
    rw [quittingRootSequenceUpdate_quittingTruncatedRoots,
      quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum,
      Finset.sum_range_one, quittingJointSurvivalWeight_eq_prod,
      Finset.prod_range_zero, one_mul]
    rfl
  have hsurvival : quittingJointSurvivalWeight
      (quittingRootSequenceUpdate roots who hazard) 0 1 =
      quittingStationaryContinueMass
        (Function.update (roots 0) who (hazard 0)) := by
    rw [quittingJointSurvivalWeight_eq_prod, Finset.prod_range_one]
    rfl
  have hcomm : (fun offset => hazard (1 + offset)) =
      fun offset => hazard (offset + 1) := by
    funext offset
    rw [Nat.add_comm]
  rw [hphase, quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots,
    htrunc, hsurvival, hcomm]

omit [DecidableEq ι] in
/-- A root sequence whose stage-zero row absorbs surely is worth exactly that
row's absorbing contribution. -/
theorem quittingRootSequenceTerminalValue_zero_of_continueMass_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hmass : quittingStationaryContinueMass (roots 0) = 0) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      quittingRootAbsorbingContribution reward (roots 0) who := by
  rw [quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
      reward roots who 1,
    quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum,
    Finset.sum_range_one, quittingJointSurvivalWeight_eq_prod,
    Finset.prod_range_zero, one_mul, quittingJointSurvivalWeight_eq_prod,
    Finset.prod_range_one, Nat.add_zero, hmass, zero_mul, add_zero]

/-- Realising a hazard sequence as a behavior deviation. -/
theorem quittingTerminalPayoff_update_hazardStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hazard : ℕ → PMF Bool) :
    quittingTerminalPayoff reward
        (Function.update profile who (fun time _history => hazard time)) who =
      quittingRootSequenceHazardTerminalValue reward
        (quittingProfileLiveRoot reward profile) who hazard 0 := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue]
  rfl

/-- **Quitting at once.**  Whatever the profile prescribes afterwards, the
deviation that quits immediately is worth the stage-zero quit value. -/
theorem quittingTerminalPayoff_update_quitNow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (fun _time _history => (PMF.pure true : PMF Bool))) who =
      quittingStationaryFixedOpponentsQuitValue reward
        (quittingProfileLiveRoot reward profile 0) who := by
  rw [quittingTerminalPayoff_update_hazardStrategy reward profile who
      (fun _ => PMF.pure true),
    quittingRootSequenceHazardTerminalValue_zero_split,
    quittingStationaryContinueMass_update_pure_true_eq_zero, zero_mul, add_zero]
  rfl

/-- **Never quitting, against opponents who absorb surely.**  If the
deviator's opponents already absorb the game at stage zero, continuing
forever is worth the stage-zero continue reward. -/
theorem quittingTerminalPayoff_update_neverQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hmass : quittingStationaryFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward profile 0) who = 0) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (fun _time _history => (PMF.pure false : PMF Bool))) who =
      quittingStationaryFixedOpponentsContinueReward reward
        (quittingProfileLiveRoot reward profile 0) who := by
  rw [quittingTerminalPayoff_update_hazardStrategy reward profile who
      (fun _ => PMF.pure false),
    quittingRootSequenceHazardTerminalValue_zero_split]
  rw [show quittingStationaryContinueMass (Function.update
      (quittingProfileLiveRoot reward profile 0) who (PMF.pure false)) = 0 from
    hmass, zero_mul, add_zero]
  rfl

/-- **Continuing first, then anything.**  For every continuation hazard `g`
there is a behavior deviation that continues at stage zero and afterwards
plays `g`; its value is the stage-zero continue reward plus the opponents'
stage-zero survival times `g`'s value against the shifted sequence. -/
theorem exists_quittingTerminalPayoff_update_continueThen
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (g : ℕ → PMF Bool) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
          (Function.update profile who deviation) who =
        quittingStationaryFixedOpponentsContinueReward reward
            (quittingProfileLiveRoot reward profile 0) who +
          quittingStationaryFixedOpponentsContinueMass
              (quittingProfileLiveRoot reward profile 0) who *
            quittingRootSequenceHazardTerminalValue reward
              (fun time => quittingProfileLiveRoot reward profile (time + 1))
              who g 0 := by
  refine ⟨fun time _history => quittingContinueThenHazard g time, ?_⟩
  rw [quittingTerminalPayoff_update_hazardStrategy reward profile who
      (quittingContinueThenHazard g),
    quittingRootSequenceHazardTerminalValue_zero_split]
  rfl

/-! ## The one-stage punished profile, in general form

The next three theorems are stated for an arbitrary stage-zero row and an
arbitrary constant punishment row; the collision mechanism is the instance in
which the row is the sure-blocker repair row. -/

/-- The profile that plays `root` once and then the constant row `punishRow`
forever. -/
def quittingOneStagePunishedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root punishRow : ι → PMF Bool) : (quittingGame reward).BehaviorProfile :=
  quittingPhaseSwitchProfile reward (fun _ => root) (fun _ => punishRow) 1

omit [DecidableEq ι] in
/-- The one-stage punished profile plays `root` at the unique live history of
stage zero. -/
@[simp] theorem quittingProfileLiveRoot_oneStagePunishedProfile_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root punishRow : ι → PMF Bool) :
    quittingProfileLiveRoot reward
        (quittingOneStagePunishedProfile reward root punishRow) 0 = root := by
  rw [quittingOneStagePunishedProfile,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile]
  exact quittingPhaseSwitchRoots_of_lt _ _ Nat.one_pos

omit [DecidableEq ι] in
/-- If the stage-zero row absorbs surely, the one-stage punished profile pays
exactly that row's absorbing contribution. -/
theorem quittingTerminalPayoff_oneStagePunishedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root punishRow : ι → PMF Bool) (who : ι)
    (hmass : quittingStationaryContinueMass root = 0) :
    quittingTerminalPayoff reward
        (quittingOneStagePunishedProfile reward root punishRow) who =
      quittingRootAbsorbingContribution reward root who := by
  have hroot : quittingProfileLiveRoot reward
      (quittingOneStagePunishedProfile reward root punishRow) 0 = root :=
    quittingProfileLiveRoot_oneStagePunishedProfile_zero reward root punishRow
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingRootSequenceTerminalValue_zero_of_continueMass_eq_zero reward _ who
      (by rw [hroot]; exact hmass), hroot]

/-- **The one-stage punished deviation cap.**  Every unilateral behavior
deviation against the one-stage punished profile is worth at most the
one-stage Bellman value whose continuation is the deviator's own constant-row
cap against the punishment row. -/
theorem quittingTerminalPayoff_update_oneStagePunishedProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root punishRow : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingOneStagePunishedProfile reward root punishRow)
          who deviation) who ≤
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
        (quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who *
            quittingStationaryUnilateralCap reward punishRow who) := by
  set hazard := quittingBehaviorLiveHazard reward deviation with hhazard
  set cap := quittingStationaryUnilateralCap reward punishRow who with hcap
  set dev := Function.update root who (hazard 0) with hdev
  have hvalue : quittingTerminalPayoff reward
      (Function.update (quittingOneStagePunishedProfile reward root punishRow)
        who deviation) who =
      quittingRootAbsorbingContribution reward dev who +
        quittingStationaryContinueMass dev *
          quittingRootSequenceHazardTerminalValue reward (fun _ => punishRow) who
            (fun time => hazard (time + 1)) 0 := by
    have hzero : quittingPhaseSwitchRoots (fun _ => root)
        (fun _ => punishRow) 1 0 = root :=
      quittingPhaseSwitchRoots_of_lt _ _ Nat.one_pos
    have hshift : (fun time => quittingPhaseSwitchRoots (fun _ => root)
        (fun _ => punishRow) 1 (time + 1)) = fun _ : ℕ => punishRow := by
      funext time
      exact quittingPhaseSwitchRoots_of_le _ _ (Nat.le_add_left 1 time)
    rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
      quittingOneStagePunishedProfile,
      quittingProfileLiveRoot_quittingPhaseSwitchProfile,
      quittingRootSequenceHazardTerminalValue_zero_split, hzero, hshift]
  have hpunish := quittingRootSequenceHazardTerminalValue_const_le_cap reward
    punishRow who (fun time => hazard (time + 1))
  have hmass : 0 ≤ quittingStationaryContinueMass dev :=
    quittingStationaryContinueMass_nonneg dev
  have hstep : quittingRootAbsorbingContribution reward dev who +
      quittingStationaryContinueMass dev * cap ≤
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
        (quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who * cap) := by
    have hbellman := quittingRootSuccessorPayoff_le_liveBellmanValue reward
      (fun _ => dev) who (fun _ => cap) 0
    have hleft : quittingRootSuccessorPayoff reward (fun _ => cap) dev who =
        quittingRootAbsorbingContribution reward dev who +
          quittingStationaryContinueMass dev * cap :=
      quittingRootExpectedPayoff_eq_absorbingContribution_add reward _ dev who
    have hquit : quittingFixedOpponentsQuitValue reward (fun _ => dev) who 0 =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
      change quittingRootAbsorbingContribution reward
        (Function.update dev who (PMF.pure true)) who = _
      rw [hdev, Function.update_idem]
      rfl
    have hcontinue :
        quittingFixedOpponentsContinueReward reward (fun _ => dev) who 0 =
        quittingStationaryFixedOpponentsContinueReward reward root who := by
      change quittingRootAbsorbingContribution reward
        (Function.update dev who (PMF.pure false)) who = _
      rw [hdev, Function.update_idem]
      rfl
    have hmassEq : quittingFixedOpponentsContinueMass (fun _ => dev) who 0 =
        quittingStationaryFixedOpponentsContinueMass root who := by
      change quittingStationaryContinueMass
        (Function.update dev who (PMF.pure false)) = _
      rw [hdev, Function.update_idem]
      rfl
    rw [hleft] at hbellman
    unfold quittingLiveBellmanValue at hbellman
    rwa [hquit, hcontinue, hmassEq] at hbellman
  refine le_trans (le_of_eq hvalue) (le_trans ?_ hstep)
  have hscaled := mul_le_mul_of_nonneg_left hpunish hmass
  linarith

/-! ## The mechanism -/

/-- The **sure-blocker repair row** at collision rate `rate`: the blocker
quits surely, the owner quits with probability `rate`, every spectator
continues. -/
def quittingCollisionRepairRoot (owner blocker : ι) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) : ι → PMF Bool :=
  quittingSureSetOwnerRoot ({blocker} : Finset ι) owner rate hrate0 hrate1

/-- The **prescribed payoff** of the mechanism: the `rate`-mixture of the
blocker's solo exit and the owner-blocker collision. -/
def quittingCollisionRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (rate : ℝ) : Payoff ι :=
  quittingSureSetOwnerValue reward ({blocker} : Finset ι) owner rate

omit [Fintype ι] in
@[simp] theorem quittingCollisionRepairValue_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (rate : ℝ) (who : ι) :
    quittingCollisionRepairValue reward owner blocker rate who =
      (1 - rate) * quittingSetReward reward ({blocker} : Finset ι) who +
        rate * quittingSetReward reward ({owner, blocker} : Finset ι) who :=
  rfl

/-- **Owner endpoint optimality.**  The owner's prescribed mixture already
attains the better of its two stage-zero endpoints. -/
def QuittingCollisionOwnerOptimal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (rate : ℝ) : Prop :=
  max (quittingSetReward reward ({owner, blocker} : Finset ι) owner)
      (quittingSetReward reward ({blocker} : Finset ι) owner) ≤
    quittingCollisionRepairValue reward owner blocker rate owner

/-- **Spectator no-join.**  No spectator gains by joining the exit at the
same mixture rate.  Both of a spectator's actions absorb the game at stage
zero, so this inequality is independent of every punishment promise. -/
def QuittingCollisionSpectatorNoJoin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (rate : ℝ) : Prop :=
  ∀ spectator, spectator ≠ owner → spectator ≠ blocker →
    (1 - rate) *
          quittingSetReward reward ({spectator, blocker} : Finset ι) spectator +
        rate * quittingSetReward reward
          ({owner, spectator, blocker} : Finset ι) spectator ≤
      quittingCollisionRepairValue reward owner blocker rate spectator

/-- **Blocker-floor balance.**  Continuing at stage zero pays the blocker the
owner's solo exit with probability `rate` and, otherwise, at best its exact
punishment value; the prescribed payoff must dominate that. -/
def QuittingCollisionBlockerBalance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (rate : ℝ) : Prop :=
  rate * quittingSetReward reward ({owner} : Finset ι) blocker +
      (1 - rate) * quittingPunishmentValue reward blocker ≤
    quittingCollisionRepairValue reward owner blocker rate blocker

/-- The balance condition, written as the exact collision-compensation
balance between the blocker's sub-floor gap and its pair bonus. -/
theorem quittingCollisionBlockerBalance_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (rate : ℝ) :
    QuittingCollisionBlockerBalance reward owner blocker rate ↔
      0 ≤ (1 - rate) * (quittingSetReward reward ({blocker} : Finset ι) blocker -
            quittingPunishmentValue reward blocker) +
          rate * (quittingSetReward reward ({owner, blocker} : Finset ι) blocker -
            quittingSetReward reward ({owner} : Finset ι) blocker) := by
  unfold QuittingCollisionBlockerBalance
  rw [quittingCollisionRepairValue_apply]
  constructor <;> intro h <;> nlinarith [h]

/-- The **mechanism works** at `rate`: for every positive tolerance some
behavior profile whose stage-zero row is the repair row is a terminal
`ε`-Nash equilibrium.  The continuation is unconstrained, so the punishment
may be made more accurate as the tolerance shrinks. -/
def QuittingCollisionRepairWorks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ profile : (quittingGame reward).BehaviorProfile,
    quittingProfileLiveRoot reward profile 0 =
        quittingCollisionRepairRoot owner blocker rate hrate0 hrate1 ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        profile

/-! ## Exact stage-zero data of the repair row -/

section RowData

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner blocker : ι} {rate : ℝ} {hrate0 : 0 ≤ rate} {hrate1 : rate ≤ 1}

omit [Fintype ι] [DecidableEq ι] in
/-- The owner is outside the blocker's singleton exit set. -/
theorem quittingCollisionOwner_notMem {owner blocker : ι}
    (hne : owner ≠ blocker) : owner ∉ ({blocker} : Finset ι) := by simpa using hne

/-- The repair row absorbs at stage zero with probability one. -/
theorem quittingCollisionRepairRoot_continueMass (hne : owner ≠ blocker) :
    quittingStationaryContinueMass
      (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) = 0 :=
  stationaryContinueMass_sureSetOwnerRoot_of_nonempty
    (Finset.singleton_nonempty blocker) (quittingCollisionOwner_notMem hne)
    rate hrate0 hrate1

/-- The repair row's prescribed payoff. -/
theorem quittingCollisionRepairRoot_absorbingContribution
    (hne : owner ≠ blocker) (who : ι) :
    quittingRootAbsorbingContribution reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) who =
      quittingCollisionRepairValue reward owner blocker rate who :=
  quittingRootAbsorbingContribution_sureSetOwnerRoot reward
    (quittingCollisionOwner_notMem hne) rate hrate0 hrate1 who

/-- Quitting now, for the owner, is the owner-blocker collision. -/
theorem quittingCollisionRepairRoot_owner_quitValue :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) owner =
      quittingSetReward reward ({owner, blocker} : Finset ι) owner :=
  fixedOpponentsQuitValue_sureSetOwnerRoot_owner reward rate hrate0 hrate1

/-- Continuing now, for the owner, is the blocker's solo exit. -/
theorem quittingCollisionRepairRoot_owner_continueReward (hne : owner ≠ blocker) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) owner =
      quittingSetReward reward ({blocker} : Finset ι) owner :=
  fixedOpponentsContinueReward_sureSetOwnerRoot_owner reward
    (quittingCollisionOwner_notMem hne) rate hrate0 hrate1

/-- The owner's opponents absorb surely: the blocker quits. -/
theorem quittingCollisionRepairRoot_owner_continueMass (hne : owner ≠ blocker) :
    quittingStationaryFixedOpponentsContinueMass
      (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) owner = 0 :=
  fixedOpponentsContinueMass_sureSetOwnerRoot_owner
    (Finset.singleton_nonempty blocker) (quittingCollisionOwner_notMem hne)
    rate hrate0 hrate1

/-- Quitting now, for a spectator, is the joined mixture. -/
theorem quittingCollisionRepairRoot_spectator_quitValue (hne : owner ≠ blocker)
    {spectator : ι} (hspectator : spectator ≠ owner) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
        spectator =
      (1 - rate) *
          quittingSetReward reward ({spectator, blocker} : Finset ι) spectator +
        rate * quittingSetReward reward
          ({owner, spectator, blocker} : Finset ι) spectator :=
  fixedOpponentsQuitValue_sureSetOwnerRoot_other reward
    (quittingCollisionOwner_notMem hne) hspectator rate hrate0 hrate1

/-- Continuing now, for a spectator, is the prescribed payoff itself. -/
theorem quittingCollisionRepairRoot_spectator_continueReward
    (hne : owner ≠ blocker) {spectator : ι} (hspectator : spectator ≠ owner)
    (hblocker : spectator ≠ blocker) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
        spectator =
      quittingCollisionRepairValue reward owner blocker rate spectator := by
  rw [quittingCollisionRepairRoot,
    fixedOpponentsContinueReward_sureSetOwnerRoot_other reward
      (quittingCollisionOwner_notMem hne) hspectator rate hrate0 hrate1,
    Finset.erase_eq_of_notMem (by simpa using hblocker)]
  rfl

/-- A spectator's opponents absorb surely: the blocker quits. -/
theorem quittingCollisionRepairRoot_spectator_continueMass
    (hne : owner ≠ blocker) {spectator : ι} (hspectator : spectator ≠ owner)
    (hblocker : spectator ≠ blocker) :
    quittingStationaryFixedOpponentsContinueMass
      (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
      spectator = 0 := by
  refine fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_nonempty
    (quittingCollisionOwner_notMem hne) hspectator ?_ rate hrate0 hrate1
  rw [Finset.erase_eq_of_notMem (by simpa using hblocker)]
  exact Finset.singleton_nonempty blocker

/-- Quitting now, for the blocker, is the prescribed payoff itself. -/
theorem quittingCollisionRepairRoot_blocker_quitValue (hne : owner ≠ blocker) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) blocker =
      quittingCollisionRepairValue reward owner blocker rate blocker := by
  rw [quittingCollisionRepairRoot,
    fixedOpponentsQuitValue_sureSetOwnerRoot_other reward
      (quittingCollisionOwner_notMem hne) (Ne.symm hne) rate hrate0 hrate1,
    Finset.insert_eq_self.mpr (Finset.mem_singleton_self blocker)]
  rfl

/-- Continuing now, for the blocker, collects the owner's solo exit at the
collision rate and nothing otherwise. -/
theorem quittingCollisionRepairRoot_blocker_continueReward
    (hne : owner ≠ blocker) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) blocker =
      rate * quittingSetReward reward ({owner} : Finset ι) blocker := by
  rw [quittingCollisionRepairRoot,
    fixedOpponentsContinueReward_sureSetOwnerRoot_other reward
      (quittingCollisionOwner_notMem hne) (Ne.symm hne) rate hrate0 hrate1,
    Finset.erase_singleton, quittingSureSetOwnerValue_empty]

/-- The blocker's opponents survive exactly when the owner does not quit. -/
theorem quittingCollisionRepairRoot_blocker_continueMass
    (hne : owner ≠ blocker) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) blocker =
      1 - rate :=
  fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_empty
    (Ne.symm hne) (Finset.erase_singleton blocker) rate hrate0 hrate1

end RowData

/-! ## Necessity -/

section Necessity

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner blocker : ι} {rate : ℝ} {hrate0 : 0 ≤ rate} {hrate1 : rate ≤ 1}

/-- Under the mechanism shape the prescribed payoff is the two-set mixture,
whatever the continuation. -/
theorem quittingTerminalPayoff_of_collisionRepairShape (hne : owner ≠ blocker)
    {profile : (quittingGame reward).BehaviorProfile}
    (hshape : quittingProfileLiveRoot reward profile 0 =
      quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
    (who : ι) :
    quittingTerminalPayoff reward profile who =
      quittingCollisionRepairValue reward owner blocker rate who := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingRootSequenceTerminalValue_zero_of_continueMass_eq_zero reward _ who
      (by rw [hshape]; exact quittingCollisionRepairRoot_continueMass hne),
    hshape, quittingCollisionRepairRoot_absorbingContribution hne]

/-- **Necessity of owner endpoint optimality, `ε` form.** -/
theorem quittingCollisionOwnerCap_le_of_isεAsymptoticNash (hne : owner ≠ blocker)
    {profile : (quittingGame reward).BehaviorProfile}
    (hshape : quittingProfileLiveRoot reward profile 0 =
      quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
    {ε : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    max (quittingSetReward reward ({owner, blocker} : Finset ι) owner)
        (quittingSetReward reward ({blocker} : Finset ι) owner) ≤
      quittingCollisionRepairValue reward owner blocker rate owner + ε := by
  have hvalue := quittingTerminalPayoff_of_collisionRepairShape hne hshape owner
  refine max_le ?_ ?_
  · have hdev := hnash owner
      (fun _time _history => (PMF.pure true : PMF Bool))
    rw [quittingTerminalPayoff_update_quitNow, hvalue, hshape,
      quittingCollisionRepairRoot_owner_quitValue] at hdev
    exact hdev
  · have hmass : quittingStationaryFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward profile 0) owner = 0 := by
      rw [hshape]
      exact quittingCollisionRepairRoot_owner_continueMass hne
    have hdev := hnash owner
      (fun _time _history => (PMF.pure false : PMF Bool))
    rw [quittingTerminalPayoff_update_neverQuit reward profile owner hmass,
      hvalue, hshape,
      quittingCollisionRepairRoot_owner_continueReward hne] at hdev
    exact hdev

/-- **Necessity of spectator no-join, `ε` form.** -/
theorem quittingCollisionSpectatorJoin_le_of_isεAsymptoticNash
    (hne : owner ≠ blocker)
    {profile : (quittingGame reward).BehaviorProfile}
    (hshape : quittingProfileLiveRoot reward profile 0 =
      quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
    {ε : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    {spectator : ι} (hspectator : spectator ≠ owner) :
    (1 - rate) *
          quittingSetReward reward ({spectator, blocker} : Finset ι) spectator +
        rate * quittingSetReward reward
          ({owner, spectator, blocker} : Finset ι) spectator ≤
      quittingCollisionRepairValue reward owner blocker rate spectator + ε := by
  have hvalue := quittingTerminalPayoff_of_collisionRepairShape hne hshape
    spectator
  have hdev := hnash spectator
    (fun _time _history => (PMF.pure true : PMF Bool))
  rw [quittingTerminalPayoff_update_quitNow, hvalue, hshape,
    quittingCollisionRepairRoot_spectator_quitValue hne hspectator] at hdev
  exact hdev

/-- **Necessity of blocker-floor balance, `ε` form.**  The blocker continues
at stage zero and then best responds; no continuation, however history
dependent, holds it below its exact punishment value. -/
theorem quittingCollisionBlockerFloor_le_of_isεAsymptoticNash
    (hne : owner ≠ blocker)
    {profile : (quittingGame reward).BehaviorProfile}
    (hshape : quittingProfileLiveRoot reward profile 0 =
      quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
    {ε : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    rate * quittingSetReward reward ({owner} : Finset ι) blocker +
        (1 - rate) * quittingPunishmentValue reward blocker ≤
      quittingCollisionRepairValue reward owner blocker rate blocker + ε := by
  have hvalue := quittingTerminalPayoff_of_collisionRepairShape hne hshape blocker
  have hfamily : ∀ g : ℕ → PMF Bool,
      rate * quittingSetReward reward ({owner} : Finset ι) blocker +
          (1 - rate) * quittingRootSequenceHazardTerminalValue reward
            (fun time => quittingProfileLiveRoot reward profile (time + 1))
            blocker g 0 ≤
        quittingCollisionRepairValue reward owner blocker rate blocker + ε := by
    intro g
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingTerminalPayoff_update_continueThen reward profile blocker g
    have hdev := hnash blocker deviation
    rw [hdeviation, hvalue, hshape,
      quittingCollisionRepairRoot_blocker_continueReward hne,
      quittingCollisionRepairRoot_blocker_continueMass hne] at hdev
    exact hdev
  rcases eq_or_lt_of_le hrate1 with hone | hlt
  · have hfam := hfamily (fun _ => PMF.pure false)
    rw [← hone] at hfam ⊢
    simpa using hfam
  · have hpos : 0 < 1 - rate := by linarith
    have hbound : ∀ g : ℕ → PMF Bool,
        quittingRootSequenceHazardTerminalValue reward
            (fun time => quittingProfileLiveRoot reward profile (time + 1))
            blocker g 0 ≤
          (quittingCollisionRepairValue reward owner blocker rate blocker + ε -
            rate * quittingSetReward reward ({owner} : Finset ι) blocker) /
              (1 - rate) := by
      intro g
      rw [le_div_iff₀ hpos]
      nlinarith [hfamily g]
    have hchi := quittingStationaryPunishmentValue_le_of_forall_hazard_le reward
      (fun time => quittingProfileLiveRoot reward profile (time + 1)) blocker
      hbound
    rw [← quittingPunishmentValue_eq_stationaryPunishmentValue] at hchi
    have hscaled := mul_le_mul_of_nonneg_left hchi hpos.le
    rw [mul_div_cancel₀ _ (ne_of_gt hpos)] at hscaled
    linarith

end Necessity

/-! ## Sufficiency -/

section Sufficiency

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner blocker : ι} {rate : ℝ} {hrate0 : 0 ≤ rate} {hrate1 : rate ≤ 1}

/-- **Sufficiency, at a supplied punishment row.**  With the three conditions
in force and a constant row that punishes the blocker to within `ε` of its
exact min-max, the one-stage punished profile is a terminal `ε`-Nash
equilibrium. -/
theorem isεAsymptoticNash_quittingCollisionRepairProfile (hne : owner ≠ blocker)
    (howner : QuittingCollisionOwnerOptimal reward owner blocker rate)
    (hspectator : QuittingCollisionSpectatorNoJoin reward owner blocker rate)
    (hbalance : QuittingCollisionBlockerBalance reward owner blocker rate)
    {ε : ℝ} (hε : 0 ≤ ε) {punishRow : ι → PMF Bool}
    (hpunish : quittingStationaryUnilateralCap reward punishRow blocker ≤
      quittingPunishmentValue reward blocker + ε) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
      (quittingOneStagePunishedProfile reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
        punishRow) := by
  have hopt : max (quittingSetReward reward ({owner, blocker} : Finset ι) owner)
      (quittingSetReward reward ({blocker} : Finset ι) owner) ≤
      quittingCollisionRepairValue reward owner blocker rate owner := howner
  have hbal : rate * quittingSetReward reward ({owner} : Finset ι) blocker +
      (1 - rate) * quittingPunishmentValue reward blocker ≤
      quittingCollisionRepairValue reward owner blocker rate blocker := hbalance
  intro who deviation
  have hvalue : quittingTerminalPayoff reward
      (quittingOneStagePunishedProfile reward
        (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1)
        punishRow) who =
      quittingCollisionRepairValue reward owner blocker rate who := by
    rw [quittingTerminalPayoff_oneStagePunishedProfile reward _ punishRow who
      (quittingCollisionRepairRoot_continueMass hne),
      quittingCollisionRepairRoot_absorbingContribution hne]
  have hcap := quittingTerminalPayoff_update_oneStagePunishedProfile_le reward
    (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) punishRow who
    deviation
  rw [ge_iff_le, hvalue]
  refine le_trans hcap ?_
  by_cases hwho : who = owner
  · subst who
    rw [quittingCollisionRepairRoot_owner_quitValue,
      quittingCollisionRepairRoot_owner_continueReward hne,
      quittingCollisionRepairRoot_owner_continueMass hne, zero_mul, add_zero]
    linarith
  · by_cases hblocker : who = blocker
    · subst who
      rw [quittingCollisionRepairRoot_blocker_quitValue hne,
        quittingCollisionRepairRoot_blocker_continueReward hne,
        quittingCollisionRepairRoot_blocker_continueMass hne]
      have hnonneg : (0 : ℝ) ≤ 1 - rate := by linarith
      have hle : (1 - rate) *
          quittingStationaryUnilateralCap reward punishRow blocker ≤
          (1 - rate) * quittingPunishmentValue reward blocker + ε := by
        nlinarith [mul_le_mul_of_nonneg_left hpunish hnonneg]
      exact max_le (by linarith) (by linarith)
    · have hjoin := hspectator who hwho hblocker
      rw [quittingCollisionRepairRoot_spectator_quitValue hne hwho,
        quittingCollisionRepairRoot_spectator_continueReward hne hwho hblocker,
        quittingCollisionRepairRoot_spectator_continueMass hne hwho hblocker,
        zero_mul, add_zero]
      exact max_le (by linarith) (by linarith)

end Sufficiency

/-! ## The characterization -/

/-- **The exact sure-blocker collision-repair characterization.**  The
mechanism admits accuracy-indexed terminal equilibria at collision rate
`rate` if and only if the owner's endpoint optimality, every spectator's
no-join inequality, and the blocker's floor balance against the exact min-max
all hold. -/
theorem quittingCollisionRepairWorks_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : owner ≠ blocker)
    {rate : ℝ} (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1 ↔
      QuittingCollisionOwnerOptimal reward owner blocker rate ∧
        QuittingCollisionSpectatorNoJoin reward owner blocker rate ∧
          QuittingCollisionBlockerBalance reward owner blocker rate := by
  constructor
  · intro hworks
    refine ⟨?_, ?_, ?_⟩
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨profile, hshape, hnash⟩ := hworks ε hε
      exact quittingCollisionOwnerCap_le_of_isεAsymptoticNash hne hshape hnash
    · intro spectator hspectator _hblocker
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨profile, hshape, hnash⟩ := hworks ε hε
      exact quittingCollisionSpectatorJoin_le_of_isεAsymptoticNash hne hshape
        hnash hspectator
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨profile, hshape, hnash⟩ := hworks ε hε
      exact quittingCollisionBlockerFloor_le_of_isεAsymptoticNash hne hshape hnash
  · rintro ⟨howner, hspectator, hbalance⟩ ε hε
    haveI : Nonempty (ι → PMF Bool) := ⟨fun _ => PMF.pure false⟩
    obtain ⟨punishRow, hpunishRow⟩ : ∃ punishRow : ι → PMF Bool,
        quittingStationaryUnilateralCap reward punishRow blocker <
          quittingPunishmentValue reward blocker + ε := by
      refine exists_lt_of_ciInf_lt (f := fun punishRow : ι → PMF Bool =>
        quittingStationaryUnilateralCap reward punishRow blocker) ?_
      change quittingStationaryPunishmentValue reward blocker < _
      rw [← quittingPunishmentValue_eq_stationaryPunishmentValue]
      linarith
    refine ⟨quittingOneStagePunishedProfile reward
      (quittingCollisionRepairRoot owner blocker rate hrate0 hrate1) punishRow,
      quittingProfileLiveRoot_oneStagePunishedProfile_zero reward _ _, ?_⟩
    exact isεAsymptoticNash_quittingCollisionRepairProfile hne howner
      hspectator hbalance hε.le hpunishRow.le

/-! ## The sure rate collapses to the sure-exit pair

At `rate = 1` the mechanism prescribes the sure joint exit of the owner and
the blocker.  Nobody can then reach the punishment phase, and the three
conditions degenerate to the exact sure-exit-set test for the pair: the
punishment threat is worth nothing at the sure rate. -/

/-- **The sure collision rate is the sure-exit pair.**  At `rate = 1` the
mechanism works exactly when `{owner, blocker}` is a sure exit set, so the
exact min-max drops out of the criterion entirely. -/
theorem quittingCollisionRepairWorks_one_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : owner ≠ blocker) :
    QuittingCollisionRepairWorks reward owner blocker 1 zero_le_one le_rfl ↔
      IsQuittingSureExitSet reward ({owner, blocker} : Finset ι) := by
  have hownerErase : ({owner, blocker} : Finset ι).erase owner = {blocker} :=
    Finset.erase_insert (by simp [hne])
  have hblockerErase :
      ({owner, blocker} : Finset ι).erase blocker = {owner} := by
    rw [Finset.pair_comm]
    exact Finset.erase_insert (by simp [Ne.symm hne])
  have hownerInsert : insert owner ({owner, blocker} : Finset ι) =
      {owner, blocker} := Finset.insert_eq_self.mpr (by simp)
  have hblockerInsert : insert blocker ({owner, blocker} : Finset ι) =
      {owner, blocker} := Finset.insert_eq_self.mpr (by simp)
  rw [quittingCollisionRepairWorks_iff reward hne,
    isQuittingSureExitSet_iff_forall_max]
  constructor
  · rintro ⟨howner, hspectator, hbalance⟩ who
    by_cases hwho : who = owner
    · subst who
      have h : max (quittingSetReward reward ({owner, blocker} : Finset ι) owner)
          (quittingSetReward reward ({blocker} : Finset ι) owner) ≤
          (1 - (1 : ℝ)) * quittingSetReward reward ({blocker} : Finset ι) owner +
            1 * quittingSetReward reward ({owner, blocker} : Finset ι) owner :=
        howner
      rw [hownerInsert, hownerErase]
      linarith [h]
    · by_cases hblocker : who = blocker
      · subst who
        have h : 1 * quittingSetReward reward ({owner} : Finset ι) blocker +
            (1 - (1 : ℝ)) * quittingPunishmentValue reward blocker ≤
            (1 - (1 : ℝ)) *
                quittingSetReward reward ({blocker} : Finset ι) blocker +
              1 * quittingSetReward reward
                ({owner, blocker} : Finset ι) blocker :=
          hbalance
        rw [hblockerInsert, hblockerErase]
        exact max_le le_rfl (by linarith [h])
      · have h : (1 - (1 : ℝ)) *
              quittingSetReward reward ({who, blocker} : Finset ι) who +
            1 * quittingSetReward reward
              ({owner, who, blocker} : Finset ι) who ≤
            (1 - (1 : ℝ)) * quittingSetReward reward ({blocker} : Finset ι) who +
              1 * quittingSetReward reward
                ({owner, blocker} : Finset ι) who :=
          hspectator who hwho hblocker
        rw [Finset.erase_eq_of_notMem (by simp [hwho, hblocker]),
          Finset.insert_comm]
        exact max_le (by linarith [h]) le_rfl
  · intro htoggle
    refine ⟨?_, ?_, ?_⟩
    · have h := htoggle owner
      rw [hownerInsert, hownerErase] at h
      unfold QuittingCollisionOwnerOptimal
      rw [quittingCollisionRepairValue_apply]
      linarith [h]
    · intro spectator hspectator hblocker
      have h := htoggle spectator
      rw [Finset.erase_eq_of_notMem (by simp [hspectator, hblocker]),
        Finset.insert_comm] at h
      rw [quittingCollisionRepairValue_apply]
      have hmax := le_trans (le_max_left _ _) h
      linarith [hmax]
    · have h := htoggle blocker
      rw [hblockerInsert, hblockerErase] at h
      unfold QuittingCollisionBlockerBalance
      rw [quittingCollisionRepairValue_apply]
      have hmax := le_trans (le_max_right _ _) h
      linarith [hmax]

/-! ## What the owner condition forces

The owner's prescribed payoff is a convex combination of its two stage-zero
endpoints, so endpoint optimality is an *equality* with their maximum.  Away
from a tie it therefore pins the collision rate to an endpoint, and at an
interior rate it forces exact owner indifference. -/

section OwnerEndpoint

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner blocker : ι} {rate : ℝ}

omit [Fintype ι] in
/-- **Endpoint optimality is the equality form.**  At a legal collision rate
the prescribed owner mixture is optimal exactly when it *equals* the better
endpoint. -/
theorem quittingCollisionOwnerOptimal_iff_eq_max
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    QuittingCollisionOwnerOptimal reward owner blocker rate ↔
      (1 - rate) * quittingSetReward reward ({blocker} : Finset ι) owner +
          rate * quittingSetReward reward ({owner, blocker} : Finset ι) owner =
        max (quittingSetReward reward ({owner, blocker} : Finset ι) owner)
          (quittingSetReward reward ({blocker} : Finset ι) owner) := by
  unfold QuittingCollisionOwnerOptimal
  rw [quittingCollisionRepairValue_apply]
  have hconvex : (1 - rate) *
        quittingSetReward reward ({blocker} : Finset ι) owner +
      rate * quittingSetReward reward ({owner, blocker} : Finset ι) owner ≤
      max (quittingSetReward reward ({owner, blocker} : Finset ι) owner)
        (quittingSetReward reward ({blocker} : Finset ι) owner) := by
    nlinarith [le_max_left
        (quittingSetReward reward ({owner, blocker} : Finset ι) owner)
        (quittingSetReward reward ({blocker} : Finset ι) owner),
      le_max_right (quittingSetReward reward ({owner, blocker} : Finset ι) owner)
        (quittingSetReward reward ({blocker} : Finset ι) owner)]
  exact ⟨fun h => le_antisymm hconvex h, fun h => h.ge⟩

omit [Fintype ι] in
/-- A strictly profitable collision forces the sure collision rate. -/
theorem eq_one_of_quittingCollisionOwnerOptimal_of_lt (hrate1 : rate ≤ 1)
    (hlt : quittingSetReward reward ({blocker} : Finset ι) owner <
      quittingSetReward reward ({owner, blocker} : Finset ι) owner)
    (hopt : QuittingCollisionOwnerOptimal reward owner blocker rate) :
    rate = 1 := by
  unfold QuittingCollisionOwnerOptimal at hopt
  rw [quittingCollisionRepairValue_apply, max_eq_left hlt.le] at hopt
  nlinarith [hopt]

omit [Fintype ι] in
/-- A strictly costly collision forces the vanishing collision rate. -/
theorem eq_zero_of_quittingCollisionOwnerOptimal_of_lt (hrate0 : 0 ≤ rate)
    (hlt : quittingSetReward reward ({owner, blocker} : Finset ι) owner <
      quittingSetReward reward ({blocker} : Finset ι) owner)
    (hopt : QuittingCollisionOwnerOptimal reward owner blocker rate) :
    rate = 0 := by
  unfold QuittingCollisionOwnerOptimal at hopt
  rw [quittingCollisionRepairValue_apply, max_eq_right hlt.le] at hopt
  nlinarith [hopt]

omit [Fintype ι] in
/-- **Interior rates force exact owner indifference.**  A collision carried
at a rate strictly between the endpoints requires the owner to be exactly
indifferent between leaving the blocker alone and joining it. -/
theorem quittingCollisionOwnerOptimal_iff_of_mem_Ioo
    (hrate0 : 0 < rate) (hrate1 : rate < 1) :
    QuittingCollisionOwnerOptimal reward owner blocker rate ↔
      quittingSetReward reward ({blocker} : Finset ι) owner =
        quittingSetReward reward ({owner, blocker} : Finset ι) owner := by
  constructor
  · intro hopt
    rcases lt_trichotomy (quittingSetReward reward ({blocker} : Finset ι) owner)
      (quittingSetReward reward ({owner, blocker} : Finset ι) owner) with
      hlt | heq | hgt
    · exact absurd (eq_one_of_quittingCollisionOwnerOptimal_of_lt hrate1.le hlt
        hopt) (ne_of_lt hrate1)
    · exact heq
    · exact absurd (eq_zero_of_quittingCollisionOwnerOptimal_of_lt hrate0.le hgt
        hopt) (ne_of_gt hrate0)
  · intro heq
    unfold QuittingCollisionOwnerOptimal
    rw [quittingCollisionRepairValue_apply, ← heq, max_self]
    have hring : (1 - rate) *
          quittingSetReward reward ({blocker} : Finset ι) owner +
        rate * quittingSetReward reward ({blocker} : Finset ι) owner =
        quittingSetReward reward ({blocker} : Finset ι) owner := by ring
    rw [hring]

end OwnerEndpoint

/-! ## The blocker's floor: forced intensity and the fixed-gap obstruction -/

section BlockerFloor

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner blocker : ι} {rate : ℝ}

/-- **Forced collision intensity.**  A blocker whose solo exit sits a
positive gap below its exact punishment value can be compensated only at a
collision rate at least the loss share `γ / (γ + π)`, where `γ` is that gap
and `π` the pair bonus. -/
theorem quittingCollisionRate_ge_of_blockerBalance
    (hgap : 0 < quittingPunishmentValue reward blocker -
      quittingSetReward reward ({blocker} : Finset ι) blocker)
    (hbonus : 0 < quittingSetReward reward ({owner, blocker} : Finset ι) blocker -
      quittingSetReward reward ({owner} : Finset ι) blocker)
    (hbalance : QuittingCollisionBlockerBalance reward owner blocker rate) :
    (quittingPunishmentValue reward blocker -
          quittingSetReward reward ({blocker} : Finset ι) blocker) /
        ((quittingPunishmentValue reward blocker -
            quittingSetReward reward ({blocker} : Finset ι) blocker) +
          (quittingSetReward reward ({owner, blocker} : Finset ι) blocker -
            quittingSetReward reward ({owner} : Finset ι) blocker)) ≤ rate := by
  have h := (quittingCollisionBlockerBalance_iff reward owner blocker rate).mp
    hbalance
  rw [div_le_iff₀ (by linarith)]
  nlinarith [h]

/-- **No repair without a pair bonus.**  A sub-floor blocker with a
nonpositive pair bonus cannot be balanced at any collision rate short of the
degenerate sure rate. -/
theorem not_quittingCollisionBlockerBalance_of_bonus_nonpos
    (hgap : 0 < quittingPunishmentValue reward blocker -
      quittingSetReward reward ({blocker} : Finset ι) blocker)
    (hbonus : quittingSetReward reward ({owner, blocker} : Finset ι) blocker -
      quittingSetReward reward ({owner} : Finset ι) blocker ≤ 0)
    (hrate0 : 0 ≤ rate) (hrate1 : rate < 1) :
    ¬ QuittingCollisionBlockerBalance reward owner blocker rate := by
  intro hbalance
  have h := (quittingCollisionBlockerBalance_iff reward owner blocker rate).mp
    hbalance
  nlinarith [mul_nonneg hrate0 (neg_nonneg.mpr hbonus),
    mul_pos hgap (sub_pos.mpr hrate1)]

omit [DecidableEq ι] in
/-- Every extended set reward is inside the canonical reward bound. -/
theorem abs_quittingSetReward_le_quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (S : Finset ι) (who : ι) :
    |quittingSetReward reward S who| ≤ quittingRewardBound reward := by
  by_cases hS : S.Nonempty
  · rw [quittingSetReward_of_nonempty reward hS]
    exact abs_reward_le_quittingRewardBound reward _ who
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, quittingSetReward_empty,
      abs_zero]
    exact quittingRewardBound_nonneg reward

/-- The exact punishment value is inside the canonical reward bound. -/
theorem abs_quittingPunishmentValue_le_quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    |quittingPunishmentValue reward who| ≤ quittingRewardBound reward := by
  refine abs_le.mpr
    ⟨neg_quittingRewardBound_le_quittingPunishmentValue reward who, ?_⟩
  refine (quittingPunishmentValue_le_max_solo reward who).trans (max_le ?_ ?_)
  · exact (le_abs_self _).trans
      (abs_quittingSetReward_le_quittingRewardBound reward {who} who)
  · exact quittingRewardBound_nonneg reward

/-- **The fixed-gap obstruction.**  Against the canonical reward bound `M`, a
blocker whose solo exit sits a gap `γ` below its exact punishment value keeps
a one-stage continuation gain of at least `γ - 4 * M * rate`: the erosion the
collision rate can buy is linear in the rate, so a fixed positive gap
survives every sufficiently small rate. -/
theorem quittingCollisionBlockerGain_ge_of_subFloor
    (hrate0 : 0 ≤ rate) {γ : ℝ}
    (hgap : quittingSetReward reward ({blocker} : Finset ι) blocker + γ ≤
      quittingPunishmentValue reward blocker) :
    γ - 4 * quittingRewardBound reward * rate ≤
      (rate * quittingSetReward reward ({owner} : Finset ι) blocker +
          (1 - rate) * quittingPunishmentValue reward blocker) -
        quittingCollisionRepairValue reward owner blocker rate blocker := by
  rw [quittingCollisionRepairValue_apply]
  have hsolo := abs_le.mp
    (abs_quittingSetReward_le_quittingRewardBound reward ({owner} : Finset ι)
      blocker)
  have hpair := abs_le.mp
    (abs_quittingSetReward_le_quittingRewardBound reward
      ({owner, blocker} : Finset ι) blocker)
  have hown := abs_le.mp
    (abs_quittingSetReward_le_quittingRewardBound reward
      ({blocker} : Finset ι) blocker)
  have hchi := abs_le.mp
    (abs_quittingPunishmentValue_le_quittingRewardBound reward blocker)
  have hkey : 0 ≤ 4 * quittingRewardBound reward -
      (quittingPunishmentValue reward blocker -
        quittingSetReward reward ({blocker} : Finset ι) blocker) +
      (quittingSetReward reward ({owner} : Finset ι) blocker -
        quittingSetReward reward ({owner, blocker} : Finset ι) blocker) := by
    linarith [hown.1, hchi.2, hsolo.1, hpair.2]
  nlinarith [hgap, mul_nonneg hrate0 hkey]

/-- A fixed sub-floor gap defeats the balance condition at every sufficiently
small collision rate. -/
theorem not_quittingCollisionBlockerBalance_of_subFloor_of_rate_lt
    (hrate0 : 0 ≤ rate) {γ : ℝ}
    (hgap : quittingSetReward reward ({blocker} : Finset ι) blocker + γ ≤
      quittingPunishmentValue reward blocker)
    (hsmall : 4 * quittingRewardBound reward * rate < γ) :
    ¬ QuittingCollisionBlockerBalance reward owner blocker rate := by
  intro hbalance
  have hbal : rate * quittingSetReward reward ({owner} : Finset ι) blocker +
      (1 - rate) * quittingPunishmentValue reward blocker ≤
      quittingCollisionRepairValue reward owner blocker rate blocker := hbalance
  have hgain := quittingCollisionBlockerGain_ge_of_subFloor
    (reward := reward) (owner := owner) (blocker := blocker) hrate0 hgap
  linarith

/-- **Sub-floor compensation does not survive a vanishing collision rate.**
No sure-blocker repair whose blocker sits a fixed gap below its exact min-max
works at a collision rate below `γ / (4 * M)`. -/
theorem not_quittingCollisionRepairWorks_of_subFloor_of_rate_lt
    (hne : owner ≠ blocker) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) {γ : ℝ}
    (hgap : quittingSetReward reward ({blocker} : Finset ι) blocker + γ ≤
      quittingPunishmentValue reward blocker)
    (hsmall : 4 * quittingRewardBound reward * rate < γ) :
    ¬ QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1 := by
  intro hworks
  exact not_quittingCollisionBlockerBalance_of_subFloor_of_rate_lt hrate0
    hgap hsmall
    ((quittingCollisionRepairWorks_iff reward hne hrate0 hrate1).mp hworks).2.2

/-- **The vanishing-owner limit.**  At collision rate zero the balance is
exactly the blocker's own floor inequality: its solo exit must already sit at
or above its exact punishment value. -/
theorem quittingCollisionBlockerBalance_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner blocker : ι) :
    QuittingCollisionBlockerBalance reward owner blocker 0 ↔
      quittingPunishmentValue reward blocker ≤
        quittingSetReward reward ({blocker} : Finset ι) blocker := by
  rw [quittingCollisionBlockerBalance_iff]
  constructor <;> intro h <;> linarith [h]

end BlockerFloor

end GameTheory
