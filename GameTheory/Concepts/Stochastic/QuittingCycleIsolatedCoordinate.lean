/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCycleMismatchContraction

/-!
# The isolated coordinate: the `P_who = 1` branch of the cycle mismatch

`QuittingCycleMismatchContraction.lean` treats the branch where the deleted
survival product

`P_who = quittingOpponentSurvivalWeight roots who 0 period`

of an absorbing cyclic continuation block is strictly below one: there the
cyclic companion composite contracts and the anchored mismatch vanishes, with
no sign hypothesis.  This file treats the complementary branch `P_who = 1` and
combines the two into the full characterization.

## The four steps

1. **`P_who = 1` forces isolation.**  Each phase factor
   `c_{-who}(y_k) = quittingRootDeletedContinueMass (roots k) who` lies in
   `[0,1]`, so the product is `1` iff every factor is `1`, iff every opponent
   `j ≠ who` continues surely at every phase
   (`quittingRootDeletedContinueMass_eq_one_iff_isQuittingIsolatedRoot`,
   `isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one`).  An isolated
   root *is* the solo-quitter row of `QuittingSoloQuitterEquilibrium.lean`
   carrying `who`'s own marginal
   (`isQuittingIsolatedRoot_iff_exists_soloStationaryRoot`), which is where all
   of its endpoint formulas come from.
2. **In the isolated configuration the cyclic value is the solo weight.**  With
   all opponents silent the one-stage backward value map at `who` collapses to
   the scalar convex combination `z_k = y_k · r_who({who}) + (1 - y_k) · z_{k+1}`
   (`quittingRootSuccessorPayoff_of_isolated`), so the deviation of the phase
   value from `r_who({who})` is transported around the cycle by the product of
   the *joint* all-continue masses.  One absorbing stage makes that product
   strictly below one -- with all opponents silent only `who` can supply
   absorbing mass -- and the block's origin and cutoff values agree, so the
   deviation is zero:
   `quittingCyclicContinuationBlock_value_eq_soloReward_of_isolated`.
3. **The mismatch.**  The isolated companion map is `w ↦ max {r_who({who}), w}`
   (`quittingRootCompanionMap_of_isolated`), so the anchored orbit from
   `Λ_who = max {0, r_who({who})}` is *constant* at `Λ_who`, and the mismatch is
   exactly `Λ_who - r_who({who}) = max {0, -r_who({who})}`
   (`quittingCyclicContinuationBlock_mismatch_eq_of_isolated`).
4. **At most one coordinate is isolated.**  Two isolated coordinates would leave
   every coordinate silent at the absorbing stage
   (`eq_of_isQuittingIsolatedRoot_of_absorbing`, and its block form
   `eq_of_isQuittingIsolatedWindow_of_cyclicBlock`).  This step is independent
   of steps 1--3.

## What is proved and what is not

The combined characterization
`quittingCyclicContinuationBlock_mismatch_characterization` covers the anchored
companion mismatch of an absorbing cyclic continuation block at a single
coordinate, at arbitrary period, with no sign hypothesis.  It says nothing
about the deviation gain of the infinitely repeated block beyond the scalar
companion recursion, and nothing about blocks that fail to absorb.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

/-! ## Two elementary ingredients -/

/-- If a finite product of factors in `[0,1]` equals one, every factor is
one. -/
theorem eq_one_of_prod_eq_one_of_mem {α : Type*} {s : Finset α} {f : α → ℝ}
    (hnonneg : ∀ a ∈ s, 0 ≤ f a) (hle : ∀ a ∈ s, f a ≤ 1)
    (hprod : ∏ a ∈ s, f a = 1) {a : α} (ha : a ∈ s) : f a = 1 := by
  classical
  have hsplit := Finset.mul_prod_erase s f ha
  have hrestLe : (∏ b ∈ s.erase a, f b) ≤ 1 :=
    Finset.prod_le_one (fun b hb ↦ hnonneg b (Finset.mem_of_mem_erase hb))
      (fun b hb ↦ hle b (Finset.mem_of_mem_erase hb))
  have hkey : f a * (∏ b ∈ s.erase a, f b) ≤ f a * 1 :=
    mul_le_mul_of_nonneg_left hrestLe (hnonneg a ha)
  rw [hsplit, hprod] at hkey
  exact le_antisymm (hle a ha) (by linarith)

/-- A Boolean marginal whose Continue mass is one is the pure Continue law. -/
theorem eq_pure_false_of_continueProbability_eq_one {marginal : PMF Bool}
    (hcontinue : (marginal false).toReal = 1) : marginal = PMF.pure false := by
  have hsum := quittingSoloHazardMass_add marginal
  have hquitReal : (marginal true).toReal = 0 := by linarith
  have hquit : marginal true = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hquitReal with hzero | htop
    · exact hzero
    · exact absurd htop (PMF.apply_ne_top marginal true)
  have htotal : marginal true + marginal false = 1 := by
    have hcoe := marginal.tsum_coe
    rwa [tsum_fintype, Fintype.sum_bool] at hcoe
  have hfalse : marginal false = 1 := by
    rw [hquit, zero_add] at htotal
    exact htotal
  refine PMF.ext fun action ↦ ?_
  cases action with
  | false => simp [hfalse]
  | true => simp [hquit]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Isolation

The *isolated* configuration for `who` is the one in which every opponent
continues surely.  Such a root is exactly the solo-quitter row owned by `who`,
which is where every endpoint formula below comes from. -/

/-- **The isolated configuration for `who`**: every opponent continues surely
at `root`. -/
def IsQuittingIsolatedRoot (root : ι → PMF Bool) (who : ι) : Prop :=
  ∀ other : ι, other ≠ who → root other = PMF.pure false

/-- Isolation for `who` at every phase of the window `[0, bound)` of a root
sequence. -/
def IsQuittingIsolatedWindow
    (roots : ℕ → ι → PMF Bool) (who : ι) (bound : ℕ) : Prop :=
  ∀ time : ℕ, time < bound → IsQuittingIsolatedRoot (roots time) who

omit [Fintype ι] in
/-- **The isolated roots are exactly the solo-quitter rows owned by `who`.** -/
theorem isQuittingIsolatedRoot_iff_exists_soloStationaryRoot
    (root : ι → PMF Bool) (who : ι) :
    IsQuittingIsolatedRoot root who ↔
      ∃ hazard : PMF Bool, root = quittingSoloStationaryRoot who hazard := by
  constructor
  · intro hiso
    exact ⟨root who, eq_quittingSoloStationaryRoot_of_others_continue hiso⟩
  · rintro ⟨hazard, rfl⟩ other hother
    exact quittingSoloStationaryRoot_apply_other hother hazard

omit [Fintype ι] [DecidableEq ι] in
/-- The solo weight of `who` is its singleton reward. -/
theorem quittingSoloReward_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingSoloReward reward who who =
      reward (quittingSingletonTerminal who) who := rfl

/-! ## Step 1: `P_who = 1` is exactly isolation -/

/-- In the isolated configuration the deleted survival factor is one: with
every opponent silent, nobody but `who` can absorb. -/
theorem quittingRootDeletedContinueMass_eq_one_of_isolated
    {root : ι → PMF Bool} {who : ι} (hiso : IsQuittingIsolatedRoot root who) :
    quittingRootDeletedContinueMass root who = 1 := by
  obtain ⟨hazard, rfl⟩ :=
    (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot root who).mp hiso
  rw [quittingRootDeletedContinueMass, update_quittingSoloStationaryRoot_owner,
    quittingStationaryContinueMass_solo]
  simp

/-- Conversely, a deleted survival factor equal to one forces isolation: that
factor is the product of the opponents' Continue probabilities, all in
`[0,1]`. -/
theorem isQuittingIsolatedRoot_of_deletedContinueMass_eq_one
    {root : ι → PMF Bool} {who : ι}
    (hmass : quittingRootDeletedContinueMass root who = 1) :
    IsQuittingIsolatedRoot root who := by
  classical
  intro other hother
  have hprod : ∏ player : ι,
      ((Function.update root who (PMF.pure false)) player false).toReal = 1 := by
    rw [← quittingStationaryContinueMass_eq_prod_continueProbability]
    exact hmass
  have hfactor : ((Function.update root who (PMF.pure false)) other false).toReal
      = 1 :=
    eq_one_of_prod_eq_one_of_mem
      (fun _ _ ↦ ENNReal.toReal_nonneg)
      (fun player _ ↦ ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (Function.update root who (PMF.pure false) player) false))
      hprod (Finset.mem_univ other)
  rw [Function.update_of_ne hother] at hfactor
  exact eq_pure_false_of_continueProbability_eq_one hfactor

/-- **Step 1, one phase.**  The deleted survival factor at `who` is one exactly
in the isolated configuration. -/
theorem quittingRootDeletedContinueMass_eq_one_iff_isQuittingIsolatedRoot
    (root : ι → PMF Bool) (who : ι) :
    quittingRootDeletedContinueMass root who = 1 ↔
      IsQuittingIsolatedRoot root who :=
  ⟨isQuittingIsolatedRoot_of_deletedContinueMass_eq_one,
    quittingRootDeletedContinueMass_eq_one_of_isolated⟩

/-- **Step 1, around the cycle.**  The deleted survival product over
`[0, bound)` is one exactly when `who` is isolated at every phase of the
window. -/
theorem isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one
    (roots : ℕ → ι → PMF Bool) (who : ι) (bound : ℕ) :
    IsQuittingIsolatedWindow roots who bound ↔
      quittingOpponentSurvivalWeight roots who 0 bound = 1 := by
  constructor
  · intro hiso
    refine Finset.prod_eq_one fun offset hoffset ↦ ?_
    rw [← quittingRootDeletedContinueMass_eq_fixedOpponents]
    exact quittingRootDeletedContinueMass_eq_one_of_isolated
      (hiso (0 + offset) (by simpa using Finset.mem_range.mp hoffset))
  · intro hweight time htime
    have hfactor := eq_one_of_prod_eq_one_of_mem
      (f := fun offset ↦ quittingFixedOpponentsContinueMass roots who (0 + offset))
      (fun offset _ ↦ quittingRootDeletedContinueMass_nonneg
        (roots (0 + offset)) who)
      (fun offset _ ↦ quittingRootDeletedContinueMass_le_one
        (roots (0 + offset)) who)
      hweight (a := time) (Finset.mem_range.mpr htime)
    rw [← quittingRootDeletedContinueMass_eq_fixedOpponents, zero_add] at hfactor
    exact isQuittingIsolatedRoot_of_deletedContinueMass_eq_one hfactor

/-! ## Step 4: at most one coordinate is isolated

This step needs only that an isolated *pair* of coordinates leaves no
coordinate able to absorb; it uses nothing from steps 1--3. -/

omit [DecidableEq ι] in
/-- **Step 4, one root.**  At a root where two coordinates are simultaneously
isolated every coordinate is silent, so the absorption mass is zero. -/
theorem eq_of_isQuittingIsolatedRoot_of_absorbing
    {root : ι → PMF Bool} {who other : ι}
    (hwho : IsQuittingIsolatedRoot root who)
    (hother : IsQuittingIsolatedRoot root other)
    (habsorb : 0 < quittingRootAbsorptionMass root) : who = other := by
  by_contra hne
  have hsilent : ∀ player : ι, root player = PMF.pure false := by
    intro player
    by_cases hplayer : player = who
    · rw [hplayer]; exact hother who hne
    · exact hwho player hplayer
  have hmass : quittingStationaryContinueMass root = 1 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    have hone : ∀ player : ι, (root player false).toReal = 1 := by
      intro player
      rw [hsilent player]
      simp
    simp [hone]
  rw [quittingRootAbsorptionMass, hmass] at habsorb
  linarith

/-- The absorbing stage of a cyclic continuation block, read on the block's
operational root sequence. -/
theorem quittingCyclicContinuationBlock_exists_absorbing_time
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block) :
    ∃ time : ℕ, time < period ∧
      0 < quittingRootAbsorptionMass
        (quittingFiniteNashBellmanPathRoots period block time) := by
  obtain ⟨stage, hstage⟩ := hblock.2.2
  refine ⟨stage.val, stage.isLt, ?_⟩
  rw [quittingFiniteNashBellmanPathRoots_of_lt period block stage.val stage.isLt]
  exact hstage

/-- **Step 4, for a block.**  An absorbing cyclic continuation block has at most
one isolated coordinate. -/
theorem eq_of_isQuittingIsolatedWindow_of_cyclicBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    {who other : ι}
    (hwho : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period)
    (hother : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) other period) :
    who = other := by
  obtain ⟨time, htime, habsorb⟩ :=
    quittingCyclicContinuationBlock_exists_absorbing_time reward terminal period
      block hblock
  exact eq_of_isQuittingIsolatedRoot_of_absorbing (hwho time htime)
    (hother time htime) habsorb

/-! ## Step 2: in the isolated configuration the cyclic value is the solo weight -/

omit [DecidableEq ι] in
/-- **The isolated one-stage value law.**  With every opponent silent the
backward value map at `who` is the scalar convex combination
`y · r_who({who}) + (1 - y) · w`, where `y` is `who`'s own quit probability. -/
theorem quittingRootSuccessorPayoff_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {root : ι → PMF Bool} {who : ι}
    (hiso : IsQuittingIsolatedRoot root who) :
    quittingRootSuccessorPayoff reward tail root who =
      (root who true).toReal * reward (quittingSingletonTerminal who) who +
        (root who false).toReal * tail who := by
  classical
  obtain ⟨hazard, rfl⟩ :=
    (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot root who).mp hiso
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_soloStationaryRoot_owner,
    quittingRootContinuePayoff_soloStationaryRoot_owner,
    quittingSoloReward_self]

omit [DecidableEq ι] in
/-- The joint all-continue mass of an isolated root is `who`'s own Continue
probability: no opponent contributes. -/
theorem quittingStationaryContinueMass_of_isolated
    {root : ι → PMF Bool} {who : ι} (hiso : IsQuittingIsolatedRoot root who) :
    quittingStationaryContinueMass root = (root who false).toReal := by
  classical
  obtain ⟨hazard, rfl⟩ :=
    (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot root who).mp hiso
  rw [quittingStationaryContinueMass_solo,
    quittingSoloStationaryRoot_apply_owner]

omit [DecidableEq ι] in
/-- **The isolated transport step.**  The deviation of the one-stage value from
the solo weight is the joint all-continue mass times the deviation of the
continuation. -/
theorem quittingRootSuccessorPayoff_sub_soloReward_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {root : ι → PMF Bool} {who : ι}
    (hiso : IsQuittingIsolatedRoot root who) :
    quittingRootSuccessorPayoff reward tail root who -
        reward (quittingSingletonTerminal who) who =
      quittingStationaryContinueMass root *
        (tail who - reward (quittingSingletonTerminal who) who) := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  rw [quittingRootSuccessorPayoff_of_isolated reward tail hiso,
    quittingStationaryContinueMass_of_isolated hiso]
  have hquit : (root who true).toReal = 1 - (root who false).toReal := by linarith
  rw [hquit]
  ring

omit [DecidableEq ι] in
/-- **Step 2, the window transport law.**  Along an isolated window the
deviation of the displayed value from the solo weight is transported by the
product of the *joint* all-continue masses. -/
theorem quittingIsolatedValue_sub_soloReward_eq_prod_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → Payoff ι) (bound : ℕ)
    (hvalue : ∀ time, time < bound →
      value time =
        quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hiso : IsQuittingIsolatedWindow roots who bound) :
    ∀ start fuel, start + fuel ≤ bound →
      value start who - reward (quittingSingletonTerminal who) who =
        (∏ offset ∈ Finset.range fuel,
            quittingStationaryContinueMass (roots (start + offset))) *
          (value (start + fuel) who -
            reward (quittingSingletonTerminal who) who) := by
  intro start fuel
  induction fuel generalizing start with
  | zero => intro _; simp
  | succ fuel ih =>
      intro hwindow
      have hstep : value start who -
            reward (quittingSingletonTerminal who) who =
          quittingStationaryContinueMass (roots start) *
            (value (start + 1) who -
              reward (quittingSingletonTerminal who) who) := by
        rw [congrFun (hvalue start (by omega)) who]
        exact quittingRootSuccessorPayoff_sub_soloReward_of_isolated reward
          (value (start + 1)) (hiso start (by omega))
      have htail := ih (start + 1) (by omega)
      rw [show start + 1 + fuel = start + (fuel + 1) by omega] at htail
      rw [hstep, htail, Finset.prod_range_succ']
      have hfactor : (∏ offset ∈ Finset.range fuel,
            quittingStationaryContinueMass (roots (start + (offset + 1)))) =
          ∏ offset ∈ Finset.range fuel,
            quittingStationaryContinueMass (roots (start + 1 + offset)) :=
        Finset.prod_congr rfl fun offset _ ↦ by
          rw [show start + (offset + 1) = start + 1 + offset by omega]
      rw [hfactor, add_zero]
      ring

omit [DecidableEq ι] in
/-- One absorbing stage in `[0, bound)` makes the product of the joint
all-continue masses over that window strictly below one. -/
theorem prod_range_quittingStationaryContinueMass_lt_one_of_absorbing
    (roots : ℕ → ι → PMF Bool) (bound stage : ℕ) (hstage : stage < bound)
    (habsorb : 0 < quittingRootAbsorptionMass (roots stage)) :
    (∏ offset ∈ Finset.range bound,
      quittingStationaryContinueMass (roots offset)) < 1 := by
  classical
  have hlt : quittingStationaryContinueMass (roots stage) < 1 := by
    rw [quittingRootAbsorptionMass] at habsorb; linarith
  have hsplit := Finset.mul_prod_erase (Finset.range bound)
    (fun offset ↦ quittingStationaryContinueMass (roots offset))
    (Finset.mem_range.mpr hstage)
  have hrestLe : (∏ offset ∈ (Finset.range bound).erase stage,
      quittingStationaryContinueMass (roots offset)) ≤ 1 :=
    Finset.prod_le_one
      (fun offset _ ↦ quittingStationaryContinueMass_nonneg (roots offset))
      (fun offset _ ↦ quittingStationaryContinueMass_le_one (roots offset))
  have hkey : quittingStationaryContinueMass (roots stage) *
        (∏ offset ∈ (Finset.range bound).erase stage,
          quittingStationaryContinueMass (roots offset)) ≤
      quittingStationaryContinueMass (roots stage) * 1 :=
    mul_le_mul_of_nonneg_left hrestLe
      (quittingStationaryContinueMass_nonneg (roots stage))
  rw [hsplit] at hkey
  linarith

/-- **Step 2.**  In the isolated configuration an absorbing cyclic continuation
block's own value at `who` is `who`'s solo weight `r_who({who})`.

Absorption is what forces this: with every opponent silent only `who` can
supply absorbing mass, so the transported deviation contracts strictly, and the
block's origin and cutoff values are the same vector. -/
theorem quittingCyclicContinuationBlock_value_eq_soloReward_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    {who : ι}
    (hiso : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period) :
    terminal who = reward (quittingSingletonTerminal who) who := by
  obtain ⟨stage, hstage, habsorb⟩ :=
    quittingCyclicContinuationBlock_exists_absorbing_time reward terminal period
      block hblock
  have htransport := quittingIsolatedValue_sub_soloReward_eq_prod_mul reward
    (quittingFiniteNashBellmanPathRoots period block) who
    (quittingFiniteNashBellmanPathValue period block) period
    (fun time htime ↦ quittingAnchoredPathValue_eq_successor reward terminal
      period block hblock.1 time htime)
    hiso 0 period (by omega)
  simp only [zero_add] at htransport
  rw [quittingCyclicBlockValue_at_zero reward terminal period block hblock,
    quittingAnchoredPathValue_at_cutoff reward terminal period block hblock.1]
    at htransport
  have hcontract := prod_range_quittingStationaryContinueMass_lt_one_of_absorbing
    (quittingFiniteNashBellmanPathRoots period block) period stage hstage habsorb
  have hfactored : (terminal who - reward (quittingSingletonTerminal who) who) *
      (1 - ∏ offset ∈ Finset.range period,
        quittingStationaryContinueMass
          (quittingFiniteNashBellmanPathRoots period block offset)) = 0 := by
    linear_combination htransport
  rcases mul_eq_zero.mp hfactored with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · linarith

/-! ## Step 3: the isolated companion map and the constant anchored orbit -/

/-- **The isolated companion map.**  With every opponent silent the deleted quit
value is `r_who({who})`, the deleted continue reward is `0` and the deleted
continue mass is `1`, so the companion map is `w ↦ max {r_who({who}), w}`. -/
theorem quittingRootCompanionMap_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {who : ι} (hiso : IsQuittingIsolatedRoot root who)
    (continuation : ℝ) :
    quittingRootCompanionMap reward root who continuation =
      max (reward (quittingSingletonTerminal who) who) continuation := by
  have hmass : quittingRootDeletedContinueMass root who = 1 :=
    quittingRootDeletedContinueMass_eq_one_of_isolated hiso
  have hquit : quittingRootDeletedQuitValue reward root who =
      reward (quittingSingletonTerminal who) who := by
    rw [← quittingRootQuitPayoff_eq_deletedQuitValue reward (0 : Payoff ι)]
    obtain ⟨hazard, rfl⟩ :=
      (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot root who).mp hiso
    rw [quittingRootQuitPayoff_soloStationaryRoot_owner, quittingSoloReward_self]
  have hreward : quittingRootDeletedContinueReward reward root who = 0 := by
    have hdeleted := quittingRootContinuePayoff_eq_deleted reward
      (0 : Payoff ι) root who
    rw [hmass] at hdeleted
    obtain ⟨hazard, rfl⟩ :=
      (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot root who).mp hiso
    rw [quittingRootContinuePayoff_soloStationaryRoot_owner] at hdeleted
    simp only [Pi.zero_apply, mul_zero, add_zero] at hdeleted
    exact hdeleted.symm
  rw [quittingRootCompanionMap, hquit, hreward, hmass]
  norm_num

/-- **Step 3, the composite fixes every point above the solo weight.**  Along an
isolated window every phase map is `w ↦ max {r_who({who}), w}`, so the composite
fixes every `w ≥ r_who({who})`. -/
theorem quittingCompanionComposite_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (bound : ℕ)
    (hiso : IsQuittingIsolatedWindow roots who bound)
    {continuation : ℝ}
    (hle : reward (quittingSingletonTerminal who) who ≤ continuation) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingCompanionComposite reward roots who start fuel continuation =
        continuation := by
  intro start fuel
  induction fuel generalizing start with
  | zero => intro _; rfl
  | succ fuel ih =>
      intro hwindow
      rw [quittingCompanionComposite_succ, ih (start + 1) (by omega),
        quittingRootCompanionMap_of_isolated reward (hiso start (by omega))]
      exact max_eq_right hle

/-- **The anchored orbit is constant in the isolated configuration.**  The
solo-quit anchor `Λ_who = max {0, r_who({who})}` sits at or above
`r_who({who})`, hence is a fixed point of the cyclic composite. -/
theorem quittingCompanionComposite_soloQuitAnchor_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (hiso : IsQuittingIsolatedWindow roots who period) (N : ℕ) :
    (quittingCompanionComposite reward roots who 0 period)^[N]
        (quittingPositiveSingletonDebtCap reward who) =
      quittingPositiveSingletonDebtCap reward who := by
  have hanchor : reward (quittingSingletonTerminal who) who ≤
      quittingPositiveSingletonDebtCap reward who := by
    rw [quittingSoloQuitAnchor_eq]
    exact le_max_right _ _
  exact Function.iterate_fixed
    (quittingCompanionComposite_of_isolated reward roots who period hiso hanchor
      0 period (by omega)) N

/-- The anchored companion orbit of an isolated coordinate converges -- indeed
it is constant -- at the solo-quit anchor. -/
theorem tendsto_iterate_soloQuitAnchor_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (hiso : IsQuittingIsolatedWindow roots who period) :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward roots who 0 period)^[N]
          (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds (quittingPositiveSingletonDebtCap reward who)) := by
  have hconstant : (fun N : ℕ =>
      (quittingCompanionComposite reward roots who 0 period)^[N]
        (quittingPositiveSingletonDebtCap reward who)) =
      fun _ : ℕ => quittingPositiveSingletonDebtCap reward who :=
    funext fun N ↦ quittingCompanionComposite_soloQuitAnchor_of_isolated reward
      roots who period hiso N
  rw [hconstant]
  exact tendsto_const_nhds

/-- **Step 3.**  In the isolated configuration the anchored mismatch of an
absorbing cyclic continuation block is exactly `max {0, -r_who({who})}`.

The phase gap between the value and the solo weight is identically zero by
step 2, so the anchored orbit never moves and the mismatch is the pure
anchoring discrepancy `Λ_who - r_who({who})`. -/
theorem quittingCyclicContinuationBlock_mismatch_eq_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    {who : ι}
    (hiso : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period)
    (anchorLimit : ℝ)
    (hanchor : Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds anchorLimit)) :
    anchorLimit - terminal who =
      max 0 (-reward (quittingSingletonTerminal who) who) := by
  have hunique := tendsto_nhds_unique hanchor
    (tendsto_iterate_soloQuitAnchor_of_isolated reward
      (quittingFiniteNashBellmanPathRoots period block) who period hiso)
  have hvalue :=
    quittingCyclicContinuationBlock_value_eq_soloReward_of_isolated reward
      terminal period block hblock hiso
  rw [hunique, hvalue, quittingSoloQuitAnchor_eq]
  rcases le_total 0 (reward (quittingSingletonTerminal who) who) with hsign | hsign
  · rw [max_eq_right hsign, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left hsign, max_eq_right (by linarith)]
    ring

/-! ## The combined characterization -/

/-- **The full cycle mismatch characterization.**

For an absorbing cyclic continuation block of any period and any coordinate
`who`, the anchored companion mismatch is zero *unless* `who` is isolated --
every opponent silent at every phase, equivalently the deleted survival product
`P_who` equal to one -- and `r_who({who}) < 0`; in that exceptional case the
block's own value at `who` is `r_who({who})` and the mismatch is exactly
`-r_who({who})`.

`HEADLINE` — the complete mismatch characterization for absorbing cyclic
continuation blocks, combining the contraction branch
`quittingCyclicContinuationBlock_mismatch_eq_zero` (`P_who < 1`) with the
isolated branch (`P_who = 1`) proved here.  It characterizes only the *scalar
companion* mismatch measured from the solo-quit anchor; it makes no claim about
the deviation gain of the infinitely repeated block, and it says nothing about
blocks that fail to absorb.  No sign hypothesis is used in either branch. -/
theorem quittingCyclicContinuationBlock_mismatch_characterization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    (who : ι) (anchorLimit : ℝ)
    (hanchor : Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds anchorLimit)) :
    anchorLimit - terminal who = 0 ∨
      (IsQuittingIsolatedWindow
          (quittingFiniteNashBellmanPathRoots period block) who period ∧
        terminal who = reward (quittingSingletonTerminal who) who ∧
        reward (quittingSingletonTerminal who) who < 0 ∧
        anchorLimit - terminal who =
          -reward (quittingSingletonTerminal who) who) := by
  rcases lt_or_eq_of_le (quittingOpponentSurvivalWeight_le_one
      (quittingFiniteNashBellmanPathRoots period block) who 0 period) with
    hsurvival | hsurvival
  · exact Or.inl (quittingCyclicContinuationBlock_mismatch_eq_zero reward
      terminal period block hblock who hsurvival anchorLimit hanchor)
  · have hiso : IsQuittingIsolatedWindow
        (quittingFiniteNashBellmanPathRoots period block) who period :=
      (isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one _ who
        period).mpr hsurvival
    have hmismatch := quittingCyclicContinuationBlock_mismatch_eq_of_isolated
      reward terminal period block hblock hiso anchorLimit hanchor
    by_cases hsign : reward (quittingSingletonTerminal who) who < 0
    · exact Or.inr ⟨hiso,
        quittingCyclicContinuationBlock_value_eq_soloReward_of_isolated reward
          terminal period block hblock hiso, hsign,
        by rw [hmismatch, max_eq_right (by linarith)]⟩
    · have hnonneg : 0 ≤ reward (quittingSingletonTerminal who) who :=
        not_lt.mp hsign
      exact Or.inl (by rw [hmismatch, max_eq_left (by linarith)])

/-- **The admissibility hypothesis is discharged.**  The disjunction "the
deleted survival product contracts, or the solo reward is nonnegative" -- the
shape consumed by the conditional reduction of
`QuittingAdmissibleCycleTerminalEquilibrium.lean` -- is exactly what makes the
anchored mismatch vanish. -/
theorem quittingCyclicContinuationBlock_mismatch_eq_zero_of_admissible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    (who : ι)
    (hadmissible : quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots period block) who 0 period < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who)
    (anchorLimit : ℝ)
    (hanchor : Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds anchorLimit)) :
    anchorLimit - terminal who = 0 := by
  rcases quittingCyclicContinuationBlock_mismatch_characterization reward
      terminal period block hblock who anchorLimit hanchor with
    hzero | ⟨hiso, _, hsign, _⟩
  · exact hzero
  · rcases hadmissible with hcontract | hnonneg
    · exact absurd
        ((isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one _ who
          period).mp hiso) (ne_of_lt hcontract)
    · linarith

/-- **The exceptional mismatch is exactly the negative part of the solo
reward.**  Stated as the single closed form covering both branches at an
isolated coordinate. -/
theorem quittingCyclicContinuationBlock_isolated_mismatch_eq_negPart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal period block)
    {who : ι}
    (hiso : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots period block) who period)
    (anchorLimit : ℝ)
    (hanchor : Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots period block) who 0
          period)^[N] (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds anchorLimit)) :
    anchorLimit - terminal who =
      quittingPositiveSingletonDebtCap reward who -
        reward (quittingSingletonTerminal who) who := by
  rw [quittingCyclicContinuationBlock_mismatch_eq_of_isolated reward terminal
    period block hblock hiso anchorLimit hanchor, quittingSoloQuitAnchor_eq]
  rcases le_total 0 (reward (quittingSingletonTerminal who) who) with hsign | hsign
  · rw [max_eq_left (by linarith), max_eq_right hsign]
    ring
  · rw [max_eq_right (by linarith), max_eq_left hsign]
    ring

/-! ## Regression: the exceptional branch is inhabited

Both disjuncts of the characterization are reachable.  The contracting one is
witnessed by `QuittingCycleMismatchAudit` in the companion module, at the
non-owner coordinate `false` where `P_false = 1/2 < 1`.

The exceptional one is witnessed below.  Two coordinates indexed by `Bool`; the
owner `true` quits at rate `1/2` and the coordinate `false` continues surely, so
`true` is isolated.  Every reward entry is `0` except `r_true({true}) = -1`.  The
row is an absorbing exact complementary cycle by
`quittingRowBlock_isQuittingCyclicContinuationBlock`, its value at `true` is
`-1`, the anchored orbit is constant at `Λ_true = max {0, -1} = 0`, and the
mismatch is `1`.

This is the scalar-companion half of the *hand check* recorded in the module
docstring of `QuittingAdmissibleCycleTerminalEquilibrium.lean` (that its
hypothesis (H2) is not redundant).  It is not the game-level statement: nothing
here claims that the periodic profile fails to be terminal `ε`-Nash. -/

namespace QuittingIsolatedNegativeSoloRegression

/-- The regression weight: every entry `0` except `r_true({true}) = -1`. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S who ↦ if who then (if S.1 = {true} then (-1 : ℝ) else 0) else 0

theorem hazardRate_pos : (0 : ℝ) < 1 / 2 := by norm_num

theorem hazardRate_le_one : (1 : ℝ) / 2 ≤ 1 := by norm_num

/-- The owner `true` quits at rate `1/2`; the coordinate `false` continues
surely, which is exactly isolation of `true`. -/
def hazard : PMF Bool :=
  quittingHazardCoin (1 / 2) hazardRate_pos.le hazardRate_le_one

/-- The regression row. -/
def root : Bool → PMF Bool := quittingSoloStationaryRoot true hazard

/-- The regression value `z = (0, -1)`, indexed `(false, true)`. -/
def value : Payoff Bool := quittingSoloReward reward true

@[simp] theorem hazard_true : (hazard true).toReal = 1 / 2 :=
  quittingHazardCoin_true_toReal _ _ _

@[simp] theorem hazard_false : (hazard false).toReal = 1 / 2 := by
  rw [hazard, quittingHazardCoin_false_toReal]
  norm_num

@[simp] theorem soloReward_true_true :
    reward (quittingSingletonTerminal true) true = -1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem value_true : value true = -1 := soloReward_true_true

@[simp] theorem reward_false (S : {S : Finset Bool // S.Nonempty}) :
    reward S false = 0 := by
  simp [reward]

/-- The row reproduces its own value. -/
theorem value_eq_successor :
    value = quittingRootSuccessorPayoff reward value root :=
  (quittingRootSuccessorPayoff_soloStationaryRoot_self reward true hazard).symm

/-- The row is exactly (`ε = 0`) endpoint Nash: the owner is indifferent, and
the silent coordinate is indifferent too since all its entries vanish. -/
theorem isEndpointNash : IsεQuittingRootEndpointNash reward value 0 root := by
  refine isεQuittingRootEndpointNash_soloStationaryRoot reward true hazard ?_
  intro other hother
  cases other with
  | false =>
      simp [quittingSoloReward, quittingSingletonCollisionReward]
  | true => exact absurd rfl hother

/-- The row absorbs at rate `1/2`. -/
theorem absorptionMass_pos : 0 < quittingRootAbsorptionMass root := by
  rw [root, quittingRootAbsorptionMass_soloStationaryRoot, hazard_true]
  norm_num

theorem abs_value_le : ∀ who, |value who| ≤ quittingRewardBound reward :=
  fun who ↦
    abs_reward_le_quittingRewardBound reward (quittingSingletonTerminal true) who

/-- The regression row is a cyclic continuation block of length one. -/
theorem isCyclicContinuationBlock :
    IsQuittingCyclicContinuationBlock reward value 1
      (quittingRowBlock value root) :=
  quittingRowBlock_isQuittingCyclicContinuationBlock reward value root
    abs_value_le value_eq_successor isEndpointNash absorptionMass_pos

/-- **The owner is isolated**: its only opponent continues surely. -/
theorem isIsolated : IsQuittingIsolatedWindow
    (quittingFiniteNashBellmanPathRoots 1 (quittingRowBlock value root))
    true 1 := by
  intro time htime
  have htime0 : time = 0 := by omega
  subst htime0
  rw [quittingFiniteNashBellmanPathRoots_of_lt 1 _ 0 (by omega),
    quittingRootOfSimplex_quittingRowBlock]
  exact (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot root true).mpr
    ⟨hazard, rfl⟩

/-- Consequently the deleted survival product is exactly one: the contraction
branch is unavailable here. -/
theorem opponentSurvivalWeight_eq_one :
    quittingOpponentSurvivalWeight
      (quittingFiniteNashBellmanPathRoots 1 (quittingRowBlock value root))
      true 0 1 = 1 :=
  (isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one _ true 1).mp
    isIsolated

/-- The solo-quit anchor at `true` is `max {0, -1} = 0`. -/
@[simp] theorem soloQuitCap_true :
    quittingPositiveSingletonDebtCap reward true = 0 := by
  rw [quittingSoloQuitAnchor_eq, soloReward_true_true]
  norm_num

theorem tendsto_iterate_soloQuitAnchor :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots 1 (quittingRowBlock value root))
          true 0 1)^[N] (quittingPositiveSingletonDebtCap reward true))
      Filter.atTop (nhds (quittingPositiveSingletonDebtCap reward true)) :=
  tendsto_iterate_soloQuitAnchor_of_isolated reward _ true 1 isIsolated

/-- **The exceptional mismatch is `1`, not `0`.**  So the second disjunct of
`quittingCyclicContinuationBlock_mismatch_characterization` is not vacuous, and
the admissibility hypothesis it discharges cannot simply be dropped. -/
theorem mismatch_eq_one :
    quittingPositiveSingletonDebtCap reward true - value true = 1 := by
  rw [quittingCyclicContinuationBlock_mismatch_eq_of_isolated reward value 1
    (quittingRowBlock value root) isCyclicContinuationBlock isIsolated
    (quittingPositiveSingletonDebtCap reward true) tendsto_iterate_soloQuitAnchor,
    soloReward_true_true]
  norm_num

end QuittingIsolatedNegativeSoloRegression

end GameTheory
