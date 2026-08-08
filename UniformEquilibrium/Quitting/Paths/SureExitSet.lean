/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair
import UniformEquilibrium.Quitting.Stationary.BestResponse
import GameTheory.Concepts.Stochastic.Models.Quitting.SimpleBranches
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetRepairCounterexample

/-!
# Sure exit sets in quitting games

Fix a quitting game on a finite player set with reward table `r`, where
`r(S)` is the payoff vector at the terminal state reached when exactly the
nonempty coalition `S` quits simultaneously.  Extend `r` by `r(∅) = 0`, the
payoff of never absorbing.  For a set `S` of players consider the pure
stationary profile

`every player in S quits at every live history, every other player continues`

— the repository's `quittingStationaryProfile reward (quittingPureSetRoot S)`.
It absorbs at date zero whenever `S` is nonempty, so its terminal payoff is
`r(S)`.

The main theorem characterizes exactly when this profile is a terminal Nash
equilibrium.  A player's only two alternatives are to be in the exit set or
out of it, so the answer is a *membership-toggling* test:

**Theorem.**  The profile is a terminal `ε`-equilibrium if and only if

`max (r_who(S ∪ {who}), r_who(S ∖ {who})) ≤ r_who(S) + ε` for every player.

At `ε = 0` and after splitting on membership, the two halves are the exact
sure-exit-set conditions

* `r_i(S ∖ {i}) ≤ r_i(S)` for every `i ∈ S` — no member gains by staying;
* `r_j(S ∪ {j}) ≤ r_j(S)` for every `j ∉ S` — no outsider gains by joining.

Only one of the two toggles is nontrivial at each player, since
`S ∪ {i} = S` for `i ∈ S` and `S ∖ {j} = S` for `j ∉ S`.

## Scope and sharpness

Nothing is assumed about `S`: the statement is an equivalence for *every*
finite subset of the player set, at every number of players, and the
deviation class is all behavior strategies (arbitrary history-dependent
randomized stopping), not merely stationary or pure-time ones.

Three special values of `S` are recovered below as instances, and the first
two of them reproduce landed exact branches:

* `S = ∅` — the all-continue profile; the test reads `r_i({i}) ≤ 0` for
  every player, since `r(∅) = 0`;
* `S = {i}` — one sure solo quitter at the sure rate; the test reads
  `0 ≤ r_i({i})` together with `r_j({i,j}) ≤ r_j({i})` for every `j ≠ i`;
* `S = univ` — the grand-coalition exit; only the member conditions survive,
  there being no outsider.  At two players this is the joint exit of both
  players, whose two conditions are exactly the hypotheses of the joint-exit
  branch of the two-player closure of the quitting conjecture.

The `S = ∅` and `S = {i}` cases are exactly where the profile fails to
absorb after a unilateral deviation: the deviator is then the *only* possible
source of absorption, its opponents all continuing forever.  The stationary
Snell-cap machinery does not apply there — it assumes strict opponent
contraction — and those two cases are discharged instead by the all-continue
deviation bound.  The uniform cap formula below nevertheless remains valid
at them, because the never-quit alternative and the continue reward both
collapse to `r_who(S ∖ {who}) = r(∅) = 0`.

The characterization is a statement about one *given* set `S`, not about the
existence of a good one.  Tables for which no set at all passes the test do
exist; see the three-player sure-set repair regressions.

## Reference

Quitting games and their uniform equilibria are those of Solan and Vieille,
*Quitting games*, Israel J. Math. 119 (2001).  The characterization proved
here is original to this development.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The pure sure-exit root and its terminal payoff -/

/-- **Absorption at date zero.**  A nonempty exit set absorbs the game at
the very first stage with probability one.  This is the non-degeneracy guard
behind the payoff formula below: the declared value `r(S)` is a genuine
expected terminal payoff and not the vacuous all-continue fixed point. -/
theorem quittingRootAbsorptionMass_pureSetRoot_of_nonempty
    {S : Finset ι} (hS : S.Nonempty) :
    quittingRootAbsorptionMass (quittingPureSetRoot S) = 1 := by
  unfold quittingRootAbsorptionMass
  rw [stationaryContinueMass_pureSetRoot_of_nonempty hS]
  norm_num

omit [Fintype ι] in
/-- The empty exit set is the all-continue root. -/
@[simp] theorem quittingPureSetRoot_empty :
    quittingPureSetRoot (∅ : Finset ι) = fun _ ↦ PMF.pure false := by
  funext who
  simp [quittingPureSetRoot, quittingSetAction]

/-- The empty exit set generates the all-continue profile. -/
theorem quittingStationaryProfile_pureSetRoot_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingStationaryProfile reward (quittingPureSetRoot (∅ : Finset ι)) =
      quittingAlwaysContinueProfile reward := by
  rw [quittingPureSetRoot_empty]
  rfl

/-- The all-continue root never absorbs. -/
theorem quittingStationaryContinueMass_pureSetRoot_empty :
    quittingStationaryContinueMass (quittingPureSetRoot (∅ : Finset ι)) = 1 := by
  rw [quittingPureSetRoot_empty]
  change ((pmfPi fun _ : ι ↦ PMF.pure false) (fun _ : ι ↦ false)).toReal = 1
  rw [pmfPi_pure]
  simp

/-- **The exit set is the payoff.**  The pure sure-exit profile pays exactly
the extended set reward, at every set including the empty one. -/
theorem quittingTerminalPayoff_pureSetRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingPureSetRoot S)) who =
      quittingSetReward reward S who := by
  by_cases hS : S.Nonempty
  · rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
    · rw [quittingRootAbsorbingContribution_pureSetRoot,
        stationaryContinueMass_pureSetRoot_of_nonempty hS]
      norm_num
    · rw [stationaryContinueMass_pureSetRoot_of_nonempty hS]
      norm_num
  · obtain rfl : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [quittingStationaryProfile_pureSetRoot_empty,
      quittingTerminalPayoff_quittingAlwaysContinue, quittingSetReward_empty]

/-! ## The two membership toggles -/

/-- Quitting now against a sure exit set joins it. -/
theorem quittingStationaryFixedOpponentsQuitValue_pureSetRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingPureSetRoot S) who =
      quittingSetReward reward (insert who S) who := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
  rw [update_quittingPureSetRoot_true,
    quittingRootAbsorbingContribution_pureSetRoot]

/-- Continuing against a sure exit set leaves it. -/
theorem quittingStationaryFixedOpponentsContinueReward_pureSetRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingPureSetRoot S) who =
      quittingSetReward reward (S.erase who) who := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  rw [update_quittingPureSetRoot_false,
    quittingRootAbsorbingContribution_pureSetRoot]

/-- A player who leaves a still-nonempty exit set is absorbed at once. -/
theorem quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_nonempty
    {S : Finset ι} {who : ι} (herase : (S.erase who).Nonempty) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingPureSetRoot S) who = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_quittingPureSetRoot_false,
    stationaryContinueMass_pureSetRoot_of_nonempty herase]

/-- A player who is the exit set's only possible quitter faces opponents who
continue forever. -/
theorem quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_empty
    {S : Finset ι} {who : ι} (herase : S.erase who = ∅) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingPureSetRoot S) who = 1 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_quittingPureSetRoot_false, herase,
    quittingStationaryContinueMass_pureSetRoot_empty]

/-! ## The membership-toggling cap -/

/-- **The exact unilateral cap of a sure-exit root.**  A player's best
behavioral deviation is worth the better of the two membership toggles:
join the exit set, or leave it.

The formula is unconditional.  When the deviator is the exit set's only
member the opponents never absorb, the never-quit alternative pays zero, and
`quittingSetReward reward (S.erase who) who = r(∅) = 0` reproduces that value
even though the selected-cap quotient degenerates. -/
theorem quittingStationaryUnilateralCap_pureSetRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingStationaryUnilateralCap reward (quittingPureSetRoot S) who =
      max (quittingSetReward reward (insert who S) who)
        (quittingSetReward reward (S.erase who) who) := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [quittingStationaryFixedOpponentsQuitValue_pureSetRoot,
    quittingStationaryFixedOpponentsContinueReward_pureSetRoot]
  by_cases herase : (S.erase who).Nonempty
  · rw [quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_nonempty
      herase]
    norm_num
  · have heraseEq : S.erase who = ∅ := Finset.not_nonempty_iff_eq_empty.mp herase
    rw [quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_empty
      heraseEq, heraseEq, quittingSetReward_empty]
    norm_num

/-! ## The two witnessing deviations -/

/-- Replacing one coordinate of a stationary profile by the always-continue
strategy is again stationary, at the root with that coordinate pinned to
Continue. -/
theorem update_quittingStationaryProfile_alwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    Function.update (quittingStationaryProfile reward root) who
        (quittingAlwaysContinueStrategy reward who) =
      quittingStationaryProfile reward
        (Function.update root who (PMF.pure false)) := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    simp only [Function.update_self, quittingAlwaysContinueStrategy,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile]
    rfl
  · simp [Function.update_of_ne hplayer, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile]

/-- Leaving the exit set forever pays the reward of the set without the
deviator. -/
theorem quittingTerminalPayoff_update_pureSetRoot_alwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingStationaryProfile reward (quittingPureSetRoot S)) who
          (quittingAlwaysContinueStrategy reward who)) who =
      quittingSetReward reward (S.erase who) who := by
  rw [update_quittingStationaryProfile_alwaysContinue,
    update_quittingPureSetRoot_false, quittingTerminalPayoff_pureSetRoot]

/-- Joining the exit set at once pays the reward of the enlarged set. -/
theorem quittingTerminalPayoff_update_pureSetRoot_quitNow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingStationaryProfile reward (quittingPureSetRoot S)) who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
      quittingSetReward reward (insert who S) who := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue,
    quittingProfileLiveRoot_stationary,
    quittingStationaryFixedOpponentsQuitValue_pureSetRoot]

/-! ## The deviation bound -/

/-- When the exit set has no member other than the deviator, a unilateral
deviation leaves every opponent continuing forever, so the deviated profile
is the all-continue profile with the same single deviation. -/
theorem update_quittingStationaryProfile_pureSetRoot_of_erase_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {S : Finset ι} {who : ι} (herase : S.erase who = ∅)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    Function.update
        (quittingStationaryProfile reward (quittingPureSetRoot S)) who
        deviation =
      Function.update (quittingAlwaysContinueProfile reward) who deviation := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    simp
  · have hmem : player ∉ S := by
      intro hplayerMem
      have : player ∈ S.erase who := Finset.mem_erase.mpr ⟨hplayer, hplayerMem⟩
      rw [herase] at this
      exact absurd this (Finset.notMem_empty player)
    simp only [Function.update_of_ne hplayer, quittingStationaryProfile,
      quittingAlwaysContinueProfile, StochasticGame.stationaryBehaviorProfile,
      quittingPureSetRoot, quittingSetAction, hmem, if_false]
    rfl

/-- **No behavioral deviation beats the membership toggle.**  Against the
pure sure-exit profile, every history-dependent randomized deviation of a
single player is worth at most the better of joining and leaving the exit
set.  No hypothesis on `S` is needed. -/
theorem quittingTerminalPayoff_update_pureSetRoot_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingStationaryProfile reward (quittingPureSetRoot S)) who
          deviation) who ≤
      max (quittingSetReward reward (insert who S) who)
        (quittingSetReward reward (S.erase who) who) := by
  by_cases herase : (S.erase who).Nonempty
  · have hcontracts : quittingStationaryFixedOpponentsContinueMass
        (quittingPureSetRoot S) who < 1 := by
      rw [quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_nonempty
        herase]
      norm_num
    refine (quittingTerminalPayoff_update_stationary_le_unilateralCap
      reward (quittingPureSetRoot S) who deviation hcontracts).trans ?_
    exact le_of_eq (quittingStationaryUnilateralCap_pureSetRoot reward S who)
  · have heraseEq : S.erase who = ∅ := Finset.not_nonempty_iff_eq_empty.mp herase
    have hsubset : S ⊆ {who} := by
      intro player hplayer
      by_contra hne
      have : player ∈ S.erase who :=
        Finset.mem_erase.mpr ⟨by simpa using hne, hplayer⟩
      rw [heraseEq] at this
      exact absurd this (Finset.notMem_empty player)
    have hinsert : insert who S = {who} :=
      Finset.Subset.antisymm (Finset.insert_subset_iff.mpr ⟨by simp, hsubset⟩)
        (by simp)
    rw [update_quittingStationaryProfile_pureSetRoot_of_erase_empty
      reward heraseEq, hinsert, heraseEq, quittingSetReward_empty,
      quittingSetReward_of_nonempty reward (Finset.singleton_nonempty who),
      max_comm]
    exact quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
      reward who deviation

/-! ## The characterization -/

/-- **The sure-exit-set characterization, `ε` form.**  The pure profile in
which exactly `S` quits surely is a terminal `ε`-equilibrium precisely when
no player gains more than `ε` by toggling its own membership in `S`. -/
theorem isεAsymptoticNash_pureSetRoot_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (ε : ℝ) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward (quittingPureSetRoot S)) ↔
      ∀ who, max (quittingSetReward reward (insert who S) who)
          (quittingSetReward reward (S.erase who) who) ≤
        quittingSetReward reward S who + ε := by
  constructor
  · intro hnash who
    refine max_le ?_ ?_
    · have hquit := hnash who
        (quittingPureTimeBehaviorStrategy reward who (some 0))
      rw [quittingTerminalPayoff_update_pureSetRoot_quitNow,
        quittingTerminalPayoff_pureSetRoot] at hquit
      exact hquit
    · have hnever := hnash who (quittingAlwaysContinueStrategy reward who)
      rw [quittingTerminalPayoff_update_pureSetRoot_alwaysContinue,
        quittingTerminalPayoff_pureSetRoot] at hnever
      exact hnever
  · intro htoggle who deviation
    rw [quittingTerminalPayoff_pureSetRoot]
    exact (quittingTerminalPayoff_update_pureSetRoot_le reward S who
      deviation).trans (htoggle who)

/-- **Sure exit sets.**  No member of `S` gains by staying behind and no
outsider gains by joining, both measured against the payoff `r(S)` of the
set's own simultaneous exit.  The empty set is admitted, with the extended
convention `r(∅) = 0` for nonabsorption. -/
def IsQuittingSureExitSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (S : Finset ι) : Prop :=
  (∀ member ∈ S,
      quittingSetReward reward (S.erase member) member ≤
        quittingSetReward reward S member) ∧
    ∀ outsider ∉ S,
      quittingSetReward reward (insert outsider S) outsider ≤
        quittingSetReward reward S outsider

omit [Fintype ι] in
/-- The membership split is only bookkeeping: at each player one of the two
toggles is the identity, so the sure-exit conditions are exactly the uniform
toggle test. -/
theorem isQuittingSureExitSet_iff_forall_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (S : Finset ι) :
    IsQuittingSureExitSet reward S ↔
      ∀ who, max (quittingSetReward reward (insert who S) who)
          (quittingSetReward reward (S.erase who) who) ≤
        quittingSetReward reward S who := by
  constructor
  · rintro ⟨hmember, houtsider⟩ who
    by_cases hwho : who ∈ S
    · rw [Finset.insert_eq_self.mpr hwho]
      exact max_le le_rfl (hmember who hwho)
    · rw [Finset.erase_eq_of_notMem hwho]
      exact max_le (houtsider who hwho) le_rfl
  · intro htoggle
    exact ⟨fun member _ ↦ le_trans (le_max_right _ _) (htoggle member),
      fun outsider _ ↦ le_trans (le_max_left _ _) (htoggle outsider)⟩

/-- **Theorem B: the sure-exit-set characterization.**  For every finite set
`S` of players, the stationary pure profile at which exactly the members of
`S` quit at every live history is an exact terminal Nash equilibrium of the
quitting game if and only if `S` is a sure exit set: no member `i` prefers
the exit `S ∖ {i}` it would leave behind, and no outsider `j` prefers the
enlarged exit `S ∪ {j}` it could force.

The deviation class is all behavior strategies.  No restriction on the size
of `S` or on the number of players is imposed; the two conditions are also
sufficient, so the test is exact rather than merely conservative. -/
theorem isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (S : Finset ι) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingPureSetRoot S)) ↔
      IsQuittingSureExitSet reward S := by
  rw [isεAsymptoticNash_pureSetRoot_iff, isQuittingSureExitSet_iff_forall_max]
  simp

/-- **Theorem B, unpacked.**  The characterization with both families of
inequalities written out. -/
theorem isεAsymptoticNash_pureSetRoot_iff_forall_mem_notMem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (S : Finset ι) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingPureSetRoot S)) ↔
      (∀ member ∈ S,
          quittingSetReward reward (S.erase member) member ≤
            quittingSetReward reward S member) ∧
        ∀ outsider ∉ S,
          quittingSetReward reward (insert outsider S) outsider ≤
            quittingSetReward reward S outsider :=
  isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet reward S

/-- **A sure exit set delivers its own reward uniformly.**  The exit payoff
`r(S)` of a sure exit set is a uniform-equilibrium payoff of the quitting
game. -/
theorem isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {S : Finset ι}
    (hS : IsQuittingSureExitSet reward S) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward S) := by
  have hnash := (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
    reward S).mpr hS
  have huniform :=
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
      reward _ hnash
  have hpayoff : quittingTerminalPayoff reward
      (quittingStationaryProfile reward (quittingPureSetRoot S)) =
      quittingSetReward reward S :=
    funext fun who ↦ quittingTerminalPayoff_pureSetRoot reward S who
  rwa [hpayoff] at huniform

/-! ## The degenerate exit sets -/

omit [Fintype ι] in
/-- The empty exit set is the all-continue branch: no player may have a
profitable solo exit. -/
theorem isQuittingSureExitSet_empty_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsQuittingSureExitSet reward (∅ : Finset ι) ↔
      ∀ who, quittingSoloReward reward who who ≤ 0 := by
  unfold IsQuittingSureExitSet
  simp [quittingSoloReward, quittingSetReward]

omit [Fintype ι] in
/-- Joining a solo exit is a singleton collision. -/
theorem quittingSetReward_insert_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner other : ι) :
    quittingSetReward reward (insert other {owner}) other =
      quittingSingletonCollisionReward reward owner other := by
  rw [quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _)]
  unfold quittingSingletonCollisionReward
  congr 1
  exact Subtype.ext (Finset.pair_comm other owner)

omit [Fintype ι] in
/-- The singleton exit set is the solo-quitter branch: the quitter's own
solo reward must be nonnegative, and no opponent may prefer joining it. -/
theorem isQuittingSureExitSet_singleton_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    IsQuittingSureExitSet reward ({owner} : Finset ι) ↔
      0 ≤ quittingSoloReward reward owner owner ∧
        ∀ other, other ≠ owner →
          quittingSingletonCollisionReward reward owner other ≤
            quittingSoloReward reward owner other := by
  unfold IsQuittingSureExitSet
  constructor
  · rintro ⟨hmember, houtsider⟩
    refine ⟨?_, fun other hother ↦ ?_⟩
    · have h := hmember owner (Finset.mem_singleton_self owner)
      simpa [quittingSoloReward, quittingSetReward] using h
    · have h := houtsider other (by simpa using hother)
      rwa [quittingSetReward_insert_singleton, quittingSetReward_of_nonempty
        reward (Finset.singleton_nonempty owner)] at h
  · rintro ⟨howner, hother⟩
    constructor
    · intro member hmember
      obtain rfl : member = owner := Finset.mem_singleton.mp hmember
      simpa [quittingSoloReward, quittingSetReward] using howner
    · intro outsider houtsider
      have hne : outsider ≠ owner := by simpa using houtsider
      rw [quittingSetReward_insert_singleton, quittingSetReward_of_nonempty
        reward (Finset.singleton_nonempty owner)]
      exact hother outsider hne

/-- The grand-coalition exit has no outsider, so only the member conditions
survive: nobody prefers being left behind by everyone else. -/
theorem isQuittingSureExitSet_univ_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsQuittingSureExitSet reward (Finset.univ : Finset ι) ↔
      ∀ who, quittingSetReward reward (Finset.univ.erase who) who ≤
        quittingSetReward reward Finset.univ who := by
  unfold IsQuittingSureExitSet
  simp

/-- **The grand-coalition exit.**  Everybody quitting at once is an exact
terminal Nash equilibrium exactly when no player prefers the exit of all the
others to the exit of all. -/
theorem isεAsymptoticNash_pureSetRoot_univ_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward
          (quittingPureSetRoot (Finset.univ : Finset ι))) ↔
      ∀ who, quittingSetReward reward (Finset.univ.erase who) who ≤
        quittingSetReward reward Finset.univ who := by
  rw [isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet,
    isQuittingSureExitSet_univ_iff]

/-! ## The two-element exit set

The pair `{first, second}` is the smallest exit set at which both member
conditions are nontrivial: each member's alternative is the *other* member's
solo exit.  At two players it is the grand-coalition exit and the outsider
family is empty, which is the joint-exit branch of the two-player existence
theorem; at more players the outsider conditions persist. -/

omit [Fintype ι] in
/-- A pair's exit reward, read at its second member, is that member's
collision reward with the first. -/
theorem quittingSetReward_pair_right
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : ι) :
    quittingSetReward reward ({first, second} : Finset ι) second =
      quittingSingletonCollisionReward reward first second :=
  quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _) second

omit [Fintype ι] in
/-- A pair's exit reward, read at its first member, is that member's
collision reward with the second. -/
theorem quittingSetReward_pair_left
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : ι) :
    quittingSetReward reward ({first, second} : Finset ι) first =
      quittingSingletonCollisionReward reward second first := by
  rw [quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _)]
  unfold quittingSingletonCollisionReward
  congr 1
  exact Subtype.ext (Finset.pair_comm first second)

omit [Fintype ι] in
/-- The pair exit set, unpacked.  Each member compares the joint exit with
the other member's solo exit; each outsider compares the joint exit with the
triple exit it would create. -/
theorem isQuittingSureExitSet_pair_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι} (hne : first ≠ second) :
    IsQuittingSureExitSet reward ({first, second} : Finset ι) ↔
      quittingSoloReward reward second first ≤
          quittingSingletonCollisionReward reward second first ∧
        quittingSoloReward reward first second ≤
            quittingSingletonCollisionReward reward first second ∧
          ∀ outsider, outsider ≠ first → outsider ≠ second →
            quittingSetReward reward (insert outsider {first, second})
                outsider ≤
              quittingSetReward reward {first, second} outsider := by
  rw [← quittingSetReward_pair_left, ← quittingSetReward_pair_right]
  have hfirst : ({first, second} : Finset ι).erase first = {second} :=
    Finset.erase_insert (by simp [hne])
  have hsecond : ({first, second} : Finset ι).erase second = {first} := by
    rw [Finset.pair_comm]
    exact Finset.erase_insert (by simp [hne.symm])
  unfold IsQuittingSureExitSet
  constructor
  · rintro ⟨hmember, houtsider⟩
    refine ⟨?_, ?_, fun outsider hfirstNe hsecondNe ↦ ?_⟩
    · have h := hmember first (by simp)
      rwa [hfirst, quittingSetReward_of_nonempty reward
        (Finset.singleton_nonempty second)] at h
    · have h := hmember second (by simp)
      rwa [hsecond, quittingSetReward_of_nonempty reward
        (Finset.singleton_nonempty first)] at h
    · exact houtsider outsider (by simp [hfirstNe, hsecondNe])
  · rintro ⟨hfirstLe, hsecondLe, houtsider⟩
    refine ⟨fun member hmember ↦ ?_, fun outsider hout ↦ ?_⟩
    · rcases Finset.mem_insert.mp hmember with rfl | hmem
      · rwa [hfirst, quittingSetReward_of_nonempty reward
          (Finset.singleton_nonempty second)]
      · obtain rfl : member = second := Finset.mem_singleton.mp hmem
        rwa [hsecond, quittingSetReward_of_nonempty reward
          (Finset.singleton_nonempty first)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
      exact houtsider outsider hout.1 hout.2

/-- **The two-player joint exit.**  On two coordinates the pair exit set is
the grand-coalition exit, the outsider family is empty, and the two member
conditions say that neither player prefers the other's solo exit to the
joint exit.  Both players quitting surely is then an exact terminal Nash
equilibrium and the joint exit reward is a uniform-equilibrium payoff.

This is exactly the joint-exit branch of the two-player closure of the
quitting conjecture, recovered here as the two-coordinate instance of the
general characterization: that branch's own proof runs through the
sure-set/owner root at full hazard `p = 1` and carries the same two
hypotheses. -/
theorem quittingGame_isUniformEquilibriumPayoff_jointExit_of_bool
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (owner : Bool)
    (howner : quittingSoloReward reward (!owner) owner ≤
      quittingSingletonCollisionReward reward (!owner) owner)
    (hblocker : quittingSoloReward reward owner (!owner) ≤
      quittingSingletonCollisionReward reward owner (!owner)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward ({owner, !owner} : Finset Bool)) := by
  refine isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward
    ((isQuittingSureExitSet_pair_iff reward (by simp)).mpr
      ⟨howner, hblocker, fun outsider hfirst hsecond ↦ ?_⟩)
  exact absurd (Bool.eq_not_of_ne hfirst) hsecond

omit [Fintype ι] in
/-- The singleton exit set is the sure-rate solo root. -/
theorem quittingPureSetRoot_singleton (owner : ι) :
    quittingPureSetRoot ({owner} : Finset ι) =
      quittingSoloStationaryRoot owner (PMF.pure true) := by
  funext who
  by_cases hwho : who = owner
  · subst who
    simp [quittingPureSetRoot, quittingSetAction, quittingSoloStationaryRoot]
  · simp [quittingPureSetRoot, quittingSetAction, quittingSoloStationaryRoot,
      hwho]

/-! ## Cross-checks against the landed degenerate branches

The empty and singleton exit sets are the two cases in which a deviator's
opponents never absorb, so they are the two cases the Snell-cap route above
cannot reach.  Both already have landed exact characterizations, and the
theorems below rebuild the corresponding instances of the main equivalence
out of those landed statements alone.  They therefore check that the
sure-exit conditions are the *same* inequalities, not merely equivalent ones
by an accident of the new proof. -/

/-- **Cross-check at the empty exit set.**  Rebuilt from the landed
all-continue test of the simple-branch module. -/
theorem isεAsymptoticNash_pureSetRoot_empty_iff_isQuittingSureExitSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward
          (quittingPureSetRoot (∅ : Finset ι))) ↔
      IsQuittingSureExitSet reward (∅ : Finset ι) := by
  rw [quittingStationaryProfile_pureSetRoot_empty,
    isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl,
    isQuittingSureExitSet_empty_iff]
  simp [quittingSoloReward, quittingSingletonTerminal]

/-- **Cross-check at a singleton exit set.**  Rebuilt from the landed exact
owner-solo characterization, read at the sure rate `p = 1`. -/
theorem isεAsymptoticNash_pureSetRoot_singleton_iff_isQuittingSureExitSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward
          (quittingPureSetRoot ({owner} : Finset ι))) ↔
      IsQuittingSureExitSet reward ({owner} : Finset ι) := by
  rw [quittingPureSetRoot_singleton,
    isεAsymptoticNash_soloStationary_exact_iff reward owner (PMF.pure true)
      (by simp),
    isQuittingSureExitSet_singleton_iff]
  constructor
  · rintro ⟨howner, hother⟩
    exact ⟨howner, fun other hne ↦ by simpa using hother other hne⟩
  · rintro ⟨howner, hother⟩
    exact ⟨howner, fun other hne ↦ by simpa using hother other hne⟩

/-! ## Consistency with the sure-set repair regression

The characterization is an exact test on a *given* set, and says nothing
about the existence of one.  The landed three-player repair regression below
is a statement of the second kind, and the test confirms that the two
readings agree on its table.  A companion regression table, on which no
nonempty coalition passes the sure-exit test at all, carries the matching
cross-check next to its own direct-pure-set exploitability bound. -/

section RepairRegression

open QuittingSureSetRepairCounterexample

/-- In the three-player sure-set repair regression the coalition `{0,1}`
*is* a sure exit set: player zero does not prefer player one's solo exit,
player one does not prefer player zero's solo exit, and player two does not
prefer joining. -/
theorem isQuittingSureExitSet_repairRegression_zeroOne :
    IsQuittingSureExitSet reward ({0, 1} : Finset Player) := by
  rw [isQuittingSureExitSet_iff_forall_max]
  intro who
  fin_cases who <;>
    norm_num [quittingSetReward, reward, Finset.erase_insert_of_ne,
      Finset.insert_comm]

/-- Its exit reward is the landed direct-First payoff `(1,1,0)`. -/
theorem quittingSetReward_repairRegression_zeroOne :
    quittingSetReward reward ({0, 1} : Finset Player) = firstValue := by
  funext who
  fin_cases who <;> norm_num [quittingSetReward, reward, firstValue]

/-- **Cross-check.**  The characterization reproves the landed
`QuittingSureSetRepairCounterexample.firstValue_isUniformEquilibriumPayoff`
along a different route: the landed proof runs through the cutoff-one safe
root, whereas here `{0,1}` passes the sure-exit test and the stationary
profile itself is an exact terminal equilibrium. -/
theorem firstValue_isUniformEquilibriumPayoff_of_sureExitSet :
    (quittingGame reward).IsUniformEquilibriumPayoff none firstValue := by
  rw [← quittingSetReward_repairRegression_zeroOne]
  exact isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward
    isQuittingSureExitSet_repairRegression_zeroOne

end RepairRegression

end GameTheory
