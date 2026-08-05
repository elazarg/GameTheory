/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingTwoPlayerPairRepair
import GameTheory.Concepts.Stochastic.QuittingSureSetOwnerRepair
import GameTheory.Concepts.Stochastic.QuittingZeroSoloDisjunct

/-!
# Every two-player finite quitting game has a uniform equilibrium payoff

The quitting conjecture is closed on two coordinates.  Writing `owner` for one
player and `!owner` for the other, the numbers that matter are the solo values
`r_x({x})`, the cross values `r_y({x})`, and the joint values `r_y({x,y})`.
The proof is a four-way split, each branch discharged by a theorem already in
the repository except for the joint-exit branch built below.

* **Zero solo.**  If `r_x({x}) ≤ 0` at both coordinates, all-continue is an
  exact terminal equilibrium and the payoff is `0`
  (`quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`).
* **Solo quitter.**  Otherwise fix `owner` with `r_owner({owner}) > 0`.  If
  some rate `p ∈ (0,1]` keeps the blocker from joining, the owner's solo row
  is an exact terminal equilibrium
  (`isUniformEquilibriumPayoff_soloReward_of_inactive`).
* **Pair repair.**  If no rate does, then `p = 1` fails, which gives
  `r_blocker({owner}) < r_blocker({owner,blocker})`, and the vanishing-rate
  end fails too, which forces `r_blocker({owner}) ≤ r_blocker({blocker})`.
  If additionally `r_owner({owner,blocker}) ≤ r_owner({blocker})`, the landed
  two-player pair repair applies: the blocker quits surely, the owner quits at
  a vanishing rate (`exists_uniformEquilibriumPayoff_of_bool_pairRepair`).
* **Joint exit.**  In the remaining case `r_owner({blocker})` is *below*
  `r_owner({owner,blocker})`, and `p = 1`'s failure already gave
  `r_blocker({owner}) ≤ r_blocker({owner,blocker})`.  Both players quitting
  surely is then an exact terminal equilibrium.  That branch is the new
  content here: a full-rate `p = 1` instance of the sure-set/owner machinery.

## Exact rows versus equilibria at two coordinates

Every two-coordinate weight has a period-one *exact row*, by the same
`p = 1` argument used in the joint-exit branch; the case analysis is
reproduced by the split above.  But a row certificate is not an equilibrium: the sure-set row needs no
side condition, whereas a *solo* row certifies an equilibrium of the game only
when the owner's own solo value is nonnegative — its `IsQuittingCycleAdmissible`
obligation, since the owner's opponents never absorb at a solo row.  This
exact-row trichotomy therefore does not close the two-player conjecture on its own: a
weight whose only exact singleton row belongs to a coordinate with negative
solo value, such as `r({owner}) = (1, -2)`, `r({blocker}) = (0, -1)`,
`r({owner,blocker}) = (-1, 0)`, has no exact *stationary* equilibrium at all
(hand-checked over the four corners and the interior of the rate square, not
formalized).  The pair-repair branch, whose error is linear in the owner's
vanishing rate and therefore genuinely approximate, is what covers those
weights.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability QuittingSureSetOwnerRepair

namespace QuittingTwoPlayerExistence

/-! ## A scalar interpolation lemma -/

/-- If an affine function of `p` stays strictly above a target throughout
`(0,1]`, then its value at `p = 0` is already at least that target.  This is
the vanishing-rate end of the solo-quitter criterion, made explicit: the
witness rate is `min 1 ((target - base) / (1 + |slope|))`. -/
theorem le_of_lt_affine_on_unitInterval {base slope target : ℝ}
    (haffine : ∀ p : ℝ, 0 < p → p ≤ 1 → target < base + p * slope) :
    target ≤ base := by
  by_contra hlt
  push Not at hlt
  have hgap : 0 < target - base := by linarith
  have hspread : (0 : ℝ) ≤ |slope| := abs_nonneg slope
  have hden : (0 : ℝ) < 1 + |slope| := by linarith
  have hp0 : 0 < min 1 ((target - base) / (1 + |slope|)) :=
    lt_min one_pos (div_pos hgap hden)
  have hstrict := haffine _ hp0 (min_le_left _ _)
  have hslope : min 1 ((target - base) / (1 + |slope|)) * slope ≤
      min 1 ((target - base) / (1 + |slope|)) * |slope| :=
    mul_le_mul_of_nonneg_left (le_abs_self slope) hp0.le
  have hsmall : min 1 ((target - base) / (1 + |slope|)) * |slope| <
      target - base := by
    have hbound : min 1 ((target - base) / (1 + |slope|)) * |slope| ≤
        (target - base) / (1 + |slope|) * |slope| :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hspread
    have hfrac : (target - base) / (1 + |slope|) * |slope| < target - base := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    linarith
  linarith

/-! ## The joint-exit branch -/

/-- The terminal state in which both players quit. -/
def jointExitTerminal (owner : Bool) : {S : Finset Bool // S.Nonempty} :=
  ⟨{owner, !owner}, Finset.insert_nonempty _ _⟩

/-- A player is not a member of the other player's singleton. -/
theorem owner_notMem_blocker (owner : Bool) :
    owner ∉ ({!owner} : Finset Bool) := by
  simp

/-- The joint exit set, read at the blocker's coordinate, is the blocker's
collision reward with the owner. -/
theorem quittingSetReward_jointExit_blocker
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (owner : Bool) :
    quittingSetReward reward (insert owner {!owner}) (!owner) =
      quittingSingletonCollisionReward reward owner (!owner) := by
  rw [quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _)]
  rfl

/-- The joint exit set, read at the owner's coordinate, is the owner's
collision reward with the blocker. -/
theorem quittingSetReward_jointExit_owner
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (owner : Bool) :
    quittingSetReward reward (insert owner {!owner}) owner =
      quittingSingletonCollisionReward reward (!owner) owner := by
  rw [quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _)]
  unfold quittingSingletonCollisionReward
  congr 1
  exact Subtype.ext (Finset.pair_comm owner (!owner))

/-- The blocker's singleton set reward is its solo reward vector. -/
theorem quittingSetReward_blocker
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (owner who : Bool) :
    quittingSetReward reward ({!owner} : Finset Bool) who =
      quittingSoloReward reward (!owner) who := by
  rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty _)]
  rfl

/-- The owner's singleton set reward is its solo reward vector. -/
theorem quittingSetReward_owner
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (owner who : Bool) :
    quittingSetReward reward ({owner} : Finset Bool) who =
      quittingSoloReward reward owner who := by
  rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty _)]
  rfl

/-- At full rate the sure-set/owner mixture degenerates to the joint exit. -/
theorem quittingSureSetOwnerValue_bothQuit
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (owner who : Bool) :
    quittingSureSetOwnerValue reward ({!owner} : Finset Bool) owner 1 who =
      quittingSetReward reward (insert owner {!owner}) who := by
  unfold quittingSureSetOwnerValue
  ring

/-- **The joint-exit cap bound.**  If neither player prefers the other's solo
exit to the joint exit, the exact unilateral cap of the both-quit row equals
the row's own value at both coordinates. -/
theorem quittingSureSetOwnerExactCap_bothQuit_le
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (owner : Bool)
    (howner : quittingSoloReward reward (!owner) owner ≤
      quittingSingletonCollisionReward reward (!owner) owner)
    (hblocker : quittingSoloReward reward owner (!owner) ≤
      quittingSingletonCollisionReward reward owner (!owner))
    (who : Bool) :
    quittingSureSetOwnerExactCap reward ({!owner} : Finset Bool) owner 1 who ≤
      quittingSureSetOwnerValue reward ({!owner} : Finset Bool) owner 1 who +
        0 := by
  rw [add_zero, quittingSureSetOwnerValue_bothQuit]
  unfold quittingSureSetOwnerExactCap
  by_cases hwho : who = owner
  · subst who
    rw [if_pos rfl]
    refine max_le le_rfl ?_
    rw [quittingSetReward_blocker, quittingSetReward_jointExit_owner]
    exact howner
  · obtain rfl : who = !owner := Bool.eq_not_of_ne hwho
    have hempty : ¬ ((({!owner} : Finset Bool).erase (!owner)).Nonempty) := by
      simp
    rw [if_neg hwho, if_neg hempty, Finset.pair_eq_singleton,
      quittingSureSetOwnerValue_bothQuit]
    refine max_le le_rfl ?_
    rw [quittingSetReward_owner, quittingSetReward_jointExit_blocker]
    exact hblocker

/-- **The joint-exit branch.**  If neither player prefers the other's solo
exit to the joint exit, both players quitting surely is an exact terminal
Nash profile, so the joint exit reward is a uniform-equilibrium payoff. -/
theorem quittingGame_isUniformEquilibriumPayoff_jointExit
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (owner : Bool)
    (howner : quittingSoloReward reward (!owner) owner ≤
      quittingSingletonCollisionReward reward (!owner) owner)
    (hblocker : quittingSoloReward reward owner (!owner) ≤
      quittingSingletonCollisionReward reward owner (!owner)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (reward (jointExitTerminal owner)) := by
  have hnash := isεAsymptoticNash_sureSetOwnerRoot_of_exactCap_le reward
    (T := ({!owner} : Finset Bool)) (owner := owner)
    (Finset.singleton_nonempty _) (owner_notMem_blocker owner)
    1 zero_le_one le_rfl one_pos 0
    (quittingSureSetOwnerExactCap_bothQuit_le reward owner howner hblocker)
  have huniform := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward _ hnash
  have hpayoff : quittingTerminalPayoff reward
      (quittingStationaryProfile reward
        (quittingSureSetOwnerRoot ({!owner} : Finset Bool) owner 1
          zero_le_one le_rfl)) = reward (jointExitTerminal owner) := by
    funext who
    rw [terminalPayoff_sureSetOwnerRoot reward (Finset.singleton_nonempty _)
      (owner_notMem_blocker owner) 1 zero_le_one le_rfl who,
      quittingSureSetOwnerValue_bothQuit,
      quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _)]
    rfl
  rwa [hpayoff] at huniform

/-! ## The solo-quitter branch, two-player form -/

/-- **The solo-quitter branch.**  A nonnegative solo value together with a
rate at which the blocker does not want to join delivers the owner's solo
payoff vector uniformly. -/
theorem quittingGame_isUniformEquilibriumPayoff_soloRate
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (owner : Bool)
    (hsolo : 0 ≤ quittingSoloReward reward owner owner)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hrate : (1 - p) * quittingSoloReward reward (!owner) (!owner) +
        p * quittingSingletonCollisionReward reward owner (!owner) ≤
      quittingSoloReward reward owner (!owner)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  refine isUniformEquilibriumPayoff_soloReward_of_inactive reward owner
    (quittingHazardCoin p hp0.le hp1) ?_ hsolo ?_
  · rw [quittingHazardCoin_true_toReal]
    exact hp0
  · intro other hother
    obtain rfl : other = !owner := Bool.eq_not_of_ne hother
    rw [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
    exact hrate

/-- **Failure of the solo-quitter criterion pins both endpoints.**  If no rate
in `(0,1]` keeps the blocker out of the owner's exit, then the blocker's own
solo value dominates the owner's solo exit, and the blocker strictly prefers
joining that exit to being left in it. -/
theorem endpoints_of_soloRate_infeasible
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (owner : Bool)
    (hfail : ∀ p : ℝ, 0 < p → p ≤ 1 →
      quittingSoloReward reward owner (!owner) <
        (1 - p) * quittingSoloReward reward (!owner) (!owner) +
          p * quittingSingletonCollisionReward reward owner (!owner)) :
    quittingSoloReward reward owner (!owner) ≤
        quittingSoloReward reward (!owner) (!owner) ∧
      quittingSoloReward reward owner (!owner) <
        quittingSingletonCollisionReward reward owner (!owner) := by
  refine ⟨le_of_lt_affine_on_unitInterval (slope :=
    quittingSingletonCollisionReward reward owner (!owner) -
      quittingSoloReward reward (!owner) (!owner)) ?_, ?_⟩
  · intro p hp0 hp1
    have hstrict := hfail p hp0 hp1
    nlinarith [hstrict]
  · have hstrict := hfail 1 one_pos le_rfl
    linarith

/-! ## The headline -/

/-- **Every two-player finite quitting game has a uniform equilibrium
payoff.**

`HEADLINE` — the first fully closed subclass of the quitting conjecture.  The
statement is unconditional: no hypothesis on the weight, no restriction to a
class of tables, and the deviation class is all behavior strategies.

Three of the four branches name their payoff: the zero vector
(`quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`), the owner's solo
reward `r(·)({owner})` (`quittingGame_isUniformEquilibriumPayoff_soloRate`),
and the joint exit reward `r(·)({0,1})`
(`quittingGame_isUniformEquilibriumPayoff_jointExit`).  The pair-repair branch
does not: its profiles are only approximate equilibria, one per accuracy, and
the payoff is extracted by compactness, so the statement below is existential
rather than an evaluation.

Three or more players are not covered.  The pair-repair branch is two-player
by construction: making a terminal set of three or more players quit surely
creates leaver deviations inside that set, which its two inequalities do not
control. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_twoPlayer
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) :
    ∃ payoff : Payoff Bool,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_cases hzero : IsQuittingZeroSolo reward
  · exact exists_uniformEquilibriumPayoff_of_zeroSolo reward hzero
  · unfold IsQuittingZeroSolo at hzero
    push Not at hzero
    obtain ⟨owner, hpos⟩ := hzero
    have hsolo : 0 ≤ quittingSoloReward reward owner owner := le_of_lt hpos
    by_cases hrate : ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
        (1 - p) * quittingSoloReward reward (!owner) (!owner) +
            p * quittingSingletonCollisionReward reward owner (!owner) ≤
          quittingSoloReward reward owner (!owner)
    · obtain ⟨p, hp0, hp1, hle⟩ := hrate
      exact ⟨_, quittingGame_isUniformEquilibriumPayoff_soloRate reward owner
        hsolo hp0 hp1 hle⟩
    · push Not at hrate
      obtain ⟨hblockerSolo, hjoin⟩ :=
        endpoints_of_soloRate_infeasible reward owner hrate
      by_cases hpair :
          quittingSingletonCollisionReward reward (!owner) owner ≤
            quittingSoloReward reward (!owner) owner
      · exact QuittingTwoPlayerPairRepair.exists_uniformEquilibriumPayoff_of_bool_pairRepair
          reward owner hpair hblockerSolo
      · push Not at hpair
        exact ⟨_, quittingGame_isUniformEquilibriumPayoff_jointExit reward
          owner hpair.le hjoin.le⟩

end QuittingTwoPlayerExistence

end GameTheory
