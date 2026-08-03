/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtPositiveLimit
import GameTheory.Concepts.Stochastic.QuittingPositiveDynamicDebtProvenance

/-!
# Join-monotone quitting games have uniform equilibria

Positive exact dynamic debt has a terminal full-set witness: some player
strictly prefers staying out of an already nonempty quitting coalition to
joining it.  Consequently the opposite payoff monotonicity rules out positive
debt on every positive-length zero-boundary chain.  Cutoff one already has
zero optimized min-max debt, so the exact finite-chain compiler closes.

The sharp condition only constrains owners whose singleton quitting reward is
positive.  The more familiar global own-joining condition is an immediate
corollary.  The final theorem records the contrapositive obstruction which
any counterexample to uniform existence would have to contain.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One player never loses by joining an already nonempty quitting coalition
which does not contain that player. -/
def QuittingOwnerJoinMonotone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  ∀ (quitters : Finset ι) (hquitters : quitters.Nonempty),
    owner ∉ quitters →
      reward ⟨quitters, hquitters⟩ owner ≤
        reward ⟨insert owner quitters, Finset.insert_nonempty owner quitters⟩
          owner

/-- Every player has the owner-joining monotonicity. -/
def QuittingOwnJoinMonotone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ owner, QuittingOwnerJoinMonotone reward owner

/-- The sharp condition: joining monotonicity is needed only for players with
a positive singleton reward, because positive exact debt forces that sign. -/
def QuittingPositiveSoloOwnJoinMonotone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ owner, 0 < reward (quittingSingletonTerminal owner) owner →
    QuittingOwnerJoinMonotone reward owner

/-- Join monotonicity makes every terminal opponent-advantage atom
nonpositive when the owner is forced to Continue. -/
theorem quittingTerminalOpponentAdvantage_nonpos_of_ownJoinMonotone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hjoin : QuittingOwnerJoinMonotone reward owner)
    (action : ι → Bool) (howner : action owner = false) :
    quittingTerminalOpponentAdvantage reward owner action ≤ 0 := by
  unfold quittingTerminalOpponentAdvantage
  unfold quittingRootPayoff
  rw [quittingQuitters_update_true_of_apply_false]
  by_cases hquitters : (quittingQuitters action).Nonempty
  · simp only [dif_pos hquitters,
      dif_pos (Finset.insert_nonempty owner (quittingQuitters action))]
    apply sub_nonpos.mpr
    apply hjoin (quittingQuitters action) hquitters
    simp [quittingQuitters, howner]
  · have hempty : quittingQuitters action = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hquitters
    simp [hempty, quittingSingletonTerminal]

/-- Every playerwise exact debt on a positive-length zero-boundary chain
vanishes under positive-solo own-joining monotonicity. -/
theorem
    quittingFiniteNashBellmanPathDynamicDebt_eq_zero_of_positiveSoloOwnJoinMonotone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hjoin : QuittingPositiveSoloOwnJoinMonotone reward)
    (last : ℕ) (path : QuittingFiniteNashBellmanPath ι (last + 1))
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1))
    (owner : ι) :
    quittingFiniteNashBellmanPathDynamicDebt
      reward (last + 1) path owner 0 = 0 := by
  have hnonneg := quittingFiniteNashBellmanPathDynamicDebt_nonneg
    reward (last + 1) path hpath owner 0
  apply le_antisymm ?_ hnonneg
  by_contra hnot
  have hpositive :
      0 < quittingFiniteNashBellmanPathDynamicDebt
        reward (last + 1) path owner 0 :=
    lt_of_not_ge hnot
  obtain ⟨action, hmass, hadvantage, -, -⟩ :=
    exists_finiteDynamicDebt_lastAtom_quantitative
      reward last path hpath owner hpositive
  let distribution := pmfPi (Function.update
    (quittingFiniteNashBellmanPathRoots (last + 1) path last)
      owner (PMF.pure false))
  have hmassOnly : 0 < (distribution action).toReal := by
    apply pos_of_mul_pos_right hmass
    exact quittingOpponentSurvivalWeight_nonneg
      (quittingFiniteNashBellmanPathRoots (last + 1) path) owner 0 last
  have hsupport : action ∈ distribution.support := by
    rw [PMF.mem_support_iff]
    intro hzero
    rw [hzero, ENNReal.toReal_zero] at hmassOnly
    exact (lt_irrefl 0 hmassOnly).elim
  have hownerFalse : action owner = false :=
    action_eq_false_of_mem_support_pmfPi_update_pure_false
      (quittingFiniteNashBellmanPathRoots (last + 1) path last)
      owner action hsupport
  have hsolo :
      0 < reward (quittingSingletonTerminal owner) owner :=
    positiveSingletonReward_of_finiteDynamicDebt_pos
      reward (last + 1) path hpath owner hpositive
  have hnonpos :=
    quittingTerminalOpponentAdvantage_nonpos_of_ownJoinMonotone
      reward owner (hjoin owner hsolo) action hownerFalse
  linarith

/-- The literal max exact-debt objective is already zero on every
positive-length admissible chain. -/
theorem
    quittingFiniteNashBellmanPathMaxDynamicDebt_eq_zero_of_positiveSoloOwnJoinMonotone
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hjoin : QuittingPositiveSoloOwnJoinMonotone reward)
    (last : ℕ) (path : QuittingFiniteNashBellmanPath ι (last + 1))
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1)) :
    quittingFiniteNashBellmanPathMaxDynamicDebt
      reward (last + 1) path = 0 := by
  apply le_antisymm
  · unfold quittingFiniteNashBellmanPathMaxDynamicDebt
    apply Finset.sup'_le
    intro owner _
    rw [quittingFiniteNashBellmanPathDynamicDebt_eq_zero_of_positiveSoloOwnJoinMonotone
      reward hjoin last path hpath owner]
  · exact quittingFiniteNashBellmanPathMaxDynamicDebt_nonneg
      reward (last + 1) path hpath

/-- The optimized min-max obstruction has zero infimum; in fact its value at
cutoff one is already zero. -/
theorem
    iInf_quittingFiniteMinMaxDynamicDebt_eq_zero_of_positiveSoloOwnJoinMonotone
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hjoin : QuittingPositiveSoloOwnJoinMonotone reward) :
    (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff) =
        0 := by
  have hcutoffOne :
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward 1 = 0 := by
    unfold quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
    simpa using
      quittingFiniteNashBellmanPathMaxDynamicDebt_eq_zero_of_positiveSoloOwnJoinMonotone
        reward hjoin 0
        (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward 1)
        (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
          reward 1)
  apply le_antisymm
  · have hbdd : BddBelow (Set.range fun cutoff : ℕ ↦
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
          reward cutoff) := by
      refine ⟨0, ?_⟩
      rintro value ⟨cutoff, rfl⟩
      exact quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
        reward cutoff
    exact (ciInf_le hbdd 1).trans_eq hcutoffOne
  · exact iInf_quittingFiniteMinMaxDynamicDebt_nonneg reward

/-- **Positive-solo own-joining uniform-existence theorem.** -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_positiveSoloOwnJoinMonotone
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hjoin : QuittingPositiveSoloOwnJoinMonotone reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_iInf_finiteMinMaxDynamicDebt_eq_zero
  exact
    iInf_quittingFiniteMinMaxDynamicDebt_eq_zero_of_positiveSoloOwnJoinMonotone
    reward hjoin

/-- Global joining monotonicity is an immediate corollary of the sharp
positive-solo condition. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_globalOwnJoinMonotone
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hjoin : QuittingOwnJoinMonotone reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_positiveSoloOwnJoinMonotone
  intro owner _
  exact hjoin owner

/-- Any counterexample to uniform existence must contain a positive-solo
player who is strictly harmed by joining some nonempty opponent quitting
coalition.  This is only a necessary obstruction, not a sufficient one. -/
theorem exists_positiveSolo_strictOwnJoinLoss_of_no_uniformEquilibriumPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ owner : ι, ∃ quitters : {T : Finset ι // T.Nonempty},
      owner ∉ quitters.1 ∧
      0 < reward (quittingSingletonTerminal owner) owner ∧
      reward
          ⟨insert owner quitters.1,
            Finset.insert_nonempty owner quitters.1⟩ owner <
        reward quitters owner := by
  by_contra hobstruction
  have hjoin : QuittingPositiveSoloOwnJoinMonotone reward := by
    intro owner hsolo quitters hquitters howner
    by_contra hloss
    have hstrict :
        reward
            ⟨insert owner quitters,
              Finset.insert_nonempty owner quitters⟩ owner <
          reward ⟨quitters, hquitters⟩ owner :=
      lt_of_not_ge hloss
    exact hobstruction
      ⟨owner, ⟨quitters, hquitters⟩, howner, hsolo, hstrict⟩
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_positiveSoloOwnJoinMonotone
      reward hjoin)

end GameTheory
