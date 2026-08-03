/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteNashBellmanMinimizer
import GameTheory.Concepts.Stochastic.QuittingExceptionalTailLimits
import GameTheory.Concepts.Stochastic.QuittingMarkedTimeAdvance

/-!
# Monotonicity of minimum finite-chain debt

An admissible zero-boundary chain of length `K` can be extended to length
`K + 1` by prepending any exact bounded Nash--Bellman predecessor of its
initial point.  The old chain is then the literal one-stage suffix.  Every
player's opponent-survival debt is multiplied by the new first-stage
opponent Continue mass, a number in `[0,1]`.  Thus fixed-cutoff minimum
aggregate debt is antitone in the cutoff.

This does not prove that the decreasing debts converge to zero.  It turns
their infimum into the limit of a canonical monotone scalar obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If every opponent of `owner` continues with probability one, each fixed
opponent's Quit probability is zero. -/
theorem quittingProbability_eq_zero_of_fixedOpponentsContinueMass_eq_one
    (root : ι → PMF Bool) (owner other : ι) (hne : other ≠ owner)
    (hmass : quittingStationaryContinueMass
      (Function.update root owner (PMF.pure false)) = 1) :
    (root other true).toReal = 0 := by
  have hle := quittingProbability_le_opponentAbsorptionMass
    root (marked := other) (who := owner) hne
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass at hle
  rw [hmass] at hle
  exact le_antisymm (by linarith) ENNReal.toReal_nonneg

/-- The first point of a finite chain, packaged in the canonical compact
box. -/
def quittingFiniteNashBellmanPathInitialBoxPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    (canonicalQuittingNashBellmanSerialRelation reward).box :=
  ⟨path 0, hpath.1 0⟩

/-- Prepend the canonical exact predecessor of the initial point. -/
def quittingFiniteNashBellmanPathPrepend
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    QuittingFiniteNashBellmanPath ι (cutoff + 1) :=
  Fin.cases
    ((canonicalQuittingNashBellmanSerialRelation reward).predecessor
      (quittingFiniteNashBellmanPathInitialBoxPoint
        reward cutoff path hpath))
    path

@[simp] theorem quittingFiniteNashBellmanPathPrepend_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathPrepend reward cutoff path hpath 0 =
      (canonicalQuittingNashBellmanSerialRelation reward).predecessor
        (quittingFiniteNashBellmanPathInitialBoxPoint
          reward cutoff path hpath) := by
  rfl

@[simp] theorem quittingFiniteNashBellmanPathPrepend_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : Fin (cutoff + 1)) :
    quittingFiniteNashBellmanPathPrepend reward cutoff path hpath
        (Fin.succ time) = path time := by
  rfl

/-- Prepending preserves the exact zero-boundary chain constraints. -/
theorem quittingFiniteNashBellmanPathPrepend_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathPrepend reward cutoff path hpath ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) := by
  classical
  let system := canonicalQuittingNashBellmanSerialRelation reward
  let initial := quittingFiniteNashBellmanPathInitialBoxPoint
    reward cutoff path hpath
  refine ⟨?_, ?_, ?_⟩
  · intro time
    refine Fin.cases ?_ (fun oldTime ↦ ?_) time
    · exact (system.predecessor initial).property
    · simpa only [quittingFiniteNashBellmanPathPrepend_succ] using
        hpath.1 oldTime
  · rw [show Fin.last (cutoff + 1) = Fin.succ (Fin.last cutoff) by rfl,
      quittingFiniteNashBellmanPathPrepend_succ]
    exact hpath.2.1
  · intro time
    refine Fin.cases ?_ (fun oldTime ↦ ?_) time
    · change IsQuittingNashBellmanEdge reward
        (system.predecessor initial) initial
      exact system.predecessor_related initial
    · rw [show oldTime.succ.castSucc = Fin.succ oldTime.castSucc by rfl,
        quittingFiniteNashBellmanPathPrepend_succ]
      simpa only [quittingFiniteNashBellmanPathPrepend_succ] using
        hpath.2.2 oldTime

/-- From time one onward, the prepended operational root sequence is the
old root sequence with its clock shifted by one. -/
theorem quittingFiniteNashBellmanPathRoots_prepend_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
        (time + 1) =
      quittingFiniteNashBellmanPathRoots cutoff path time := by
  simp only [quittingFiniteNashBellmanPathRoots,
    dif_pos (by omega : time + 1 < cutoff + 1), dif_pos htime]
  congr 1

/-- The time-one survival tail of the prepended path is exactly the old
time-zero survival. -/
theorem quittingOpponentSurvivalWeight_prepend_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots (cutoff + 1)
          (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath))
        who 1 cutoff =
      quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots cutoff path) who 0 cutoff := by
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_congr rfl
  intro offset hoffset
  have hroot := quittingFiniteNashBellmanPathRoots_prepend_succ
    reward cutoff path hpath offset (Finset.mem_range.mp hoffset)
  unfold quittingFixedOpponentsContinueMass
  rw [show 1 + offset = offset + 1 by omega, hroot]
  simp only [Nat.zero_add]

/-- Prepending multiplies each operational opponent-survival weight by the
new first-stage opponent Continue mass. -/
theorem quittingOpponentSurvivalWeight_prepend
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots (cutoff + 1)
          (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath))
        who 0 (cutoff + 1) =
      quittingFixedOpponentsContinueMass
          (quittingFiniteNashBellmanPathRoots (cutoff + 1)
            (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath))
          who 0 *
        quittingOpponentSurvivalWeight
          (quittingFiniteNashBellmanPathRoots cutoff path) who 0 cutoff := by
  let newRoots := quittingFiniteNashBellmanPathRoots (cutoff + 1)
    (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
  have hfuel : cutoff + 1 = 1 + cutoff := by omega
  calc
    quittingOpponentSurvivalWeight newRoots who 0 (cutoff + 1) =
        quittingOpponentSurvivalWeight newRoots who 0 (1 + cutoff) :=
      congrArg (fun fuel ↦
        quittingOpponentSurvivalWeight newRoots who 0 fuel) hfuel
    _ = quittingOpponentSurvivalWeight newRoots who 0 1 *
          quittingOpponentSurvivalWeight newRoots who 1 cutoff :=
      quittingOpponentSurvivalWeight_add newRoots who 0 1 cutoff
    _ = quittingFixedOpponentsContinueMass newRoots who 0 *
          quittingOpponentSurvivalWeight
            (quittingFiniteNashBellmanPathRoots cutoff path) who 0 cutoff := by
      rw [quittingOpponentSurvivalWeight_prepend_tail]
      simp [quittingOpponentSurvivalWeight]

/-- Exact playerwise debt factorization under predecessor prepending. -/
theorem quittingFiniteNashBellmanPathPlayerDebt_prepend_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathPlayerDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath) who =
      quittingFixedOpponentsContinueMass
          (quittingFiniteNashBellmanPathRoots (cutoff + 1)
            (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath))
          who 0 *
        quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who := by
  rw [quittingFiniteNashBellmanPathPlayerDebt_eq,
    quittingFiniteNashBellmanPathPlayerDebt_eq,
    quittingOpponentSurvivalWeight_prepend]
  ring

/-- Every player's surviving singleton debt weakly decreases when a
predecessor is prepended. -/
theorem quittingFiniteNashBellmanPathPlayerDebt_prepend_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathPlayerDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath) who ≤
      quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who := by
  rw [quittingFiniteNashBellmanPathPlayerDebt_prepend_eq]
  let firstMass := quittingFixedOpponentsContinueMass
    (quittingFiniteNashBellmanPathRoots (cutoff + 1)
      (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)) who 0
  let oldDebt :=
    quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who
  have hfirst1 : firstMass ≤ 1 :=
    quittingStationaryContinueMass_le_one _
  have hold0 : 0 ≤ oldDebt :=
    quittingFiniteNashBellmanPathPlayerDebt_nonneg
      reward cutoff path who
  change firstMass * oldDebt ≤ oldDebt
  exact mul_le_of_le_one_left hold0 hfirst1

/-- Aggregate surviving debt weakly decreases under predecessor
prepending. -/
theorem quittingFiniteNashBellmanPathAggregateDebt_prepend_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathAggregateDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath) ≤
      quittingFiniteNashBellmanPathAggregateDebt reward cutoff path := by
  unfold quittingFiniteNashBellmanPathAggregateDebt
  exact Finset.sum_le_sum fun who _ ↦
    quittingFiniteNashBellmanPathPlayerDebt_prepend_le
      reward cutoff path hpath who

/-- A positive old player debt and a genuine first-stage contraction make
the prepended aggregate debt strictly smaller. -/
theorem quittingFiniteNashBellmanPathAggregateDebt_prepend_lt_of_player
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι)
    (hdebt : 0 <
      quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who)
    (hcontract : quittingFixedOpponentsContinueMass
      (quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath))
      who 0 < 1) :
    quittingFiniteNashBellmanPathAggregateDebt reward (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath) <
      quittingFiniteNashBellmanPathAggregateDebt reward cutoff path := by
  unfold quittingFiniteNashBellmanPathAggregateDebt
  apply Finset.sum_lt_sum
  · intro player _
    exact quittingFiniteNashBellmanPathPlayerDebt_prepend_le
      reward cutoff path hpath player
  · refine ⟨who, Finset.mem_univ who, ?_⟩
    rw [quittingFiniteNashBellmanPathPlayerDebt_prepend_eq]
    have hpositive := mul_pos (sub_pos.mpr hcontract) hdebt
    nlinarith

/-- **Minimum-debt monotonicity.**  Increasing the cutoff by one cannot
increase the minimum aggregate surviving debt. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinDebt_succ_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinDebt reward (cutoff + 1) ≤
      quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem reward cutoff
  exact (quittingFiniteZeroBoundaryNashBellmanMinDebt_le reward (cutoff + 1)
      (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath)
      (quittingFiniteNashBellmanPathPrepend_mem
        reward cutoff path hpath)).trans
    (quittingFiniteNashBellmanPathAggregateDebt_prepend_le
      reward cutoff path hpath)

/-- If the predecessor of a minimizing chain contracts one positive-debt
player's opponent clock, minimum debt drops strictly at the next cutoff. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinDebt_succ_lt_of_player
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (who : ι)
    (hdebt : 0 < quittingFiniteNashBellmanPathPlayerDebt reward cutoff
      (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff) who)
    (hcontract : quittingFixedOpponentsContinueMass
      (quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff
          (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)
          (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem
            reward cutoff))) who 0 < 1) :
    quittingFiniteZeroBoundaryNashBellmanMinDebt reward (cutoff + 1) <
      quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff
  let hpath :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem reward cutoff
  calc
    quittingFiniteZeroBoundaryNashBellmanMinDebt reward (cutoff + 1) ≤
        quittingFiniteNashBellmanPathAggregateDebt reward (cutoff + 1)
          (quittingFiniteNashBellmanPathPrepend reward cutoff path hpath) :=
      quittingFiniteZeroBoundaryNashBellmanMinDebt_le reward (cutoff + 1) _
        (quittingFiniteNashBellmanPathPrepend_mem
          reward cutoff path hpath)
    _ < quittingFiniteNashBellmanPathAggregateDebt reward cutoff path :=
      quittingFiniteNashBellmanPathAggregateDebt_prepend_lt_of_player
        reward cutoff path hpath who hdebt hcontract
    _ = quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff := rfl

/-- Plateau rigidity: if two successive attained minimum debts agree, the
prepended predecessor has opponent Continue mass one for every player whose
old minimizing-chain debt is positive. -/
theorem quittingFixedOpponentsContinueMass_prepend_eq_one_of_minDebt_plateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ)
    (hplateau :
      quittingFiniteZeroBoundaryNashBellmanMinDebt reward (cutoff + 1) =
        quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff)
    (who : ι)
    (hdebt : 0 < quittingFiniteNashBellmanPathPlayerDebt reward cutoff
      (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff) who) :
    quittingFixedOpponentsContinueMass
      (quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff
          (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)
          (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem
            reward cutoff))) who 0 = 1 := by
  have hmassLe : quittingFixedOpponentsContinueMass
      (quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrepend reward cutoff
          (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)
          (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem
            reward cutoff))) who 0 ≤ 1 :=
    quittingStationaryContinueMass_le_one _
  rcases hmassLe.eq_or_lt with heq | hlt
  · exact heq
  · have hstrict :=
      quittingFiniteZeroBoundaryNashBellmanMinDebt_succ_lt_of_player
        reward cutoff who hdebt hlt
    rw [hplateau] at hstrict
    exact (lt_irrefl _ hstrict).elim

/-- On a minimum-debt plateau, every opponent of a positive-debt player has
zero Quit probability at the prepended predecessor root.  Thus any residual
activity there is confined to the debt owner itself. -/
theorem quittingProbability_prepend_eq_zero_of_minDebt_plateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ)
    (hplateau :
      quittingFiniteZeroBoundaryNashBellmanMinDebt reward (cutoff + 1) =
        quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff)
    (owner : ι)
    (hdebt : 0 < quittingFiniteNashBellmanPathPlayerDebt reward cutoff
      (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff) owner)
    (other : ι) (hne : other ≠ owner) :
    ((quittingFiniteNashBellmanPathRoots (cutoff + 1)
      (quittingFiniteNashBellmanPathPrepend reward cutoff
        (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)
        (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem reward cutoff)))
      0 other true).toReal = 0 := by
  let root := (quittingFiniteNashBellmanPathRoots (cutoff + 1)
    (quittingFiniteNashBellmanPathPrepend reward cutoff
      (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)
      (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem reward cutoff))) 0
  have hmass :=
    quittingFixedOpponentsContinueMass_prepend_eq_one_of_minDebt_plateau
      reward cutoff hplateau owner hdebt
  change quittingStationaryContinueMass
      (Function.update root owner (PMF.pure false)) = 1 at hmass
  exact quittingProbability_eq_zero_of_fixedOpponentsContinueMass_eq_one
    root owner other hne hmass

/-- Minimum aggregate debt is antitone over all cutoffs. -/
theorem antitone_quittingFiniteZeroBoundaryNashBellmanMinDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Antitone (quittingFiniteZeroBoundaryNashBellmanMinDebt reward) := by
  apply antitone_nat_of_succ_le
  exact quittingFiniteZeroBoundaryNashBellmanMinDebt_succ_le reward

/-- The decreasing minimum debts converge to their infimum over cutoffs. -/
theorem tendsto_quittingFiniteZeroBoundaryNashBellmanMinDebt_iInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Filter.Tendsto
      (quittingFiniteZeroBoundaryNashBellmanMinDebt reward)
      Filter.atTop
      (nhds (⨅ cutoff : ℕ,
        quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff)) := by
  apply tendsto_atTop_ciInf
    (antitone_quittingFiniteZeroBoundaryNashBellmanMinDebt reward)
  refine ⟨0, ?_⟩
  rintro debt ⟨cutoff, rfl⟩
  exact quittingFiniteZeroBoundaryNashBellmanMinDebt_nonneg reward cutoff

/-- The all-cutoff infimum criterion is exactly convergence of the attained
minimum debts to zero. -/
theorem iInf_quittingFiniteZeroBoundaryNashBellmanMinDebt_eq_zero_iff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (⨅ cutoff : ℕ,
        quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff) = 0 ↔
      Filter.Tendsto
        (quittingFiniteZeroBoundaryNashBellmanMinDebt reward)
        Filter.atTop (nhds 0) := by
  constructor
  · intro hinf
    simpa [hinf] using
      tendsto_quittingFiniteZeroBoundaryNashBellmanMinDebt_iInf reward
  · intro hzero
    exact tendsto_nhds_unique
      (tendsto_quittingFiniteZeroBoundaryNashBellmanMinDebt_iInf reward)
      hzero

/-- Limit-zero form of the minimum-debt uniform-existence criterion. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_tendsto_finiteMinDebt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzero : Filter.Tendsto
      (quittingFiniteZeroBoundaryNashBellmanMinDebt reward)
      Filter.atTop (nhds 0)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_iInf_finiteMinDebt_eq_zero
  exact
    (iInf_quittingFiniteZeroBoundaryNashBellmanMinDebt_eq_zero_iff_tendsto
      reward).2 hzero

end GameTheory
