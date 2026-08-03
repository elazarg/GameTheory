/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteChainTerminalCompiler
import GameTheory.Concepts.Stochastic.QuittingNashBellmanSpine

/-!
# Zero-boundary finite Nash--Bellman chains

This file supplies the finite-chain producer missing from the terminal
compiler.  For a fixed cutoff, start at the literal zero-payoff,
all-Continue state and repeatedly choose a predecessor in the compact exact
Nash--Bellman correspondence.  The resulting path is an exact finite
Nash--Bellman chain, equals zero at the boundary, and is extended by
all-Continue afterward.

The construction records its zero-boundary provenance explicitly.  It does
not use the arbitrary center of the compact serial system.  Its predecessor
is still fixed by classical choice, so vanishing of the resulting debt is a
sufficient scalar target for this selection, not a necessary condition over
all possible anchored selections.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Canonically bounded exact Nash--Bellman predecessor system. -/
def canonicalQuittingNashBellmanSerialRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    CompactSerialRelation (QuittingNashBellmanPoint ι) :=
  quittingNashBellmanSerialRelation reward (quittingRewardBound reward)
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)

/-- Simplex presentation of the all-Continue root. -/
def quittingAllContinueSimplexRoot : QuittingRootSimplex ι :=
  fun _ => stdSimplexEquiv (PMF.pure false)

omit [DecidableEq ι] in
/- The simplex all-Continue root converts back to the PMF all-Continue
root. -/
theorem quittingRootOfSimplex_allContinueSimplexRoot :
    quittingRootOfSimplex (quittingAllContinueSimplexRoot (ι := ι)) =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (PMF.pure false)

/-- Literal zero-payoff/all-Continue terminal anchor in the canonical compact
box. -/
def quittingZeroBoundaryAnchor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (canonicalQuittingNashBellmanSerialRelation reward).box := by
  refine ⟨((0 : Payoff ι), quittingAllContinueSimplexRoot), ?_⟩
  change (0 : Payoff ι) ∈ Set.Icc
    (fun _ => -quittingRewardBound reward)
    (fun _ => quittingRewardBound reward)
  constructor
  · intro who
    dsimp
    linarith [quittingRewardBound_nonneg reward]
  · intro who
    dsimp
    exact quittingRewardBound_nonneg reward

/-- The cutoff-indexed state path obtained by iterating chosen predecessors
backward from the zero anchor; from the cutoff onward it stays at the
anchor. -/
def quittingFiniteNashBellmanState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) : QuittingNashBellmanPoint ι :=
  if time ≤ cutoff then
    compactSerialIteratedPredecessor
      (canonicalQuittingNashBellmanSerialRelation reward)
      (cutoff - time) (quittingZeroBoundaryAnchor reward)
  else
    quittingZeroBoundaryAnchor reward

/-- Every finite-factory state remains in the canonical compact box. -/
theorem quittingFiniteNashBellmanState_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) :
    quittingFiniteNashBellmanState reward cutoff time ∈
      quittingNashBellmanBox (quittingRewardBound reward) := by
  classical
  unfold quittingFiniteNashBellmanState
  split_ifs
  · exact (compactSerialIteratedPredecessor
      (canonicalQuittingNashBellmanSerialRelation reward) _
      (quittingZeroBoundaryAnchor reward)).property
  · exact (quittingZeroBoundaryAnchor reward).property

/-- At and after the cutoff, the finite-factory state is literally the zero
anchor. -/
theorem quittingFiniteNashBellmanState_eq_anchor_of_cutoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingFiniteNashBellmanState reward cutoff time =
      quittingZeroBoundaryAnchor reward := by
  classical
  by_cases hreverse : time ≤ cutoff
  · have heq : time = cutoff := le_antisymm hreverse htime
    subst time
    simp [quittingFiniteNashBellmanState]
  · simp [quittingFiniteNashBellmanState, hreverse]

/-- Before the cutoff, adjacent factory states satisfy the exact
Nash--Bellman relation. -/
theorem quittingFiniteNashBellmanState_related
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (htime : time < cutoff) :
    IsQuittingNashBellmanEdge reward
      (quittingFiniteNashBellmanState reward cutoff time)
      (quittingFiniteNashBellmanState reward cutoff (time + 1)) := by
  classical
  have htime0 : time ≤ cutoff := htime.le
  have htime1 : time + 1 ≤ cutoff := by omega
  unfold quittingFiniteNashBellmanState
  rw [if_pos htime0, if_pos htime1]
  have hsub : cutoff - time = (cutoff - (time + 1)) + 1 := by omega
  rw [hsub, compactSerialIteratedPredecessor_succ]
  exact (canonicalQuittingNashBellmanSerialRelation reward).predecessor_related _

/-- Payoff path projected from the anchored finite-state path. -/
def quittingFiniteNashBellmanValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) : Payoff ι :=
  (quittingFiniteNashBellmanState reward cutoff time).1

/-- Root path projected from the anchored finite-state path. -/
def quittingFiniteNashBellmanRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) : ι → PMF Bool :=
  quittingRootOfSimplex
    (quittingFiniteNashBellmanState reward cutoff time).2

/-- Factory values vanish at and after the cutoff. -/
theorem quittingFiniteNashBellmanValue_eq_zero_of_cutoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingFiniteNashBellmanValue reward cutoff time = 0 := by
  rw [quittingFiniteNashBellmanValue,
    quittingFiniteNashBellmanState_eq_anchor_of_cutoff_le reward cutoff time
      htime]
  rfl

/-- Factory roots are all-Continue at and after the cutoff. -/
theorem quittingFiniteNashBellmanRoots_eq_allContinue_of_cutoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingFiniteNashBellmanRoots reward cutoff time =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  rw [quittingFiniteNashBellmanRoots,
    quittingFiniteNashBellmanState_eq_anchor_of_cutoff_le reward cutoff time
      htime]
  exact quittingRootOfSimplex_allContinueSimplexRoot

/-- The projected finite factory obeys exact Bellman evaluation before its
cutoff. -/
theorem quittingFiniteNashBellmanValue_eq_successor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanValue reward cutoff time =
      quittingRootSuccessorPayoff reward
        (quittingFiniteNashBellmanValue reward cutoff (time + 1))
        (quittingFiniteNashBellmanRoots reward cutoff time) :=
  (quittingFiniteNashBellmanState_related reward cutoff time htime).1

/-- Every pre-cutoff factory root is exact Nash against its next value. -/
theorem quittingFiniteNashBellmanRoots_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (htime : time < cutoff) :
    IsεQuittingRootNash reward
      (quittingFiniteNashBellmanValue reward cutoff (time + 1)) 0
      (quittingFiniteNashBellmanRoots reward cutoff time) := by
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (quittingFiniteNashBellmanValue reward cutoff (time + 1))
      (quittingFiniteNashBellmanRoots reward cutoff time)).1
    (quittingFiniteNashBellmanState_related reward cutoff time htime).2

/-- Every projected factory value stays in the canonical reward cube. -/
theorem abs_quittingFiniteNashBellmanValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (who : ι) :
    |quittingFiniteNashBellmanValue reward cutoff time who| ≤
      quittingRewardBound reward := by
  have hmem := quittingFiniteNashBellmanState_mem reward cutoff time
  exact abs_le.mpr ⟨hmem.1 who, hmem.2 who⟩

/-- **Finite zero-boundary Nash--Bellman factory.**  Every cutoff admits an
exact bounded finite chain in precisely the interface consumed by the finite
terminal compiler. -/
theorem exists_finiteZeroBoundaryExactQuittingNashBellmanChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    ∃ (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι),
      (∀ time, cutoff ≤ time →
        roots time = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      value cutoff = 0 ∧
      (∀ time, time < cutoff →
        value time = quittingRootSuccessorPayoff reward
          (value (time + 1)) (roots time)) ∧
      (∀ time, time < cutoff →
        IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) ∧
      ∀ time who, |value time who| ≤ quittingRewardBound reward := by
  exact ⟨quittingFiniteNashBellmanRoots reward cutoff,
    quittingFiniteNashBellmanValue reward cutoff,
    quittingFiniteNashBellmanRoots_eq_allContinue_of_cutoff_le reward cutoff,
    quittingFiniteNashBellmanValue_eq_zero_of_cutoff_le reward cutoff cutoff
      le_rfl,
    quittingFiniteNashBellmanValue_eq_successor reward cutoff,
    quittingFiniteNashBellmanRoots_isZeroNash reward cutoff,
    abs_quittingFiniteNashBellmanValue_le reward cutoff⟩

/-! ## Immediate finite compiler output -/

/-- Canonical aggregate of the surviving playerwise singleton debts at a
factory cutoff. -/
def quittingFiniteNashBellmanDebtBudget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : ℝ :=
  ∑ who,
    quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanRoots reward cutoff) who 0 cutoff *
      max 0 (reward (quittingSingletonTerminal who) who)

/-- Every playerwise surviving debt is bounded by the aggregate factory
budget. -/
theorem quittingFiniteNashBellman_survivingDebt_le_budget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (who : ι) :
    quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanRoots reward cutoff) who 0 cutoff *
        max 0 (reward (quittingSingletonTerminal who) who) ≤
      quittingFiniteNashBellmanDebtBudget reward cutoff := by
  unfold quittingFiniteNashBellmanDebtBudget
  exact Finset.single_le_sum
    (fun player _ => mul_nonneg
      (quittingOpponentSurvivalWeight_nonneg
        (quittingFiniteNashBellmanRoots reward cutoff) player 0 cutoff)
      (le_max_left 0 (reward (quittingSingletonTerminal player) player)))
    (Finset.mem_univ who)

/-- The produced all-Continue extension delivers its declared initial value
exactly. -/
theorem quittingTerminalPayoff_finiteNashBellmanFactory
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingTerminalPayoff reward
        (quittingInfinitePathProfile reward
          (quittingFiniteNashBellmanRoots reward cutoff)) =
      quittingFiniteNashBellmanValue reward cutoff 0 := by
  exact quittingTerminalPayoff_finiteExactChainProfile reward
    (quittingFiniteNashBellmanRoots reward cutoff)
    (quittingFiniteNashBellmanValue reward cutoff) cutoff
    (quittingFiniteNashBellmanRoots_eq_allContinue_of_cutoff_le reward cutoff)
    (quittingFiniteNashBellmanValue_eq_zero_of_cutoff_le reward cutoff cutoff
      le_rfl)
    (quittingFiniteNashBellmanValue_eq_successor reward cutoff)

/-- **Unconditional finite approximation scheme.**  At every cutoff, the
factory profile is a terminal approximate Nash equilibrium with error equal
to the aggregate surviving positive-singleton debt.  Making this particular
chosen budget vanish is sufficient for uniform existence; failure need not
rule out another Nash predecessor selection. -/
theorem finiteNashBellmanFactoryProfile_isεAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (quittingFiniteNashBellmanDebtBudget reward cutoff)
      (quittingInfinitePathProfile reward
        (quittingFiniteNashBellmanRoots reward cutoff)) := by
  exact finiteExactChainProfile_isεAsymptoticNash reward
    (quittingFiniteNashBellmanRoots reward cutoff)
    (quittingFiniteNashBellmanValue reward cutoff) cutoff
    (quittingFiniteNashBellmanDebtBudget reward cutoff)
    (quittingFiniteNashBellmanRoots_eq_allContinue_of_cutoff_le reward cutoff)
    (quittingFiniteNashBellmanValue_eq_zero_of_cutoff_le reward cutoff cutoff
      le_rfl)
    (quittingFiniteNashBellmanValue_eq_successor reward cutoff)
    (quittingFiniteNashBellmanRoots_isZeroNash reward cutoff)
    (quittingFiniteNashBellman_survivingDebt_le_budget reward cutoff)

/-- Vanishing of the explicit debt budgets of the fixed anchored factory is
a sufficient one-scalar condition for a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finiteNashBellmanDebtBudget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hbudget : ∀ ε : ℝ, 0 < ε →
      ∃ cutoff,
        quittingFiniteNashBellmanDebtBudget reward cutoff ≤ ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteExactChains
    reward
  intro ε hε
  obtain ⟨cutoff, hcutoff⟩ := hbudget ε hε
  refine ⟨quittingFiniteNashBellmanRoots reward cutoff,
    quittingFiniteNashBellmanValue reward cutoff, cutoff,
    quittingFiniteNashBellmanRoots_eq_allContinue_of_cutoff_le reward cutoff,
    quittingFiniteNashBellmanValue_eq_zero_of_cutoff_le reward cutoff cutoff
      le_rfl,
    quittingFiniteNashBellmanValue_eq_successor reward cutoff,
    quittingFiniteNashBellmanRoots_isZeroNash reward cutoff, fun who => ?_⟩
  exact (quittingFiniteNashBellman_survivingDebt_le_budget
    reward cutoff who).trans hcutoff

end GameTheory
