/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteNashBellmanFactory

/-!
# Minimum-debt finite Nash--Bellman chains

For a fixed cutoff `K`, this file considers the full compact space of exact
Nash--Bellman state paths indexed by `Fin (K + 1)` whose terminal payoff is
zero.  The terminal simplex coordinate is deliberately unconstrained: it is
not used by any of the preceding edges.

Opponent survival, and hence every player's surviving positive-singleton
debt, is a finite polynomial in the pre-terminal simplex coordinates.  It is
therefore continuous.  The aggregate debt consequently attains a minimum on
the nonempty compact chain space.  This removes the arbitrary predecessor
selection from the fixed-cutoff optimization problem.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite Nash--Bellman state path with `cutoff + 1` displayed states. -/
abbrev QuittingFiniteNashBellmanPath (ι : Type) [Fintype ι]
    (cutoff : ℕ) :=
  Fin (cutoff + 1) → QuittingNashBellmanPoint ι

/-- All canonically bounded exact Nash--Bellman chains with zero terminal
payoff.  The terminal root is irrelevant and remains free. -/
def quittingFiniteZeroBoundaryNashBellmanChainSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : Set (QuittingFiniteNashBellmanPath ι cutoff) :=
  {path |
    (∀ time, path time ∈
      quittingNashBellmanBox (quittingRewardBound reward)) ∧
    (path (Fin.last cutoff)).1 = 0 ∧
    ∀ time : Fin cutoff,
      IsQuittingNashBellmanEdge reward
        (path (Fin.castSucc time)) (path (Fin.succ time))}

/-- The chosen-predecessor factory witnesses nonemptiness of the full
fixed-cutoff chain space. -/
theorem quittingFiniteZeroBoundaryNashBellmanChainSet_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    (quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff).Nonempty := by
  classical
  refine ⟨fun time =>
    quittingFiniteNashBellmanState reward cutoff time, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro time
    exact quittingFiniteNashBellmanState_mem reward cutoff time
  · simpa [quittingFiniteNashBellmanValue] using
      quittingFiniteNashBellmanValue_eq_zero_of_cutoff_le
        reward cutoff cutoff le_rfl
  · intro time
    simpa using
      quittingFiniteNashBellmanState_related reward cutoff time time.isLt

/-- The space of all zero-boundary exact chains at a fixed cutoff is closed. -/
theorem quittingFiniteZeroBoundaryNashBellmanChainSet_isClosed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    IsClosed (quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) := by
  let ambient : Set (QuittingFiniteNashBellmanPath ι cutoff) :=
    {path | ∀ time, path time ∈
      quittingNashBellmanBox (quittingRewardBound reward)}
  let terminal : Set (QuittingFiniteNashBellmanPath ι cutoff) :=
    {path | (path (Fin.last cutoff)).1 = 0}
  let edgeGraph : Set
      (QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι) :=
    {edge |
      edge.1 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
      edge.2 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
      IsQuittingNashBellmanEdge reward edge.1 edge.2}
  have hambientCompact : IsCompact ambient := by
    dsimp only [ambient]
    exact isCompact_pi_infinite fun _ =>
      quittingNashBellmanBox_isCompact (ι := ι)
        (quittingRewardBound reward)
  have hambientClosed : IsClosed ambient := hambientCompact.isClosed
  have hterminalClosed : IsClosed terminal := by
    dsimp only [terminal]
    exact isClosed_eq
      (continuous_fst.comp (continuous_apply (Fin.last cutoff)))
      continuous_const
  have hedgeGraphClosed : IsClosed edgeGraph := by
    simpa only [edgeGraph] using
      isClosed_quittingNashBellmanEdgeGraph reward
        (quittingRewardBound reward)
  have hedgeClosed : ∀ time : Fin cutoff,
      IsClosed {path : QuittingFiniteNashBellmanPath ι cutoff |
        (path (Fin.castSucc time), path (Fin.succ time)) ∈ edgeGraph} := by
    intro time
    have hpair : Continuous
        (fun path : QuittingFiniteNashBellmanPath ι cutoff =>
          (path (Fin.castSucc time), path (Fin.succ time))) :=
      (continuous_apply (Fin.castSucc time)).prodMk
        (continuous_apply (Fin.succ time))
    exact hedgeGraphClosed.preimage hpair
  have hclosed : IsClosed
      (ambient ∩ terminal ∩ ⋂ time : Fin cutoff,
        {path : QuittingFiniteNashBellmanPath ι cutoff |
          (path (Fin.castSucc time), path (Fin.succ time)) ∈ edgeGraph}) :=
    (hambientClosed.inter hterminalClosed).inter
      (isClosed_iInter hedgeClosed)
  have heq : quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff =
      ambient ∩ terminal ∩ ⋂ time : Fin cutoff,
        {path : QuittingFiniteNashBellmanPath ι cutoff |
          (path (Fin.castSucc time), path (Fin.succ time)) ∈ edgeGraph} := by
    ext path
    simp only [quittingFiniteZeroBoundaryNashBellmanChainSet, ambient,
      terminal, edgeGraph, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    constructor
    · intro hpath
      refine ⟨⟨hpath.1, hpath.2.1⟩, fun time => ?_⟩
      exact ⟨hpath.1 (Fin.castSucc time),
        hpath.1 (Fin.succ time), hpath.2.2 time⟩
    · intro hpath
      exact ⟨hpath.1.1, hpath.1.2,
        fun time => (hpath.2 time).2.2⟩
  rw [heq]
  exact hclosed

/-- The space of all zero-boundary exact chains at a fixed cutoff is compact. -/
theorem quittingFiniteZeroBoundaryNashBellmanChainSet_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    IsCompact (quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) := by
  have hambient : IsCompact
      {path : QuittingFiniteNashBellmanPath ι cutoff |
        ∀ time, path time ∈
          quittingNashBellmanBox (quittingRewardBound reward)} :=
    isCompact_pi_infinite fun _ =>
      quittingNashBellmanBox_isCompact (ι := ι)
        (quittingRewardBound reward)
  exact hambient.of_isClosed_subset
    (quittingFiniteZeroBoundaryNashBellmanChainSet_isClosed reward cutoff)
    (fun _ hpath => hpath.1)

/-! ## Continuous surviving-debt objective -/

/-- Extend the pre-terminal roots of a finite state path by all-Continue.
The terminal root coordinate is intentionally ignored. -/
def quittingFiniteNashBellmanPathRoots
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) : ι → PMF Bool :=
  if htime : time < cutoff then
    quittingRootOfSimplex
      (path ⟨time, Nat.lt_succ_of_lt htime⟩).2
  else
    quittingAllContinueRoot

/-- Extend a finite path's displayed values by zero after the terminal
state. -/
def quittingFiniteNashBellmanPathValue
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) : Payoff ι :=
  if htime : time < cutoff + 1 then
    (path ⟨time, htime⟩).1
  else
    0

omit [DecidableEq ι] in
/-- Before the cutoff, the operational root extension reads the path's own
simplex coordinate.  Purely definitional -- no admissibility hypothesis is
needed -- so it serves every chain family alike, not only the zero
boundary. -/
theorem quittingFiniteNashBellmanPathRoots_of_lt
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathRoots cutoff path time =
      quittingRootOfSimplex (path ⟨time, Nat.lt_succ_of_lt htime⟩).2 :=
  dif_pos htime

omit [DecidableEq ι] in
/-- Before the cutoff, the padded displayed value reads the path's own
value.  Purely definitional, for the same reason as
`quittingFiniteNashBellmanPathRoots_of_lt`. -/
theorem quittingFiniteNashBellmanPathValue_of_lt
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path time =
      (path ⟨time, Nat.lt_succ_of_lt htime⟩).1 :=
  dif_pos (Nat.lt_succ_of_lt htime)

omit [DecidableEq ι] in
/-- The operational root extension is all-Continue from the cutoff onward. -/
theorem quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) (htime : cutoff ≤ time) :
    quittingFiniteNashBellmanPathRoots cutoff path time =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  simp [quittingFiniteNashBellmanPathRoots, not_lt.mpr htime]

omit [DecidableEq ι] in
/-- The displayed value at the cutoff is the path's own terminal payoff,
whatever it is.  This is the mechanism underlying
`quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff`: the proof never
inspects the path's terminal value, so it holds for any chain family, not
only the zero boundary. -/
theorem quittingFiniteNashBellmanPathValue_eq_last
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path cutoff =
      (path (Fin.last cutoff)).1 := by
  rw [quittingFiniteNashBellmanPathValue, dif_pos (Nat.lt_succ_self cutoff)]
  rfl

omit [DecidableEq ι] in
/-- Beyond the cutoff, the padded displayed value is unconditionally zero.
Purely definitional: the padding is the literal `0` written into
`quittingFiniteNashBellmanPathValue`, regardless of which chain set (if any)
`path` belongs to. -/
theorem quittingFiniteNashBellmanPathValue_eq_zero_of_cutoff_lt
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) (htime : cutoff < time) :
    quittingFiniteNashBellmanPathValue cutoff path time = 0 := by
  unfold quittingFiniteNashBellmanPathValue
  rw [dif_neg]
  omega

/-- An admissible finite path has zero terminal value.  Specializes
`quittingFiniteNashBellmanPathValue_eq_last` via the zero-boundary chain
set's terminal clause. -/
theorem quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path cutoff = 0 := by
  rw [quittingFiniteNashBellmanPathValue_eq_last]
  exact hpath.2.1

/-- The value projection of a path obeys its exact Bellman equation before
the cutoff, given only the per-stage edge condition.  This is the mechanism
underlying `quittingFiniteNashBellmanPathValue_eq_successor`: the proof
never inspects the path's terminal value, so it holds for any anchor, not
only the zero boundary. -/
theorem quittingFiniteNashBellmanPathValue_eq_successor_of_edges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hedges : ∀ stage : Fin cutoff, IsQuittingNashBellmanEdge reward
      (path (Fin.castSucc stage)) (path (Fin.succ stage)))
    (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path time =
      quittingRootSuccessorPayoff reward
        (quittingFiniteNashBellmanPathValue cutoff path (time + 1))
        (quittingFiniteNashBellmanPathRoots cutoff path time) := by
  have htime0 : time < cutoff + 1 :=
    lt_trans htime (Nat.lt_succ_self cutoff)
  have htime1 : time + 1 < cutoff + 1 := Nat.succ_lt_succ htime
  simpa [quittingFiniteNashBellmanPathValue,
    quittingFiniteNashBellmanPathRoots, htime, htime0, htime1] using
    (hedges ⟨time, htime⟩).1

/-- The value projection of an admissible path obeys its exact Bellman
equation before the cutoff.  Specializes
`quittingFiniteNashBellmanPathValue_eq_successor_of_edges` to the
zero-boundary chain set's edge clause. -/
theorem quittingFiniteNashBellmanPathValue_eq_successor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path time =
      quittingRootSuccessorPayoff reward
        (quittingFiniteNashBellmanPathValue cutoff path (time + 1))
        (quittingFiniteNashBellmanPathRoots cutoff path time) :=
  quittingFiniteNashBellmanPathValue_eq_successor_of_edges reward cutoff path
    hpath.2.2 time htime

/-- Every pre-terminal root along an edge-satisfying path is exact Nash
against its displayed successor value, given only the per-stage edge
condition.  This is the mechanism underlying
`quittingFiniteNashBellmanPathRoots_isZeroNash`; it holds for any anchor. -/
theorem quittingFiniteNashBellmanPathRoots_isZeroNash_of_edges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hedges : ∀ stage : Fin cutoff, IsQuittingNashBellmanEdge reward
      (path (Fin.castSucc stage)) (path (Fin.succ stage)))
    (time : ℕ) (htime : time < cutoff) :
    IsεQuittingRootNash reward
      (quittingFiniteNashBellmanPathValue cutoff path (time + 1)) 0
      (quittingFiniteNashBellmanPathRoots cutoff path time) := by
  have htime1 : time + 1 < cutoff + 1 := Nat.succ_lt_succ htime
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward
      (quittingFiniteNashBellmanPathValue cutoff path (time + 1))
      (quittingFiniteNashBellmanPathRoots cutoff path time)).1
  simpa [quittingFiniteNashBellmanPathValue,
    quittingFiniteNashBellmanPathRoots, htime, htime1] using
    (hedges ⟨time, htime⟩).2

/-- Every pre-terminal root of an admissible path is exact Nash against its
displayed successor value.  Specializes
`quittingFiniteNashBellmanPathRoots_isZeroNash_of_edges` to the
zero-boundary chain set's edge clause. -/
theorem quittingFiniteNashBellmanPathRoots_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : time < cutoff) :
    IsεQuittingRootNash reward
      (quittingFiniteNashBellmanPathValue cutoff path (time + 1)) 0
      (quittingFiniteNashBellmanPathRoots cutoff path time) :=
  quittingFiniteNashBellmanPathRoots_isZeroNash_of_edges reward cutoff path
    hpath.2.2 time htime

/-- One pre-terminal stage's probability that every opponent of `who`
continues, written directly in simplex coordinates.  It is set to one away
from the displayed pre-terminal range. -/
def quittingFiniteNashBellmanPathOpponentContinueMass
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) (time : ℕ) : ℝ :=
  if htime : time < cutoff then
    ∏ player ∈ Finset.univ.erase who,
      (path ⟨time, Nat.lt_succ_of_lt htime⟩).2 player false
  else
    1

/-- Product of the opponent-continuation masses before the cutoff. -/
def quittingFiniteNashBellmanPathOpponentSurvival
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) : ℝ :=
  ∏ time ∈ Finset.range cutoff,
    quittingFiniteNashBellmanPathOpponentContinueMass cutoff path who time

/-- Playerwise surviving positive-singleton debt of a finite chain. -/
def quittingFiniteNashBellmanPathPlayerDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) : ℝ :=
  quittingFiniteNashBellmanPathOpponentSurvival cutoff path who *
    max 0 (reward (quittingSingletonTerminal who) who)

/-- Aggregate surviving positive-singleton debt of a finite chain. -/
def quittingFiniteNashBellmanPathAggregateDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) : ℝ :=
  ∑ who, quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who

/-- Forcing `who` to Continue leaves the product of the other simplex
Continue coordinates. -/
theorem quittingFixedOpponentsContinueMass_quittingRootOfSimplex
    (root : QuittingRootSimplex ι) (who : ι) :
    quittingStationaryContinueMass
        (Function.update (quittingRootOfSimplex root) who (PMF.pure false)) =
      ∏ player ∈ Finset.univ.erase who, root player false := by
  classical
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  have hupdate :
      (fun player =>
        ((Function.update (quittingRootOfSimplex root) who
          (PMF.pure false) player) false).toReal) =
        Function.update
          (fun player => ((quittingRootOfSimplex root player) false).toReal)
          who 1 := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Function.update_of_ne hplayer]
  change (∏ player,
    ((Function.update (quittingRootOfSimplex root) who
      (PMF.pure false) player) false).toReal) = _
  rw [hupdate, Finset.prod_update_of_mem (Finset.mem_univ who)]
  rw [one_mul, Finset.sdiff_singleton_eq_erase]
  apply Finset.prod_congr rfl
  intro player _
  exact quittingRootOfSimplex_apply_toReal root player false

/-- The simplex-coordinate opponent factor agrees with the operational
fixed-opponent Continue mass at every pre-terminal time. -/
theorem quittingFixedOpponentsContinueMass_pathRoots_eq
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) (time : ℕ) (htime : time < cutoff) :
    quittingFixedOpponentsContinueMass
        (quittingFiniteNashBellmanPathRoots cutoff path) who time =
      quittingFiniteNashBellmanPathOpponentContinueMass
        cutoff path who time := by
  rw [quittingFixedOpponentsContinueMass]
  simp only [quittingFiniteNashBellmanPathRoots,
    quittingFiniteNashBellmanPathOpponentContinueMass, dif_pos htime]
  exact quittingFixedOpponentsContinueMass_quittingRootOfSimplex _ who

/-- The polynomial survival objective is exactly the survival weight used by
the terminal-chain compiler. -/
theorem quittingOpponentSurvivalWeight_pathRoots_eq
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) :
    quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots cutoff path) who 0 cutoff =
      quittingFiniteNashBellmanPathOpponentSurvival cutoff path who := by
  unfold quittingOpponentSurvivalWeight
    quittingFiniteNashBellmanPathOpponentSurvival
  apply Finset.prod_congr rfl
  intro time htime
  simpa only [Nat.zero_add] using
    quittingFixedOpponentsContinueMass_pathRoots_eq
      cutoff path who time (Finset.mem_range.mp htime)

/-- Each playerwise polynomial component is exactly the compiler's surviving
positive-singleton debt. -/
theorem quittingFiniteNashBellmanPathPlayerDebt_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who =
      quittingOpponentSurvivalWeight
          (quittingFiniteNashBellmanPathRoots cutoff path) who 0 cutoff *
        max 0 (reward (quittingSingletonTerminal who) who) := by
  rw [quittingFiniteNashBellmanPathPlayerDebt,
    quittingOpponentSurvivalWeight_pathRoots_eq]

/-- A pre-terminal opponent-continuation factor is continuous in the full
finite path. -/
theorem continuous_quittingFiniteNashBellmanPathOpponentContinueMass
    (cutoff : ℕ) (who : ι) (time : ℕ) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff =>
      quittingFiniteNashBellmanPathOpponentContinueMass
        cutoff path who time) := by
  classical
  unfold quittingFiniteNashBellmanPathOpponentContinueMass
  split_ifs with htime
  · apply continuous_finsetProd
    intro player _
    exact (continuous_apply false).comp
      (continuous_subtype_val.comp
        ((continuous_apply player).comp
          (continuous_snd.comp
            (continuous_apply
              (⟨time, Nat.lt_succ_of_lt htime⟩ : Fin (cutoff + 1))))))
  · exact continuous_const

/-- Finite opponent survival is continuous in the chain. -/
theorem continuous_quittingFiniteNashBellmanPathOpponentSurvival
    (cutoff : ℕ) (who : ι) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff =>
      quittingFiniteNashBellmanPathOpponentSurvival cutoff path who) := by
  classical
  unfold quittingFiniteNashBellmanPathOpponentSurvival
  exact continuous_finsetProd (Finset.range cutoff) fun time _ =>
    continuous_quittingFiniteNashBellmanPathOpponentContinueMass
      cutoff who time

/-- Every playerwise debt component is continuous in the chain. -/
theorem continuous_quittingFiniteNashBellmanPathPlayerDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (who : ι) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff =>
      quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who) := by
  exact
    (continuous_quittingFiniteNashBellmanPathOpponentSurvival cutoff who).mul
      continuous_const

/-- Aggregate debt is a continuous finite sum. -/
theorem continuous_quittingFiniteNashBellmanPathAggregateDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff =>
      quittingFiniteNashBellmanPathAggregateDebt reward cutoff path) := by
  classical
  unfold quittingFiniteNashBellmanPathAggregateDebt
  exact continuous_finsetSum Finset.univ fun who _ =>
    continuous_quittingFiniteNashBellmanPathPlayerDebt reward cutoff who

/-- Every displayed opponent-continuation factor is nonnegative. -/
theorem quittingFiniteNashBellmanPathOpponentContinueMass_nonneg
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) (time : ℕ) :
    0 ≤ quittingFiniteNashBellmanPathOpponentContinueMass
      cutoff path who time := by
  classical
  unfold quittingFiniteNashBellmanPathOpponentContinueMass
  split_ifs
  · apply Finset.prod_nonneg
    intro player _
    exact (path _).2 player |>.property.1 false
  · exact zero_le_one

/-- Every playerwise surviving debt is nonnegative. -/
theorem quittingFiniteNashBellmanPathPlayerDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) :
    0 ≤ quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who := by
  unfold quittingFiniteNashBellmanPathPlayerDebt
    quittingFiniteNashBellmanPathOpponentSurvival
  exact mul_nonneg
    (Finset.prod_nonneg fun time _ =>
      quittingFiniteNashBellmanPathOpponentContinueMass_nonneg
        cutoff path who time)
    (le_max_left 0 (reward (quittingSingletonTerminal who) who))

/-- Aggregate debt is nonnegative. -/
theorem quittingFiniteNashBellmanPathAggregateDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) :
    0 ≤ quittingFiniteNashBellmanPathAggregateDebt reward cutoff path := by
  unfold quittingFiniteNashBellmanPathAggregateDebt
  exact Finset.sum_nonneg fun who _ =>
    quittingFiniteNashBellmanPathPlayerDebt_nonneg reward cutoff path who

/-- Each playerwise component is bounded by the aggregate debt. -/
theorem quittingFiniteNashBellmanPathPlayerDebt_le_aggregate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathPlayerDebt reward cutoff path who ≤
      quittingFiniteNashBellmanPathAggregateDebt reward cutoff path := by
  unfold quittingFiniteNashBellmanPathAggregateDebt
  exact Finset.single_le_sum
    (fun player _ =>
      quittingFiniteNashBellmanPathPlayerDebt_nonneg
        reward cutoff path player)
    (Finset.mem_univ who)

/-! ## Fixed-cutoff minimizer -/

/-- At each cutoff, aggregate surviving debt attains a minimum over all
zero-boundary exact Nash--Bellman chains. -/
theorem exists_quittingFiniteZeroBoundaryNashBellmanDebtMinimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    ∃ path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff,
      IsMinOn
        (quittingFiniteNashBellmanPathAggregateDebt reward cutoff)
        (quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) path := by
  exact
    (quittingFiniteZeroBoundaryNashBellmanChainSet_isCompact reward cutoff).exists_isMinOn
      (quittingFiniteZeroBoundaryNashBellmanChainSet_nonempty reward cutoff)
      (continuous_quittingFiniteNashBellmanPathAggregateDebt
        reward cutoff).continuousOn

/-- A debt-minimizing zero-boundary exact chain at a fixed cutoff. -/
def quittingFiniteZeroBoundaryNashBellmanDebtMinimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : QuittingFiniteNashBellmanPath ι cutoff :=
  Classical.choose
    (exists_quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)

/-- The minimum aggregate surviving debt at a fixed cutoff. -/
def quittingFiniteZeroBoundaryNashBellmanMinDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : ℝ :=
  quittingFiniteNashBellmanPathAggregateDebt reward cutoff
    (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)

/-- The selected minimizer is an admissible zero-boundary exact chain. -/
theorem quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
  (Classical.choose_spec
    (exists_quittingFiniteZeroBoundaryNashBellmanDebtMinimizer
      reward cutoff)).1

/-- The selected chain minimizes aggregate debt among every admissible chain
at the same cutoff. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinDebt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff ≤
      quittingFiniteNashBellmanPathAggregateDebt reward cutoff path := by
  exact (Classical.choose_spec
    (exists_quittingFiniteZeroBoundaryNashBellmanDebtMinimizer
      reward cutoff)).2 hpath

/-- Minimum aggregate debt is nonnegative. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    0 ≤ quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff :=
  quittingFiniteNashBellmanPathAggregateDebt_nonneg reward cutoff _

/-! ## Compiler interface and the all-cutoff criterion -/

/-- Every operational playerwise debt of the minimizing chain is at most its
minimum aggregate debt. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinimizer_survivingDebt_le_minDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (who : ι) :
    quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots cutoff
          (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff))
        who 0 cutoff *
        max 0 (reward (quittingSingletonTerminal who) who) ≤
      quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff := by
  rw [← quittingFiniteNashBellmanPathPlayerDebt_eq]
  exact quittingFiniteNashBellmanPathPlayerDebt_le_aggregate
    reward cutoff
      (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff) who

/-- A cutoff whose minimum debt is below `ε` supplies an exact finite chain
in the terminal compiler's operational root/value interface, with every
playerwise surviving debt below `ε`. -/
theorem exists_finiteZeroBoundaryExactQuittingNashBellmanChain_of_minDebt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (ε : ℝ)
    (hdebt : quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff ≤ ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι),
      (∀ time, cutoff ≤ time →
        roots time = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      value cutoff = 0 ∧
      (∀ time, time < cutoff →
        value time = quittingRootSuccessorPayoff reward
          (value (time + 1)) (roots time)) ∧
      (∀ time, time < cutoff →
        IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) ∧
      ∀ who,
        quittingOpponentSurvivalWeight roots who 0 cutoff *
          max 0 (reward (quittingSingletonTerminal who) who) ≤ ε := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem reward cutoff
  refine ⟨quittingFiniteNashBellmanPathRoots cutoff path,
    quittingFiniteNashBellmanPathValue cutoff path,
    quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
      cutoff path,
    quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
      reward cutoff path hpath,
    quittingFiniteNashBellmanPathValue_eq_successor
      reward cutoff path hpath,
    quittingFiniteNashBellmanPathRoots_isZeroNash
      reward cutoff path hpath, ?_⟩
  intro who
  exact (quittingFiniteZeroBoundaryNashBellmanMinimizer_survivingDebt_le_minDebt
    reward cutoff who).trans hdebt

/-- **Minimum-debt finite-chain criterion.**  If the infimum over cutoffs of
the attained minimum aggregate debts is zero, the quitting game has a
uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_iInf_finiteMinDebt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmin : (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff) = 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteExactChains
    reward
  intro ε hε
  have hinf : (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff) < ε := by
    rw [hmin]
    exact hε
  obtain ⟨cutoff, hcutoff⟩ := exists_lt_of_ciInf_lt hinf
  rcases
      exists_finiteZeroBoundaryExactQuittingNashBellmanChain_of_minDebt_le
        reward cutoff ε hcutoff.le with
    ⟨roots, value, htail, hterminal, hpolicy, hnash, hdebt⟩
  exact ⟨roots, value, cutoff, htail, hterminal, hpolicy, hnash, hdebt⟩

end GameTheory
