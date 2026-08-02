/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.SingleControllerNoTrap
import Math.Probability.ReachableClosedClass

/-!
# Rank-decreasing completion of a Vrieze controller policy

The first total-policy compiler in `SingleController.lean` chooses, at every
zero-occupation state, an action with a successor from which the positive
occupation support remains reachable.  Independent choices of that form can
cycle.  This file removes that gap by assigning every state its least support-
graph distance to the target set and selecting an action with a successor of
strictly smaller rank.

The resulting stationary policy agrees with normalized dual occupation on
the positive support.  Off that support it has a positive-probability edge of
strictly smaller rank, and consequently every initial state reaches the
positive support under the one fixed completed kernel.

This is still a support-reachability statement.  The conversion from this
finite-kernel fact to the exact mean-ergodic projection identity required by
`IsControllerProjectionWitness` remains separate.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

namespace FiniteReachability

variable {S : Type*} (Succ : S → S → Prop) (R : S → Prop)

/-- A path of exactly `steps` successor edges from `source` to the target
set `R`. -/
inductive CanReachSetIn : ℕ → S → Prop
  | target {state : S} : R state → CanReachSetIn 0 state
  | step {steps : ℕ} {source destination : S} :
      Succ source destination →
      CanReachSetIn steps destination →
      CanReachSetIn (steps + 1) source

/-- A bounded path gives ordinary reflexive--transitive reachability. -/
theorem canReachSet_of_canReachSetIn {steps : ℕ} {source : S}
    (path : CanReachSetIn Succ R steps source) :
    CanReachSet Succ R source := by
  induction path with
  | target htarget =>
      exact ⟨_, htarget, Relation.ReflTransGen.refl⟩
  | @step steps source destination hedge tail ih =>
      obtain ⟨target, htarget, hpath⟩ := ih
      exact ⟨target, htarget,
        Relation.ReflTransGen.head hedge hpath⟩

/-- Ordinary reachability has a path with some finite edge count. -/
theorem canReachSet_iff_exists_canReachSetIn {source : S} :
    CanReachSet Succ R source ↔
      ∃ steps, CanReachSetIn Succ R steps source := by
  constructor
  · rintro ⟨target, htarget, hpath⟩
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, CanReachSetIn.target htarget⟩
    | @head source destination hedge tail ih =>
        obtain ⟨steps, hsteps⟩ := ih
        exact ⟨steps + 1, CanReachSetIn.step hedge hsteps⟩
  · rintro ⟨steps, path⟩
    exact canReachSet_of_canReachSetIn Succ R path

/-- Least number of successor edges needed to reach `R`, with value zero on
unreachable states (the latter branch is never used by the completion
theorem). -/
noncomputable def reachRank
    (relation : S → S → Prop) (target : S → Prop)
    (source : S) : ℕ := by
  classical
  exact
    if hreach : CanReachSet relation target source then
      Nat.find
        ((canReachSet_iff_exists_canReachSetIn relation target).mp hreach)
    else 0

/-- The least-distance rank is witnessed by a path of exactly that length. -/
theorem canReachSetIn_reachRank {source : S}
    (hreach : CanReachSet Succ R source) :
    CanReachSetIn Succ R (reachRank Succ R source) source := by
  classical
  simp only [reachRank, dif_pos hreach]
  exact Nat.find_spec
    ((canReachSet_iff_exists_canReachSetIn Succ R).mp hreach)

/-- Minimality of `reachRank`. -/
theorem reachRank_le_of_canReachSetIn {steps : ℕ} {source : S}
    (path : CanReachSetIn Succ R steps source) :
    reachRank Succ R source ≤ steps := by
  classical
  have hreach : CanReachSet Succ R source :=
    canReachSet_of_canReachSetIn Succ R path
  simp only [reachRank, dif_pos hreach]
  exact Nat.find_min'
    ((canReachSet_iff_exists_canReachSetIn Succ R).mp hreach) path

/-- Outside `R`, a reachable state has a successor with strictly smaller
least-distance rank.  This is the acyclic strengthening of the older
"reachability remains possible" one-step lemma. -/
theorem exists_succ_reachRank_lt {source : S}
    (hsource : ¬ R source)
    (hreach : CanReachSet Succ R source) :
    ∃ destination,
      Succ source destination ∧
        reachRank Succ R destination < reachRank Succ R source := by
  have path := canReachSetIn_reachRank Succ R hreach
  generalize hrank : reachRank Succ R source = rank at path
  cases path with
  | target htarget => exact False.elim (hsource htarget)
  | @step steps source destination hedge tail =>
      refine ⟨destination, hedge, ?_⟩
      have hle : reachRank Succ R destination ≤ steps :=
        reachRank_le_of_canReachSetIn Succ R tail
      exact Nat.lt_succ_of_le hle

end FiniteReachability

variable {G : StochasticGame Bool} [Finite G.State]
  [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

/-- Convert real nonnegative weights of total mass one to a finite PMF. -/
private noncomputable def rankCompletionWeightsToPMF
    {alpha : Type*} [Fintype alpha] (weight : alpha → ℝ)
    (hnonneg : ∀ item, 0 ≤ weight item)
    (hsum : ∑ item, weight item = 1) : PMF alpha :=
  PMF.ofFintype (fun item => ENNReal.ofReal (weight item)) (by
    rw [← ENNReal.ofReal_one, ← hsum]
    exact
      (ENNReal.ofReal_sum_of_nonneg
        (fun item _ => hnonneg item)).symm)

private theorem rankCompletionWeightsToPMF_apply_toReal
    {alpha : Type*} [Fintype alpha] (weight : alpha → ℝ)
    (hnonneg : ∀ item, 0 ≤ weight item)
    (hsum : ∑ item, weight item = 1) (item : alpha) :
    ((rankCompletionWeightsToPMF weight hnonneg hsum) item).toReal =
      weight item := by
  unfold rankCompletionWeightsToPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (hnonneg item)

/-- Certificate produced by rank-decreasing completion of a Vrieze dual
occupation policy. -/
structure IsVriezeRankCompletion
    (controller : Bool)
    (z : G.State → G.Act controller → ℝ)
    (tau : G.State → PMF (G.Act controller)) : Prop where
  normalized_on_support :
    ∀ state (_ : G.vriezeOccupationSupport controller z state)
      (action : G.Act controller),
      ((tau state) action).toReal =
        z state action / (∑ candidate, z state candidate)
  rank_decreases_off_support :
    ∀ state (_ : ¬ G.vriezeOccupationSupport controller z state),
      ∃ destination,
        PMFSupportStep (G.controllerKernel controller tau)
            state destination ∧
          FiniteReachability.reachRank
              (G.controllerSucc controller)
              (G.vriezeOccupationSupport controller z) destination <
            FiniteReachability.reachRank
              (G.controllerSucc controller)
              (G.vriezeOccupationSupport controller z) state
  reaches_support_under_kernel :
    ∀ source,
      ∃ target,
        G.vriezeOccupationSupport controller z target ∧
          PMFReachable (G.controllerKernel controller tau) source target

/-- A dual-feasible occupation measure whose support is graph-reachable from
every state admits one stationary completion that actually reaches that
support under its own fixed kernel. -/
theorem exists_vriezeRankCompletion_of_dualFeasible
    {controller : Bool}
    {z yGain : G.State → G.Act controller → ℝ}
    {lam : G.State → ℝ}
    (hdual : G.IsVriezeDualFeasible controller z yGain lam)
    (hreach : ∀ state,
      FiniteReachability.CanReachSet
        (G.controllerSucc controller)
        (G.vriezeOccupationSupport controller z) state) :
    ∃ tau : G.State → PMF (G.Act controller),
      G.IsVriezeRankCompletion controller z tau := by
  classical
  have hprogress : ∀ state,
      ¬ G.vriezeOccupationSupport controller z state →
      ∃ (action : G.Act controller) (destination : G.State),
        destination ∈
            (G.controllerKernel controller
              (fun _ => PMF.pure action) state).support ∧
          FiniteReachability.reachRank
              (G.controllerSucc controller)
              (G.vriezeOccupationSupport controller z) destination <
            FiniteReachability.reachRank
              (G.controllerSucc controller)
              (G.vriezeOccupationSupport controller z) state := by
    intro state hstate
    obtain ⟨destination, hstep, hlt⟩ :=
      FiniteReachability.exists_succ_reachRank_lt
        (G.controllerSucc controller)
        (G.vriezeOccupationSupport controller z)
        hstate (hreach state)
    obtain ⟨action, hsupport⟩ := hstep
    exact ⟨action, destination, hsupport, hlt⟩
  choose actionOf destinationOf hsupportOf hrankOf using hprogress
  let tau : G.State → PMF (G.Act controller) := fun state =>
    if hstate : G.vriezeOccupationSupport controller z state then
      rankCompletionWeightsToPMF
        (fun action => z state action / (∑ candidate, z state candidate))
        (fun action => div_nonneg (hdual.z_nonneg state action) hstate.le)
        (by
          rw [← Finset.sum_div]
          exact div_self hstate.ne')
    else PMF.pure (actionOf state hstate)
  have htau_off : ∀ state
      (hstate : ¬ G.vriezeOccupationSupport controller z state),
      tau state = PMF.pure (actionOf state hstate) := by
    intro state hstate
    dsimp only [tau]
    rw [dif_neg hstate]
  have hkernel_off : ∀ state
      (hstate : ¬ G.vriezeOccupationSupport controller z state),
      G.controllerKernel controller tau state =
        G.controllerKernel controller
          (fun _ => PMF.pure (actionOf state hstate)) state := by
    intro state hstate
    unfold controllerKernel
    rw [htau_off state hstate]
  have hrank_step : ∀ state
      (hstate : ¬ G.vriezeOccupationSupport controller z state),
      ∃ destination,
        PMFSupportStep (G.controllerKernel controller tau)
            state destination ∧
          FiniteReachability.reachRank
              (G.controllerSucc controller)
              (G.vriezeOccupationSupport controller z) destination <
            FiniteReachability.reachRank
              (G.controllerSucc controller)
              (G.vriezeOccupationSupport controller z) state := by
    intro state hstate
    refine ⟨destinationOf state hstate, ?_, hrankOf state hstate⟩
    unfold PMFSupportStep
    rw [hkernel_off state hstate]
    exact (PMF.mem_support_iff _ _).mp (hsupportOf state hstate)
  have hfixed_reach : ∀ source,
      ∃ target,
        G.vriezeOccupationSupport controller z target ∧
          PMFReachable (G.controllerKernel controller tau) source target := by
    intro source
    generalize hrank :
      FiniteReachability.reachRank
        (G.controllerSucc controller)
        (G.vriezeOccupationSupport controller z) source = rank
    induction rank using Nat.strong_induction_on generalizing source with
    | h rank ih =>
        by_cases hsource :
            G.vriezeOccupationSupport controller z source
        · exact ⟨source, hsource, Relation.ReflTransGen.refl⟩
        · obtain ⟨destination, hstep, hlt⟩ :=
            hrank_step source hsource
          have hlt_rank :
              FiniteReachability.reachRank
                  (G.controllerSucc controller)
                  (G.vriezeOccupationSupport controller z) destination <
                rank := by
            simpa only [hrank] using hlt
          obtain ⟨target, htarget, hpath⟩ :=
            ih _ hlt_rank destination rfl
          exact ⟨target, htarget,
            Relation.ReflTransGen.head hstep hpath⟩
  refine ⟨tau, {
    normalized_on_support := ?_
    rank_decreases_off_support := hrank_step
    reaches_support_under_kernel := hfixed_reach
  }⟩
  intro state hstate action
  have htau_on : tau state =
      rankCompletionWeightsToPMF
        (fun candidate =>
          z state candidate / (∑ other, z state other))
        (fun candidate =>
          div_nonneg (hdual.z_nonneg state candidate) hstate.le)
        (by
          rw [← Finset.sum_div]
          exact div_self hstate.ne') := by
    dsimp only [tau]
    rw [dif_pos hstate]
  rw [htau_on]
  exact rankCompletionWeightsToPMF_apply_toReal _ _ _ action

/-- Strong complementarity supplies both dual feasibility and the all-state
support reachability needed by the rank-decreasing completion compiler. -/
theorem exists_vriezeRankCompletion_of_strongComplementary
    {controller : Bool} (hSC : G.IsSingleController controller)
    {q : VriezeCol G controller → ℝ}
    {w : VriezeRow G controller → ℝ}
    (hstrong : Math.LinearProgramming.IsStrongComplementaryPair
      (G.vriezeA controller) (G.vriezeB controller)
        (G.vriezeC controller) q w) :
    ∃ tau : G.State → PMF (G.Act controller),
      G.IsVriezeRankCompletion controller
        (G.vriezeDualZ controller w) tau := by
  exact G.exists_vriezeRankCompletion_of_dualFeasible
    (G.isVriezeDualFeasible_vriezeDualZ_vriezeDualYGain hstrong.2.1)
    (G.all_canReach_vriezeOccupationSupport_of_strongComplementary
      hSC hstrong)

end StochasticGame
end GameTheory
