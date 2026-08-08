/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.Basic

/-!
# Executing a multivalued essential-APS SCC

A finite SCC does not determine a chronological orbit by occupation balance.
The relation used here contains only witnessed exact singleton segments.  From
one reached SCC node, classical dependent choice gives a sharp alternative:

* an ordinary finite execution reaches a viable absorbing endpoint;
* a single infinite internal execution carries the requested charge on every
  edge; or
* a finite charged execution reaches a typed local obstruction.

The obstruction distinguishes absence of any executable segment from the
presence of physical segments whose masses all miss the requested charge
floor.  Thus failure does not get hidden inside the full convex-hull APS
operator.  The absorbing branch deliberately uses ordinary executable edges:
a low-charge segment may still be part of a valid finite route to absorption.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem infinite_path_or_reachable_stuck
    {α : Type*} (step : α → α → Prop) (initial : α) :
    (∃ path : ℕ → α, path 0 = initial ∧
      ∀ time, step (path time) (path (time + 1))) ∨
      ∃ stuck, Relation.ReflTransGen step initial stuck ∧
        ¬ ∃ next, step stuck next := by
  classical
  by_cases hstuck :
      ∃ stuck, Relation.ReflTransGen step initial stuck ∧
        ¬ ∃ next, step stuck next
  · exact Or.inr hstuck
  left
  let Reachable := {state : α // Relation.ReflTransGen step initial state}
  have hnext : ∀ state : Reachable, ∃ next, step state.1 next := by
    intro state
    by_contra hnone
    exact hstuck ⟨state.1, state.2, hnone⟩
  let chooseNext : Reachable → α :=
    fun state => Classical.choose (hnext state)
  have chooseNext_spec : ∀ state : Reachable,
      step state.1 (chooseNext state) :=
    fun state => Classical.choose_spec (hnext state)
  let advance : Reachable → Reachable := fun state =>
    ⟨chooseNext state, state.2.tail (chooseNext_spec state)⟩
  let orbit : ℕ → Reachable := fun time =>
    Nat.rec ⟨initial, Relation.ReflTransGen.refl⟩
      (fun _ state => advance state) time
  refine ⟨fun time => (orbit time).1, ?_, ?_⟩
  · rfl
  · intro time
    have hnextOrbit : orbit (time + 1) = advance (orbit time) := rfl
    rw [hnextOrbit]
    exact chooseNext_spec (orbit time)

/-- **Multivalued essential-APS SCC execution.**

Starting at an actually reached continuation node of a finite successor SCC,
one obtains an executable absorbing exit, one infinite chronological charged
path inside that same SCC, or a reached typed obstruction.  No occupation
measure, convex mixture of successor fibers, or cancellation across components
is used.

The exit search uses all witnessed exact segments.  Only after finite
absorption has been excluded does the theorem follow the charged subrelation.
Consequently a low-charge finite route to a terminal endpoint is not
misclassified as a charge obstruction. -/
theorem quittingEssentialAPSSCC_executionOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (initial : QuittingEssentialAPSSCCNode reward family component) :
    QuittingEssentialAPSSCCExecutionOutcome reward family component
      chargeFloor initial := by
  classical
  by_cases hexit :
      ∃ terminal,
        QuittingEssentialAPSSCCFiniteExecution reward family component
          initial terminal ∧
        terminal.IsTerminal
  · rcases hexit with ⟨terminal, hexecution, hterminal⟩
    exact .absorbingExit {
      terminal := terminal
      execution := hexecution
      terminal_mem := hterminal }
  rcases infinite_path_or_reachable_stuck
      (QuittingEssentialAPSChargedSCCStepRel reward family component chargeFloor)
      initial with hinfinite | hstuck
  · rcases hinfinite with ⟨node, hinitial, hstep⟩
    let witnessedStep : ∀ time,
        QuittingEssentialAPSSCCStep reward family component
          (node time) (node (time + 1)) :=
      fun time => Classical.choose (hstep time)
    have hcharged : ∀ time,
        chargeFloor ≤ (witnessedStep time).mass :=
      fun time => Classical.choose_spec (hstep time)
    exact .recurrentPath {
      node := node
      initial_eq := hinitial
      step := witnessedStep
      charged := hcharged }
  · rcases hstuck with ⟨state, hexecution, hnoChargedStep⟩
    have hnonterminal : ¬ state.IsTerminal := by
      intro hterminal
      exact hexit ⟨state,
        QuittingEssentialAPSChargedSCCFiniteExecution.toFiniteExecution
          hexecution, hterminal⟩
    by_cases hstep : ∃ target,
        QuittingEssentialAPSSCCStepRel reward family component state target
    · exact .obstructed {
        state := state
        execution := hexecution
        obstruction := .chargeGap hnonterminal hstep hnoChargedStep }
    · exact .obstructed {
        state := state
        execution := hexecution
        obstruction := .noExecutableSegment hnonterminal hstep }

/-- If every nonterminal SCC node has a charged executable continuation, the
obstruction branch disappears: one gets either a finite absorbing execution or
one infinite charged chronological path. -/
theorem quittingEssentialAPSSCC_absorbingExit_or_recurrentPath_of_progress
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (initial : QuittingEssentialAPSSCCNode reward family component)
    (hprogress : ∀ state : QuittingEssentialAPSSCCNode reward family component,
      state.IsTerminal ∨
        ∃ target,
          QuittingEssentialAPSChargedSCCStepRel reward family component
            chargeFloor state target) :
    Nonempty (QuittingEssentialAPSSCCAbsorbingExit reward family component
      initial) ∨
      Nonempty (QuittingEssentialAPSSCCInfiniteExecution reward family
        component chargeFloor initial) := by
  cases quittingEssentialAPSSCC_executionOutcome reward family component
      chargeFloor initial with
  | absorbingExit exit =>
      exact Or.inl ⟨exit⟩
  | recurrentPath execution =>
      exact Or.inr ⟨execution⟩
  | obstructed reached =>
      rcases hprogress reached.state with hterminal | hcharged
      · cases reached.obstruction with
        | noExecutableSegment hnonterminal _ =>
            exact False.elim (hnonterminal hterminal)
        | chargeGap hnonterminal _ _ =>
            exact False.elim (hnonterminal hterminal)
      · rcases hcharged with ⟨target, hcharged⟩
        cases reached.obstruction with
        | noExecutableSegment _ hnoStep =>
            exact False.elim (hnoStep ⟨target,
              QuittingEssentialAPSChargedSCCStepRel.toStepRel hcharged⟩)
        | chargeGap _ _ hnoChargedStep =>
            exact False.elim (hnoChargedStep ⟨target, hcharged⟩)

/-- Terminal-freeness plus charged seriality produces one infinite executable
path in the selected SCC.  This is the direct multivalued counterpart of the
existing unique-live dependent-choice theorem, with local segment production
left as an explicit hypothesis. -/
theorem exists_quittingEssentialAPSSCCInfiniteExecution_of_terminalFree_of_chargedSerial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (initial : QuittingEssentialAPSSCCNode reward family component)
    (hterminalFree :
      ∀ state : QuittingEssentialAPSSCCNode reward family component,
        ¬ state.IsTerminal)
    (hserial :
      ∀ state : QuittingEssentialAPSSCCNode reward family component,
        ∃ target,
          QuittingEssentialAPSChargedSCCStepRel reward family component
            chargeFloor state target) :
    Nonempty (QuittingEssentialAPSSCCInfiniteExecution reward family component
      chargeFloor initial) := by
  rcases quittingEssentialAPSSCC_absorbingExit_or_recurrentPath_of_progress
      reward family component chargeFloor initial
      (fun state => Or.inr (hserial state)) with hexit | hexecution
  · rcases hexit with ⟨exit⟩
    exact False.elim (hterminalFree exit.terminal exit.terminal_mem)
  · exact hexecution

/-- An infinite multivalued SCC execution is directly an instance of the
existing executable essential-APS infinite-run API.  The owner path is no
longer functional in the current owner, but every edge is a genuine Flesch
successor and every continuation remains in the supplied family. -/
theorem QuittingEssentialAPSSCCInfiniteExecution.exists_infiniteRun
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {component : QuittingEssentialAPSSCC reward}
    {chargeFloor : ℝ}
    {initial : QuittingEssentialAPSSCCNode reward family component}
    (execution : QuittingEssentialAPSSCCInfiniteExecution reward family
      component chargeFloor initial) :
    ∃ owner mass value,
      owner 0 = initial.owner ∧
      IsQuittingEssentialAPSInfiniteRun reward family owner initial.value
        mass value ∧
      (∀ time, owner time ∈ component.vertices) ∧
      (∀ time, QuittingFleschSuccessor reward
        (owner time) (owner (time + 1))) ∧
      ∀ time, chargeFloor ≤ mass time := by
  let owner : ℕ → ι := fun time => (execution.node time).owner
  let mass : ℕ → ℝ := fun time => (execution.step time).mass
  let value : ℕ → Payoff ι := fun time => (execution.node time).value
  refine ⟨owner, mass, value, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun node => node.owner) execution.initial_eq
  · refine ⟨?_, ?_, ?_⟩
    · exact congrArg (fun node => node.value) execution.initial_eq
    · intro time
      exact (execution.node time).value_mem
    · intro time
      exact ⟨(execution.step time).mass_mem, (execution.step time).arc⟩
  · intro time
    exact (execution.node time).owner_mem
  · intro time
    exact (execution.step time).edge
  · intro time
    exact execution.charged time

/-- Componentwise charge grows at least linearly along the single executable
path.  This is path charge, not charge obtained by cancelling occupations in
different SCCs. -/
theorem QuittingEssentialAPSSCCInfiniteExecution.prefixCharge_lowerBound
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {component : QuittingEssentialAPSSCC reward}
    {chargeFloor : ℝ}
    {initial : QuittingEssentialAPSSCCNode reward family component}
    (execution : QuittingEssentialAPSSCCInfiniteExecution reward family
      component chargeFloor initial)
    (horizon : ℕ) :
    (horizon : ℝ) * chargeFloor ≤
      ∑ time in Finset.range horizon, (execution.step time).mass := by
  calc
    (horizon : ℝ) * chargeFloor =
        ∑ _time in Finset.range horizon, chargeFloor := by
      simp
    _ ≤ ∑ time in Finset.range horizon, (execution.step time).mass := by
      exact Finset.sum_le_sum fun time _ => execution.charged time

/-- A positive per-edge charge floor makes prefix charge unbounded on the one
chronological SCC path. -/
theorem QuittingEssentialAPSSCCInfiniteExecution.exists_prefixCharge_ge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {component : QuittingEssentialAPSSCC reward}
    {chargeFloor : ℝ}
    {initial : QuittingEssentialAPSSCCNode reward family component}
    (execution : QuittingEssentialAPSSCCInfiniteExecution reward family
      component chargeFloor initial)
    (hcharge : 0 < chargeFloor) (target : ℝ) :
    ∃ horizon : ℕ,
      target ≤ ∑ time in Finset.range horizon,
        (execution.step time).mass := by
  obtain ⟨horizon, hhorizon⟩ := exists_nat_gt (target / chargeFloor)
  refine ⟨horizon, le_trans ?_ (execution.prefixCharge_lowerBound horizon)⟩
  exact ((div_lt_iff₀ hcharge).mp hhorizon).le

end GameTheory
