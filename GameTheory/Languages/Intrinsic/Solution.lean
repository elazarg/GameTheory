module

/-
# Causal solvability and selected intrinsic closed-loop solutions

This opt-in theorem leaf derives unique solvability from a causal schedule
and selects the decision profile certified by unique solvability.
-/

public import GameTheory.Languages.Intrinsic
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace GameTheory.Languages.Intrinsic.Model

universe uAgent uNature uDecision

/-- Causality makes closed-loop fixed points unique whenever they exist. -/
theorem IsCausalWith.fixedPoint_unique
    {M : Model.{uAgent, uNature, uDecision}} {slots : Nat}
    {schedule : M.Schedule slots} (causal : IsCausalWith schedule)
    (profile : M.PureProfile) (nature : M.Nature)
    (left right : (agent : M.Agent) → M.Decision agent)
    (hleft : M.IsFixedPoint profile nature left)
    (hright : M.IsFixedPoint profile nature right) : left = right := by
  have agreement : ∀ count : Nat, ∀ slot : Fin slots, slot.val < count →
      left (schedule.orderAt ⟨nature, left⟩ slot) =
        right (schedule.orderAt ⟨nature, left⟩ slot) := by
    intro count
    induction count with
    | zero => intro slot hslot; exact (Nat.not_lt_zero _ hslot).elim
    | succ count ih =>
      intro slot hslot
      have hinfo := (causal ⟨nature, left⟩ ⟨nature, right⟩ slot
        ⟨rfl, fun earlier hearlier =>
          ih earlier (Nat.lt_of_lt_of_le hearlier (Nat.le_of_lt_succ hslot))⟩).2
      rw [hleft, hright]
      exact (profile _).respects _ _ hinfo
  funext agent
  obtain ⟨slot, rfl⟩ := (schedule.orderAt ⟨nature, left⟩).surjective agent
  exact agreement slots slot slot.isLt

/-- A causal exhaustive schedule gives a unique closed-loop solution for every
profile and nature state. Decision nonemptiness supplies an initial complete
configuration; successive rule applications stabilize one more scheduled
coordinate until all closed-loop equations hold. -/
theorem isSolvable_of_isCausalWith
    {M : Model.{uAgent, uNature, uDecision}} {slots : Nat}
    {schedule : M.Schedule slots} (causal : IsCausalWith schedule)
    (decisions_nonempty : ∀ agent, Nonempty (M.Decision agent)) : M.IsSolvable := by
  intro profile nature
  let seed : (agent : M.Agent) → M.Decision agent :=
    fun agent => Classical.choice (decisions_nonempty agent)
  let advance (decision : (agent : M.Agent) → M.Decision agent) :=
    fun agent => (profile agent).act ⟨nature, decision⟩
  let approximation (count : Nat) := advance^[count] seed
  have step (count : Nat) (agent : M.Agent) :
      approximation (count + 1) agent =
        (profile agent).act ⟨nature, approximation count⟩ := by
    exact congrFun (Function.iterate_succ_apply' advance count seed) agent
  have agreement : ∀ count : Nat, ∀ slot : Fin slots, slot.val < count →
      approximation count (schedule.orderAt ⟨nature, approximation count⟩ slot) =
        approximation (count + 1) (schedule.orderAt ⟨nature, approximation count⟩ slot) := by
    intro count
    induction count with
    | zero => intro slot hslot; exact (Nat.not_lt_zero _ hslot).elim
    | succ count ih =>
      intro slot hslot
      have hcausal := causal ⟨nature, approximation count⟩
        ⟨nature, approximation (count + 1)⟩ slot
        ⟨rfl, fun earlier hearlier =>
          ih earlier (Nat.lt_of_lt_of_le hearlier (Nat.le_of_lt_succ hslot))⟩
      rw [← hcausal.1 slot (Nat.le_refl _), step, step]
      exact (profile _).respects _ _ hcausal.2
  have fixed : M.IsFixedPoint profile nature (approximation slots) := by
    intro agent
    obtain ⟨slot, rfl⟩ := (schedule.orderAt ⟨nature, approximation slots⟩).surjective agent
    exact (agreement slots slot slot.isLt).trans (step slots _)
  exact ⟨approximation slots, fixed, fun decision hfixed =>
    causal.fixedPoint_unique profile nature decision (approximation slots) hfixed fixed⟩

/-- Select the unique closed-loop decision profile certified by solvability. -/
noncomputable def solution (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (profile : M.PureProfile) (nature : M.Nature) :
    (agent : M.Agent) → M.Decision agent :=
  (solvable profile nature).choose

/-- The selected profile satisfies the closed-loop equations. -/
theorem solution_isFixedPoint (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (profile : M.PureProfile) (nature : M.Nature) :
    M.IsFixedPoint profile nature (M.solution solvable profile nature) :=
  (solvable profile nature).choose_spec.1

/-- Any profile satisfying the same closed-loop equations is the selected one. -/
theorem solution_unique (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (profile : M.PureProfile) (nature : M.Nature)
    (decision : (agent : M.Agent) → M.Decision agent)
    (fixed : M.IsFixedPoint profile nature decision) :
    decision = M.solution solvable profile nature :=
  (solvable profile nature).choose_spec.2 decision fixed

/-- The selected decision at each agent has the declared strategy value. -/
theorem solution_apply (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (profile : M.PureProfile) (nature : M.Nature)
    (agent : M.Agent) :
    M.solution solvable profile nature agent =
      (profile agent).act ⟨nature, M.solution solvable profile nature⟩ :=
  M.solution_isFixedPoint solvable profile nature agent

/-- Pointwise equal strategy actions select equal closed-loop decisions. -/
theorem solution_congr (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (left right : M.PureProfile) (nature : M.Nature)
    (actions : ∀ agent (configuration : M.Configuration),
      (left agent).act configuration = (right agent).act configuration) :
    M.solution solvable left nature = M.solution solvable right nature := by
  apply M.solution_unique solvable right nature
  intro agent
  rw [M.solution_apply]
  exact actions agent _

end GameTheory.Languages.Intrinsic.Model
