/-
# Continuation contexts

A context assigns a PMF outcome law to each choice and evaluates it with a
real continuation payoff. Choices are compared by their extended-real expected
continuation payoffs, so a choice worth `+∞` or `−∞` is compared like any other;
every compared choice must have an expectation. A choice with an integrable
payoff also has a real value, and between such choices the comparison is the
real one.
-/

import GameTheory.Math.Probability.ExtendedExpectation

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uh uc uo

/-- The outcome law of each choice and the payoff of each outcome. -/
structure Context (Choice : Type uc) (Outcome : Type uo) where
  /-- Continuation outcome law induced by each available choice. -/
  outcome : Choice → PMF Outcome
  /-- Realized continuation payoff on the outcome carrier. -/
  continuation : Outcome → ℝ

namespace Context

variable {Choice : Type uc} {Outcome : Type uo}

/-- Build a context by first drawing a hidden state from one belief and then
applying a state- and choice-dependent outcome kernel. -/
def ofBelief {Hidden : Type uh} (belief : PMF Hidden)
    (branch : Hidden → Choice → PMF Outcome)
    (continuation : Outcome → ℝ) : Context Choice Outcome where
  outcome choice := belief.bind fun hidden => branch hidden choice
  continuation := continuation

/-- A choice has a defined finite real continuation value. -/
def IntegrableAt (ctx : Context Choice Outcome) (choice : Choice) : Prop :=
  PayoffIntegrable (ctx.outcome choice) ctx.continuation

/-- The continuation value of a choice, meaningful when `ctx.IntegrableAt choice`. -/
def value (ctx : Context Choice Outcome) (choice : Choice) : ℝ :=
  expect (ctx.outcome choice) ctx.continuation

/-- A choice's continuation payoff has an expectation. -/
def HasValueAt (ctx : Context Choice Outcome) (choice : Choice) : Prop :=
  HasExpectation (ctx.outcome choice) ctx.continuation

/-- The extended-real continuation value of a choice, meaningful when
`ctx.HasValueAt choice`. -/
def extendedValue (ctx : Context Choice Outcome) (choice : Choice) : EReal :=
  extendedExpect (ctx.outcome choice) ctx.continuation

theorem IntegrableAt.hasValueAt {ctx : Context Choice Outcome} {choice : Choice}
    (h : ctx.IntegrableAt choice) : ctx.HasValueAt choice :=
  hasExpectation_of_payoffIntegrable h

theorem extendedValue_eq {ctx : Context Choice Outcome} {choice : Choice}
    (h : ctx.IntegrableAt choice) : ctx.extendedValue choice = ctx.value choice :=
  extendedExpect_eq_expect h

/-- The incumbent and every allowed alternative have expected continuation
payoffs, and no allowed alternative has a larger one. The incumbent must have an
expectation even when `allowed` is empty. -/
def IsLocallyOptimal (ctx : Context Choice Outcome) (allowed : Set Choice)
    (choice : Choice) : Prop :=
  ctx.HasValueAt choice ∧
    (∀ alternative ∈ allowed, ctx.HasValueAt alternative) ∧
      ∀ alternative ∈ allowed, ctx.extendedValue alternative ≤ ctx.extendedValue choice

/-- An admissible alternative whose expected continuation payoff is strictly
larger. -/
def IsProfitableDeviation (ctx : Context Choice Outcome) (allowed : Set Choice)
    (choice alternative : Choice) : Prop :=
  alternative ∈ allowed ∧ ctx.HasValueAt choice ∧ ctx.HasValueAt alternative ∧
    ctx.extendedValue choice < ctx.extendedValue alternative

/-- Between integrable choices local optimality is the real comparison of
values. -/
theorem isLocallyOptimal_iff_of_integrable {ctx : Context Choice Outcome}
    {allowed : Set Choice} {choice : Choice} (hchoice : ctx.IntegrableAt choice)
    (hall : ∀ alternative ∈ allowed, ctx.IntegrableAt alternative) :
    ctx.IsLocallyOptimal allowed choice ↔
      ∀ alternative ∈ allowed, ctx.value alternative ≤ ctx.value choice := by
  refine ⟨fun h alternative hmem => ?_, fun h => ⟨hchoice.hasValueAt,
    fun alternative hmem => (hall alternative hmem).hasValueAt, fun alternative hmem => ?_⟩⟩
  · have hle := h.2.2 alternative hmem
    rwa [extendedValue_eq (hall alternative hmem), extendedValue_eq hchoice,
      EReal.coe_le_coe_iff] at hle
  · rw [extendedValue_eq (hall alternative hmem), extendedValue_eq hchoice,
      EReal.coe_le_coe_iff]
    exact h alternative hmem

/-- When every compared choice has an expectation, local optimality means no
allowed profitable deviation. Expectations cannot be inferred from the absence
of a profitable deviation. -/
theorem isLocallyOptimal_iff_no_profitable_deviation
    (ctx : Context Choice Outcome) (allowed : Set Choice) (choice : Choice) :
    ctx.IsLocallyOptimal allowed choice ↔
      ctx.HasValueAt choice ∧
        (∀ alternative ∈ allowed, ctx.HasValueAt alternative) ∧
          ¬ ∃ alternative, ctx.IsProfitableDeviation allowed choice alternative := by
  constructor
  · rintro ⟨hchoice, hall, hopt⟩
    refine ⟨hchoice, hall, ?_⟩
    rintro ⟨alternative, hmem, -, -, hlt⟩
    exact (not_le.mpr hlt) (hopt alternative hmem)
  · rintro ⟨hchoice, hall, hnone⟩
    refine ⟨hchoice, hall, fun alternative hmem => ?_⟩
    by_contra hgt
    exact hnone ⟨alternative, hmem, hchoice, hall alternative hmem, not_le.mp hgt⟩

/-- Local optimality is preserved by contexts with the same expectations and
extended values. -/
theorem isLocallyOptimal_congr {first second : Context Choice Outcome}
    {allowed : Set Choice} {choice : Choice}
    (hexpectation : ∀ option, option = choice ∨ option ∈ allowed →
      (first.HasValueAt option ↔ second.HasValueAt option))
    (hvalue : ∀ option, option = choice ∨ option ∈ allowed →
      first.extendedValue option = second.extendedValue option) :
    first.IsLocallyOptimal allowed choice ↔
      second.IsLocallyOptimal allowed choice := by
  constructor <;> rintro ⟨incumbent, alternatives, optimal⟩
  · refine ⟨(hexpectation choice (Or.inl rfl)).mp incumbent,
      fun option mem => (hexpectation option (Or.inr mem)).mp (alternatives option mem),
      fun option mem => ?_⟩
    rw [← hvalue option (Or.inr mem), ← hvalue choice (Or.inl rfl)]
    exact optimal option mem
  · refine ⟨(hexpectation choice (Or.inl rfl)).mpr incumbent,
      fun option mem => (hexpectation option (Or.inr mem)).mpr (alternatives option mem),
      fun option mem => ?_⟩
    rw [hvalue option (Or.inr mem), hvalue choice (Or.inl rfl)]
    exact optimal option mem

end Context

end GameTheory.Protocol
