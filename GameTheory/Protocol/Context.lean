/-
# Continuation contexts

A context assigns a PMF outcome law to each choice and evaluates it with a
real continuation payoff. The value of a choice is its expected continuation
payoff; comparisons of values state the integrability of every compared law.
-/

import GameTheory.Math.Probability.Expectation

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

/-- The incumbent and every allowed alternative have finite real values, and
no allowed alternative has a larger value. The incumbent must be integrable
even when `allowed` is empty. -/
def IsLocallyOptimal (ctx : Context Choice Outcome) (allowed : Set Choice)
    (choice : Choice) : Prop :=
  ctx.IntegrableAt choice ∧
    (∀ alternative ∈ allowed, ctx.IntegrableAt alternative) ∧
      ∀ alternative ∈ allowed, ctx.value alternative ≤ ctx.value choice

/-- An admissible alternative with a defined, strictly larger real value. -/
def IsProfitableDeviation (ctx : Context Choice Outcome) (allowed : Set Choice)
    (choice alternative : Choice) : Prop :=
  alternative ∈ allowed ∧ ctx.IntegrableAt choice ∧ ctx.IntegrableAt alternative ∧
    ctx.value choice < ctx.value alternative

/-- Under integrability of every compared law, local optimality means no
allowed profitable deviation. Integrability cannot be inferred from the
absence of a profitable deviation. -/
theorem isLocallyOptimal_iff_no_profitable_deviation
    (ctx : Context Choice Outcome) (allowed : Set Choice) (choice : Choice) :
    ctx.IsLocallyOptimal allowed choice ↔
      ctx.IntegrableAt choice ∧
        (∀ alternative ∈ allowed, ctx.IntegrableAt alternative) ∧
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

/-- Local optimality is preserved by contexts with the same admissible values. -/
theorem isLocallyOptimal_congr {first second : Context Choice Outcome}
    {allowed : Set Choice} {choice : Choice}
    (hintegrable : ∀ option,
      first.IntegrableAt option ↔ second.IntegrableAt option)
    (hvalue : ∀ option, first.IntegrableAt option →
      first.value option = second.value option) :
    first.IsLocallyOptimal allowed choice ↔
      second.IsLocallyOptimal allowed choice := by
  constructor
  · rintro ⟨hchoice, hall, hopt⟩
    refine ⟨(hintegrable choice).mp hchoice,
      fun alternative hmem => (hintegrable alternative).mp (hall alternative hmem),
      fun alternative hmem => ?_⟩
    rw [← hvalue alternative (hall alternative hmem), ← hvalue choice hchoice]
    exact hopt alternative hmem
  · rintro ⟨hchoice, hall, hopt⟩
    have hchoice' := (hintegrable choice).mpr hchoice
    refine ⟨hchoice', fun alternative hmem => (hintegrable alternative).mpr (hall alternative hmem),
      fun alternative hmem => ?_⟩
    rw [hvalue alternative ((hintegrable alternative).mpr (hall alternative hmem)),
      hvalue choice hchoice']
    exact hopt alternative hmem

end Context

end GameTheory.Protocol
