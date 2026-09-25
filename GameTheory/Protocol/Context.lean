/-
# Guarded continuation contexts

A context assigns a PMF outcome law to each choice and evaluates it with a
real continuation payoff. Finite real expected utility is available only when
the chosen law and payoff have an integrability certificate.
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

/-- The guarded continuation value of a choice. -/
def value (ctx : Context Choice Outcome) (choice : Choice)
    (h : ctx.IntegrableAt choice) : ℝ :=
  expect (ctx.outcome choice) ctx.continuation h

/-- The incumbent and every allowed alternative have finite real values, and
no allowed alternative has a larger value. The incumbent certificate remains
required even when `allowed` is empty. -/
def IsLocallyOptimal (ctx : Context Choice Outcome) (allowed : Set Choice)
    (choice : Choice) : Prop :=
  ctx.IntegrableAt choice ∧
    (∀ alternative ∈ allowed, ctx.IntegrableAt alternative) ∧
      ∀ alternative ∈ allowed,
        ∀ hchoice : ctx.IntegrableAt choice,
          ∀ halt : ctx.IntegrableAt alternative,
            ctx.value alternative halt ≤ ctx.value choice hchoice

/-- An admissible alternative with a defined, strictly larger real value. -/
def IsProfitableDeviation (ctx : Context Choice Outcome) (allowed : Set Choice)
    (choice alternative : Choice) : Prop :=
  alternative ∈ allowed ∧
    ∃ hchoice : ctx.IntegrableAt choice,
      ∃ halt : ctx.IntegrableAt alternative,
        ctx.value choice hchoice < ctx.value alternative halt

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
  · intro ⟨hchoice, hall, hopt⟩
    refine ⟨hchoice, hall, ?_⟩
    rintro ⟨alternative, hmem, hchoice', halt, hlt⟩
    exact (not_le.mpr hlt) (hopt alternative hmem hchoice' halt)
  · intro ⟨hchoice, hall, hnone⟩
    refine ⟨hchoice, hall, ?_⟩
    intro alternative hmem hchoice' halt
    by_contra hgt
    exact hnone ⟨alternative, hmem, hchoice', halt, not_le.mp hgt⟩

/-- Local optimality is preserved by contexts with the same admissible values. -/
theorem isLocallyOptimal_congr {first second : Context Choice Outcome}
    {allowed : Set Choice} {choice : Choice}
    (hintegrable : ∀ option,
      first.IntegrableAt option ↔ second.IntegrableAt option)
    (hvalue : ∀ option (hf : first.IntegrableAt option)
      (hs : second.IntegrableAt option),
        first.value option hf = second.value option hs) :
    first.IsLocallyOptimal allowed choice ↔
      second.IsLocallyOptimal allowed choice := by
  constructor
  · intro ⟨hchoice, hall, hopt⟩
    refine ⟨(hintegrable choice).mp hchoice,
      (fun alternative hmem => (hintegrable alternative).mp (hall alternative hmem)), ?_⟩
    intro alternative hmem hchoice' halt
    rw [← hvalue alternative ((hintegrable alternative).mpr halt) halt,
      ← hvalue choice ((hintegrable choice).mpr hchoice') hchoice']
    exact hopt alternative hmem _ _
  · intro ⟨hchoice, hall, hopt⟩
    refine ⟨(hintegrable choice).mpr hchoice,
      (fun alternative hmem => (hintegrable alternative).mpr (hall alternative hmem)), ?_⟩
    intro alternative hmem hchoice' halt
    rw [hvalue alternative halt ((hintegrable alternative).mp halt),
      hvalue choice hchoice' ((hintegrable choice).mp hchoice')]
    exact hopt alternative hmem _ _

end Context

end GameTheory.Protocol
