/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Online Algorithms

Deterministic online algorithms as state machines, plus small reusable
vocabularies for secretary, prophet, and AdWords-style allocation problems.

The common online constraint is structural: `step` sees only the current state
and the current request, never the tail of the request stream.
-/

namespace Math.OnlineAlgorithms

/-- A deterministic online algorithm.

`step s (some r)` consumes one request. `step s none` is the explicit
end-of-input step, allowing stopping algorithms to make a final decision when
the stream is exhausted. Emitting `some o` is a decision/output; whether that
halts is determined by the driver. -/
structure OnlineAlgorithm (Input State Output : Type*) where
  /-- Initial state. -/
  init : State
  /-- One online step. -/
  step : State → Option Input → State × Option Output

namespace OnlineAlgorithm

variable {α σ β : Type*}

/-- Run a stopping problem, halting at the first emitted output. -/
def run (alg : OnlineAlgorithm α σ β) : σ → List α → σ × Option β
  | s, [] => alg.step s none
  | s, r :: rs =>
      match alg.step s (some r) with
      | (s', some o) => (s', some o)
      | (s', none) => alg.run s' rs

@[simp] theorem run_nil (alg : OnlineAlgorithm α σ β) (s : σ) :
    alg.run s [] = alg.step s none := rfl

theorem run_cons (alg : OnlineAlgorithm α σ β) (s : σ) (r : α) (rs : List α) :
    alg.run s (r :: rs) =
      match alg.step s (some r) with
      | (s', some o) => (s', some o)
      | (s', none) => alg.run s' rs := rfl

@[simp] theorem run_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.run s (r :: rs) = (s', some o) := by
  rw [run_cons, h]

@[simp] theorem run_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
    alg.run s (r :: rs) = alg.run s' rs := by
  rw [run_cons, h]

/-- The stopping decision produced by `run`. -/
abbrev runResult (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : Option β :=
  (alg.run s rs).2

/-- The terminal state produced by `run`. -/
abbrev runStatus (alg : OnlineAlgorithm α σ β) (s : σ) (rs : List α) : σ :=
  (alg.run s rs).1

/-- Run a streaming problem, collecting every emitted output. -/
def runAll (alg : OnlineAlgorithm α σ β) : σ → List α → List β
  | s, [] =>
      match (alg.step s none).2 with
      | some o => [o]
      | none => []
  | s, r :: rs =>
      match alg.step s (some r) with
      | (s', some o) => o :: alg.runAll s' rs
      | (s', none) => alg.runAll s' rs

theorem runAll_cons (alg : OnlineAlgorithm α σ β) (s : σ) (r : α) (rs : List α) :
    alg.runAll s (r :: rs) =
      match alg.step s (some r) with
      | (s', some o) => o :: alg.runAll s' rs
      | (s', none) => alg.runAll s' rs := rfl

@[simp] theorem runAll_cons_some (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (o : β) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', some o)) :
    alg.runAll s (r :: rs) = o :: alg.runAll s' rs := by
  rw [runAll_cons, h]

@[simp] theorem runAll_cons_none (alg : OnlineAlgorithm α σ β)
    (s s' : σ) (r : α) (rs : List α)
    (h : alg.step s (some r) = (s', none)) :
    alg.runAll s (r :: rs) = alg.runAll s' rs := by
  rw [runAll_cons, h]

end OnlineAlgorithm

variable {α F : Type*}

/-- `c`-competitive for a maximization objective. -/
def IsCompetitiveMax [Mul F] [LE F] (value opt : List α → F) (c : F) : Prop :=
  ∀ reqs, c * opt reqs ≤ value reqs

/-- `c`-competitive for a minimization objective. -/
def IsCompetitiveMin [Mul F] [LE F] (value opt : List α → F) (c : F) : Prop :=
  ∀ reqs, value reqs ≤ c * opt reqs

namespace Secretary

/-- A candidate revealed online with an identifier and score. -/
structure Candidate (Id Score : Type*) where
  id : Id
  score : Score

/-- A secretary algorithm observes candidates and may stop with one candidate. -/
abbrev Algorithm (Id Score State : Type*) :=
  OnlineAlgorithm (Candidate Id Score) State (Candidate Id Score)

/-- Offline benchmark: a selected candidate is optimal in the observed stream. -/
def IsOfflineBest {Id Score : Type*} [LE Score]
    (c : Candidate Id Score) (cs : List (Candidate Id Score)) : Prop :=
  c ∈ cs ∧ ∀ d ∈ cs, d.score ≤ c.score

end Secretary

namespace Prophet

/-- One online reward observation. -/
structure Observation (Ω Reward : Type*) where
  outcome : Ω
  reward : Reward

/-- A prophet-style stopping algorithm may accept one observation. -/
abbrev Algorithm (Ω Reward State : Type*) :=
  OnlineAlgorithm (Observation Ω Reward) State (Observation Ω Reward)

/-- Offline benchmark: an accepted observation has maximum realized reward. -/
def IsRealizedMax {Ω Reward : Type*} [LE Reward]
    (o : Observation Ω Reward) (obs : List (Observation Ω Reward)) : Prop :=
  o ∈ obs ∧ ∀ p ∈ obs, p.reward ≤ o.reward

end Prophet

namespace AdWords

/-- An online ad request carrying a query and bidder-indexed bids. -/
structure Request (Query Bidder Money : Type*) where
  query : Query
  bid : Bidder → Money

/-- Allocation decision for one request: either no sale or a chosen bidder. -/
abbrev Allocation (Bidder : Type*) := Option Bidder

/-- Remaining-budget state for AdWords-style allocation. -/
abbrev BudgetState (Bidder Money : Type*) := Bidder → Money

/-- An AdWords algorithm emits one allocation decision per request. -/
abbrev Algorithm (Query Bidder Money State : Type*) :=
  OnlineAlgorithm (Request Query Bidder Money) State (Allocation Bidder)

/-- A streaming allocation has the same length as the request stream. -/
def IsCompleteAllocation {Query Bidder Money : Type*}
    (reqs : List (Request Query Bidder Money)) (allocs : List (Allocation Bidder)) : Prop :=
  allocs.length = reqs.length

end AdWords

end Math.OnlineAlgorithms
