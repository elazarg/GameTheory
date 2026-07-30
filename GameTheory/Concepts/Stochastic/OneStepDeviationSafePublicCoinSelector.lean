/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicFixedDepthApproximateTargetCertificate

/-!
# One-step deviation-safe public-child selection

This file constructs a concrete `DeviationSafePublicCoinSelector` from an
action-independent one-step public transition.

The initial state is the only nonterminal selector state.  Every other state
is terminal and absorbing under every joint action.  The common transition
law from the initial state is supported on terminal states, and a public
observation maps those states to a finite child type.

The global absorption hypothesis is not cosmetic.  The existing
`DeviationSafePublicCoinSelector` requires equality with the stopped kernel
at every game state, including states unreachable from the chosen initial
state.  A merely local construction would instead produce only a
`FinitePublicCoinStoppingRegion`.

The support condition also rules out a positive self-loop at the
nonterminal initial state.  This consequence is proved explicitly below;
it is the corner case needed for the rank-one/rank-zero process.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.OutcomeClosure Math.Probability
  Math.ProbabilityMassFunction
open FixedDepthAdaptivePotentialSplice

variable {ι Child : Type} {G : StochasticGame ι}

/-- Explicit finite data for one action-independent public draw followed by
globally absorbing terminal states. -/
structure OneStepDeviationSafePublicCoinData
    (G : StochasticGame ι) (Child : Type) where
  initial : G.State
  kernel : PMF G.State
  terminal : G.State → Prop
  observe : G.State → Child
  initial_nonterminal : ¬ terminal initial
  terminal_or_initial : ∀ state, terminal state ∨ state = initial
  kernel_support_terminal :
    ∀ state, kernel state ≠ 0 → terminal state
  transition_initial :
    ∀ action, G.transition initial action = kernel
  transition_terminal :
    ∀ state, terminal state →
      ∀ action, G.transition state action = PMF.pure state

namespace OneStepDeviationSafePublicCoinData

variable (data : OneStepDeviationSafePublicCoinData G Child)

/-- The common draw cannot put positive mass back on the nonterminal
initial state. -/
theorem kernel_apply_initial_eq_zero :
    data.kernel data.initial = 0 := by
  by_contra nonzero
  exact data.initial_nonterminal
    (data.kernel_support_terminal data.initial nonzero)

/-- Selector rank: one at the unique nonterminal state and zero at every
terminal state. -/
def rank (state : G.State) : ℕ := by
  classical
  exact if data.terminal state then 0 else 1

/-- Semantic terminal-child law.  At a terminal state it is the observed
point mass; at the unique nonterminal state it is the observation of the
common public draw. -/
def value (state : G.State) : PMF Child := by
  classical
  exact
    if data.terminal state then
      PMF.pure (data.observe state)
    else
      PMF.map data.observe data.kernel

/-- The rank-one/rank-zero semantic value process associated with the
one-step public draw. -/
def process : OutcomeClosure.ValueProcess G.State Child := by
  classical
  refine {
    terminal := data.terminal
    step := fun _ => data.kernel
    rank := rank data
    observe := data.observe
    value := value data
    terminal_of_rank_zero := ?_
    terminal_value := ?_
    step_value := ?_
    step_rank := ?_
  }
  · intro state rank_zero
    by_contra nonterminal
    change (if data.terminal state then 0 else 1) = 0 at rank_zero
    simp [nonterminal] at rank_zero
  · intro state terminal
    change
      (if data.terminal state then
          PMF.pure (data.observe state)
        else PMF.map data.observe data.kernel) =
        PMF.pure (data.observe state)
    simp [terminal]
  · intro state nonterminal
    have state_eq : state = data.initial := by
      rcases data.terminal_or_initial state with terminal | equal
      · exact False.elim (nonterminal terminal)
      · exact equal
    subst state
    change
      data.kernel.bind (value data) =
        (if data.terminal data.initial then
            PMF.pure (data.observe data.initial)
          else PMF.map data.observe data.kernel)
    rw [if_neg data.initial_nonterminal]
    rw [← PMF.bind_pure_comp]
    apply bind_congr_on_support
    intro successor successor_mem
    have successor_terminal :
        data.terminal successor := by
      apply data.kernel_support_terminal successor
      simpa [PMF.mem_support_iff] using successor_mem
    change
      (if data.terminal successor then
          PMF.pure (data.observe successor)
        else PMF.map data.observe data.kernel) =
        PMF.pure (data.observe successor)
    simp [successor_terminal]
  · intro state successor nonterminal successor_mass
    have state_eq : state = data.initial := by
      rcases data.terminal_or_initial state with terminal | equal
      · exact False.elim (nonterminal terminal)
      · exact equal
    have successor_terminal :
        data.terminal successor :=
      data.kernel_support_terminal successor successor_mass
    subst state
    change
      (if data.terminal successor then 0 else 1) + 1 =
        if data.terminal data.initial then 0 else 1
    simp [data.initial_nonterminal, successor_terminal]

/-- The semantic value at the initial state is exactly the observed common
kernel. -/
@[simp]
  theorem process_value_initial :
    data.process.value data.initial =
      PMF.map data.observe data.kernel := by
  classical
  change
    (if data.terminal data.initial then
        PMF.pure (data.observe data.initial)
      else PMF.map data.observe data.kernel) =
      PMF.map data.observe data.kernel
  simp [data.initial_nonterminal]

/-- The initial selector rank is exactly one. -/
@[simp]
theorem process_rank_initial :
    data.process.rank data.initial = 1 := by
  classical
  change (if data.terminal data.initial then 0 else 1) = 1
  simp [data.initial_nonterminal]

/-- Every terminal selector state has rank zero. -/
theorem process_rank_eq_zero_of_terminal
    {state : G.State} (terminal : data.terminal state) :
    data.process.rank state = 0 := by
  classical
  change (if data.terminal state then 0 else 1) = 0
  simp [terminal]

/-- The stopped process is realized by the actual game transition after
every joint action. -/
def selector : DeviationSafePublicCoinSelector G Child where
  process := data.process
  transition_eq_stoppedStep := by
    intro state action
    by_cases terminal : data.terminal state
    · rw [data.process.stoppedStep_terminal terminal]
      exact data.transition_terminal state terminal action
    · have state_eq : state = data.initial := by
        rcases data.terminal_or_initial state with isTerminal | equal
        · exact False.elim (terminal isTerminal)
        · exact equal
      subst state
      rw [data.process.stoppedStep_nonterminal
        data.initial_nonterminal]
      exact data.transition_initial action

/-- The child law selected from the initial state is the observation of the
common action-independent kernel. -/
@[simp]
theorem selector_value_initial :
    data.selector.process.value data.initial =
      PMF.map data.observe data.kernel :=
  data.process_value_initial

/-- A supplied terminal-entry identification is exactly the entry
compatibility required by the fixed-depth splice. -/
theorem selector_terminal_entry
    (entry : Child → G.State)
    (terminal_entry :
      ∀ state, data.terminal state →
        state = entry (data.observe state)) :
    ∀ state, data.selector.process.terminal state →
      state = entry (data.selector.process.observe state) := by
  intro state terminal
  exact terminal_entry state terminal

variable [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  [Finite Child]

/-- Exact expected target preservation under the common public draw,
together with child adaptive certificates at every positive accuracy,
constructs the parent adaptive certificate.

The behavior profile used during the one-step selector phase is arbitrary:
the selector's transition equality makes its terminal-child law invariant
under every unilateral deviation. -/
theorem isAdaptivePotentialCertificateAt_of_exactExpectedTarget
    (entry : Child → G.State)
    (target : Child → Payoff ι)
    (selection : G.BehaviorProfile)
    (parentTarget : Payoff ι)
    (error : ℝ) (error_pos : 0 < error)
    (terminal_entry :
      ∀ state, data.terminal state →
        state = entry (data.observe state))
    (exact_target :
      ∀ who,
        expect (PMF.map data.observe data.kernel)
            (fun child => target child who) =
          parentTarget who)
    (childCertificates :
      ∀ child childError, 0 < childError →
        G.IsAdaptivePotentialCertificateAt
          (entry child) (target child) childError) :
    G.IsAdaptivePotentialCertificateAt
      data.initial parentTarget error := by
  letI : Fintype Child := Fintype.ofFinite Child
  apply
    isAdaptivePotentialCertificateAt_of_fixedDepthSelector_allErrors
      (selector := data.selector)
      (entry := entry) (target := target)
      (initial := data.initial) (fuel := 1)
      selection parentTarget error error_pos
  · change data.process.rank data.initial ≤ 1
    rw [data.process_rank_initial]
  · exact data.selector_terminal_entry entry terminal_entry
  · intro who
    rw [data.selector_value_initial]
    exact exact_target who
  · exact childCertificates

/-- The same concrete one-step selector permits an approximate parent
target.  A mismatch of at most half the requested tolerance is absorbed by
the generic target-retargeting theorem. -/
theorem isAdaptivePotentialCertificateAt_of_approximateExpectedTarget
    (entry : Child → G.State)
    (target : Child → Payoff ι)
    (selection : G.BehaviorProfile)
    (parentTarget : Payoff ι)
    (error : ℝ) (error_pos : 0 < error)
    (terminal_entry :
      ∀ state, data.terminal state →
        state = entry (data.observe state))
    (target_close :
      ∀ who,
        |expect (PMF.map data.observe data.kernel)
            (fun child => target child who) -
          parentTarget who| ≤ error / 2)
    (childCertificates :
      ∀ child childError, 0 < childError →
        G.IsAdaptivePotentialCertificateAt
          (entry child) (target child) childError) :
    G.IsAdaptivePotentialCertificateAt
      data.initial parentTarget error := by
  letI : Fintype Child := Fintype.ofFinite Child
  apply
    FixedDepthAdaptivePotentialSplice.isAdaptivePotentialCertificateAt_of_approximateTarget
      (selector := data.selector)
      (entry := entry) (target := target)
      (initial := data.initial) (fuel := 1)
      selection parentTarget error error_pos
  · change data.process.rank data.initial ≤ 1
    rw [data.process_rank_initial]
  · exact data.selector_terminal_entry entry terminal_entry
  · intro who
    simpa using target_close who
  · exact childCertificates

end OneStepDeviationSafePublicCoinData
end StochasticGame
end GameTheory
