/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralAnalyticDeflationTerminal
import Math.Probability.HarmonicStateAccount

/-!
# The exact account carried by a terminal zero pairing

A player-neutral zero-pairing terminal supplies a nonzero state potential
which is harmonic for every surviving active occupation kernel.  Therefore,
along any source-compatible sequence of surviving kernels, the observed
successor-versus-kernel discrepancy is the increment of the state-potential
account.  Since the state space is finite, this is a bounded realized account
and its cumulative discrepancy is asymptotically sublinear.

This is an account for the observed residual transition discrepancy, not for
the terminal's positive strategic response charge.  In fact, the same
terminal datum proves that its positive response charge, if incurred at every
stage, cannot be realized by any bounded account.  Thus an identification of
the strategic charge with the observed discrepancy remains indispensable.

The deflation trace gives a second exact boundary: either it is stationary at
the initial active set, or its terminal active-set rank is strictly smaller.
Zero pairing itself does not rule out the stationary case.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability
namespace AnalyticOccupationDeflationTrace

/-- A zero-length analytic deflation trace is reflexive. -/
theorem initial_eq_terminal_of_length_eq_zero
    {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {anchor : S}
    {initial terminal : FiniteDeflationState I}
    (trace :
      AnalyticOccupationDeflationTrace
        column charge anchor initial terminal)
    (length_eq_zero : trace.length = 0) :
    initial = terminal := by
  cases trace with
  | refl _ =>
      rfl
  | strict next strict_nonempty tail =>
      simp only [length] at length_eq_zero
      omega

/-- A deflation trace either makes no move or strictly lowers active-set
rank.  This packages the strongest unconditional rank information carried
by the trace. -/
theorem initial_eq_terminal_or_terminal_rank_lt
    {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {anchor : S}
    {initial terminal : FiniteDeflationState I}
    (trace :
      AnalyticOccupationDeflationTrace
        column charge anchor initial terminal) :
    initial = terminal ∨ terminal.rank < initial.rank := by
  by_cases length_eq_zero : trace.length = 0
  · exact Or.inl
      (trace.initial_eq_terminal_of_length_eq_zero length_eq_zero)
  · right
    have length_pos : 0 < trace.length :=
      Nat.pos_of_ne_zero length_eq_zero
    have rank_bound :=
      trace.terminal_rank_add_length_le_initial_rank
    omega

end AnalyticOccupationDeflationTrace
end Probability
end Math

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace PlayerNeutralZeroPairingTerminalData

open Math Math.Probability

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}
  {B : G.State → Payoff ι} {who : ι}
  {initial :
    FiniteDeflationState (germ.PlayerNeutralOccupationIndex who)}
  {terminalAnchor : G.State}

local instance terminalAccountIndexDecidableEq :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

/-- The nonzero leading state potential exposed by the terminal zero
pairing. -/
def leadingPotential
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor) :
    G.State → ℝ :=
  data.next.gaugeFixedJet.factor 0

/-- Evaluate the terminal leading potential along a realized state path. -/
def leadingAccount
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor)
    (path : ℕ → G.State) : ℕ → ℝ :=
  statePotentialAccount data.leadingPotential path

/-- The observed residual discrepancy for a time-indexed selection of
surviving active kernels. -/
def activeObservedCharge
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor)
    (choice : ℕ → data.terminal.ActiveIndex)
    (path : ℕ → G.State) (t : ℕ) : ℝ :=
  data.leadingPotential (path (t + 1)) -
    expect
      (germ.playerNeutralOccupationKernel who (choice t).1)
      data.leadingPotential

/-- The terminal leading potential is genuinely nonzero. -/
theorem leadingPotential_ne_zero
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor) :
    data.leadingPotential ≠ 0 := by
  simpa [leadingPotential] using data.leadingPotential_nonzero

/-- Source compatibility turns the observed active-kernel discrepancy into
the exact increment of the terminal state-potential account. -/
theorem activeObservedCharge_isRealizedByAccount
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor)
    (choice : ℕ → data.terminal.ActiveIndex)
    (path : ℕ → G.State)
    (source_compatible :
      ∀ t,
        germ.playerNeutralOccupationSource who (choice t).1 =
          path t) :
    IsRealizedByAccount
      (data.activeObservedCharge choice path)
      (data.leadingAccount path) := by
  intro t
  have harmonic := data.active_harmonic (choice t)
  rw [source_compatible t] at harmonic
  have harmonic' :
    expect
        (germ.playerNeutralOccupationKernel who (choice t).1)
        data.leadingPotential -
      data.leadingPotential (path t) = 0 := by
    simpa [leadingPotential] using harmonic
  change
    data.leadingPotential (path (t + 1)) -
        expect
          (germ.playerNeutralOccupationKernel who (choice t).1)
          data.leadingPotential =
      data.leadingPotential (path (t + 1)) -
        data.leadingPotential (path t)
  linarith

/-- The terminal leading account is uniformly bounded on every path. -/
theorem abs_leadingAccount_le
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor)
    (path : ℕ → G.State) (t : ℕ) :
    |data.leadingAccount path t| ≤
      finiteStatePotentialBound data.leadingPotential :=
  abs_statePotentialAccount_le_finiteStatePotentialBound
    data.leadingPotential path t

/-- The realized cumulative active discrepancy is asymptotically sublinear
for every source-compatible schedule of surviving kernels. -/
theorem activeObservedCharge_cumulative_isAsymptoticallySublinear
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor)
    (choice : ℕ → data.terminal.ActiveIndex)
    (path : ℕ → G.State)
    (source_compatible :
      ∀ t,
        germ.playerNeutralOccupationSource who (choice t).1 =
          path t) :
    IsAsymptoticallySublinear
      (fun T =>
        ∑ t ∈ Finset.range T,
          data.activeObservedCharge choice path t) :=
  (data.activeObservedCharge_isRealizedByAccount
      choice path source_compatible).cumulative_isAsymptoticallySublinear
    (data.abs_leadingAccount_le path)

/-- Exact structural information in the terminal trace: either no active-set
move occurred, or the terminal active-set rank strictly decreased. -/
theorem initial_eq_terminal_or_terminal_rank_lt
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor) :
    initial = data.terminal ∨ data.terminal.rank < initial.rank :=
  data.trace.initial_eq_terminal_or_terminal_rank_lt

/-- The named positive response charge cannot itself be a recurring bounded
account increment.  Hence the residual discrepancy account above does not
discharge the response without an additional charge-identification theorem. -/
theorem no_boundedAccount_realizes_constant_responseCharge
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor) :
    ¬∃ (account : ℕ → ℝ) (bound : ℝ),
      (∀ t, |account t| ≤ bound) ∧
        IsRealizedByAccount
          (fun _ => germ.neutralActionCharge B who data.response)
          account := by
  rintro ⟨account, bound, account_bounded, realized⟩
  let responseCharge :=
    germ.neutralActionCharge B who data.response
  have responseCharge_pos : 0 < responseCharge :=
    data.responseCharge_pos
  obtain ⟨T, hT⟩ :=
    exists_nat_gt ((2 * bound) / responseCharge)
  have cumulative_bound :=
    realized.abs_sum_range_le_two_mul account_bounded T
  have linear_bound :
      (T : ℝ) * responseCharge ≤ 2 * bound := by
    simpa [responseCharge,
      abs_of_nonneg
        (show (0 : ℝ) ≤ (T : ℝ) from Nat.cast_nonneg T),
      abs_of_pos responseCharge_pos] using cumulative_bound
  have exceeds :
      2 * bound < (T : ℝ) * responseCharge := by
    exact (div_lt_iff₀ responseCharge_pos).mp hT
  exact (not_lt_of_ge linear_bound) exceeds

end PlayerNeutralZeroPairingTerminalData
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
