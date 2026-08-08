/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.AnalyticDeflationTerminal
import Math.Probability.HarmonicStateAccount
import Math.Probability.AnalyticOccupationDeflationTraceRank

/-!
# The exact account carried by a terminal zero pairing

A player-neutral zero-pairing terminal supplies a nonzero state potential
which is harmonic for every surviving active occupation kernel.  Therefore,
along any source-compatible sequence of surviving kernels, the observed
successor-versus-kernel discrepancy is the increment of the state-potential
account.  Since the state space is finite, this is a bounded realized account
and its cumulative discrepancy is asymptotically sublinear.

This is an account for the observed residual transition discrepancy, not for
the terminal's positive strategic response charge.  The repaired terminal
provenance makes the distinction exact: the named positive response is a
surviving active index, so its endpoint drift against the leading potential
is zero by active harmonicity, while its strategic charge is strictly
positive.  Thus those two quantities cannot be identified.

The deflation trace gives a second exact boundary: either it is stationary at
the initial active set, or its terminal active-set rank is strictly smaller.
Zero pairing itself does not rule out the stationary case.
-/

noncomputable section

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

/-- Provenance repair: the named positive response is represented by a
surviving active index. -/
theorem response_mem_terminal
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor) :
    Sum.inr data.response ∈ data.terminal.active := by
  rw [← data.responseIndex_eq]
  exact data.responseIndex.2

/-- The active harmonic identity annihilates the endpoint drift of the named
positive response.  In particular, this drift cannot equal its strictly
positive strategic charge. -/
theorem response_leadingDrift_eq_zero
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor) :
    expect data.response.kernel data.leadingPotential -
      data.leadingPotential data.response.source = 0 := by
  have harmonic := data.active_harmonic data.responseIndex
  rw [data.responseIndex_eq] at harmonic
  simpa only [leadingPotential,
    playerNeutralOccupationKernel,
    playerNeutralOccupationSource] using harmonic

/-- The positive strategic response charge is not controlled by its zero
endpoint leading-potential drift. -/
theorem responseCharge_not_le_leadingDrift
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor) :
    ¬germ.neutralActionCharge B who data.response ≤
      expect data.response.kernel data.leadingPotential -
        data.leadingPotential data.response.source := by
  rw [data.response_leadingDrift_eq_zero]
  exact not_le_of_gt data.responseCharge_pos

/-- The named positive response charge cannot itself be a recurring bounded
account increment.  Hence the leading residual-discrepancy account above
cannot discharge the response; a different higher-order or stage-gain
mechanism is required. -/
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
