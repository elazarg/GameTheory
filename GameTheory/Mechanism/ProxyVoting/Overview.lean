/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.Counterexamples
import GameTheory.Mechanism.ProxyVoting.FollowerPNE
import GameTheory.Mechanism.ProxyVoting.Example3
import GameTheory.Mechanism.ProxyVoting.AppendixA
import GameTheory.Mechanism.ProxyVoting.AppendixB
import GameTheory.Mechanism.ProxyVoting.TieBreak
import GameTheory.Mechanism.ProxyVoting.Preferences

/-!
# Strategic Proxy Voting — formalization overview

This module contains no declarations.  It is the reading entry point for the
proxy-voting development: a formalization of the median and weighted-median
voting rules under proxy (one-step) delegation, for voters with single-peaked
preferences on the real line, under both complete and partial information.  It
maps the model definitions, the theorems, and the machine-checked
counterexamples to their homes, so the development can be read against the
source material paragraph by paragraph.

The full development rests on `GameTheory.Mechanism.EuclideanPreference`,
`GameTheory.Mechanism.MedianVoter`, `Math.WeightedMedian`, and
`Math.WindowedContraction`.

## Module map

* `ProxyVoting` — the model: `delegate`, `socialMedian`, `winner`, `outcome`,
  the single-peaked comparisons `SPPrefers`/`SPWeaklyPrefers`, delegate-cell
  geometry, and the follower/proxy strategyproofness results (Lemma 1,
  Theorems 1–2).
* `Dynamics` — better responses, monotone dynamics, distance-progress lemmas,
  and the windowed-contraction convergence theorem.
* `Bounded` / `TruthOriented` / `PeakAnchored` — the truth-oriented bounded
  dynamics (Theorem 3) and its band invariants.
* `PartialInformation` — information sets, dominating manipulations,
  strong-monotone dynamics, the regret calculus, and the minimax-regret
  characterization (Theorem 4).
* `Preferences` — the preference-parametric layer (results stated for arbitrary
  single-peaked, possibly asymmetric, proxy preferences).
* `TieBreak` — the tie-break-agnostic (`IsNearestSelector`) forms of Theorems
  1–2 and the follower band worst-case result.
* `Example3` / `Counterexamples` / `FollowerPNE` / `AppendixA` / `AppendixB` —
  the machine-checked witnesses (see below).

## Model definitions

* `delegate` — a follower delegates to the nearest proxy, ties broken by proxy
  order (Tullock delegation).
* `weight` / `IsWMWinner` / `allPos` — delegation weight, the weighted-median
  winner predicate, and the combined proxy⊕follower position family.
* `socialMedian` — the weighted median of the full population; `winner` — the
  proxy nearest to it; `outcome` — the winner's report; `socialCost` — the sum
  of distances.
* `SPPrefers` / `SPWeaklyPrefers` — the strict/weak comparisons forced by
  single-peakedness; `Prefers` (in `EuclideanPreference`) — Euclidean distance
  from a peak.
* `IsBetterResponse` / `IsPNE` — a report that changes the outcome without
  being single-peaked-dominated, and a pure Nash equilibrium of the proxy game.
* `MonotoneReport` / `SameSide` / `MonotoneStep` / `IsMonotoneDynamics` — the
  same-side monotonicity structure on reports and dynamics.
* `winnerInfoSet` / `historyInfoSet` — the follower profiles consistent with an
  observed winner, and with a whole observation history.
* `DominatesOver` / `IsDominatingManipulation` — a report that is weakly at
  least as good on every consistent profile and strictly better on one.
* `StrongMonotoneOver` / `WeakStrongMonotoneOver` and their dynamics — reports
  that stay strictly / weakly on the current report's side of every consistent
  median.
* `regret` / `maxRegretOver` / `IsMinimaxRegret` — ex-post regret against the
  best attainable outcome, its supremum over the information set, and a report
  minimizing that supremum.
* `BetterResponseStep` / `ReachesFromTruth` / `IsReachablePNEOutcome` — the
  better-response reachability relation from the truthful state, and the
  outcomes realized at reachable equilibria.

## Theorems

Entries note the hypotheses the Lean statement carries.

* `winner_isWMWinner` (Lemma 1) — the proxy nearest the population median is a
  weighted-median winner; weighted medians form an interval and `winner` selects
  one canonically.
* `follower_strategyproof` (Theorem 1) — no follower has a beneficial misreport;
  `follower_strategyproof_of_nearestSelector` gives the tie-break-agnostic form.
* `proxy_manipulation_iff` (Theorem 2) — a proxy has a manipulation in the
  truthful state iff no proxy sits at the median and proxies straddle it;
  `proxy_manipulation_iff_of_singlePeaked` states it for arbitrary single-peaked
  preferences, `proxy_manipulation_iff_of_nearestSelector` for any nearest
  selector.
* `socialMedian_eq_of_isMonotoneDynamics` (Observation 1) — monotone play fixes
  the population median.
* `monotoneStep_dist_le` / `monotoneStep_dist_lt` (Lemma 3) — a monotone
  non-winner better response never increases the distance to the median, and
  strictly decreases it under a no-mirror-tie hypothesis.
* `metaMove_dist_le` / `metaMove_dist_lt` (Lemma 4) — the analogous weak bound
  over a meta-move, with strict decrease under no-mirror-tie and peak
  separation.
* `tendsto_outcome_of_windowed_contraction` (convergence) — the outcome
  converges to the median under an explicit windowed fixed-factor contraction
  premise; `tendsto_outcome_of_weakStrongMonotone_windowed_contraction` and its
  history form give the partial-information versions;
  `eventually_outcome_eq_socialMedian_of_integral_nonWinnerTieFree_dynamics` is
  the discrete one-step form (integral, no-mirror-tie).
* `strongBandInvariant_of_isTruthOrientedDynamics` and
  `median_and_outcome_mem_band_of_isTruthOrientedDynamics` (Theorem 3, Cor. 1)
  — truth-oriented better-response dynamics keep the median and outcome within
  the `Δ`-band around the true median.
* `isMinimaxRegret_iff_eq_left_boundary` / `_right_boundary` (Theorem 4) — for a
  non-winning proxy with peak outside the winner interval and the far endpoint
  past the near-endpoint/winner midpoint, the minimax-regret report is the near
  boundary of the possible-median interval.
* `isMinimaxRegret_report_le_socialMedian` — a minimax-regret report stays
  weakly on the peak's side of the median (the same-side conclusion).
* `isMinimaxRegret_dominatesOver_leftBoundary` / `_right` — a boundary
  minimax-regret report is a dominating manipulation in those regimes.
* `isMinimaxRegret_winner_stay` — a winner off its peak stays put optimally when
  no other report lies strictly inside the reflected interval and a report sits
  at the reflected far boundary.
* `not_dominatesOver_univ_of_truthful` — with no information beyond the truthful
  state (follower majority, distinct peaks), truthful reporting admits no
  dominating manipulation.
* `dominatesOver_left_side_set_eq_Ioo` / `_right_side_set_eq_Ioo` — the exact
  open-interval characterization of a non-winning proxy's dominating
  manipulations, with endpoints at the reflected boundaries.
* `image_socialMedian_winnerInfoSet` / `historyInfoSet_succ` /
  `image_socialMedian_historyInfoSet` — the possible-median interval and its
  refinement along a history; `StrongMonotoneOver.report_le_socialMedian` is the
  side-preservation refinement step.

## Machine-checked counterexamples

Each is a finite, fully-evaluated instance establishing that a hypothesis is
necessary or that a natural strengthening is false.

* `paperDisplayWeightedMedian_rejects_duplicate_median` — the weak-inequality,
  exclude-self weighted-median formula rejects a triply-repeated position that
  the strict-side definition selects.
* `monotoneStep_not_dist_lt_with_mirror_tie` — a monotone non-winner better
  response can preserve the outcome distance across a mirror tie (also with
  integral data).
* `integral_monotoneStep_not_dist_add_one_le_without_noMirrorTie` /
  `integral_truthful_monotoneStep_hits_mirrorTie` — the integer `+1`-decrease
  can fail, and a mirror tie can arise immediately from a truthful integral
  state with distinct peaks.
* `metaMove_not_dist_lt_without_peak_separation` — a meta-move can finish at the
  old winning distance when the mover's peak lies inside the winner interval.
* `strongBandInvariant_does_not_refute_bandViolatingReports` /
  `weakBandForcingCounterexample_truth_not_weaklyBest` — a band-violating report
  can be strictly beneficial, and the winner-drift clause is load-bearing for
  the bounded-dynamics argument.
* `insidePeak_boundary_not_isMinimaxRegret` / `midBreak_boundary_not_isMinimaxRegret`
  / `knownMedian_no_isMinimaxRegret` — the peak-outside, median-midpoint, and
  uncertainty-spread hypotheses of the boundary minimax theorem are each
  necessary.
* `winnerStay_not_isMinimaxRegret` — a winner staying put is not minimax-regret
  when a runner-up sits strictly between its reflected peak and its report.
* `paperBaseInterval_endpoints_reversed` / `paperMinEndpoint_report_not_dominates`
  / `moveRight_socialMedian_lt` — the possible-median base interval endpoints,
  the lower endpoint of the dominating-manipulation interval, and the
  winner-moved half-line refinement rule each require correction.
* `example3_strongMonotone_not_tendsto` / `example3_no_identity_windowed_contraction`
  — an infinite strong-monotone better-response dynamics with the median
  preserved whose outcome distance stays above `1/2`, and which admits no fixed
  contraction factor.
* `minimaxTrap_minimaxRegretInfo_not_tendsto` — active minimax-regret play over
  a nested, true-containing information-set sequence whose outcome does not
  converge to the true median.
* `socialCost_and_median_distance_diverge` — an outcome closer to the true
  median than the truthful one yet with strictly higher social cost.
* `appendixA_integer_pne` / `appendixA_not_pne_real` / `appendixA_socialCost` —
  a socially worse (cost `86 > 84`) integer pure equilibrium that is not an
  equilibrium over `ℝ`.
* `appendixB_left_has_no_dominating` / `appendixB_outcome_stuck` /
  `appendixB_socialCost` — a dominating-manipulation dynamics whose outcome is
  pinned at a socially worse (cost `235 > 210`) value.
* `realTruthMinusTwo_gridPNE_not_realPNE` / `realMisreportOne_gridPNE_not_realPNE`
  — over `ℝ`, states that are pure equilibria among integer reports admit
  non-integer better responses.

## Reusable, domain-general components

These carry no proxy-voting dependency and are usable elsewhere.

* `Math.WeightedMedian` — the canonical weighted median on a `Fintype`, with
  existence, majority characterization, monotonicity, single-coordinate
  immunity, and the median strategyproofness core.
* `Math.WindowedContraction` — a nonnegative sequence contracted on each window
  tends to zero, with fixed-factor, variable-factor, and harmonic-factor forms,
  a discrete descent version, and a sharpness counterexample.
* `abs_right_sub_le_abs_left_sub_iff` and its three siblings (in `ProxyVoting`)
  — which of two ordered points is nearer a target, in terms of the midpoint.
* `setOf_delegate_eq_eq_Ioo_of_neighbor_bounds` and its `Icc`/`Ico`/`Ioc`
  variants — the interval structure of nearest-neighbor cells on the line under
  an order tie-break.
-/
