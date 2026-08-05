/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticEndpointAtlas
import GameTheory.Concepts.Stochastic.PlayerNeutralStrictSetDeflation

/-!
# Operational deflation in the player-neutral full-support branch

A reachable recurrent class with full active state support cannot decrease
the state-support coordinate.  The strict leading drift that precedes this
branch nevertheless deletes a nonempty finite set of operational columns.
Consequently a third, operational-family coordinate decreases strictly even
when both harmonic rank and state-support rank remain unchanged.

The same deleted set has sublinear expected pure use and predictable mixed
mass under every source-compatible implementation.  Thus the analytic
deflation step has both ingredients needed for well-founded bookkeeping:

* a strict finite rank decrease on the retained operational family;
* a sublinear account for the exceptional family removed at the step.

This resolves the combinatorial stagnation of the full-support analytic
branch.  It does not identify the child's whole payoff-vector target,
construct a legal public entry into the residual problem, or prove
punishment credibility.  Those are strategic reconstruction obligations,
not rank defects.

An isolated full-support circulation need not carry such a decrease.  The
decrease here uses information present in the actual analytic atlas leaf:
the full-support class is reached only after a strict leading-drift
certificate has removed its nonempty exceptional set.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

/-- Harmonic rank, state-support rank, and retained operational-family
cardinality, ordered lexicographically in that order. -/
abbrev AnalyticEndpointDeflationRank := ℕ × (ℕ × ℕ)

/-- Lexicographic order on the three finite endpoint coordinates. -/
def AnalyticEndpointDeflationRankLt :
    AnalyticEndpointDeflationRank →
      AnalyticEndpointDeflationRank → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

/-- The three-coordinate endpoint rank is well founded. -/
theorem analyticEndpointDeflationRankLt_wellFounded :
    WellFounded AnalyticEndpointDeflationRankLt :=
  wellFounded_lt.prod_lex
    (wellFounded_lt.prod_lex wellFounded_lt)

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ who, Fintype (G.Act who)]
  [∀ who, DecidableEq (G.Act who)]

namespace AnalyticBellmanGerm

local instance fullSupportDeflationIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

variable {germ : G.AnalyticBellmanGerm}
  {span : germ.EndpointHarmonicJetSpan}
  {entry : G.State}

omit [DecidableEq G.State] in
/-- A new harmonic direction decreases the first coordinate of the common
three-coordinate rank. -/
theorem HarmonicRankDecreaseData.deflationRankDecrease
    (data : HarmonicRankDecreaseData germ span)
    (childSupport parentSupport childOperational
      parentOperational : ℕ) :
    AnalyticEndpointDeflationRankLt
      ((span.extend data.direction data.harmonic).rank,
        (childSupport, childOperational))
      (span.rank, (parentSupport, parentOperational)) :=
  Prod.Lex.left
    (childSupport, childOperational)
    (parentSupport, parentOperational)
    data.decrease

/-- A proper recurrent support decreases the second coordinate of the
common rank, independently of both operational-family cardinalities. -/
theorem PlayerNeutralProperSupportData.deflationRankDecrease
    (data : PlayerNeutralProperSupportData germ entry)
    (childOperational parentOperational : ℕ) :
    AnalyticEndpointDeflationRankLt
      (span.rank,
        (data.reachable.positiveClass.supportRank,
          childOperational))
      (span.rank,
        (data.reachable.circulation.activeSupportRank,
          parentOperational)) :=
  Prod.Lex.right span.rank
    (Prod.Lex.left childOperational parentOperational
      data.proper.2)

namespace PlayerNeutralFullSupportData

/-- The ambient operational node before the strict leading-drift
deflation. -/
def parentOperationalState
    (data : PlayerNeutralFullSupportData germ entry) :
    FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex data.who) :=
  PlayerNeutralStrictLeadingDrift.fullDeflationState

/-- The retained zero-drift operational node. -/
def childOperationalState
    (data : PlayerNeutralFullSupportData germ entry) :
    FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex data.who) :=
  data.drift.drift.zeroDriftDeflationState

/-- The exceptional operational set deleted before entering the
full-support residual branch is nonempty. -/
theorem deletedOperationalSet_nonempty
    (data : PlayerNeutralFullSupportData germ entry) :
    data.drift.drift.strictIndexSet.Nonempty :=
  data.drift.drift.strictIndexSet_nonempty

/-- Full state support does not prevent a genuine operational-family
deflation. -/
theorem childOperationalState_deflates
    (data : PlayerNeutralFullSupportData germ entry) :
    data.childOperationalState.Deflates
      data.parentOperationalState :=
  data.drift.drift.zeroDriftDeflationState_deflates

/-- The retained operational-family cardinality is strictly smaller. -/
theorem childOperationalRank_lt
    (data : PlayerNeutralFullSupportData germ entry) :
    data.childOperationalState.rank <
      data.parentOperationalState.rank :=
  FiniteDeflationState.rankLt_of_deflates
    data.childOperationalState_deflates

/-- In the full-state-support branch, the third coordinate supplies the
strict descent that the first two coordinates cannot provide. -/
theorem deflationRankDecrease
    (data : PlayerNeutralFullSupportData germ entry) :
    AnalyticEndpointDeflationRankLt
      (span.rank,
        (data.reachable.positiveClass.supportRank,
          data.childOperationalState.rank))
      (span.rank,
        (data.reachable.circulation.activeSupportRank,
          data.parentOperationalState.rank)) := by
  rw [data.fullSupport.2.1]
  exact
    Prod.Lex.right span.rank
      (Prod.Lex.right
        data.reachable.circulation.activeSupportRank
        data.childOperationalRank_lt)

/-- Pure use of every operational column deleted by the full-support
deflation is sublinear in expectation. -/
theorem deletedExpectedUse_isAsymptoticallySublinear
    (data : PlayerNeutralFullSupportData germ entry)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex data.who)
    (sourceCompatible :
      ∀ n history,
        germ.playerNeutralOccupationSource data.who
            (choice n history) =
          history (Fin.last n)) :
    IsAsymptoticallySublinear
      (data.drift.drift.strictSetExpectedUse initial choice) :=
  data.drift.drift.strictSetExpectedUse_isAsymptoticallySublinear
    initial choice sourceCompatible

/-- Predictable behavioral mass assigned to every deleted operational
column is sublinear in expectation. -/
theorem deletedExpectedMass_isAsymptoticallySublinear
    (data : PlayerNeutralFullSupportData germ entry)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex data.who))
    (sourceCompatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource data.who index =
            history (Fin.last n)) :
    IsAsymptoticallySublinear
      (data.drift.drift.strictSetExpectedMass initial selection) :=
  data.drift.drift.strictSetExpectedMass_isAsymptoticallySublinear
    initial selection sourceCompatible

/-- Every path contribution uniformly dominated by deleted-column use has
a sublinear expected absolute value. -/
theorem deletedUseContribution_isAsymptoticallySublinear
    (data : PlayerNeutralFullSupportData germ entry)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex data.who)
    (sourceCompatible :
      ∀ n history,
        germ.playerNeutralOccupationSource data.who
            (choice n history) =
          history (Fin.last n))
    (contribution : ∀ T, (Fin (T + 1) → G.State) → ℝ)
    (L : ℝ)
    (dominated :
      ∀ T history,
        |contribution T history| ≤
          L *
            ∑ index :
                {index // index ∈ data.drift.drift.strictIndexSet},
              selectedTransitionUseCount choice index.1 T history) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison
                (germ.playerNeutralOccupationKernel data.who)
                choice))
            (T + 1))
          (fun history => |contribution T history|)) :=
  data.drift.drift.strictSetUseContribution_isAsymptoticallySublinear
    initial choice sourceCompatible contribution L dominated

/-- Every path contribution uniformly dominated by deleted-column
predictable mass has a sublinear expected absolute value. -/
theorem deletedMassContribution_isAsymptoticallySublinear
    (data : PlayerNeutralFullSupportData germ entry)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex data.who))
    (sourceCompatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource data.who index =
            history (Fin.last n))
    (contribution : ∀ T, (Fin (T + 1) → G.State) → ℝ)
    (L : ℝ)
    (dominated :
      ∀ T history,
        |contribution T history| ≤
          L *
            ∑ index :
                {index // index ∈ data.drift.drift.strictIndexSet},
              selectedTransitionMassSum
                selection index.1 T history) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison
                (germ.playerNeutralOccupationKernel data.who)
                selection))
            (T + 1))
          (fun history => |contribution T history|)) :=
  data.drift.drift.strictSetMassContribution_isAsymptoticallySublinear
    initial selection sourceCompatible contribution L dominated

end PlayerNeutralFullSupportData
end AnalyticBellmanGerm

end StochasticGame
end GameTheory
