/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticEndpointAtlas
import Mathlib.Order.RelClasses

/-!
# A common rank for analytic endpoint descent

Two endpoint branches already carry strict finite decreases:

* a new harmonic direction decreases the remaining harmonic dimension;
* a proper recurrent class decreases active-support cardinality.

This file puts them into one well-founded lexicographic rank.  It also
proves that a full-support recurrent class is stagnant in both coordinates,
so this two-coordinate rank cannot silently close that branch.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

/-- Remaining harmonic dimension followed by active-support cardinality. -/
abbrev AnalyticEndpointLexRank := ℕ × ℕ

/-- Lexicographic descent: harmonic dimension is primary, support
cardinality is secondary. -/
def AnalyticEndpointLexRankLt :
    AnalyticEndpointLexRank → AnalyticEndpointLexRank → Prop :=
  Prod.Lex (· < ·) (· < ·)

/-- The combined endpoint rank is well founded. -/
theorem analyticEndpointLexRankLt_wellFounded :
    WellFounded AnalyticEndpointLexRankLt :=
  wellFounded_lt.prod_lex wellFounded_lt

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ who, Fintype (G.Act who)]
  [∀ who, DecidableEq (G.Act who)]

namespace AnalyticBellmanGerm

variable {germ : G.AnalyticBellmanGerm}
  {span : germ.EndpointHarmonicJetSpan}

omit [DecidableEq G.State] in
/-- A genuinely new harmonic direction decreases the primary coordinate,
independently of the child support size. -/
theorem HarmonicRankDecreaseData.lexRankDecrease
    (data : HarmonicRankDecreaseData germ span)
    (childSupport parentSupport : ℕ) :
    AnalyticEndpointLexRankLt
      ((span.extend data.direction data.harmonic).rank,
        childSupport)
      (span.rank, parentSupport) :=
  Prod.Lex.left childSupport parentSupport data.decrease

/-- A reachable proper-support class decreases the secondary coordinate
while the processed harmonic span is unchanged. -/
theorem PlayerNeutralProperSupportData.lexRankDecrease
    {entry : G.State}
    (data : PlayerNeutralProperSupportData germ entry) :
    AnalyticEndpointLexRankLt
      (span.rank, data.reachable.positiveClass.supportRank)
      (span.rank, data.reachable.circulation.activeSupportRank) :=
  Prod.Lex.right span.rank data.proper.2

/-- Full active support is stagnant in the combined rank when no new
harmonic direction is added. -/
theorem PlayerNeutralFullSupportData.not_lexRankDecrease
    {entry : G.State}
    (data : PlayerNeutralFullSupportData germ entry) :
    ¬AnalyticEndpointLexRankLt
      (span.rank, data.reachable.positiveClass.supportRank)
      (span.rank, data.reachable.circulation.activeSupportRank) := by
  rw [data.fullSupport.2.1]
  intro decrease
  cases decrease with
  | left _ _ harmonicDecrease =>
      exact (Nat.lt_irrefl span.rank) harmonicDecrease
  | right _ supportDecrease =>
      exact
        (Nat.lt_irrefl
          data.reachable.circulation.activeSupportRank)
          supportDecrease

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
