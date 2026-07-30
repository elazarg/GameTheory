/-
# Public-surface test for Arrow's theorem

The proof module uses a private strict-order representation. This file stays
entirely on the weak `Ranking` surface and checks both a concrete admissible
aggregator and the finite-cardinality flagship.
-/

import GameTheory.Core.Arrow

namespace GameTheory.Tests.Arrow

open GameTheory

/-- A concrete aggregator on three voters and three alternatives. -/
def firstVoter : Aggregator (Fin 3) (Fin 3) :=
  Aggregator.dictator 0

theorem firstVoter_collectivelyRational :
    firstVoter.IsCollectivelyRational :=
  Aggregator.dictator_collectivelyRational 0

theorem firstVoter_pareto : firstVoter.IsPareto :=
  Aggregator.dictator_pareto 0

theorem firstVoter_iia : firstVoter.IsIIA :=
  Aggregator.dictator_iia 0

/-- The hypotheses are jointly satisfiable, and the theorem recovers an exact
dictator through only the public weak-ranking API. -/
theorem threeVoters_threeAlternatives :
    ∃ dictator, firstVoter.IsDictator dictator := by
  apply GameTheory.Arrow.impossibility_of_card
    firstVoter_collectivelyRational firstVoter_pareto firstVoter_iia
  simp

end GameTheory.Tests.Arrow
