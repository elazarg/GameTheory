/-
# EXP-109: executable checker consumers

The executable edge-addition checker accepts the two existing semantic
fixpoint certificates with explicit complete player enumerations.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointChecker
import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointPositiveTest
import GameTheory.Experimental.PostArchitecture.MAIDForgetfulMovieStarAudit

namespace GameTheory.Experimental.PostArchitecture

open MAIDPruningFixpointGraph

namespace MAIDPruningFixpointCheckerTest

open MAIDPruningFixpointPositiveTest

def positivePlayers : List Unit := [()]

theorem positivePlayers_complete : ∀ owner : Unit, owner ∈ positivePlayers := by
  intro owner
  simp [positivePlayers]

theorem positive_checker_true :
    UtilityView.edgeAdditionFixpoint? view topological positivePlayers pruning =
      true := by
  apply (UtilityView.edgeAdditionFixpoint?_eq_true_iff view topological
    positivePlayers positivePlayers_complete pruning).mpr
  exact edgeAdditionFixpoint

theorem positive_checker_extracts_fixpoint :
    UtilityView.edgeAdditionFixpoint? view topological positivePlayers pruning =
      true → UtilityView.IsEdgeAdditionFixpoint view pruning := by
  intro hchecker
  exact (UtilityView.edgeAdditionFixpoint?_eq_true_iff view topological
    positivePlayers positivePlayers_complete pruning).mp hchecker

end MAIDPruningFixpointCheckerTest

namespace MAIDForgetfulMovieStarCheckerTest

open MAIDForgetfulMovieStarAudit

def movieStarPlayers : List Player := [.star, .robot]

theorem movieStarPlayers_complete : ∀ owner : Player, owner ∈ movieStarPlayers := by
  intro owner
  cases owner <;> simp [movieStarPlayers]

theorem movieStar_checker_true :
    UtilityView.edgeAdditionFixpoint? utilityView topological movieStarPlayers
      pruning = true := by
  apply (UtilityView.edgeAdditionFixpoint?_eq_true_iff utilityView topological
    movieStarPlayers movieStarPlayers_complete pruning).mpr
  exact candidate_isEdgeAdditionFixpoint

theorem movieStar_checker_extracts_fixpoint :
    UtilityView.edgeAdditionFixpoint? utilityView topological movieStarPlayers
      pruning = true → UtilityView.IsEdgeAdditionFixpoint utilityView pruning := by
  intro hchecker
  exact (UtilityView.edgeAdditionFixpoint?_eq_true_iff utilityView topological
    movieStarPlayers movieStarPlayers_complete pruning).mp hchecker

end MAIDForgetfulMovieStarCheckerTest

end GameTheory.Experimental.PostArchitecture
