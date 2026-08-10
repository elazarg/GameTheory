/-
# Public-surface tests for the Shapley value

The existing majority game has an empty core, but its Shapley value always
exists. Symmetry and efficiency force each of its three agents to receive one
third. The second theorem exercises the four named axioms as a public
characterization rather than unfolding the weighted marginal formula.
-/

import GameTheory.Core.Shapley

namespace GameTheory.Tests.Shapley

open GameTheory

theorem majorityGame_areSymmetric
    (first second : Fin 3) :
    majorityGame.AreSymmetric first second := by
  intro coalition hfirst hsecond
  simp only [majorityGame]
  rw [Finset.card_insert_of_notMem hfirst,
    Finset.card_insert_of_notMem hsecond]

/-- The no-core example still has a canonical Shapley allocation. -/
theorem majorityGame_shapleyValue (agent : Fin 3) :
    majorityGame.shapleyValue agent = 1 / 3 := by
  rw [CoalitionalGame.shapleyValue_eq_of_all_symmetric
    majorityGame
    (fun first second _ =>
      majorityGame_areSymmetric first second)
    agent]
  norm_num [majorityGame]

/-- Any rule satisfying the four public axioms agrees with the Shapley value
on the existing majority game. -/
theorem majorityGame_rule_unique
    (rule : CoalitionalGame.AllocationRule (Fin 3))
    (hefficient : rule.IsEfficient)
    (hsymmetric : rule.IsSymmetric)
    (hnull : rule.RespectsNull)
    (hadditive : rule.IsAdditive) :
    rule majorityGame = majorityGame.shapleyValue :=
  CoalitionalGame.shapleyValue_unique
    rule hefficient hsymmetric hnull hadditive majorityGame

/-- A singleton unanimity game is a nondegenerate asymmetric witness: player
zero creates all value, while player one is null. -/
private def asymmetricGame : CoalitionalGame (Fin 2) :=
  CoalitionalGame.unanimityGame ({0} : Finset (Fin 2))
    (Finset.singleton_nonempty 0)

/-- The public efficiency and null-player theorems distinguish the two
Shapley shares in the asymmetric witness. -/
theorem asymmetricGame_shapleyValue :
    asymmetricGame.shapleyValue 0 = 1 ∧
      asymmetricGame.shapleyValue 1 = 0 := by
  have hnull : asymmetricGame.IsNull (1 : Fin 2) := by
    simpa only [asymmetricGame] using
      (CoalitionalGame.unanimityGame_isNull_of_notMem
        ({0} : Finset (Fin 2)) (Finset.singleton_nonempty 0)
        (agent := (1 : Fin 2)) (by decide))
  have hone := asymmetricGame.shapleyValue_null hnull
  have hsum := asymmetricGame.shapleyValue_efficient
  have hgrand : asymmetricGame.value Finset.univ = 1 := by
    simpa only [asymmetricGame] using
      (CoalitionalGame.unanimityGame_value_univ
        ({0} : Finset (Fin 2)) (Finset.singleton_nonempty 0))
  rw [Fin.sum_univ_two, hone, add_zero, hgrand] at hsum
  exact ⟨hsum, hone⟩

end GameTheory.Tests.Shapley
