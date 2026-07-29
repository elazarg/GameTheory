/-
# The Condorcet paradox

Three voters, three alternatives, and a rotation: each voter ranks the
alternatives completely and transitively, and each starts one step further round
the cycle than the last. Majority rule then prefers the first alternative to the
second, the second to the third, and the third to the first.

The point is not the arithmetic, which is elementary. It is that the individual
rankings and the social ranking are stated in exactly the same vocabulary, with
no probability in either: the same `Total` and `Transitive` that a game's
preference satisfies are what the voters satisfy and what society fails.
-/

import GameTheory.Core.SocialChoice

namespace GameTheory.Examples

open GameTheory

/-- Voter `agent` ranks the alternatives by how far each is past `agent` in the
cycle, so the three voters rank them in three rotations of the same order. -/
def rotation : Ranking (Fin 3) (Fin 3) :=
  fun agent preferred alternative => preferred - agent ≤ alternative - agent

instance (agent a b : Fin 3) : Decidable (rotation agent a b) := by
  unfold rotation; infer_instance

/-- Every voter compares every pair. -/
theorem rotation_total : Preference.Total rotation := by
  unfold Preference.Total Rank.Total
  decide

/-- Every voter is transitive: nobody here is confused. -/
theorem rotation_transitive : Preference.Transitive rotation := by
  unfold Preference.Transitive Rank.Transitive
  decide

/-- **The Condorcet paradox.** The voters are individually impeccable and the
majority ranking they induce is not transitive. -/
theorem majority_rotation_not_transitive : ¬ Rank.Transitive (majority rotation) := by
  unfold Rank.Transitive majority
  decide

/-- And the failure is a genuine cycle rather than a technicality: majority
strictly prefers each alternative to the next, all the way round. -/
theorem majority_rotation_cycle :
    Rank.strict (majority rotation) 0 1 ∧ Rank.strict (majority rotation) 1 2 ∧
      Rank.strict (majority rotation) 2 0 := by
  unfold Rank.strict majority
  decide

end GameTheory.Examples
