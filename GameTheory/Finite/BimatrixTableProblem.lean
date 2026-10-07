import GameTheory.Core.ConstrainedNash
import GameTheory.Finite.BimatrixTableCorrectness

/-! The decision language for payoff-constrained equilibria of explicit symmetric
integer payoff tables. Its game semantics and decoding use no machine library. -/

noncomputable section

namespace GameTheory.Finite.BimatrixTable

/-- Explicit symmetric tables admitting a mixed Nash equilibrium with both
expected payoffs at least one. Column payoffs are the transpose of row payoffs. -/
def unitPayoffLanguage : Set (List Bool) :=
  {input | (decodedGame input).HasNashWithPayoffAtLeast (fun _ => 1)}

end GameTheory.Finite.BimatrixTable
