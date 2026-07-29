/-
# What the fixed-point argument buys

Matching pennies is the game the existence theorem exists for. It has no
equilibrium in pure strategies at all — the executable frontend decides that, and
the decision is a theorem here rather than a computation the reader is asked to
trust — and yet it has one in mixed strategies.

The contrast with the potential-game argument is the point. There, existence
came from maximizing a function and the maximizer was exhibited. Here nothing is
maximized globally and no profile is supplied: the equilibrium is produced by a
fixed point, which is why the dependency that proves fixed points exist is worth
its cost.
-/

import GameTheory.Analysis.Nash
import GameTheory.Examples.Classic

namespace GameTheory.Examples

open GameTheory GameTheory.Finite

instance : Nonempty Side := ⟨.heads⟩

/-- No pure profile survives, and the frontend enumerates that exhaustively. -/
theorem matchingPennies_enumerateNash : matchingPennies.enumerateNash = ∅ := by decide

/-- **Matching pennies has no equilibrium in pure strategies.** -/
theorem matchingPennies_not_isNash (profile : Profile matchingPennies.sig) :
    ¬ IsNash matchingPennies.toForm (euPreference matchingPennies.utility) profile := by
  rw [← TableGame.mem_enumerateNash_iff, matchingPennies_enumerateNash]
  exact Finset.notMem_empty profile

/-- **And yet it has one in mixed strategies.** The profile is not supplied: the
statement asserts existence and the fixed-point argument delivers it. -/
theorem matchingPennies_exists_isNash_mixed :
    ∃ μ, IsNash matchingPennies.toForm.mixed (euPreference matchingPennies.utility) μ := by
  haveI : ∀ i, Nonempty (matchingPennies.toForm.sig.Strategy i) := fun _ => ⟨Side.heads⟩
  exact exists_isNash_mixed _

end GameTheory.Examples
