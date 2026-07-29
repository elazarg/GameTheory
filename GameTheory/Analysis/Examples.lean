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

import GameTheory.Analysis.Minimax
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

/-! ## The value of matching pennies -/

/-- Matching pennies is zero-sum: whatever one player wins the other loses. -/
theorem matchingPennies_isZeroSum : IsZeroSum matchingPennies.utility := by
  intro outcome
  rw [Fin.sum_univ_two, TableGame.utility_apply, TableGame.utility_apply,
    matchingPennies_payoff, matchingPennies_payoff]
  split_ifs <;> simp_all

/-- The verified uniform profile is a saddle point, so it carries the value. -/
theorem matchingPennies_uniform_isSaddlePoint :
    IsSaddlePoint (F := matchingPennies.toForm) matchingPennies.utility
      (matchingPennies.toMixed uniformPennies uniformPennies_isMixed) :=
  matchingPennies_uniform_isNash.isSaddlePoint matchingPennies_isZeroSum

/-- **And every saddle point of matching pennies is worth exactly that.** The
uniqueness of the value is what makes the word *value* mean anything, and here
it anchors the abstract theorem to a profile the frontend checked by
arithmetic. -/
theorem matchingPennies_value_eq_uniform (σ : Profile matchingPennies.toForm.sig.mixed)
    (hσ : IsSaddlePoint (F := matchingPennies.toForm) matchingPennies.utility σ) :
    expectedUtility matchingPennies.utility 0 (matchingPennies.toForm.mixed.play σ) =
      expectedUtility matchingPennies.utility 0 (matchingPennies.toForm.mixed.play
        (matchingPennies.toMixed uniformPennies uniformPennies_isMixed)) :=
  hσ.value_eq matchingPennies_uniform_isSaddlePoint

end GameTheory.Examples
