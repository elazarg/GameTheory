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
import GameTheory.Analysis.MatrixValue
import GameTheory.Analysis.Correlated
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

/-- **Matching pennies nevertheless has a correlated equilibrium.**  This
consumer is intentionally existential: it witnesses the general theorem on a
game whose pure-equilibrium set was just proved empty. -/
theorem matchingPennies_exists_isCorrelatedEq :
    ∃ law : GameTheory.Math.Probability.FinDist (Profile matchingPennies.sig),
      IsCorrelatedEq matchingPennies.toForm
        (euPreference matchingPennies.utility) law := by
  haveI : ∀ i, Nonempty (matchingPennies.toForm.sig.Strategy i) := fun _ => ⟨Side.heads⟩
  exact exists_isCorrelatedEq (ι := Fin 2) (F := matchingPennies.toForm)
    matchingPennies.utility

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

/-! ## A nontrivial pure security certificate -/

/-- A matrix with a strict row maximin choice and a strict column minimax
choice.  Its saddle entry is `1`, while all three other entries differ. -/
def securityMatrix (row col : Fin 2) : ℝ :=
  if row = 0 then
    if col = 0 then 2 else 0
  else if col = 0 then 3 else 1

/-- The bottom-right pure profile is Nash in the canonical matrix form. -/
theorem securityMatrix_pure_isNash :
    IsNash (MatrixGame.form (Fin 2) (Fin 2))
      (euPreference (MatrixGame.utility securityMatrix))
      (MatrixGame.pureProfile 1 1) := by
  rw [isNash_iff]
  intro who alternative
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · fin_cases alternative <;>
      simp [euPreference_apply, MatrixGame.form, MatrixGame.pureProfile,
        MatrixGame.utility, securityMatrix, expectedUtility]
  · fin_cases alternative <;>
      simp [euPreference_apply, MatrixGame.form, MatrixGame.pureProfile,
        MatrixGame.utility, securityMatrix, expectedUtility]

/-- The corresponding point-mass mixed profile is a saddle point. -/
theorem securityMatrix_pure_isSaddlePoint :
    IsSaddlePoint (F := MatrixGame.form (Fin 2) (Fin 2))
      (MatrixGame.utility securityMatrix)
      (MatrixGame.mixedProfile (GameTheory.Math.Probability.FinDist.pure 1)
        (GameTheory.Math.Probability.FinDist.pure 1)) := by
  rw [MatrixGame.mixedProfile_pure]
  exact securityMatrix_pure_isNash.purify.isSaddlePoint
    (MatrixGame.utility_isZeroSum securityMatrix)

@[simp]
theorem securityMatrix_pure_expectedPayoff :
    MatrixGame.expectedPayoff securityMatrix
      (GameTheory.Math.Probability.FinDist.pure 1)
      (GameTheory.Math.Probability.FinDist.pure 1) = 1 := by
  rw [MatrixGame.expectedPayoff, MatrixGame.mixedProfile_pure,
    GameForm.mixed_play_purify]
  simp [MatrixGame.form, MatrixGame.pureProfile, MatrixGame.utility,
    securityMatrix, expectedUtility]

/-- The bottom row guarantees the nonzero value against every mixed column. -/
theorem securityMatrix_row_guarantees :
    MatrixGame.RowGuarantees securityMatrix (GameTheory.Math.Probability.FinDist.pure 1) 1 := by
  have h := (MatrixGame.isSaddlePoint_iff_guarantees_caps securityMatrix
    (GameTheory.Math.Probability.FinDist.pure 1) (GameTheory.Math.Probability.FinDist.pure 1)).1
    securityMatrix_pure_isSaddlePoint
  simpa only [securityMatrix_pure_expectedPayoff] using h.1

/-- The right column caps the row payoff at the same nonzero value. -/
theorem securityMatrix_column_caps :
    MatrixGame.ColumnCaps securityMatrix (GameTheory.Math.Probability.FinDist.pure 1) 1 := by
  have h := (MatrixGame.isSaddlePoint_iff_guarantees_caps securityMatrix
    (GameTheory.Math.Probability.FinDist.pure 1) (GameTheory.Math.Probability.FinDist.pure 1)).1
    securityMatrix_pure_isSaddlePoint
  simpa only [securityMatrix_pure_expectedPayoff] using h.2

/-- The abstract selected matrix value is forced to equal the explicit common
security certificate. -/
theorem securityMatrix_value_eq_one : MatrixGame.value securityMatrix = 1 := by
  symm
  exact MatrixGame.common_guarantee_eq_value securityMatrix
    ⟨GameTheory.Math.Probability.FinDist.pure 1, securityMatrix_row_guarantees⟩
    ⟨GameTheory.Math.Probability.FinDist.pure 1, securityMatrix_column_caps⟩

end GameTheory.Examples
