/-
# Finite economic games

Executable rational presentations of four standard economic examples. Each
game compiles through `TableGame`; public equilibrium statements use the
canonical semantic `IsNash` predicate.

The discrete Cournot and Traveler tables deliberately expose all of their pure
equilibria. This corrects stronger prose claims in the pinned v1 examples that
are refuted by exhaustive enumeration of those same payoff tables.
-/

import GameTheory.Finite.Correctness
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace GameTheory.Examples.Economic

open GameTheory GameTheory.Finite

private def opponent (i : Fin 2) : Fin 2 := 1 - i

/-! ## Dictator game -/

/-- The dictator's possible divisions of a ten-unit endowment. -/
inductive Split
  | keepAll
  | giveHalf
  | giveAll
  deriving DecidableEq, Fintype, Repr

/-- The dictator (`true`) has a real choice; the receiver (`false`) has
exactly one action. -/
def dictatorAction : Bool → Type
  | true => Split
  | false => PUnit

instance (i : Bool) : Fintype (dictatorAction i) := by
  cases i <;> simp [dictatorAction] <;> infer_instance

instance (i : Bool) : DecidableEq (dictatorAction i) := by
  cases i <;> simp [dictatorAction] <;> infer_instance

/-- A dictator chooses the division while the receiver is strategically
passive. Unlike the pinned presentation, the receiver is not assigned fake
division choices. -/
def dictatorGame : TableGame Bool where
  Action := dictatorAction
  actionFintype := inferInstance
  actionDecEq := inferInstance
  payoff profile i :=
    match profile true, i with
    | .keepAll, true => 10
    | .keepAll, false => 0
    | .giveHalf, _ => 5
    | .giveAll, true => 0
    | .giveAll, false => 10

/-- The dictator keeps the whole endowment. -/
def dictatorKeepsAll : Profile dictatorGame.sig
  | true => .keepAll
  | false => PUnit.unit

/-- The dictator gives the whole endowment away. -/
def dictatorGivesAll : Profile dictatorGame.sig
  | true => .giveAll
  | false => PUnit.unit

#guard dictatorGame.enumerateNash.card = 1
#guard dictatorGame.isNash dictatorKeepsAll
#guard !dictatorGame.isNash dictatorGivesAll

/-- Keeping everything is the unique pure Nash profile. -/
theorem dictatorKeepsAll_isNash :
    IsNash dictatorGame.toForm (euPreference dictatorGame.utility)
      dictatorKeepsAll := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- Giving everything away is not Nash. -/
theorem dictatorGivesAll_not_isNash :
    ¬ IsNash dictatorGame.toForm (euPreference dictatorGame.utility)
      dictatorGivesAll := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-! ## Traveler's Dilemma -/

/-- The two claims in the small Traveler's Dilemma. -/
inductive Claim
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- A two-claim Traveler's Dilemma with a one-unit reward or penalty. -/
def travelersDilemma : TableGame (Fin 2) where
  Action _ := Claim
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i :=
    match profile i, profile (opponent i) with
    | .two, .two => 2
    | .two, .three => 3
    | .three, .two => 1
    | .three, .three => 3

/-- Both travelers make the lower claim. -/
def bothClaimTwo : Profile travelersDilemma.sig := fun _ => .two

/-- Both travelers make the higher claim. -/
def bothClaimThree : Profile travelersDilemma.sig := fun _ => .three

#guard travelersDilemma.enumerateNash.card = 2
#guard travelersDilemma.isNash bothClaimTwo
#guard travelersDilemma.isNash bothClaimThree

/-- The lower-claim profile is Nash (and deviations strictly lose). -/
theorem travelersDilemma_bothClaimTwo_isNash :
    IsNash travelersDilemma.toForm (euPreference travelersDilemma.utility)
      bothClaimTwo := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- With only two claims, the higher-claim profile is a second weak Nash
equilibrium: undercutting ties rather than improves the payoff. -/
theorem travelersDilemma_bothClaimThree_isNash :
    IsNash travelersDilemma.toForm (euPreference travelersDilemma.utility)
      bothClaimThree := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-! ## Cournot duopoly -/

/-- Available integer quantities in the discrete Cournot example. -/
inductive Quantity
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- Cournot profit for own quantity and the rival's quantity. -/
def cournotProfit : Quantity → Quantity → ℚ
  | .one, .one => 3
  | .one, .two => 2
  | .one, .three => 1
  | .two, .one => 4
  | .two, .two => 2
  | .two, .three => 0
  | .three, .one => 3
  | .three, .two => 0
  | .three, .three => 0

/-- The three-quantity Cournot duopoly from the pinned example. -/
def cournotDuopoly : TableGame (Fin 2) where
  Action _ := Quantity
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i :=
    cournotProfit (profile i) (profile (opponent i))

/-- Both firms produce quantity two. -/
def bothQuantityTwo : Profile cournotDuopoly.sig := fun _ => .two

#guard cournotDuopoly.enumerateNash.card = 3
#guard cournotDuopoly.isNash bothQuantityTwo

/-- `(2, 2)` is one of the three pure Nash equilibria of this discrete table. -/
theorem cournotDuopoly_bothQuantityTwo_isNash :
    IsNash cournotDuopoly.toForm (euPreference cournotDuopoly.utility)
      bothQuantityTwo := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- Exhaustive enumeration refutes the pinned prose claim that `(2, 2)` is
the unique pure equilibrium of this particular table. -/
theorem cournotDuopoly_nashCount :
    cournotDuopoly.enumerateNash.card = 3 := by
  decide

/-! ## Bertrand competition -/

/-- Available prices in the discrete Bertrand example. -/
inductive Price
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The numeric value represented by a price action. -/
def Price.value : Price → ℚ
  | .one => 1
  | .two => 2
  | .three => 3

/-- Twice the per-firm profit at marginal cost one. Scaling by two preserves
every preference and keeps the executable table in integer-valued rationals. -/
def bertrandProfit : Price → Price → ℚ
  | .one, .one => 0
  | .one, .two => 0
  | .one, .three => 0
  | .two, .one => 0
  | .two, .two => 1
  | .two, .three => 2
  | .three, .one => 0
  | .three, .two => 0
  | .three, .three => 2

/-- The three-price Bertrand duopoly. -/
def bertrandDuopoly : TableGame (Fin 2) where
  Action _ := Price
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i :=
    bertrandProfit (profile i) (profile (opponent i))

/-- Both firms charge price two. -/
def bothPriceTwo : Profile bertrandDuopoly.sig := fun _ => .two

/-- Both firms charge the marginal-cost price one. -/
def bothPriceOne : Profile bertrandDuopoly.sig := fun _ => .one

#guard bertrandDuopoly.enumerateNash.card = 3
#guard bertrandDuopoly.isNash bothPriceTwo
#guard bertrandDuopoly.isNash bothPriceOne

/-- `(2, 2)` is a pure Nash equilibrium. -/
theorem bertrandDuopoly_bothPriceTwo_isNash :
    IsNash bertrandDuopoly.toForm (euPreference bertrandDuopoly.utility)
      bothPriceTwo := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- `(1, 1)` is a weak pure Nash equilibrium at the price floor. -/
theorem bertrandDuopoly_bothPriceOne_isNash :
    IsNash bertrandDuopoly.toForm (euPreference bertrandDuopoly.utility)
      bothPriceOne := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-! ## Braess-style welfare loss -/

/-- Actions before the additional shortcut is available. -/
inductive RestrictedRoute
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- Actions after adding the shortcut `c`. -/
inductive AugmentedRoute
  | a
  | b
  | c
  deriving DecidableEq, Fintype, Repr

/-- The restricted coordination game. -/
def braessRestricted : TableGame (Fin 2) where
  Action _ := RestrictedRoute
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile _ := if profile 0 = profile 1 then 3 else 0

/-- The augmented game, where `c` strictly dominates both old actions but
mutual use of it lowers welfare. -/
def braessAugmented : TableGame (Fin 2) where
  Action _ := AugmentedRoute
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i :=
    match profile i, profile (opponent i) with
    | .a, .a => 3
    | .a, .b => 0
    | .a, .c => 1
    | .b, .a => 0
    | .b, .b => 3
    | .b, .c => 1
    | .c, .a => 5
    | .c, .b => 5
    | .c, .c => 2

/-- Both players use old route `a`. -/
def braessRestrictedAA : Profile braessRestricted.sig := fun _ => .a

/-- Both players use the new shortcut `c`. -/
def braessAugmentedCC : Profile braessAugmented.sig := fun _ => .c

/-- Both players retain route `a` after the shortcut is added. -/
def braessAugmentedAA : Profile braessAugmented.sig := fun _ => .a

#guard braessRestricted.enumerateNash.card = 2
#guard braessAugmented.enumerateNash.card = 1
#guard braessRestricted.isNash braessRestrictedAA
#guard braessAugmented.isNash braessAugmentedCC
#guard !braessAugmented.isNash braessAugmentedAA
#guard braessAugmented.isDominantProfile braessAugmentedCC

@[simp]
theorem braessRestricted_payoff_AA (who : Fin 2) :
    braessRestricted.payoff braessRestrictedAA who = 3 := by
  fin_cases who <;> rfl

@[simp]
theorem braessAugmented_payoff_CC (who : Fin 2) :
    braessAugmented.payoff braessAugmentedCC who = 2 := by
  fin_cases who <;> rfl

/-- Coordinating on `a` is Nash before the shortcut is available. -/
theorem braessRestrictedAA_isNash :
    IsNash braessRestricted.toForm (euPreference braessRestricted.utility)
      braessRestrictedAA := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- Mutual use of the dominant shortcut is the augmented equilibrium. -/
theorem braessAugmentedCC_isNash :
    IsNash braessAugmented.toForm (euPreference braessAugmented.utility)
      braessAugmentedCC := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- The old coordination profile ceases to be Nash after adding `c`. -/
theorem braessAugmentedAA_not_isNash :
    ¬ IsNash braessAugmented.toForm (euPreference braessAugmented.utility)
      braessAugmentedAA := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- Total equilibrium welfare falls from six to four after the dominant
shortcut is introduced. -/
theorem braessWelfareDecreases :
    braessRestricted.payoff braessRestrictedAA 0 +
          braessRestricted.payoff braessRestrictedAA 1 >
      braessAugmented.payoff braessAugmentedCC 0 +
          braessAugmented.payoff braessAugmentedCC 1 := by
  rw [braessRestricted_payoff_AA, braessRestricted_payoff_AA,
    braessAugmented_payoff_CC, braessAugmented_payoff_CC]
  norm_num

/-! ## Parametric public goods -/

/-- Payoff in a linear public-goods game. -/
noncomputable def publicGoodsPayoff {n : ℕ} (endowment mpcr : ℝ)
    (contributions : Fin n → ℝ) (who : Fin n) : ℝ :=
  endowment + mpcr * ∑ j, contributions j - contributions who

/-- Replace one player's contribution by zero without exposing a raw
function-update representation. -/
def removeContribution {n : ℕ} (contributions : Fin n → ℝ)
    (who : Fin n) : Fin n → ℝ :=
  fun j => if j = who then 0 else contributions j

@[simp]
theorem removeContribution_self {n : ℕ} (contributions : Fin n → ℝ)
    (who : Fin n) :
    removeContribution contributions who who = 0 := by
  simp [removeContribution]

@[simp]
theorem removeContribution_of_ne {n : ℕ} (contributions : Fin n → ℝ)
    {who other : Fin n} (hne : other ≠ who) :
    removeContribution contributions who other = contributions other := by
  simp [removeContribution, hne]

theorem sum_removeContribution {n : ℕ} (contributions : Fin n → ℝ)
    (who : Fin n) :
    ∑ j, removeContribution contributions who j =
      ∑ j, contributions j - contributions who := by
  classical
  calc
    ∑ j, removeContribution contributions who j =
        (∑ j ∈ Finset.univ.erase who,
          removeContribution contributions who j) +
          removeContribution contributions who who :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ who)).symm
    _ = ∑ j ∈ Finset.univ.erase who, contributions j := by
      rw [removeContribution_self, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      exact removeContribution_of_ne contributions (Finset.mem_erase.mp hj).1
    _ = ∑ j, contributions j - contributions who := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
      ring

/-- When the marginal per-capita return is below one, a player with a
nonnegative contribution weakly benefits by free-riding. -/
theorem publicGoods_freeRide {n : ℕ} (endowment mpcr : ℝ)
    (hmpcr : mpcr < 1) (contributions : Fin n → ℝ) (who : Fin n)
    (hcontribution : 0 ≤ contributions who) :
    publicGoodsPayoff endowment mpcr
        (removeContribution contributions who) who ≥
      publicGoodsPayoff endowment mpcr contributions who := by
  rw [publicGoodsPayoff, publicGoodsPayoff, sum_removeContribution]
  simp only [removeContribution_self]
  have hgain : 0 ≤ (1 - mpcr) * contributions who :=
    mul_nonneg (by linarith) hcontribution
  nlinarith

/-- Full cooperation strictly improves every player's payoff over universal
defection when the aggregate return on one contribution exceeds its cost. -/
theorem publicGoods_cooperationPareto {n : ℕ} (endowment mpcr c : ℝ)
    (hc : 0 < c) (hreturn : 1 < mpcr * (n : ℝ)) (who : Fin n) :
    publicGoodsPayoff endowment mpcr (fun _ => c) who >
      publicGoodsPayoff endowment mpcr (fun _ => 0) who := by
  simp only [publicGoodsPayoff, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul, mul_zero, sub_zero]
  have hgain : 0 < (mpcr * (n : ℝ) - 1) * c :=
    mul_pos (by linarith) hc
  nlinarith

end GameTheory.Examples.Economic
