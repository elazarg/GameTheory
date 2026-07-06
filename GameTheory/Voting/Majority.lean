/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Voting.LiquidDemocracy
import GameTheory.Mechanism.May

/-!
# Liquid majority

The two-alternative instance of liquid democracy: ballots are `SignType`
(`1` favors the first alternative, `-1` the second, `0` is indifference), and
the anonymous rule is the sign of the tally, as in May's theorem
(`Mechanism/May.lean`). Liquid majority then counts each caster's ballot with
multiplicity their delegated weight.

## Main definitions

* `Voting.multisetTally` / `Voting.majorityRule` — the anonymous majority rule
  on ballot multisets
* `Voting.liquidMajority` — its liquid extension

## Main results

* `liquidMajority_directProfile` — on all-cast profiles liquid majority is
  `May.majority`, connecting to May's axiomatization
* `multisetTally_resolvedBallots` — the tally is supporters of `1` minus
  supporters of `-1`
* `liquidMajority_eq_one_iff` / `_eq_neg_one_iff` — outcome characterizations
  by supporter counts
* `liquidMajority_eq_one_iff_weight` — the weighted-majority reading: `1` wins
  exactly when its casters carry more delegated weight
-/

namespace GameTheory.Voting

open DelegationProfile

/-- The tally of a multiset of sign ballots. -/
def multisetTally (m : Multiset SignType) : ℤ := (m.map fun s : SignType => (s : ℤ)).sum

/-- The anonymous majority rule on ballot multisets: the sign of the tally. -/
noncomputable def majorityRule (m : Multiset SignType) : SignType :=
  SignType.sign (multisetTally m)

@[simp] theorem multisetTally_zero : multisetTally 0 = 0 := by
  simp [multisetTally]

theorem multisetTally_cons (a : SignType) (m : Multiset SignType) :
    multisetTally (a ::ₘ m) = (a : ℤ) + multisetTally m := by
  simp only [multisetTally, Multiset.map_cons, Multiset.sum_cons]

/-- On sign multisets the tally is the count of `1`s minus the count of `-1`s. -/
theorem multisetTally_eq_count_sub (m : Multiset SignType) :
    multisetTally m = (m.count 1 : ℤ) - (m.count (-1) : ℤ) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [multisetTally_cons, ih]
    cases a with
    | zero =>
      have h1 : Multiset.count 1 (SignType.zero ::ₘ m) = Multiset.count 1 m :=
        Multiset.count_cons_of_ne (by decide) m
      have h2 : Multiset.count (-1) (SignType.zero ::ₘ m) = Multiset.count (-1) m :=
        Multiset.count_cons_of_ne (by decide) m
      rw [h1, h2, show (SignType.zero : ℤ) = 0 from rfl, zero_add]
    | neg =>
      have h1 : Multiset.count 1 (SignType.neg ::ₘ m) = Multiset.count 1 m :=
        Multiset.count_cons_of_ne (by decide) m
      have h2 : Multiset.count (-1) (SignType.neg ::ₘ m)
          = Multiset.count (-1) m + 1 := by
        rw [show (-1 : SignType) = SignType.neg from rfl, Multiset.count_cons_self]
      rw [h1, h2, show (SignType.neg : ℤ) = -1 from rfl]
      push_cast
      ring
    | pos =>
      have h1 : Multiset.count 1 (SignType.pos ::ₘ m)
          = Multiset.count 1 m + 1 := by
        rw [show (1 : SignType) = SignType.pos from rfl, Multiset.count_cons_self]
      have h2 : Multiset.count (-1) (SignType.pos ::ₘ m) = Multiset.count (-1) m :=
        Multiset.count_cons_of_ne (by decide) m
      rw [h1, h2, show (SignType.pos : ℤ) = 1 from rfl]
      push_cast
      ring

variable {ι : Type*} [Fintype ι] {d : DelegationProfile ι SignType}

/-- Liquid majority: the liquid extension of the majority rule. -/
noncomputable def liquidMajority (d : DelegationProfile ι SignType) : SignType :=
  liquidExtension majorityRule d

/-- On an all-cast profile, liquid majority is May's majority rule. -/
theorem liquidMajority_directProfile (p : ι → SignType) :
    liquidMajority (directProfile p) = May.majority p := by
  rw [liquidMajority, liquidExtension_directProfile, majorityRule, May.majority]
  congr 1
  rw [multisetTally, Multiset.map_map, May.tally]
  rfl

/-- The liquid tally is the number of supporters of `1` minus the number of
supporters of `-1` (each voter counted at their resolved ballot). -/
theorem multisetTally_resolvedBallots :
    multisetTally d.resolvedBallots
      = ((d.resolversTo 1).card : ℤ) - ((d.resolversTo (-1)).card : ℤ) := by
  rw [multisetTally_eq_count_sub, count_resolvedBallots, count_resolvedBallots]

theorem liquidMajority_eq_one_iff :
    liquidMajority d = 1
      ↔ (d.resolversTo (-1)).card < (d.resolversTo 1).card := by
  rw [liquidMajority, liquidExtension, majorityRule, sign_eq_one_iff,
    multisetTally_resolvedBallots, sub_pos, Nat.cast_lt]

theorem liquidMajority_eq_neg_one_iff :
    liquidMajority d = -1
      ↔ (d.resolversTo 1).card < (d.resolversTo (-1)).card := by
  rw [liquidMajority, liquidExtension, majorityRule, sign_eq_neg_one_iff,
    multisetTally_resolvedBallots, sub_neg, Nat.cast_lt]

/-- The weighted-majority reading: alternative `1` wins exactly when its
casters carry more delegated weight than the casters of `-1`. -/
theorem liquidMajority_eq_one_iff_weight :
    liquidMajority d = 1
      ↔ ∑ j ∈ d.castersOf (-1), d.weight j < ∑ j ∈ d.castersOf 1, d.weight j := by
  rw [liquidMajority_eq_one_iff, card_resolversTo_eq_sum_weight,
    card_resolversTo_eq_sum_weight]

end GameTheory.Voting
