/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Voting.Majority
import GameTheory.Voting.Median
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Voting compilation tests

Concrete finite examples exercising delegation resolution, abstention on
cycles, the copy lemma, and the liquid majority and liquid median instances.
-/

namespace GameTheory.Voting.Tests

open GameTheory.Voting DelegationProfile

/-- Three voters in a chain: `0` delegates to `1`, `1` delegates to `2`,
`2` casts `true`. -/
def chain : DelegationProfile (Fin 3) Bool :=
  ![Sum.inl 1, Sum.inl 2, Sum.inr true]

example : chain.resolveFuel 2 0 = some true := rfl

example : chain.resolve 0 = some true :=
  resolve_eq_of_resolveFuel (n := 2) rfl

example : chain.Resolves 0 true :=
  resolves_of_resolveFuel_eq_some (n := 2) rfl

/-- Everyone in the chain resolves to the caster's ballot. -/
example (i : Fin 3) : ∃ b, chain.Resolves i b := by
  fin_cases i
  · exact ⟨true, resolves_of_resolveFuel_eq_some (n := 2) rfl⟩
  · exact ⟨true, resolves_of_resolveFuel_eq_some (n := 2) rfl⟩
  · exact ⟨true, resolves_of_resolveFuel_eq_some (n := 2) rfl⟩

/-- Copy lemma at work: voter `0` casting the resolved ballot directly changes
no voter's resolution. -/
example (k : Fin 3) (b : Bool) :
    Resolves (Function.update chain 0 (Sum.inr true)) k b ↔ chain.Resolves k b :=
  resolves_update_cast_iff (resolves_of_resolveFuel_eq_some (n := 2) rfl)

/-- Voters `0` and `1` delegate to each other; `2` casts `false`. -/
def cyclic : DelegationProfile (Fin 3) Bool :=
  ![Sum.inl 1, Sum.inl 0, Sum.inr false]

/-- Voters on the delegation cycle abstain. -/
example (b : Bool) : ¬ cyclic.Resolves 0 b :=
  not_resolves_of_cycle
    (Relation.TransGen.head rfl (Relation.TransGen.single rfl))

/-- The caster outside the cycle still resolves. -/
example : cyclic.Resolves 2 false := Casts.resolves rfl

/-- A tail into a two-cycle: `0` delegates to `1`, while `1` and `2` delegate
to each other. -/
def tailCycle : DelegationProfile (Fin 3) Bool :=
  ![Sum.inl 1, Sum.inl 2, Sum.inl 1]

/-- A voter who merely reaches a cycle also abstains. -/
example (b : Bool) : ¬ tailCycle.Resolves 0 b :=
  not_resolves_of_reflTransGen_cycle (Relation.ReflTransGen.single rfl)
    (Relation.TransGen.head rfl (Relation.TransGen.single rfl))

/-- Star delegation: `0` delegates to `2`; `1` casts `1`; `2` casts `-1`.
The caster `2` carries weight two, so liquid majority elects `-1` even though
the cast ballots alone are tied. -/
def star : DelegationProfile (Fin 3) SignType :=
  ![Sum.inl 2, Sum.inr 1, Sum.inr (-1)]

example : liquidMajority star = -1 := by
  have h0 : star.resolve 0 = some (-1) := resolve_eq_of_resolveFuel (n := 1) rfl
  have h1 : star.resolve 1 = some 1 := resolve_eq_of_resolveFuel (n := 1) rfl
  have h2 : star.resolve 2 = some (-1) := resolve_eq_of_resolveFuel (n := 1) rfl
  have hM : star.resolvedBallots
      = (↑[(-1 : SignType)] + ↑[(1 : SignType)] + ↑[(-1 : SignType)] :
          Multiset SignType) := by
    rw [DelegationProfile.resolvedBallots, Fin.sum_univ_three, h0, h1, h2]
    rfl
  have htally :
      multisetTally
        (↑[(-1 : SignType)] + ↑[(1 : SignType)] + ↑[(-1 : SignType)] :
          Multiset SignType) = -1 := by
    decide
  rw [liquidMajority, liquidExtension, hM, majorityRule, htally]
  exact sign_neg (by norm_num)

/-- On all-cast profiles liquid majority is May's majority rule. -/
example :
    liquidMajority (directProfile (![1, 1, -1] : Fin 3 → SignType))
      = May.majority (![1, 1, -1] : Fin 3 → SignType) :=
  liquidMajority_directProfile _

/-- On all-cast profiles the liquid median is the median ideal point. -/
example :
    liquidMedian (directProfile (![0, 1, 2] : Fin 3 → ℝ))
      = medianIdeal (![0, 1, 2] : Fin 3 → ℝ) :=
  liquidMedian_directProfile _

end GameTheory.Voting.Tests
