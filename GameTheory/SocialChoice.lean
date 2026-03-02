import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-!
# Social Choice Functions

Defines social welfare functions and social choice functions, along with
key axioms (Pareto, Independence of Irrelevant Alternatives, non-dictatorship).
Proves that a dictatorial SWF satisfies Pareto and IIA, establishing one
direction of Arrow's impossibility theorem.

## Main definitions

* `SWF` — social welfare function (aggregates preferences into a social ranking)
* `SWF.IsPareto` — the weak Pareto condition
* `SWF.IsIIA` — independence of irrelevant alternatives
* `SWF.IsDictatorial` — dictatorship

## Main results

* `dictatorial_isPareto` — a dictatorial SWF satisfies Pareto
* `dictatorial_isIIA` — a dictatorial SWF satisfies IIA
-/

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : Type} [DecidableEq A]

/-- A preference relation on alternatives: `pref a b` means `a` is
    weakly preferred to `b`. -/
abbrev PrefRel (A : Type) := A → A → Prop

/-- A preference profile: each voter has a preference relation. -/
abbrev PrefProfile (ι A : Type) := ι → PrefRel A

/-- A social welfare function: maps preference profiles to a social ranking. -/
abbrev SWF (ι A : Type) := PrefProfile ι A → PrefRel A

namespace SWF

variable {ι A : Type}

/-- Weak Pareto condition: if all voters strictly prefer `a` to `b`,
    then society strictly prefers `a` to `b`.
    "Strictly prefer" means `pref a b ∧ ¬pref b a`. -/
def IsPareto (f : SWF ι A) : Prop :=
  ∀ (R : PrefProfile ι A) (a b : A),
    (∀ i, R i a b ∧ ¬R i b a) → f R a b ∧ ¬f R b a

/-- Independence of Irrelevant Alternatives: the social ranking of `a` vs `b`
    depends only on individual rankings of `a` vs `b`. -/
def IsIIA (f : SWF ι A) : Prop :=
  ∀ (R R' : PrefProfile ι A) (a b : A),
    (∀ i, (R i a b ↔ R' i a b) ∧ (R i b a ↔ R' i b a)) →
    (f R a b ↔ f R' a b) ∧ (f R b a ↔ f R' b a)

/-- A dictatorial SWF: the social ranking is determined by a single voter. -/
def IsDictatorial (f : SWF ι A) : Prop :=
  ∃ d : ι, ∀ (R : PrefProfile ι A) (a b : A), f R a b ↔ R d a b

/-- Construct the dictatorial SWF for voter `d`. -/
def dictator (d : ι) : SWF ι A := fun R a b => R d a b

/-- The dictatorial SWF is indeed dictatorial. -/
theorem dictator_isDictatorial (d : ι) : IsDictatorial (dictator d : SWF ι A) :=
  ⟨d, fun _ _ _ => Iff.rfl⟩

/-- A dictatorial SWF satisfies the weak Pareto condition. -/
theorem dictatorial_isPareto (d : ι) : IsPareto (dictator d : SWF ι A) := by
  intro R a b hunanimous
  exact hunanimous d

/-- A dictatorial SWF satisfies IIA. -/
theorem dictatorial_isIIA (d : ι) : IsIIA (dictator d : SWF ι A) := by
  intro R R' a b hlocal
  simp only [dictator]
  exact ⟨(hlocal d).1, (hlocal d).2⟩

/-- The unanimity rule: `a` is socially preferred to `b` iff all voters
    prefer `a` to `b`. -/
def unanimity : SWF ι A := fun R a b => ∀ i, R i a b

/-- The unanimity rule satisfies Pareto. -/
theorem unanimity_isPareto [Nonempty ι] : IsPareto (unanimity : SWF ι A) := by
  intro R a b hunanimous
  constructor
  · intro i; exact (hunanimous i).1
  · intro h; exact (hunanimous (Classical.arbitrary ι)).2 (h (Classical.arbitrary ι))

/-- The unanimity rule satisfies IIA. -/
theorem unanimity_isIIA : IsIIA (unanimity : SWF ι A) := by
  intro R R' a b hlocal
  constructor
  · constructor
    · intro h i; exact (hlocal i).1.mp (h i)
    · intro h i; exact (hlocal i).1.mpr (h i)
  · constructor
    · intro h i; exact (hlocal i).2.mp (h i)
    · intro h i; exact (hlocal i).2.mpr (h i)

/-- A social welfare function is non-dictatorial if no single voter
    determines the social ranking. -/
def IsNonDictatorial (f : SWF ι A) : Prop := ¬f.IsDictatorial

/-- A social welfare function has unrestricted domain if it's defined
    for all logically possible preference profiles.
    (This is always true in our formalization since the SWF takes
    any function `ι → PrefRel A`.) -/
def HasUnrestrictedDomain (_f : SWF ι A) : Prop := True

end SWF

end GameTheory
