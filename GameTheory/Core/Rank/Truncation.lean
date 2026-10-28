module

/-
# Moving the outside option in ordinal reports

Truncating a linear ranking at a partner retains all partner comparisons and
places the outside option immediately below that partner. A singleton report
instead puts one partner first, the outside option second, and retains the
ranking among the remaining partners. Both operations preserve linearity.
-/

public import GameTheory.Core.Rank

@[expose] public section

namespace GameTheory.Rank

universe uα

variable {α : Type uα}

/-- Put one alternative first, preserving all comparisons between other alternatives. -/
def promote (ranks : α → α → Prop) (item : α) (first second : α) : Prop :=
  first = item ∨ second ≠ item ∧ ranks first second

theorem promote_linear {ranks : α → α → Prop} (linear : Linear ranks) (item : α) :
    Linear (promote ranks item) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro first
    by_cases equal : first = item
    · exact Or.inl equal
    · exact Or.inr ⟨equal, linear.1 first⟩
  · intro first middle last firstMiddle middleLast
    rcases firstMiddle with equal | ⟨different, firstMiddle⟩
    · exact Or.inl equal
    · rcases middleLast with equal | ⟨lastDifferent, middleLast⟩
      · exact False.elim (different equal)
      · exact Or.inr ⟨lastDifferent, linear.2.1 first middle last firstMiddle middleLast⟩
  · intro first second
    by_cases firstEqual : first = item
    · exact Or.inl (Or.inl firstEqual)
    by_cases secondEqual : second = item
    · exact Or.inr (Or.inl secondEqual)
    rcases linear.2.2.1 first second with firstSecond | secondFirst
    · exact Or.inl (Or.inr ⟨secondEqual, firstSecond⟩)
    · exact Or.inr (Or.inr ⟨firstEqual, secondFirst⟩)
  · intro first second firstSecond secondFirst
    rcases firstSecond with firstEqual | ⟨secondDifferent, firstSecond⟩
    · rcases secondFirst with secondEqual | ⟨firstDifferent, _⟩
      · exact firstEqual.trans secondEqual.symm
      · exact False.elim (firstDifferent firstEqual)
    · rcases secondFirst with secondEqual | ⟨_, secondFirst⟩
      · exact False.elim (secondDifferent secondEqual)
      · exact linear.2.2.2 first second firstSecond secondFirst

/-- Report exactly one partner as acceptable, placing it above the outside option. -/
def onlyAccept (ranks : Option α → Option α → Prop) (partner : α) :
    Option α → Option α → Prop :=
  promote (promote ranks none) (some partner)

theorem onlyAccept_linear {ranks : Option α → Option α → Prop}
    (linear : Linear ranks) (partner : α) : Linear (onlyAccept ranks partner) :=
  promote_linear (promote_linear linear none) (some partner)

@[simp]
theorem onlyAccept_some_none_iff (ranks : Option α → Option α → Prop)
    (partner alternative : α) :
    onlyAccept ranks partner (some alternative) none ↔ alternative = partner := by
  simp [onlyAccept, promote]

@[simp]
theorem onlyAccept_none_some_iff (ranks : Option α → Option α → Prop)
    (partner alternative : α) :
    onlyAccept ranks partner none (some alternative) ↔ alternative ≠ partner := by
  simp [onlyAccept, promote]

/-- The sole acceptable partner is at least as good as every reported alternative. -/
theorem onlyAccept_top (ranks : Option α → Option α → Prop)
    (partner : α) (alternative : Option α) :
    onlyAccept ranks partner (some partner) alternative :=
  Or.inl rfl

/-- Keep the partners' ranking and place the outside option just below the cutoff. -/
def truncate (ranks : Option α → Option α → Prop) (cutoff : α) :
    Option α → Option α → Prop
  | none, none => True
  | some first, some second => ranks (some first) (some second)
  | some first, none => ranks (some first) (some cutoff)
  | none, some second => ¬ ranks (some second) (some cutoff)

@[simp]
theorem truncate_some_some (ranks : Option α → Option α → Prop)
    (cutoff first second : α) :
    truncate ranks cutoff (some first) (some second) ↔ ranks (some first) (some second) :=
  Iff.rfl

@[simp]
theorem truncate_some_none (ranks : Option α → Option α → Prop) (cutoff first : α) :
    truncate ranks cutoff (some first) none ↔ ranks (some first) (some cutoff) :=
  Iff.rfl

@[simp]
theorem truncate_none_some (ranks : Option α → Option α → Prop) (cutoff second : α) :
    truncate ranks cutoff none (some second) ↔ ¬ ranks (some second) (some cutoff) :=
  Iff.rfl

theorem truncate_linear {ranks : Option α → Option α → Prop}
    (linear : Linear ranks) (cutoff : α) : Linear (truncate ranks cutoff) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro first
    cases first with
    | none => trivial
    | some first => exact linear.1 (some first)
  · intro first middle last firstMiddle middleLast
    cases first with
    | none =>
        cases middle with
        | none => exact middleLast
        | some middle =>
            cases last with
            | none => trivial
            | some last =>
                intro lastCutoff
                exact firstMiddle (linear.2.1 _ _ _ middleLast lastCutoff)
    | some first =>
        cases middle with
        | none =>
            cases last with
            | none => exact firstMiddle
            | some last =>
                exact (linear.2.2.1 (some first) (some last)).resolve_right
                  (fun lastFirst => middleLast (linear.2.1 _ _ _ lastFirst firstMiddle))
        | some middle =>
            cases last with
            | none => exact linear.2.1 _ _ _ firstMiddle middleLast
            | some last => exact linear.2.1 _ _ _ firstMiddle middleLast
  · intro first second
    cases first with
    | none =>
        cases second with
        | none => exact Or.inl trivial
        | some second => exact (em _).symm
    | some first =>
        cases second with
        | none => exact em _
        | some second => exact linear.2.2.1 _ _
  · intro first second firstSecond secondFirst
    cases first with
    | none =>
        cases second with
        | none => rfl
        | some second => exact False.elim (firstSecond secondFirst)
    | some first =>
        cases second with
        | none => exact False.elim (secondFirst firstSecond)
        | some second => exact linear.2.2.2 _ _ firstSecond secondFirst

end GameTheory.Rank
