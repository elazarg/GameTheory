module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

/-! Concrete Boolean-word operations retain their behavior on arbitrary words.
A flag reads its first bit and treats an empty word as false; additional bits
are ignored. Equality compares complete words. Indexed access and slicing use
unary natural indices, charging their values as well as the input words.
-/

namespace GameTheory.Complexity.Backend.WordOperations

open Turing.MultiTapeTM

/-- Conjunction of the first bits, with false for an absent bit. -/
def andFlag (left right : List Bool) : List Bool :=
  [left.headD false && right.headD false]

/-- Disjunction of the first bits, with false for an absent bit. -/
def orFlag (left right : List Bool) : List Bool :=
  [left.headD false || right.headD false]

/-- Negation of the first bit, with false for an absent bit. -/
def notFlag (word : List Bool) : List Bool := [!word.headD false]

/-- Full word equality produces one Boolean result bit. -/
def eqFlag (left right : List Bool) : List Bool := [decide (left = right)]

/-- Select a word using the first flag bit; an empty flag selects the second branch. -/
def select (flag yes no : List Bool) : List Bool := if flag.headD false then yes else no

/-- Read one bit, producing false when the unary index is outside the word. -/
def indexedFlag (index : ℕ) (word : List Bool) : List Bool := [word.getD index false]

@[fun_prop] theorem andFlag_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => andFlag p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  exact .bitsCons (.bool_and' (hhead.comp (.fst encBits encBits))
    (hhead.comp (.snd encBits encBits))) (.const [])

@[fun_prop] theorem orFlag_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => orFlag p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  exact .bitsCons (ComputableInPolyTime.bool_or.comp ((hhead.comp (.fst encBits encBits)).prod
    (hhead.comp (.snd encBits encBits)))) (.const [])

@[fun_prop] theorem notFlag_polyTime :
    ComputableInPolyTime notFlag encBits encBits := by
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  exact .bitsCons (ComputableInPolyTime.bool_not.comp hhead) (.const [])

@[fun_prop] theorem eqFlag_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => eqFlag p.1 p.2)
      (encPair encBits encBits) encBits :=
  .bitsCons (.decide_eq' (.fst encBits encBits) (.snd encBits encBits)) (.const [])

@[fun_prop] theorem select_polyTime :
    ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) =>
      select p.1 p.2.1 p.2.2) (encPair encBits (encPair encBits encBits)) encBits := by
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  have hrest := ComputableInPolyTime.snd encBits (encPair encBits encBits)
  exact (hhead.comp (.fst encBits (encPair encBits encBits))).ite
    ((ComputableInPolyTime.fst encBits encBits).comp hrest)
    ((ComputableInPolyTime.snd encBits encBits).comp hrest)

@[fun_prop] theorem indexedFlag_polyTime :
    ComputableInPolyTime (fun p : ℕ × List Bool => indexedFlag p.1 p.2)
      (encPair encUnary encBits) encBits :=
  .bitsCons (.bitsGetDWithInput (.snd encUnary encBits) (.fst encUnary encBits) false)
    (.const [])

@[fun_prop] theorem take_polyTime :
    ComputableInPolyTime (fun p : ℕ × List Bool => p.2.take p.1)
      (encPair encUnary encBits) encBits :=
  .bitsTakeWithInput (.snd encUnary encBits) (.fst encUnary encBits)

@[fun_prop] theorem drop_polyTime :
    ComputableInPolyTime (fun p : ℕ × List Bool => p.2.drop p.1)
      (encPair encUnary encBits) encBits :=
  .bitsDropWithInput (.snd encUnary encBits) (.fst encUnary encBits)

@[simp] theorem andFlag_eq_true_iff (left right : List Bool) :
    andFlag left right = [true] ↔ left.headD false = true ∧ right.headD false = true := by
  simp [andFlag]

@[simp] theorem orFlag_eq_true_iff (left right : List Bool) :
    orFlag left right = [true] ↔ left.headD false = true ∨ right.headD false = true := by
  simp [orFlag]

@[simp] theorem notFlag_eq_true_iff (word : List Bool) :
    notFlag word = [true] ↔ word.headD false = false := by simp [notFlag]

@[simp] theorem eqFlag_eq_true_iff (left right : List Bool) :
    eqFlag left right = [true] ↔ left = right := by simp [eqFlag]

@[simp] theorem select_nil (yes no : List Bool) : select [] yes no = no := rfl

@[simp] theorem select_cons (bit : Bool) (tail yes no : List Bool) :
    select (bit :: tail) yes no = if bit then yes else no := rfl

theorem indexedFlag_eq_getElem? (index : ℕ) (word : List Bool) :
    indexedFlag index word = [word[index]?.getD false] := by
  simp only [indexedFlag, List.getD_eq_getElem?_getD]

end GameTheory.Complexity.Backend.WordOperations
