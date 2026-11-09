module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

@[expose] public section

/-! Explicit row-major emission of payoff encodings. Unary row and column ranges
are traversed in full. Native flat-map certificates charge every callback input,
all intermediate cell words and their concatenation into the final table.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- Emit every column of one row in increasing index order. -/
def payoffRow {Context : Type} (cell : Context → ℕ → ℕ → List Bool)
    (context : Context) (row columns : ℕ) : List Bool :=
  (List.range columns).flatMap (cell context row)

/-- A certified cell evaluator and unary column count give a certified complete row. -/
theorem payoffRow_polyTime
    {Input Context : Type} {inputEncoding : Input ↪ List Bool}
    {contextEncoding : Context ↪ List Bool}
    {context : Input → Context} {row columns : Input → ℕ}
    {cell : Context → ℕ → ℕ → List Bool}
    (hcontext : ComputableInPolyTime context inputEncoding contextEncoding)
    (hrow : ComputableInPolyTime row inputEncoding encUnary)
    (hcolumns : ComputableInPolyTime columns inputEncoding encUnary)
    (hcell : ComputableInPolyTime
      (fun pair : (Context × ℕ) × ℕ => cell pair.1.1 pair.1.2 pair.2)
      (encPair (encPair contextEncoding encUnary) encUnary) encBits) :
    ComputableInPolyTime
      (fun input => payoffRow cell (context input) (row input) (columns input))
      inputEncoding encBits := by
  have hlist : ComputableInPolyTime (fun input => List.range (columns input))
      inputEncoding (encList encUnary) :=
    .of_tidy (ComputableTidilyInPolyTime.range.comp hcolumns.tidy)
  have hinput : ComputableInPolyTime (fun pair : Input × ℕ => pair.1)
      (encPair inputEncoding encUnary) inputEncoding := .fst inputEncoding encUnary
  have hcallback : ComputableInPolyTime
      (fun pair : Input × ℕ => cell (context pair.1) (row pair.1) pair.2)
      (encPair inputEncoding encUnary) encBits :=
    hcell.comp (((hcontext.comp hinput).prod (hrow.comp hinput)).prod
      (.snd inputEncoding encUnary))
  exact ComputableInPolyTime.flatMapToBitsWithInput hlist hcallback

/-- Emit every cell of a square table, ordered first by row and then by column. -/
def payoffTable {Context : Type} (cell : Context → ℕ → ℕ → List Bool)
    (context : Context) (dimension : ℕ) : List Bool :=
  (List.range dimension).flatMap fun row => payoffRow cell context row dimension

/-- The two finite traversals compute every cell. A uniform cell certificate charges
its context and both unary indices, including the growing intermediate output words. -/
theorem payoffTable_polyTime
    {Input Context : Type} {inputEncoding : Input ↪ List Bool}
    {contextEncoding : Context ↪ List Bool}
    {context : Input → Context} {dimension : Input → ℕ}
    {cell : Context → ℕ → ℕ → List Bool}
    (hcontext : ComputableInPolyTime context inputEncoding contextEncoding)
    (hdimension : ComputableInPolyTime dimension inputEncoding encUnary)
    (hcell : ComputableInPolyTime
      (fun pair : (Context × ℕ) × ℕ => cell pair.1.1 pair.1.2 pair.2)
      (encPair (encPair contextEncoding encUnary) encUnary) encBits) :
    ComputableInPolyTime
      (fun input => payoffTable cell (context input) (dimension input))
      inputEncoding encBits := by
  have hlist : ComputableInPolyTime (fun input => List.range (dimension input))
      inputEncoding (encList encUnary) :=
    .of_tidy (ComputableTidilyInPolyTime.range.comp hdimension.tidy)
  have hinput : ComputableInPolyTime (fun pair : Input × ℕ => pair.1)
      (encPair inputEncoding encUnary) inputEncoding := .fst inputEncoding encUnary
  have hcallback : ComputableInPolyTime
      (fun pair : Input × ℕ => payoffRow cell (context pair.1) pair.2 (dimension pair.1))
      (encPair inputEncoding encUnary) encBits :=
    payoffRow_polyTime (hcontext.comp hinput) (.snd inputEncoding encUnary)
      (hdimension.comp hinput) hcell
  exact ComputableInPolyTime.flatMapToBitsWithInput hlist hcallback

end GameTheory.Complexity.Backend
