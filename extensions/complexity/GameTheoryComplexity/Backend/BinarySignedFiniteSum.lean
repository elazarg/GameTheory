module

public import GameTheoryComplexity.Backend.BinarySignedAddition
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Signed query sums retain arbitrary typed context. Indexed sums visit a fixed
number of false-bit ordinal rulers in ascending order; query lists use a right fold.
Their native certificates charge the supplied context producer. -/
namespace GameTheory.Complexity.Backend
open Turing.MultiTapeTM
open scoped BigOperators

/-- Add indexed queries from zero upward, using canonical false-bit ordinal rulers. -/
def binarySignedFiniteSum {Context : Type} (term : List Bool → Context → List Bool) :
    ℕ → Context → List Bool
  | 0, _ => []
  | n + 1, context => binarySignedAdd (binarySignedFiniteSum term n context)
      (term (List.replicate n false) context)

/-- The count is fixed; each indexed query reads the same certified context producer. -/
@[fun_prop] theorem binarySignedFiniteSum_polyTime {Context Input : Type}
    {contextEncoding : Context ↪ List Bool} {input : Input ↪ List Bool}
    {term : List Bool → Context → List Bool}
    (ht : ComputableInPolyTime (fun p : Context × List Bool => term p.2 p.1)
      (encPair contextEncoding encBits) encBits) (n : ℕ)
    {context : Input → Context} (hc : ComputableInPolyTime context input contextEncoding) :
    ComputableInPolyTime (fun a => binarySignedFiniteSum term n (context a)) input encBits := by
  induction n with
  | zero => exact ComputableInPolyTime.const []
  | succ n ih =>
    exact binarySignedAdd_polyTime ih
      (ht.comp (hc.prod (ComputableInPolyTime.const (List.replicate n false))))

/-- Signed values add exactly without field-width or sign assumptions. -/
theorem binarySignedFiniteSum_value {Context : Type}
    (term : List Bool → Context → List Bool) (n : ℕ) (context : Context) :
    binarySignedValue (binarySignedFiniteSum term n context) =
      ∑ i ∈ Finset.range n, binarySignedValue (term (List.replicate i false) context) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binarySignedFiniteSum, binarySignedAdd_value, ih, Finset.sum_range_succ]

/-- Add a fixed list of signed query machines in their existing right-fold order. -/
def binarySignedQuerySum {Context : Type}
    (queries : List (Context → List Bool)) (context : Context) : List Bool :=
  queries.foldr (fun query rest => binarySignedAdd (query context) rest) []

/-- A fixed list of native query machines composes with a certified context producer. -/
@[fun_prop] theorem binarySignedQuerySum_polyTime {Context Input : Type}
    {contextEncoding : Context ↪ List Bool} {input : Input ↪ List Bool}
    (queries : List (Context → List Bool))
    (hq : ∀ query ∈ queries, ComputableInPolyTime query contextEncoding encBits)
    {context : Input → Context} (hc : ComputableInPolyTime context input contextEncoding) :
    ComputableInPolyTime (fun a => binarySignedQuerySum queries (context a)) input encBits := by
  induction queries with
  | nil => exact ComputableInPolyTime.const []
  | cons query queries ih =>
    have ht : ComputableInPolyTime
        (fun a => binarySignedQuerySum queries (context a)) input encBits :=
      ih (fun q h => hq q (List.mem_cons_of_mem _ h))
    exact binarySignedAdd_polyTime ((hq query List.mem_cons_self).comp hc) ht

/-- Signed values add without overflow or representation assumptions. -/
theorem binarySignedQuerySum_value {Context : Type}
    (queries : List (Context → List Bool)) (context : Context) :
    binarySignedValue (binarySignedQuerySum queries context) =
      (queries.map fun query => binarySignedValue (query context)).sum := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
    change binarySignedValue (binarySignedAdd (query context)
      (binarySignedQuerySum queries context)) = _
    rw [binarySignedAdd_value, ih]
    rfl

end GameTheory.Complexity.Backend
