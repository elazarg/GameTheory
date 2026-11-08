module

public import GameTheoryComplexity.Backend.BinarySignedAddition
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Signed summation over a fixed, compile-time number of indexed queries. -/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open scoped BigOperators

/-- Sum a fixed number of signed queries; indexed rulers have canonical false contents. -/
def binarySignedFiniteSum {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool) :
    ℕ → (Fin p → List Bool) → List Bool
  | 0, _ => []
  | n + 1, params => binarySignedAdd (binarySignedFiniteSum term n params)
      (term (Fin.cons (List.replicate n false) params))

private theorem binarySignedFiniteSum_step_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (ht : ComputableInPolyTime term (encPi encBits) encBits) (n : ℕ)
    (hparams : ComputableInPolyTime (binarySignedFiniteSum term n)
      (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun v : Fin p → List Bool =>
        binarySignedAdd (binarySignedFiniteSum term n v)
          (term (Fin.cons (List.replicate n false) v)))
      (encPi encBits) encBits := by
  have hcons : ComputableInPolyTime
      (fun v : Fin p → List Bool => Fin.cons (List.replicate n false) v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .const (List.replicate n false)
    · exact ComputableInPolyTime.pi_apply encBits j
  exact binarySignedAdd_polyTime hparams (ht.comp hcons)

/-- The count is fixed in this polynomial-time certificate. -/
@[fun_prop] theorem binarySignedFiniteSum_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (ht : ComputableInPolyTime term (encPi encBits) encBits) (n : ℕ) :
    ComputableInPolyTime (binarySignedFiniteSum term n) (encPi encBits) encBits := by
  induction n with
  | zero => exact .const []
  | succ n ih =>
    change ComputableInPolyTime
      (fun v : Fin p → List Bool =>
        binarySignedAdd (binarySignedFiniteSum term n v)
          (term (Fin.cons (List.replicate n false) v)))
      (encPi encBits) encBits
    exact binarySignedFiniteSum_step_polyTime ht n ih

/-- Signed values add exactly, without field-width or sign assumptions. -/
theorem binarySignedFiniteSum_value {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool) (n : ℕ) (params : Fin p → List Bool) :
    binarySignedValue (binarySignedFiniteSum term n params) =
      ∑ i ∈ Finset.range n,
        binarySignedValue (term (Fin.cons (List.replicate i false) params)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binarySignedFiniteSum, binarySignedAdd_value, ih, Finset.sum_range_succ]

/-- Add a fixed list of signed query machines; the list is fixed in its FP certificate. -/
def binarySignedQuerySum {p : ℕ}
    (queries : List ((Fin p → List Bool) → List Bool)) (v : Fin p → List Bool) : List Bool :=
  queries.foldr (fun query rest => binarySignedAdd (query v) rest) []

/-- A fixed finite collection of polynomial-time queries has a polynomial-time signed sum. -/
@[fun_prop] theorem binarySignedQuerySum_polyTime {p : ℕ}
    (queries : List ((Fin p → List Bool) → List Bool))
    (hq : ∀ query ∈ queries,
      ComputableInPolyTime query (encPi encBits) encBits) :
    ComputableInPolyTime (binarySignedQuerySum queries) (encPi encBits) encBits := by
  induction queries with
  | nil => exact .const []
  | cons query queries ih =>
    have ht : ComputableInPolyTime (binarySignedQuerySum queries) (encPi encBits) encBits :=
      ih (fun q h => hq q (List.mem_cons_of_mem _ h))
    exact binarySignedAdd_polyTime (hq query List.mem_cons_self) ht

/-- Signed values add without overflow or representation assumptions. -/
theorem binarySignedQuerySum_value {p : ℕ}
    (queries : List ((Fin p → List Bool) → List Bool)) (v : Fin p → List Bool) :
    binarySignedValue (binarySignedQuerySum queries v) =
      (queries.map fun query => binarySignedValue (query v)).sum := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
    change binarySignedValue (binarySignedAdd (query v) (binarySignedQuerySum queries v)) = _
    rw [binarySignedAdd_value, ih]
    rfl

end GameTheory.Complexity.Backend
