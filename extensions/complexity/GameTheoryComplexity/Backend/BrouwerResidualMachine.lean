module

public import GameTheoryComplexity.Backend.SpernerCornerMachine
public import GameTheoryComplexity.Backend.WordOperations
public import GameTheory.Math.GridBrouwer

@[expose] public section

/-! Exact fixed-size residual lookup for sixth-grid points in an affine triangle.
Each input field is checked against its canonical encoding before a table entry
can be selected. The table therefore rejects malformed coordinates and colors. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.Brouwer

/-- Match exact canonical residual fields against a fixed finite table, with a total fallback. -/
def residualFieldLookup {α : Type} (encode : α → List Bool)
    (table : α → List Bool) (fallback : List Bool) : List α → List Bool → List Bool
  | [], _ => fallback
  | a :: rest, word => select (eqFlag word (encode a))
      (table a) (residualFieldLookup encode table fallback rest word)

private theorem residualFieldLookup_encode {α : Type} (encode : α → List Bool)
    (hi : Function.Injective encode) (table : α → List Bool) (fallback : List Bool)
    (entries : List α) (a : α) (ha : a ∈ entries) :
    residualFieldLookup encode table fallback entries (encode a) = table a := by
  induction entries with
  | nil => simp at ha
  | cons b rest ih =>
    rw [residualFieldLookup, eqFlag]
    by_cases he : a = b
    · subst b; simp [select]
    · have hw : encode a ≠ encode b := fun h => he (hi h)
      have hm : a ∈ rest := (List.mem_cons.mp ha).resolve_left he
      simp [hw, select, ih hm]

@[fun_prop] theorem residualFieldLookup_polyTime
    {Index Input : Type} {enc : Input ↪ List Bool}
    (encode : Index → List Bool) (table : Input → Index → List Bool)
    (entries : List Index) {word fallback : Input → List Bool}
    (hw : ComputableInPolyTime word enc encBits)
    (hf : ComputableInPolyTime fallback enc encBits)
    (ht : ∀ a, ComputableInPolyTime (fun z => table z a) enc encBits) :
    ComputableInPolyTime (fun z => residualFieldLookup encode (table z) (fallback z)
      entries (word z)) enc encBits := by
  induction entries with
  | nil => exact hf
  | cons a rest ih =>
      exact select_polyTime.comp
        ((eqFlag_polyTime.comp (hw.prod (const (encode a)))).prod ((ht a).prod ih))

private theorem residualFieldLookup_flag {α : Type} (encode : α → List Bool)
    (table : α → List Bool) (entries : List α) (word : List Bool)
    (ht : ∀ a, table a = [true] ∨ table a = [false]) :
    residualFieldLookup encode table [false] entries word = [true] ∨
      residualFieldLookup encode table [false] entries word = [false] := by
  induction entries with
  | nil => exact Or.inr rfl
  | cons a rest ih =>
    rw [residualFieldLookup, eqFlag]
    by_cases he : word = encode a
    · simpa [he, select] using ht a
    · simpa [he, select] using ih

/-- The canonical three-bit local numerator of a coordinate on a sixth grid. -/
def encodeResidualOffset (r : Fin 7) : List Bool := lowBits 3 r.val

private theorem encodeResidualOffset_injective : Function.Injective encodeResidualOffset := by
  intro a b h
  have ha : a.val < 2 ^ 3 := by omega
  have hb : b.val < 2 ^ 3 := by omega
  have hv := congrArg lsbValue h
  simpa [encodeResidualOffset, lsbValue_lowBits ha,
    lsbValue_lowBits hb, Fin.ext_iff] using hv

private theorem encodeGridColor_injective : Function.Injective encodeGridColor := by
  intro a b h
  simpa only [decodeGridColor_encode] using congrArg decodeGridColor h

/-- Exact affine residual at a sixth-grid point. The diagonal is assigned to
the lower triangle; both formulas agree there. -/
def sixthGridDisplacement (rx ry : Fin 7) (a b c : Fin 3) : ℚ × ℚ :=
  if rx.val < ry.val then
    weightedDisplacement a b c ((6 - (ry.val : ℚ)) / 6)
      ((rx.val : ℚ) / 6) (((ry.val : ℚ) - rx.val) / 6)
  else
    weightedDisplacement a b c ((6 - (rx.val : ℚ)) / 6)
      (((rx.val : ℚ) - ry.val) / 6) ((ry.val : ℚ) / 6)

/-- Both coordinates of the affine residual have magnitude at most one sixth. -/
def SixthGridSmallResidual (rx ry : Fin 7) (a b c : Fin 3) : Prop :=
  |(sixthGridDisplacement rx ry a b c).1| ≤ 1 / 6 ∧
    |(sixthGridDisplacement rx ry a b c).2| ≤ 1 / 6

instance (rx ry : Fin 7) (a b c : Fin 3) :
    Decidable (SixthGridSmallResidual rx ry a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A constant finite lookup checks the exact residual, including the weights.
Invalid fields select the rejecting fallback rather than normalizing inputs. -/
def residualVerdict (rx ry a b c : List Bool) : List Bool :=
  residualFieldLookup encodeResidualOffset (fun i =>
    residualFieldLookup encodeResidualOffset (fun j =>
      residualFieldLookup encodeGridColor (fun x =>
        residualFieldLookup encodeGridColor (fun y =>
          residualFieldLookup encodeGridColor
            (fun z => [decide (SixthGridSmallResidual i j x y z)])
            [false] (List.finRange 3) c)
          [false] (List.finRange 3) b)
        [false] (List.finRange 3) a)
      [false] (List.finRange 7) ry)
    [false] (List.finRange 7) rx

/-- Lookup acceptance agrees with the actual weighted affine residual. -/
theorem residualVerdict_accept (rx ry : Fin 7) (a b c : Fin 3) :
    residualVerdict (encodeResidualOffset rx) (encodeResidualOffset ry)
      (encodeGridColor a) (encodeGridColor b) (encodeGridColor c) = [true] ↔
    SixthGridSmallResidual rx ry a b c := by
  simp only [residualVerdict,
    residualFieldLookup_encode encodeResidualOffset encodeResidualOffset_injective
      _ _ _ _ (List.mem_finRange _),
    residualFieldLookup_encode encodeGridColor encodeGridColor_injective
      _ _ _ _ (List.mem_finRange _), List.cons.injEq, and_true, decide_eq_true_eq]

/-- Exact five-field residual lookup has one native polynomial-time machine. -/
@[fun_prop] theorem residualVerdict_polyTime
    {Input : Type} {enc : Input ↪ List Bool} {rx ry a b c : Input → List Bool}
    (hx : ComputableInPolyTime rx enc encBits)
    (hy : ComputableInPolyTime ry enc encBits)
    (ha : ComputableInPolyTime a enc encBits)
    (hb : ComputableInPolyTime b enc encBits)
    (hc : ComputableInPolyTime c enc encBits) :
    ComputableInPolyTime (fun z => residualVerdict (rx z) (ry z) (a z) (b z) (c z))
      enc encBits := by
  unfold residualVerdict
  apply residualFieldLookup_polyTime _ _ _ hx (const [false])
  intro i
  apply residualFieldLookup_polyTime _ _ _ hy (const [false])
  intro j
  apply residualFieldLookup_polyTime _ _ _ ha (const [false])
  intro x
  apply residualFieldLookup_polyTime _ _ _ hb (const [false])
  intro y
  apply residualFieldLookup_polyTime _ _ _ hc (const [false])
  intro z
  exact const _

theorem residualVerdict_flag (rx ry a b c : List Bool) :
    residualVerdict rx ry a b c = [true] ∨ residualVerdict rx ry a b c = [false] := by
  unfold residualVerdict
  apply residualFieldLookup_flag
  intro i
  apply residualFieldLookup_flag
  intro j
  apply residualFieldLookup_flag
  intro x
  apply residualFieldLookup_flag
  intro y
  apply residualFieldLookup_flag
  intro z
  by_cases h : SixthGridSmallResidual i j x y z <;> simp [h]

end GameTheory.Complexity.Backend
