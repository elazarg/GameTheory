import GameTheoryComplexity.Backend.SpernerCornerMachine
import GameTheory.Math.GridBrouwer

/-! Exact fixed-size residual lookup for sixth-grid points in an affine triangle.
Each input field is checked against its canonical encoding before a table entry
can be selected. The table therefore rejects malformed coordinates and colors. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Brouwer

private def finiteLookup {α : Type} (encode : α → List Bool)
    (table : α → List Bool) (fallback : List Bool) : List α → List Bool → List Bool
  | [], _ => fallback
  | a :: rest, word => caseBit₀ (eqFlag word (encode a))
      (table a) (finiteLookup encode table fallback rest word)

private theorem eqFlag_decide (a b : List Bool) :
    eqFlag a b = [decide (a = b)] := by
  rcases eqFlag_flag a b with h | h
  · rw [h, show a = b from (eqFlag_eq_true_iff a b).mp h]
    simp
  · have he : a ≠ b := fun he => by
      have ht := (eqFlag_eq_true_iff a b).mpr he
      simp [h] at ht
    simp [h, he]

private theorem finiteLookup_encode {α : Type} (encode : α → List Bool)
    (hi : Function.Injective encode) (table : α → List Bool) (fallback : List Bool)
    (entries : List α) (a : α) (ha : a ∈ entries) :
    finiteLookup encode table fallback entries (encode a) = table a := by
  induction entries with
  | nil => simp at ha
  | cons b rest ih =>
    rw [finiteLookup, eqFlag_decide]
    by_cases he : a = b
    · subst b; simp [caseBit₀]
    · have hw : encode a ≠ encode b := fun h => he (hi h)
      have hm : a ∈ rest := (List.mem_cons.mp ha).resolve_left he
      simp [hw, caseBit₀, ih hm]

private theorem finiteLookup_cobham {α : Type} {n : ℕ}
    (encode : α → List Bool) (table : (Fin n → List Bool) → α → List Bool)
    (entries : List α) {word fallback : (Fin n → List Bool) → List Bool}
    (hw : Cobham word) (hf : Cobham fallback)
    (ht : ∀ a, Cobham (fun z => table z a)) :
    Cobham (fun z => finiteLookup encode (table z) (fallback z) entries (word z)) := by
  induction entries with
  | nil => exact hf
  | cons a rest ih =>
    exact Cobham.iteFn (Cobham.eqFlag_mem hw (Cobham.const (encode a))) (ht a) ih

private theorem finiteLookup_flag {α : Type} (encode : α → List Bool)
    (table : α → List Bool) (entries : List α) (word : List Bool)
    (ht : ∀ a, table a = [true] ∨ table a = [false]) :
    finiteLookup encode table [false] entries word = [true] ∨
      finiteLookup encode table [false] entries word = [false] := by
  induction entries with
  | nil => exact Or.inr rfl
  | cons a rest ih =>
    rw [finiteLookup, eqFlag_decide]
    by_cases he : word = encode a
    · simpa [he, caseBit₀] using ht a
    · simpa [he, caseBit₀] using ih

/-- The canonical three-bit local numerator of a coordinate on a sixth grid. -/
def encodeResidualOffset (r : Fin 7) : List Bool := Nat.toBitsLE 3 r.val

private theorem encodeResidualOffset_injective : Function.Injective encodeResidualOffset := by
  intro a b h
  have ha : a.val < 2 ^ 3 := by omega
  have hb : b.val < 2 ^ 3 := by omega
  have hv := congrArg Nat.fromBitsLE h
  simpa [encodeResidualOffset, Nat.fromBitsLE_toBitsLE ha,
    Nat.fromBitsLE_toBitsLE hb, Fin.ext_iff] using hv

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
  finiteLookup encodeResidualOffset (fun i =>
    finiteLookup encodeResidualOffset (fun j =>
      finiteLookup encodeGridColor (fun x =>
        finiteLookup encodeGridColor (fun y =>
          finiteLookup encodeGridColor
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
    finiteLookup_encode encodeResidualOffset encodeResidualOffset_injective
      _ _ _ _ (List.mem_finRange _),
    finiteLookup_encode encodeGridColor encodeGridColor_injective
      _ _ _ _ (List.mem_finRange _), List.cons.injEq, and_true, decide_eq_true_eq]

/-- The entire five-field verifier has a polynomial-time machine certificate. -/
theorem residualVerdict_cobham :
    Cobham (fun z : Fin 5 → List Bool => residualVerdict (z 0) (z 1) (z 2) (z 3) (z 4)) := by
  unfold residualVerdict
  apply finiteLookup_cobham _ _ _ (Cobham.proj 0) (Cobham.const [false])
  intro i
  apply finiteLookup_cobham _ _ _ (Cobham.proj 1) (Cobham.const [false])
  intro j
  apply finiteLookup_cobham _ _ _ (Cobham.proj 2) (Cobham.const [false])
  intro a
  apply finiteLookup_cobham _ _ _ (Cobham.proj 3) (Cobham.const [false])
  intro b
  apply finiteLookup_cobham _ _ _ (Cobham.proj 4) (Cobham.const [false])
  intro c
  exact Cobham.const _

theorem residualVerdict_mem_FPn :
    FPn (fun z : Fin 5 → List Bool => residualVerdict (z 0) (z 1) (z 2) (z 3) (z 4)) :=
  cobham_iff_FPn.mp residualVerdict_cobham

theorem residualVerdict_flag (rx ry a b c : List Bool) :
    residualVerdict rx ry a b c = [true] ∨ residualVerdict rx ry a b c = [false] := by
  unfold residualVerdict
  apply finiteLookup_flag
  intro i
  apply finiteLookup_flag
  intro j
  apply finiteLookup_flag
  intro x
  apply finiteLookup_flag
  intro y
  apply finiteLookup_flag
  intro z
  by_cases h : SixthGridSmallResidual i j x y z <;> simp [h]

/-- The residual lookup composes with arbitrary polynomial-time field producers. -/
theorem residualVerdictFn_mem_FP {rx ry a b c : List Bool → List Bool}
    (hx : rx ∈ FP) (hy : ry ∈ FP) (ha : a ∈ FP) (hb : b ∈ FP) (hc : c ∈ FP) :
    (fun z => residualVerdict (rx z) (ry z) (a z) (b z) (c z)) ∈ FP := by
  apply CobhamFP_subset_FP
  have hfields : ∀ i : Fin 5, Cobham
      (![fun z : Fin 1 → List Bool => rx (z 0), fun z => ry (z 0),
        fun z => a (z 0), fun z => b (z 0), fun z => c (z 0)] i) := by
    intro i
    fin_cases i
    · exact FP_subset_CobhamFP hx
    · exact FP_subset_CobhamFP hy
    · exact FP_subset_CobhamFP ha
    · exact FP_subset_CobhamFP hb
    · exact FP_subset_CobhamFP hc
  exact (Cobham.comp residualVerdict_cobham hfields).of_eq fun _ => rfl

end GameTheory.Complexity.Backend
