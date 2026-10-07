import GameTheoryComplexity.Backend.SATTableMachine
import GameTheoryComplexity.Backend.SATTableEmission
import GameTheoryComplexity.Backend.SATSyntaxMachine

/-! Polynomial-time explicit payoff-table generation. Scalar payoffs use fixed-width
positive and negative tally blocks. The second player's payoff is the transpose.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- A unary ruler for the padded variable and clause counts. -/
def satUnaryN (input : List Bool) : List Bool := Complexity.smash input [true] ++ [true]

/-- A unary ruler for all literal, variable, clause, and fallback actions. -/
def satUnaryQ (input : List Bool) : List Bool := (List.replicate 4 (satUnaryN input)).flatten ++ [true]

/-- Common width of each positive or negative payoff tally. -/
def satTallyWidth (input : List Bool) : List Bool := satUnaryQ input ++ [true, true]

/-- Encode a scalar payoff by its positive and negative unary magnitudes. -/
def satTallyPair (width positive negative : List Bool) : List Bool :=
  padTo width positive ++ padTo width negative

@[simp] theorem satUnaryN_length (input : List Bool) : (satUnaryN input).length = input.length + 1 := by
  simp [satUnaryN]

@[simp] theorem satUnaryQ_length (input : List Bool) : (satUnaryQ input).length = 4 * (input.length + 1) + 1 := by
  simp [satUnaryQ]
  omega

@[simp] theorem satTallyWidth_length (input : List Bool) :
    (satTallyWidth input).length = 4 * (input.length + 1) + 3 := by
  simp [satTallyWidth]

@[simp] theorem satTallyPair_length (width positive negative : List Bool) :
    (satTallyPair width positive negative).length = 2 * width.length := by
  simp [satTallyPair]
  omega

theorem satUnaryN_cobham : Cobham fun v : Fin 1 → List Bool => satUnaryN (v 0) :=
  Cobham.appendFn (Cobham.comp₂ Cobham.smash (Cobham.proj 0) (Cobham.const [true])) (Cobham.const [true])

theorem satUnaryQ_cobham : Cobham fun v : Fin 1 → List Bool => satUnaryQ (v 0) :=
  Cobham.appendFn (Cobham.repeatFn satUnaryN_cobham 4) (Cobham.const [true])

theorem satTallyWidth_cobham : Cobham fun v : Fin 1 → List Bool => satTallyWidth (v 0) :=
  Cobham.appendFn satUnaryQ_cobham (Cobham.const [true, true])

private theorem satTallyPair_cobham {n : ℕ} {w p q : (Fin n → List Bool) → List Bool}
    (hw : Cobham w) (hp : Cobham p) (hq : Cobham q) :
    Cobham fun v => satTallyPair (w v) (p v) (q v) :=
  Cobham.appendFn (Cobham.padFn hw hp) (Cobham.padFn hw hq)

/-- Encode one row payoff, using a supplied certified syntax-validity verdict.
Arguments are unary row index, unary column index, and the source SAT string. -/
def satPayoffCell (valid : List Bool → List Bool) (v : Fin 3 → List Bool) : List Bool :=
  let n := satUnaryN (v 2)
  let n2 := n ++ n
  let n3 := n2 ++ n
  let n4 := n3 ++ n
  let width := satTallyWidth (v 2)
  let row := v 0
  let col := v 1
  let rowPositive := notBit (lenLeFlag row n)
  let colPositive := notBit (lenLeFlag col n)
  let rowVar := caseBit₀ rowPositive row (row.drop n.length)
  let colVar := caseBit₀ colPositive col (col.drop n.length)
  let rowLiteral := notBit (lenLeFlag row n2)
  let colLiteral := notBit (lenLeFlag col n2)
  let z0 := satTallyPair width [] []
  let z1 := satTallyPair width [true] []
  let z2 := satTallyPair width [true, true] []
  let zm2 := satTallyPair width [] [true, true]
  let z2n := satTallyPair width ([true, true].drop n.length) (n.drop 2)
  let opposed := andBit (eqFlag rowVar colVar) (notBit (eqFlag rowPositive colPositive))
  let incidence := andBit (valid (v 2))
    (incidenceVerdictWord ![colVar, colPositive, row.drop n3.length, v 2])
  caseBit₀ (eqFlag row n4)
    (caseBit₀ (eqFlag col n4) z0 z1)
    (caseBit₀ rowLiteral (caseBit₀ colLiteral (caseBit₀ opposed zm2 z1) zm2)
      (caseBit₀ (notBit (lenLeFlag row n3))
        (caseBit₀ colLiteral (caseBit₀ (eqFlag (row.drop n2.length) colVar) z2n z2) zm2)
        (caseBit₀ (notBit (lenLeFlag row n4))
          (caseBit₀ colLiteral (caseBit₀ incidence z2n z2) zm2) zm2)))

/-- The explicit cell function has a genuine polynomial-time implementation. -/
theorem satPayoffCell_cobham {valid : List Bool → List Bool}
    (hv : Cobham fun v : Fin 1 → List Bool => valid (v 0)) : Cobham (satPayoffCell valid) := by
  let n := fun v : Fin 3 → List Bool => satUnaryN (v 2)
  let n2 := fun v => n v ++ n v
  let n3 := fun v => n2 v ++ n v
  let n4 := fun v => n3 v ++ n v
  let width := fun v : Fin 3 → List Bool => satTallyWidth (v 2)
  let rowPositive := fun v => notBit (lenLeFlag (v 0) (n v))
  let colPositive := fun v => notBit (lenLeFlag (v 1) (n v))
  let rowVar := fun v => caseBit₀ (rowPositive v) (v 0) ((v 0).drop (n v).length)
  let colVar := fun v => caseBit₀ (colPositive v) (v 1) ((v 1).drop (n v).length)
  let rowLiteral := fun v => notBit (lenLeFlag (v 0) (n2 v))
  let colLiteral := fun v => notBit (lenLeFlag (v 1) (n2 v))
  have hn : Cobham n := (Cobham.comp satUnaryN_cobham fun _ => Cobham.proj 2).of_eq fun _ => rfl
  have hn2 : Cobham n2 := Cobham.appendFn hn hn
  have hn3 : Cobham n3 := Cobham.appendFn hn2 hn
  have hn4 : Cobham n4 := Cobham.appendFn hn3 hn
  have hw : Cobham width := (Cobham.comp satTallyWidth_cobham fun _ => Cobham.proj 2).of_eq fun _ => rfl
  have hrp : Cobham rowPositive := Cobham.notFn (lenLeFlag_mem (Cobham.proj 0) hn)
  have hcp : Cobham colPositive := Cobham.notFn (lenLeFlag_mem (Cobham.proj 1) hn)
  have hrv : Cobham rowVar := Cobham.iteFn hrp (Cobham.proj 0) (Cobham.dropFn hn (Cobham.proj 0))
  have hcv : Cobham colVar := Cobham.iteFn hcp (Cobham.proj 1) (Cobham.dropFn hn (Cobham.proj 1))
  have hrl : Cobham rowLiteral := Cobham.notFn (lenLeFlag_mem (Cobham.proj 0) hn2)
  have hcl : Cobham colLiteral := Cobham.notFn (lenLeFlag_mem (Cobham.proj 1) hn2)
  have hz0 := satTallyPair_cobham hw Cobham.empty Cobham.empty
  have hz1 := satTallyPair_cobham hw (Cobham.const [true]) Cobham.empty
  have hz2 := satTallyPair_cobham hw (Cobham.const [true, true]) Cobham.empty
  have hzm2 := satTallyPair_cobham hw Cobham.empty (Cobham.const [true, true])
  have hz2n := satTallyPair_cobham hw
    (Cobham.dropFn hn (Cobham.const [true, true])) (Cobham.dropFn (Cobham.const [true, true]) hn)
  have hopposed := Cobham.andFn (eqFlag_mem hrv hcv) (Cobham.notFn (eqFlag_mem hrp hcp))
  have hquery := Cobham.comp incidenceVerdictWord_cobham
    (gs := fun i => fun v : Fin 3 → List Bool =>
      (![colVar v, colPositive v, (v 0).drop (n3 v).length, v 2] : Fin 4 → List Bool) i) (by
        intro i
        fin_cases i
        · exact hcv
        · exact hcp
        · exact Cobham.dropFn hn3 (Cobham.proj 0)
        · exact Cobham.proj 2)
  have hvalid : Cobham fun v : Fin 3 → List Bool => valid (v 2) :=
    (Cobham.comp hv fun _ => Cobham.proj 2).of_eq fun _ => rfl
  have hi := Cobham.andFn hvalid hquery
  exact Cobham.iteFn (eqFlag_mem (Cobham.proj 0) hn4)
    (Cobham.iteFn (eqFlag_mem (Cobham.proj 1) hn4) hz0 hz1)
    (Cobham.iteFn hrl (Cobham.iteFn hcl (Cobham.iteFn hopposed hzm2 hz1) hzm2)
      (Cobham.iteFn (Cobham.notFn (lenLeFlag_mem (Cobham.proj 0) hn3))
        (Cobham.iteFn hcl (Cobham.iteFn (eqFlag_mem (Cobham.dropFn hn2 (Cobham.proj 0)) hcv) hz2n hz2) hzm2)
        (Cobham.iteFn (Cobham.notFn (lenLeFlag_mem (Cobham.proj 0) hn4))
          (Cobham.iteFn hcl (Cobham.iteFn hi hz2n hz2) hzm2) hzm2)))

private theorem caseBit_length_eq {s x y : List Bool} {k : ℕ}
    (hx : x.length = k) (hy : y.length = k) : (caseBit₀ s x y).length = k := by
  cases s with
  | nil => exact hy
  | cons bit s => cases bit <;> assumption

/-- Each explicit payoff entry has exactly two common-width tally blocks. -/
theorem satPayoffCell_length (valid : List Bool → List Bool) (v : Fin 3 → List Bool) :
    (satPayoffCell valid v).length = 2 * (satTallyWidth (v 2)).length := by
  unfold satPayoffCell
  repeat (first | apply caseBit_length_eq | exact satTallyPair_length _ _ _)

/-- Bound for the polynomial-time row-major emitter. -/
def satCellWidth (input : List Bool) : List Bool := satTallyWidth input ++ satTallyWidth input

/-- Write the unary dimension header and every row-major integer payoff entry. -/
def satTableEncode (input : List Bool) : List Bool :=
  satUnaryQ input ++ [false] ++
    payoffTable (satPayoffCell satSyntaxWord) ![satUnaryQ input, input]

/-- A fixed deterministic polynomial-time machine emits the whole explicit table. -/
theorem satTableEncode_mem_FP : satTableEncode ∈ FP := by
  have hc := satPayoffCell_cobham satSyntaxWord_cobham
  have hw : Cobham fun v : Fin 1 → List Bool => satCellWidth (v 0) :=
    Cobham.appendFn satTallyWidth_cobham satTallyWidth_cobham
  have hbound (v : Fin 3 → List Bool) :
      (satPayoffCell satSyntaxWord v).length ≤ (satCellWidth (v 2)).length := by
    rw [satPayoffCell_length]
    simp [satCellWidth]
    omega
  have ht := Cobham.comp (payoffTable_cobham hc hw hbound)
    (gs := fun i => fun v : Fin 1 → List Bool =>
      (![satUnaryQ (v 0), v 0] : Fin 2 → List Bool) i) (by
        intro i
        fin_cases i
        · exact satUnaryQ_cobham
        · exact Cobham.proj 0)
  exact CobhamFP_subset_FP
    (Cobham.appendFn (Cobham.appendFn satUnaryQ_cobham (Cobham.const [false])) ht)

theorem satUnaryN_eq (input : List Bool) :
    satUnaryN input = List.replicate (input.length + 1) true := by
  simp only [satUnaryN, Complexity.smash, List.length_singleton, Nat.mul_one]
  rw [List.replicate_add]
  rfl

theorem satUnaryQ_eq (input : List Bool) :
    satUnaryQ input = List.replicate (4 * (input.length + 1) + 1) true := by
  have h : 4 * (input.length + 1) =
      (input.length + 1) + (input.length + 1) + (input.length + 1) + (input.length + 1) := by omega
  simp [satUnaryQ, satUnaryN_eq, h, List.replicate_add]

end GameTheory.Complexity.Backend
