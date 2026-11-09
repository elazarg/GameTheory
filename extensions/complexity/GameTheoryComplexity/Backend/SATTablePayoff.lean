module

public import GameTheoryComplexity.Backend.SATTableMachine
public import GameTheoryComplexity.Backend.SATTableEmission
public import GameTheoryComplexity.Backend.SATSyntaxMachine

@[expose] public section

/-! Polynomial-time explicit payoff-table generation. Scalar payoffs use fixed-width
positive and negative tally blocks. The second player's payoff is the transpose.
Every cell is evaluated during the native row-major traversal.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- Encode positive and negative magnitudes in two zero-padded tally blocks,
truncating either magnitude when it exceeds the supplied width. -/
def satTallyPair (width positive negative : ℕ) : List Bool :=
  (List.replicate (min positive width) true ++ List.replicate (width - positive) false) ++
    (List.replicate (min negative width) true ++ List.replicate (width - negative) false)

@[simp] theorem satTallyPair_length (width positive negative : ℕ) :
    (satTallyPair width positive negative).length = 2 * width := by
  simp only [satTallyPair, List.length_append, List.length_replicate]
  omega

@[fun_prop] theorem satTallyPair_polyTime :
    ComputableInPolyTime (fun pair : (ℕ × ℕ) × ℕ =>
      satTallyPair pair.1.1 pair.1.2 pair.2)
      (encPair (encPair encUnary encUnary) encUnary) encBits := by
  unfold satTallyPair
  fun_prop

/-- Encode one row payoff from its unary row and column indices. The validity
verdict gates clause incidence while the scanner remains total on every source word. -/
def satPayoffCell (valid : List Bool → Bool) (input : List Bool) (row col : ℕ) : List Bool :=
  let n := input.length + 1
  let width := 4 * n + 3
  let rowVar := if row < n then row else row - n
  let colVar := if col < n then col else col - n
  let z0 := satTallyPair width 0 0
  let z1 := satTallyPair width 1 0
  let z2 := satTallyPair width 2 0
  let zm2 := satTallyPair width 0 2
  let z2n := satTallyPair width (2 - n) (n - 2)
  if row = 4 * n then
    if col = 4 * n then z0 else z1
  else if row < 2 * n then
    if col < 2 * n then
      if rowVar = colVar ∧ decide (row < n) ≠ decide (col < n) then zm2 else z1
    else zm2
  else if row < 3 * n then
    if col < 2 * n then
      if row - 2 * n = colVar then z2n else z2
    else zm2
  else if row < 4 * n then
    if col < 2 * n then
      if valid input && scanIncidence colVar (decide (col < n)) (row - 3 * n) input then z2n else z2
    else zm2
  else zm2

/-- Every cell contains exactly two tally blocks of the common width. -/
theorem satPayoffCell_length (valid : List Bool → Bool) (input : List Bool) (row col : ℕ) :
    (satPayoffCell valid input row col).length = 2 * (4 * (input.length + 1) + 3) := by
  dsimp only [satPayoffCell]
  split_ifs <;> exact satTallyPair_length _ _ _

/-- The cell machine charges both unary indices, the complete source word and
its certified validity check, including every literal-incidence scan. -/
theorem satPayoffCell_polyTime {valid : List Bool → Bool}
    (hvalid : ComputableInPolyTime valid encBits encBool) :
    ComputableInPolyTime
      (fun pair : (List Bool × ℕ) × ℕ => satPayoffCell valid pair.1.1 pair.1.2 pair.2)
      (encPair (encPair encBits encUnary) encUnary) encBits := by
  have hsource : ComputableInPolyTime (fun pair : (List Bool × ℕ) × ℕ => pair.1.1)
      (encPair (encPair encBits encUnary) encUnary) encBits := by fun_prop
  have hrow : ComputableInPolyTime (fun pair : (List Bool × ℕ) × ℕ => pair.1.2)
      (encPair (encPair encBits encUnary) encUnary) encUnary := by fun_prop
  have hcol : ComputableInPolyTime (fun pair : (List Bool × ℕ) × ℕ => pair.2)
      (encPair (encPair encBits encUnary) encUnary) encUnary := by fun_prop
  have hn : ComputableInPolyTime
      (fun pair : (List Bool × ℕ) × ℕ => pair.1.1.length + 1)
      (encPair (encPair encBits encUnary) encUnary) encUnary := by fun_prop
  have hsign : ComputableInPolyTime
      (fun pair : (List Bool × ℕ) × ℕ => decide (pair.2 < pair.1.1.length + 1))
      (encPair (encPair encBits encUnary) encUnary) encBool :=
    .of_tidy (.unary_lt' hcol.tidy hn.tidy)
  have hvar : ComputableInPolyTime
      (fun pair : (List Bool × ℕ) × ℕ =>
        if pair.2 < pair.1.1.length + 1 then pair.2 else pair.2 - (pair.1.1.length + 1))
      (encPair (encPair encBits encUnary) encUnary) encUnary := by fun_prop
  have hclause : ComputableInPolyTime
      (fun pair : (List Bool × ℕ) × ℕ => pair.1.2 - 3 * (pair.1.1.length + 1))
      (encPair (encPair encBits encUnary) encUnary) encUnary := by fun_prop
  have hscan := scanIncidence_polyTime hvar hsign hclause hsource
  have hsyntax := hvalid.comp hsource
  have hn2 := ComputableTidilyInPolyTime.unary_mul.comp
    ((ComputableTidilyInPolyTime.const 2).prod hn.tidy)
  have hn3 := ComputableTidilyInPolyTime.unary_mul.comp
    ((ComputableTidilyInPolyTime.const 3).prod hn.tidy)
  have hn4 := ComputableTidilyInPolyTime.unary_mul.comp
    ((ComputableTidilyInPolyTime.const 4).prod hn.tidy)
  have hwidth := ComputableTidilyInPolyTime.unary_add.comp
    (hn4.prod (ComputableTidilyInPolyTime.const 3))
  have htally (positive negative : ((List Bool × ℕ) × ℕ) → ℕ)
      (hp : ComputableTidilyInPolyTime positive
        (encPair (encPair encBits encUnary) encUnary) encUnary)
      (hneg : ComputableTidilyInPolyTime negative
        (encPair (encPair encBits encUnary) encUnary) encUnary) :
      ComputableTidilyInPolyTime
        (fun pair => satTallyPair (4 * (pair.1.1.length + 1) + 3) (positive pair) (negative pair))
        (encPair (encPair encBits encUnary) encUnary) encBits :=
    satTallyPair_polyTime.tidy.comp ((hwidth.prod hp).prod hneg)
  have hz0 := htally (fun _ => 0) (fun _ => 0) (.const 0) (.const 0)
  have hz1 := htally (fun _ => 1) (fun _ => 0) (.const 1) (.const 0)
  have hz2 := htally (fun _ => 2) (fun _ => 0) (.const 2) (.const 0)
  have hzm2 := htally (fun _ => 0) (fun _ => 2) (.const 0) (.const 2)
  have hz2n := htally (fun pair => 2 - (pair.1.1.length + 1))
    (fun pair => pair.1.1.length + 1 - 2)
    (ComputableTidilyInPolyTime.unary_sub.comp ((ComputableTidilyInPolyTime.const 2).prod hn.tidy))
    (ComputableTidilyInPolyTime.unary_sub.comp (hn.tidy.prod (.const 2)))
  have hrowPositive := ComputableTidilyInPolyTime.unary_lt' hrow.tidy hn.tidy
  have hrowVar := ComputableTidilyInPolyTime.ite_decide hrowPositive hrow.tidy
    (ComputableTidilyInPolyTime.unary_sub.comp (hrow.tidy.prod hn.tidy))
  have hopposed := ComputableTidilyInPolyTime.decide_and
    (.decide_eq' hrowVar hvar.tidy) (.decide_ne hrowPositive hsign.tidy)
  have hrowSub2 := ComputableTidilyInPolyTime.unary_sub.comp (hrow.tidy.prod hn2)
  have hincidence := ComputableTidilyInPolyTime.bool_and' hsyntax.tidy hscan.tidy
  exact ComputableInPolyTime.of_tidy <|
    ComputableTidilyInPolyTime.ite_decide (.decide_eq' hrow.tidy hn4)
      (.ite_decide (.decide_eq' hcol.tidy hn4) hz0 hz1)
      (.ite_decide (.unary_lt' hrow.tidy hn2)
        (.ite_decide (.unary_lt' hcol.tidy hn2) (.ite_decide hopposed hzm2 hz1) hzm2)
        (.ite_decide (.unary_lt' hrow.tidy hn3)
          (.ite_decide (.unary_lt' hcol.tidy hn2)
            (.ite_decide (.decide_eq' hrowSub2 hvar.tidy) hz2n hz2) hzm2)
          (.ite_decide (.unary_lt' hrow.tidy hn4)
            (.ite_decide (.unary_lt' hcol.tidy hn2) (.cond hincidence hz2n hz2) hzm2) hzm2)))

/-- Write the unary dimension header, its delimiter and every row-major payoff cell. -/
def satTableEncode (input : List Bool) : List Bool :=
  let dimension := 4 * (input.length + 1) + 1
  List.replicate dimension true ++ [false] ++
    payoffTable (satPayoffCell SATWords.syntaxValid) input dimension

/-- One native polynomial-time machine emits the complete explicit table. -/
@[fun_prop] theorem satTableEncode_polyTime :
    ComputableInPolyTime satTableEncode encBits encBits := by
  have hdimension : ComputableInPolyTime
      (fun input : List Bool => 4 * (input.length + 1) + 1) encBits encUnary := by fun_prop
  have hheader : ComputableInPolyTime
      (fun input : List Bool => List.replicate (4 * (input.length + 1) + 1) true)
      encBits encBits := (ComputableInPolyTime.bitsReplicate true).comp hdimension
  have htable := payoffTable_polyTime (ComputableInPolyTime.id' (encIn := encBits))
    hdimension (satPayoffCell_polyTime satSyntaxValid_polyTime)
  exact (hheader.bitsAppend (ComputableInPolyTime.const [false])).bitsAppend htable

end GameTheory.Complexity.Backend
