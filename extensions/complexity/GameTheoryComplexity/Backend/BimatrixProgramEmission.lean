import GameTheoryComplexity.Backend.BimatrixProgramCodec

/-! A polynomial-time coefficient-table emitter for the canonical mixed-gate program codec.
Fixed-width normalization preserves each coefficient and the bytes of every packed row;
source-dependent header producers compose with the same certified table loops. -/

namespace GameTheory.Complexity.Backend.BimatrixProgramEmission
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite.BimatrixGateProgram

private def coefficientTerm (query : (Fin 3 → List Bool) → List Bool)
    (v : Fin 3 → List Bool) : List Bool := query ![v 1, v 0, v 2]

/-- Materialize all action coefficients of one output as fixed-width signed fields. -/
def row (query : (Fin 3 → List Bool) → List Bool) (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable (coefficientTerm query) (v 1 ++ v 1) (v 2) ![v 0, v 3]

/-- Materialize output-major coefficients without interpreting their packed rows numerically. -/
def coefficients (query : (Fin 3 → List Bool) → List Bool)
    (v : Fin 3 → List Bool) : List Bool :=
  binarySignedTable (row query) (v 0) (smash (v 0 ++ v 0) (v 1)) ![v 0, v 1, v 2]

@[simp] theorem row_length (query : (Fin 3 → List Bool) → List Bool)
    (v : Fin 4 → List Bool) : (row query v).length = ((v 1).length * 2) * (v 2).length := by
  rw [row, binarySignedTable_length, List.length_append]
  congr 1
  omega

@[simp] theorem coefficients_length (query : (Fin 3 → List Bool) → List Bool)
    (v : Fin 3 → List Bool) :
    (coefficients query v).length = (v 0).length * (((v 0).length * 2) * (v 1).length) := by
  simp only [coefficients, binarySignedTable_length, smash_length, List.length_append]
  congr 1
  congr 1
  omega

private theorem coefficientTerm_cobham
    {query : (Fin 3 → List Bool) → List Bool} (hq : Cobham query) :
    Cobham (coefficientTerm query) :=
  (Cobham.comp₃ hq (.proj 1) (.proj 0) (.proj 2)).of_eq fun _ => rfl

theorem row_cobham {query : (Fin 3 → List Bool) → List Bool} (hq : Cobham query) :
    Cobham (row query) := by
  have ht := binarySignedTable_cobham (coefficientTerm_cobham hq)
  have ha : ∀ i : Fin 4, Cobham (fun v : Fin 4 → List Bool =>
      ![v 1 ++ v 1, v 2, v 0, v 3] i) := by
    intro i
    fin_cases i
    · exact appendFn (.proj 1) (.proj 1)
    · exact .proj 2
    · exact .proj 0
    · exact .proj 3
  have h := Cobham.comp ht ha
  exact h.of_eq fun v => by
    change binarySignedTable (coefficientTerm query) (v 1 ++ v 1) (v 2) _ = _
    congr 1

theorem coefficients_cobham {query : (Fin 3 → List Bool) → List Bool} (hq : Cobham query) :
    Cobham (coefficients query) := by
  have ht := binarySignedTable_cobham (row_cobham hq)
  have ha : ∀ i : Fin 5, Cobham (fun v : Fin 3 → List Bool =>
      ![v 0, smash (v 0 ++ v 0) (v 1), v 0, v 1, v 2] i) := by
    intro i
    fin_cases i
    · exact .proj 0
    · exact Cobham.comp₂ Cobham.smash (appendFn (.proj 0) (.proj 0)) (.proj 1)
    · exact .proj 0
    · exact .proj 1
    · exact .proj 2
  have h := Cobham.comp ht ha
  exact h.of_eq fun v => by
    change binarySignedTable (row query) (v 0) (smash (v 0 ++ v 0) (v 1)) _ = _
    congr 1

theorem coefficients_mem_FPn {query : (Fin 3 → List Bool) → List Bool} (hq : FPn query) :
    FPn (coefficients query) := cobham_iff_FPn.mp (coefficients_cobham (cobham_iff_FPn.mpr hq))

theorem row_field (query : (Fin 3 → List Bool) → List Bool)
    (v : Fin 4 → List Bool) (j : ℕ) (hj : j < (v 1).length * 2) :
    ((row query v).drop (j * (v 2).length)).take (v 2).length =
      binarySignedFixed (v 2)
        (query ![v 0, (v 1 ++ v 1).drop ((v 1).length * 2 - j), v 3]) := by
  have h := binarySignedTable_field (coefficientTerm query)
    (v 1 ++ v 1) (v 2) ![v 0, v 3] j (by rw [List.length_append]; omega)
  rw [List.length_append, ← Nat.mul_two] at h
  exact h

theorem coefficients_row (query : (Fin 3 → List Bool) → List Bool)
    (v : Fin 3 → List Bool) (i : ℕ) (hi : i < (v 0).length) :
    ((coefficients query v).drop (i * ((v 0).length * 2 * (v 1).length))).take
      ((v 0).length * 2 * (v 1).length) =
      row query ![(v 0).drop ((v 0).length - i), v 0, v 1, v 2] := by
  have h := binarySignedTable_field (row query) (v 0)
    (smash (v 0 ++ v 0) (v 1)) ![v 0, v 1, v 2] i hi
  rw [smash_length, List.length_append, ← Nat.mul_two] at h
  change _ = binarySignedFixed (smash (v 0 ++ v 0) (v 1)) (row query _) at h
  rw [binarySignedFixed_eq_of_length] at h
  · exact h
  · rw [row_length, smash_length, List.length_append, ← Nat.mul_two]
    rfl

theorem coefficients_field (query : (Fin 3 → List Bool) → List Bool)
    (v : Fin 3 → List Bool) (i j : ℕ)
    (hi : i < (v 0).length) (hj : j < (v 0).length * 2) :
    ((coefficients query v).drop
      ((i * ((v 0).length * 2) + j) * (v 1).length)).take (v 1).length =
      binarySignedFixed (v 1) (query ![(v 0).drop ((v 0).length - i),
        (v 0 ++ v 0).drop ((v 0).length * 2 - j), v 2]) := by
  have h := congrArg (fun x : List Bool => (x.drop (j * (v 1).length)).take (v 1).length)
    (coefficients_row query v i hi)
  rw [List.drop_take, List.drop_drop, List.take_take] at h
  have hm : (v 1).length ≤ (v 0).length * 2 * (v 1).length - j * (v 1).length := by
    have hb := Nat.mul_le_mul_right (v 1).length (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hb
    omega
  rw [Nat.min_eq_left hm, ← Nat.mul_assoc, ← Nat.add_mul] at h
  exact h.trans (row_field query ![(v 0).drop ((v 0).length - i), v 0, v 1, v 2] j hj)

/-- Emit a canonical program tape from polynomial-time header and coefficient producers. -/
def programWord (dimension width baseline kinds : List Bool → List Bool)
    (query : (Fin 3 → List Bool) → List Bool) (source : List Bool) : List Bool :=
  BimatrixProgramCodec.encode (dimension source) (width source) (baseline source)
    (kinds source) (coefficients query ![dimension source, width source, source])

theorem programWord_mem_FP {dimension width baseline kinds : List Bool → List Bool}
    {query : (Fin 3 → List Bool) → List Bool}
    (hd : dimension ∈ FP) (hw : width ∈ FP) (hb : baseline ∈ FP) (hk : kinds ∈ FP)
    (hq : FPn query) : programWord dimension width baseline kinds query ∈ FP := by
  have hc : (fun source => coefficients query ![dimension source, width source, source]) ∈ FP := by
    apply CobhamFP_subset_FP
    exact (Cobham.comp₃ (coefficients_cobham (cobham_iff_FPn.mpr hq))
      (FP_subset_CobhamFP hd) (FP_subset_CobhamFP hw) (.proj 0)).of_eq fun _ => rfl
  exact pairFn_mem_FP hd (pairFn_mem_FP hw
    (pairFn_mem_FP hb (pairFn_mem_FP hk hc)))

/-- Headers and coefficient payload are preserved by canonical packing. -/
theorem programWord_fields (dimension width baseline kinds : List Bool → List Bool)
    (query : (Fin 3 → List Bool) → List Bool) (source : List Bool) :
    BimatrixProgramCodec.dimension (programWord dimension width baseline kinds query source) =
      dimension source ∧
    BimatrixProgramCodec.width (programWord dimension width baseline kinds query source) =
      width source ∧
    BimatrixProgramCodec.baselineWord (programWord dimension width baseline kinds query source) =
      baseline source ∧
    BimatrixProgramCodec.kindFlags (programWord dimension width baseline kinds query source) =
      kinds source ∧
    BimatrixProgramCodec.coefficientTape (programWord dimension width baseline kinds query source) =
      coefficients query ![dimension source, width source, source] :=
  BimatrixProgramCodec.encode_fields _ _ _ _ _

/-- Coefficient queries and representable signed values recover the canonical program. -/
theorem programWord_decode (dimension width baseline kinds : List Bool → List Bool)
    (query : (Fin 3 → List Bool) → List Bool) (source : List Bool)
    (g : Fin (BimatrixProgramCodec.dimension
      (programWord dimension width baseline kinds query source)).length →
      Gate (BimatrixProgramCodec.dimension
        (programWord dimension width baseline kinds query source)).length)
    (hw : 0 < (width source).length)
    (hq : ∀ i r, binarySignedValue (query ![
      (dimension source).drop ((dimension source).length - i.val),
      (dimension source ++ dimension source).drop ((dimension source).length * 2 - r.val),
      source]) = (g i).coefficients r)
    (hb : ∀ i r, ((g i).coefficients r).natAbs < 2 ^ ((width source).length - 1))
    (hk : ∀ i, (if (kinds source)[i.val]?.getD false then GateKind.comparator
      else GateKind.affine) = (g i).kind) :
    BimatrixProgramCodec.decode (programWord dimension width baseline kinds query source) = g := by
  have hf := programWord_fields dimension width baseline kinds query source
  apply BimatrixProgramCodec.decode_eq_of_fields
  · intro i r
    have hi : i.val < (dimension source).length := by rw [← hf.1]; exact i.isLt
    have hr : r.val < (dimension source).length * 2 := by
      rw [← hf.1]
      exact r.isLt
    have hindex := congrArg (fun n : ℕ => i.val * (n * 2) + r.val)
      (congrArg List.length hf.1)
    rw [hindex, hf.2.1, hf.2.2.2.2]
    change binarySignedValue ((coefficients query ![dimension source, width source, source]).drop
      ((i.val * ((dimension source).length * 2) + r.val) * (width source).length) |>.take
        (width source).length) = _
    have hfield := coefficients_field query ![dimension source, width source, source]
      i.val r.val hi hr
    change ((coefficients query ![dimension source, width source, source]).drop
      ((i.val * ((dimension source).length * 2) + r.val) * (width source).length)).take
      (width source).length = binarySignedFixed (width source)
        (query ![(dimension source).drop ((dimension source).length - i.val),
          (dimension source ++ dimension source).drop ((dimension source).length * 2 - r.val),
          source]) at hfield
    rw [hfield]
    exact (binarySignedFixed_value (width source) _ hw (by rw [hq i r]; exact hb i r)).trans
      (hq i r)
  · intro i
    rw [hf.2.2.2.1]
    exact hk i

end GameTheory.Complexity.Backend.BimatrixProgramEmission
