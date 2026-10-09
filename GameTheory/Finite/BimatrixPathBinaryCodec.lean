import GameTheory.Finite.BimatrixComputedPivot
import GameTheory.Finite.BimatrixPathEndOfLine
import GameTheory.Math.EndOfLineNormalization
import GameTheory.Math.FiniteSetRank
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Range

/-! Canonical binary encodings of complementary path ports. Basis membership
and a one-hot entering variable determine the node without auxiliary witnesses.
The source mask maps the unique artificial source to the all-false word.
Validation computes strict symbolic feasibility using integer Cramer rows. -/
namespace GameTheory.Finite.BimatrixPathBinaryCodec
open GameTheory.Math GameTheory.Math.CanonicalDictionary
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ}

/-- Number of node bits: one basis bit and one entering bit for each variable. -/
def width (m n : ℕ) : ℕ := 4 * (m + n)

/-- Canonical position of a slack or payoff variable. -/
def index (v : BimatrixVariable m n) : Fin (2 * (m + n)) :=
  ⟨2 * (ofLex v).1.val + if (ofLex v).2 then 1 else 0, by
    have h := (ofLex v).1.isLt
    split <;> omega⟩

/-- Recover a variable from its canonical bit position. -/
def variableAt (i : Fin (2 * (m + n))) : BimatrixVariable m n :=
  toLex (⟨i.val / 2, by have h := i.isLt; omega⟩, decide (i.val % 2 = 1))

@[simp] theorem variableAt_index (v : BimatrixVariable m n) : variableAt (index v) = v := by
  rcases v with ⟨i, b⟩
  change variableAt (index (toLex (i, b))) = toLex (i, b)
  cases b <;> apply ofLex.injective <;> simp [variableAt, index, Nat.add_div, Nat.add_mod]

@[simp] theorem index_variableAt (i : Fin (2 * (m + n))) : index (variableAt i) = i := by
  apply Fin.ext
  simp only [index, variableAt, ofLex_toLex, decide_eq_true_eq]
  split <;> omega

/-- Bit positions preserve the canonical variable order. -/
theorem index_strictMono : StrictMono (index (m := m) (n := n)) := by
  intro v w hlt
  change toLex (ofLex v) < toLex (ofLex w) at hlt
  rw [Prod.Lex.toLex_lt_toLex] at hlt
  change (index v).val < (index w).val
  simp only [index]
  rcases hlt with hl | ⟨he, hb⟩
  · have h := Fin.lt_def.mp hl
    cases hv : (ofLex v).2 <;> cases hw : (ofLex w).2 <;> simp <;> omega
  · have h := congrArg Fin.val he
    cases hv : (ofLex v).2 <;> cases hw : (ofLex w).2 <;> simp_all
    exact (by decide : ¬ true < false) hb

/-- Unmasked basis membership bits in canonical order. -/
def membershipWord (s : Finset (BimatrixVariable m n)) : List Bool :=
  List.ofFn fun i : Fin (2 * (m + n)) => decide (variableAt i ∈ s)

private theorem count_take_eq_card (word : List Bool) (i : ℕ) :
    (word.take i).count true = ((Finset.range i).filter
      (fun j => word[j]?.getD false = true)).card := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.take_add_one, List.count_append, ih, Finset.range_add_one, Finset.filter_insert]
    cases hw : word[i]? with
    | none => simp
    | some b => cases b <;> simp [hw, Finset.mem_filter]

/-- Counting true prefix bits computes the rank of any variable in the selected set. -/
theorem membershipWord_prefix_count (s : Finset (BimatrixVariable m n))
    (v : BimatrixVariable m n) :
    ((membershipWord s).take (index v).val).count true =
      (s.filter (fun u => u < v)).card := by
  let emb : BimatrixVariable m n ↪ ℕ := ⟨fun u => (index u).val,
    fun u w he => index_strictMono.injective (Fin.ext he)⟩
  have hset : (s.filter (fun u => u < v)).map emb =
      (Finset.range (index v).val).filter
        (fun j => (membershipWord s)[j]?.getD false = true) := by
    ext j
    constructor
    · intro hj
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hj
      obtain ⟨hu, hlt⟩ := Finset.mem_filter.mp hu
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (index_strictMono hlt), ?_⟩
      change (membershipWord s)[(index u).val]?.getD false = true
      simp only [membershipWord, List.getElem?_ofFn, (index u).isLt, ↓reduceDIte,
        Option.getD_some]
      change decide (variableAt (index u) ∈ s) = true
      simpa only [variableAt_index, decide_eq_true_eq] using hu
    · intro hj
      obtain ⟨hj, hb⟩ := Finset.mem_filter.mp hj
      have hlt := Finset.mem_range.mp hj
      have hfull : j < 2 * (m + n) := hlt.trans (index v).isLt
      let u := variableAt (m := m) (n := n) ⟨j, hfull⟩
      apply Finset.mem_map.mpr
      refine ⟨u, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · simpa only [membershipWord, List.getElem?_ofFn, hfull, ↓reduceDIte,
          Option.getD_some, decide_eq_true_eq] using hb
      · apply index_strictMono.lt_iff_lt.mp
        simpa only [u, index_variableAt, Fin.lt_def] using hlt
      · change (index u).val = j
        simp only [u, index_variableAt]
  rw [count_take_eq_card, ← hset, Finset.card_map]

/-- The raw membership word has exactly one true bit per selected variable. -/
theorem membershipWord_count (s : Finset (BimatrixVariable m n)) :
    (membershipWord s).count true = s.card := by
  let emb : BimatrixVariable m n ↪ ℕ := ⟨fun u => (index u).val,
    fun u w he => index_strictMono.injective (Fin.ext he)⟩
  have hset : s.map emb = (Finset.range (2 * (m + n))).filter
      (fun j => (membershipWord s)[j]?.getD false = true) := by
    ext j
    constructor
    · intro hj
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (index u).isLt, ?_⟩
      change (membershipWord s)[(index u).val]?.getD false = true
      simp only [membershipWord, List.getElem?_ofFn, (index u).isLt, ↓reduceDIte,
        Option.getD_some]
      change decide (variableAt (index u) ∈ s) = true
      simpa only [variableAt_index, decide_eq_true_eq] using hu
    · intro hj
      obtain ⟨hj, hb⟩ := Finset.mem_filter.mp hj
      have hfull := Finset.mem_range.mp hj
      refine Finset.mem_map.mpr ⟨variableAt ⟨j, hfull⟩, ?_, ?_⟩
      · simpa only [membershipWord, List.getElem?_ofFn, hfull, ↓reduceDIte,
          Option.getD_some, decide_eq_true_eq] using hb
      · change (index (variableAt ⟨j, hfull⟩)).val = j
        simp only [index_variableAt]
  have hl : (membershipWord s).length = 2 * (m + n) := List.length_ofFn
  have hc := count_take_eq_card (membershipWord s) (2 * (m + n))
  rw [← hl, List.take_length] at hc
  rw [hl] at hc
  rw [hc, ← hset, Finset.card_map]

/-- A membership bit and its true prefix count characterize canonical column lookup. -/
theorem selected_variable_iff (s : Finset (BimatrixVariable m n))
    {k : ℕ} (hs : s.card = k) (j : Fin k) (v : BimatrixVariable m n) :
    v = s.orderEmbOfFin hs j ↔
      (membershipWord s)[(index v).val]?.getD false = true ∧
        ((membershipWord s).take (index v).val).count true = j.val := by
  rw [FiniteSetRank.eq_orderEmbOfFin_iff, membershipWord_prefix_count]
  simp only [membershipWord, List.getElem?_ofFn, (index v).isLt, ↓reduceDIte,
    Option.getD_some, decide_eq_true_eq]
  rw [show variableAt (m := m) (n := n) ⟨(index v).val, (index v).isLt⟩ = v from variableAt_index v]

private def sourceEntering (d : Fin (m + n)) : BimatrixVariable m n := toLex (d, true)

/-- Encode a port with the artificial source's membership and entering masks. -/
def encode {d : Fin (m + n)} (port : BimatrixPathPort A B d) : List Bool :=
  List.ofFn fun i : Fin (width m n) =>
    if hi : i.val < 2 * (m + n) then
      let v := variableAt ⟨i.val, hi⟩
      xor (decide (v ∈ port.node.basis.basic)) (!(ofLex v).2)
    else
      let v := variableAt ⟨i.val - 2 * (m + n), by have h := i.isLt; dsimp [width] at h; omega⟩
      xor (decide (v = port.entering)) (decide (v = sourceEntering d))

@[simp] theorem encode_length {d : Fin (m + n)} (port : BimatrixPathPort A B d) :
    (encode port).length = width m n := List.length_ofFn

/-- Unmask the basis membership bits. -/
def basic (word : List Bool) : Finset (BimatrixVariable m n) :=
  Finset.univ.filter fun v => xor (word[(index v).val]?.getD false) (!(ofLex v).2)

/-- Unmask the entering-variable one-hot bits. -/
def enteringSet (d : Fin (m + n)) (word : List Bool) : Finset (BimatrixVariable m n) :=
  Finset.univ.filter fun v =>
    xor (word[2 * (m + n) + (index v).val]?.getD false) (decide (v = sourceEntering d))

@[simp] theorem basic_encode {d : Fin (m + n)} (port : BimatrixPathPort A B d) :
    basic (encode port) = port.node.basis.basic := by
  ext v
  have hi := (index v).isLt
  have hfull : (index v).val < width m n := by dsimp [width]; omega
  simp only [basic, Finset.mem_filter, Finset.mem_univ, true_and,
    encode, List.getElem?_ofFn, hfull, ↓reduceDIte, Option.getD_some, hi,
    ]
  cases h : decide (v ∈ port.node.basis.basic) <;> cases hb : (ofLex v).2 <;> simp_all

@[simp] theorem enteringSet_encode {d : Fin (m + n)} (port : BimatrixPathPort A B d) :
    enteringSet d (encode port) = {port.entering} := by
  ext v
  have hi := (index v).isLt
  have hfull : 2 * (m + n) + (index v).val < width m n := by dsimp [width]; omega
  have hn : ¬2 * (m + n) + (index v).val < 2 * (m + n) := by omega
  simp only [enteringSet, Finset.mem_filter, Finset.mem_univ, true_and,
    encode, List.getElem?_ofFn, hfull, ↓reduceDIte, Option.getD_some, hn,
    Nat.add_sub_cancel_left, Finset.mem_singleton]
  cases h : decide (v = port.entering) <;> cases hb : decide (v = sourceEntering d) <;> simp_all

theorem encode_injective {d : Fin (m + n)} : Function.Injective
    (encode : BimatrixPathPort A B d → List Bool) := by
  intro p q hpq
  apply BimatrixPathPort.ext
  · apply BimatrixBasis.ext
    exact (basic_encode p).symm.trans ((congrArg (basic (m := m) (n := n)) hpq).trans
      (basic_encode q))
  · have he := congrArg (enteringSet d) hpq
    simpa only [enteringSet_encode, Finset.singleton_inj] using he

/-- Exact width and the two unmasked fields characterize a canonical word. -/
theorem encode_eq_of_fields {d : Fin (m + n)} (port : BimatrixPathPort A B d)
    (word : List Bool) (hw : word.length = width m n)
    (hb : basic word = port.node.basis.basic)
    (he : enteringSet d word = {port.entering}) : encode port = word := by
  apply List.ext_getElem
  · exact (encode_length port).trans hw.symm
  · intro i hi hj
    simp only [encode, List.getElem_ofFn]
    split
    · rename_i hsmall
      let v := variableAt (m := m) (n := n) ⟨i, hsmall⟩
      have hbit : decide (v ∈ port.node.basis.basic) =
          xor (word[i]?.getD false) (!(ofLex v).2) := by
        rw [← hb]
        simp only [basic, Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [v, index_variableAt]
        cases word[i]?.getD false <;>
          cases (ofLex (variableAt (m := m) (n := n) ⟨i, hsmall⟩)).2 <;> rfl
      change xor (decide (v ∈ port.node.basis.basic)) (!(ofLex v).2) = word[i]
      rw [hbit]
      simp only [List.getElem?_eq_getElem hj, Option.getD_some]
      cases word[i] <;> cases (ofLex v).2 <;> rfl
    · rename_i hlarge
      have hfull : i < width m n := by simpa only [encode_length] using hi
      let v := variableAt (m := m) (n := n)
        ⟨i - 2 * (m + n), by dsimp [width] at hfull; omega⟩
      have hbit : decide (v = port.entering) =
          xor (word[i]?.getD false) (decide (v = sourceEntering d)) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        have hmem : v ∈ enteringSet d word ↔ v = port.entering := by
          rw [he]
          exact Finset.mem_singleton
        rw [← hmem]
        simp only [enteringSet, Finset.mem_filter, Finset.mem_univ, true_and]
        have hidx : 2 * (m + n) + (index v).val = i := by
          simp only [v, index_variableAt]
          omega
        rw [hidx]
      change xor (decide (v = port.entering)) (decide (v = sourceEntering d)) = word[i]
      rw [hbit]
      simp only [List.getElem?_eq_getElem hj, Option.getD_some]
      cases word[i] <;> cases decide (v = sourceEntering d) <;> rfl

/-- Integer Cramer checks for invertibility and strict symbolic feasibility. -/
def IntegerFeasible {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) : Prop :=
  IntegerCramerComputation.determinant M ≠ 0 ∧ ∀ i,
    FiniteLexicographicCompare.lexLT (fun _ => 0)
      (IntegerDictionaryComputation.coefficients M (fun _ => 1) i) = true

instance {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) : Decidable (IntegerFeasible M) := by
  unfold IntegerFeasible; infer_instance

private theorem cast_lex_pos_iff {k : ℕ} (c : Fin k → ℤ) :
    0 < toLex (fun j => (c j : ℚ)) ↔ 0 < toLex c := by
  constructor <;> rintro ⟨i, hpre, hpos⟩
  · refine ⟨i, fun j hj => ?_, ?_⟩
    · have he := hpre j hj
      change (0 : ℚ) = (c j : ℚ) at he
      change (0 : ℤ) = c j
      exact_mod_cast he
    · change (0 : ℚ) < (c i : ℚ) at hpos
      change (0 : ℤ) < c i
      exact_mod_cast hpos
  · refine ⟨i, fun j hj => ?_, ?_⟩
    · have he := hpre j hj
      change (0 : ℤ) = c j at he
      change (0 : ℚ) = (c j : ℚ)
      exact_mod_cast he
    · change (0 : ℤ) < c i at hpos
      change (0 : ℚ) < (c i : ℚ)
      exact_mod_cast hpos

/-- The executable integer checks characterize the canonical rational invariant. -/
theorem integerFeasible_iff {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) :
    IntegerFeasible M ↔ (M.map (fun z : ℤ => (z : ℚ))).det ≠ 0 ∧
      ∀ i, 0 < toLex (PerturbedDictionary.dictionaryCoefficients
        (M.map (fun z : ℤ => (z : ℚ))) (fun _ => 1) i) := by
  have hdet : (M.map (fun z : ℤ => (z : ℚ))).det ≠ 0 ↔ M.det ≠ 0 := by
    rw [← Int.cast_det, Int.cast_ne_zero]
  rw [IntegerFeasible, IntegerCramerComputation.determinant_eq, hdet]
  constructor
  · rintro ⟨hd, hf⟩
    refine ⟨hd, fun i => ?_⟩
    have hp := (FiniteLexicographicCompare.lexLT_eq_true _ _).mp (hf i)
    have hq := (cast_lex_pos_iff _).mpr hp
    have hD : (0 : ℚ) < IntegerCramerComputation.denominator M := by
      rw [IntegerCramerComputation.denominator_eq]
      exact_mod_cast IntegerCramerEncoding.denominator_pos M hd
    have hx := (FiniteLexicographic.div_lt_div_iff (x := fun _ => (0 : ℚ))
      (y := fun j => (IntegerDictionaryComputation.coefficients M (fun _ => 1) i j : ℚ)) hD).mpr hq
    simp only [zero_div, IntegerDictionaryComputation.coefficients_decode M (fun _ => 1) hd,
      Int.cast_one] at hx
    exact hx
  · rintro ⟨hd, hf⟩
    refine ⟨hd, fun i => ?_⟩
    apply (FiniteLexicographicCompare.lexLT_eq_true _ _).mpr
    apply (cast_lex_pos_iff _).mp
    have hD : (0 : ℚ) < IntegerCramerComputation.denominator M := by
      rw [IntegerCramerComputation.denominator_eq]
      exact_mod_cast IntegerCramerEncoding.denominator_pos M hd
    apply (FiniteLexicographic.div_lt_div_iff (x := fun _ => (0 : ℚ))
      (y := fun j => (IntegerDictionaryComputation.coefficients M (fun _ => 1) i j : ℚ)) hD).mp
    have hx := hf i
    change toLex (fun _ => (0 : ℚ)) < toLex _ at hx
    simpa only [zero_div, IntegerDictionaryComputation.coefficients_decode M (fun _ => 1) hd,
      Int.cast_one] using hx

/-- Canonically sorted integer columns of an unchecked candidate basis. -/
def candidateMatrix (A B : Fin m → Fin n → ℤ) (s : Finset (BimatrixVariable m n))
    (hs : s.card = m + n) : Matrix (Fin (m + n)) (Fin (m + n)) ℤ :=
  basisMatrix (bimatrixIntegerColumns A B) s hs

theorem candidateMatrix_map (A B : Fin m → Fin n → ℤ)
    (s : Finset (BimatrixVariable m n)) (hs : s.card = m + n) :
    (candidateMatrix A B s hs).map (fun z : ℤ => (z : ℚ)) =
      basisMatrix (bimatrixBasisColumns A B) s hs := by
  ext i j
  exact bimatrixIntegerColumns_cast A B i _

/-- Decide omitted-label coverage by explicit finite membership checks. -/
local instance (s : Finset (Fin (m + n) × Bool)) (d : Fin (m + n)) :
    Decidable (ComplementaryLabels.CoversExcept s d) := by
  unfold ComplementaryLabels.CoversExcept; infer_instance

/-- Decide whether a candidate entering variable is a permitted complementary port. -/
local instance (s : Finset (Fin (m + n) × Bool)) (d : Fin (m + n)) (v : Fin (m + n) × Bool) :
    Decidable (ComplementaryPorts.IsPort s d v) := by
  unfold ComplementaryPorts.IsPort; infer_instance

/-- Reconstruct a genuine path port only after all semantic and bit-shape checks. -/
def decode (A B : Fin m → Fin n → ℤ) (d : Fin (m + n)) (word : List Bool) :
    Option (BimatrixPathPort A B d) :=
  if word.length = width m n then
    if hs : (basic word).card = m + n then
      if he : (enteringSet d word).card = 1 then
        if hf : IntegerFeasible (candidateMatrix A B (basic word) hs) then
          let basis : BimatrixBasis A B := ⟨basic word, hs, by
            have hh := (integerFeasible_iff _).mp hf
            rwa [candidateMatrix_map] at hh⟩
          let v := (enteringSet d word).min' (by
            apply Finset.card_pos.mp
            omega)
          if hc : ComplementaryLabels.CoversExcept basis.nonbasic d then
            if hp : ComplementaryPorts.IsPort basis.nonbasic d (ofLex v) then
              let port : BimatrixPathPort A B d := ⟨⟨basis, hc⟩, v, hp⟩
              if encode port = word then some port else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem integerFeasible_basis (basis : BimatrixBasis A B) :
    IntegerFeasible (candidateMatrix A B basis.basic basis.cardinality) := by
  rw [integerFeasible_iff, candidateMatrix_map]
  exact basis.feasible

/-- The explicit shape, feasibility and port checks suffice to decode a word. -/
theorem exists_decode_of_checks (d : Fin (m + n)) (word : List Bool)
    (hw : word.length = width m n) (hs : (basic (m := m) (n := n) word).card = m + n)
    (he : (enteringSet d word).card = 1)
    (hf : IntegerFeasible (candidateMatrix A B (basic word) hs))
    (hc : ComplementaryLabels.CoversExcept ((basic word)ᶜ.map ofLex.toEmbedding) d)
    (hp : ∀ v ∈ enteringSet d word,
      ComplementaryPorts.IsPort ((basic word)ᶜ.map ofLex.toEmbedding) d (ofLex v)) :
    ∃ port, decode A B d word = some port := by
  let basis : BimatrixBasis A B := ⟨basic word, hs, by
    have hh := (integerFeasible_iff _).mp hf
    rwa [candidateMatrix_map] at hh⟩
  have hne : (enteringSet d word).Nonempty := by
    apply Finset.card_pos.mp
    omega
  let v := (enteringSet d word).min' hne
  have hv : v ∈ enteringSet d word := Finset.min'_mem _ _
  have hset : enteringSet d word = {v} := by
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp he
    simp only [v, hu, Finset.min'_singleton]
  let port : BimatrixPathPort A B d := ⟨⟨basis, hc⟩, v, hp v hv⟩
  have hencode : encode port = word := encode_eq_of_fields port word hw rfl hset
  refine ⟨port, ?_⟩
  simp only [decode, hw, hs, he, hf, ↓reduceIte, ↓reduceDIte]
  change (if _ : ComplementaryLabels.CoversExcept basis.nonbasic d then
    if _ : ComplementaryPorts.IsPort basis.nonbasic d (ofLex v) then
      if encode port = word then some port else none
    else none
  else none) = some port
  have hpermitted : ComplementaryPorts.IsPort basis.nonbasic d (ofLex v) := hp v hv
  simp only [show ComplementaryLabels.CoversExcept basis.nonbasic d from hc,
    hpermitted, hencode, ↓reduceDIte, ↓reduceIte]

/-- Encoding any certified port passes validation and recovers precisely that port. -/
@[simp] theorem decode_encode {d : Fin (m + n)} (port : BimatrixPathPort A B d) :
    decode A B d (encode port) = some port := by
  have hf (hs : (basic (encode port)).card = m + n) :
      IntegerFeasible (candidateMatrix A B (basic (encode port)) hs) := by
    have hfeas (s : Finset (BimatrixVariable m n)) (hs : s.card = m + n)
        (he : s = port.node.basis.basic) :
        IsFeasible (bimatrixBasisColumns A B) (fun _ => 1) s hs := by
      cases he
      exact port.node.basis.feasible
    rw [integerFeasible_iff, candidateMatrix_map]
    exact hfeas _ hs (basic_encode port)
  simp only [decode, encode_length, ↓reduceIte, basic_encode, port.node.basis.cardinality,
    hf, ↓reduceDIte, enteringSet_encode, Finset.card_singleton,
    Finset.min'_singleton]
  have hb : (⟨port.node.basis.basic, port.node.basis.cardinality, port.node.basis.feasible⟩ :
      BimatrixBasis A B) = port.node.basis := rfl
  simp only [hb, port.node.coverage, port.permitted, ↓reduceDIte]

/-- Every accepted word is the unique canonical encoding of its decoded port. -/
theorem encode_of_decode_eq_some {d : Fin (m + n)} {word : List Bool}
    {port : BimatrixPathPort A B d} (h : decode A B d word = some port) :
    encode port = word := by
  unfold decode at h
  try dsimp only at h
  split at h <;> try contradiction
  try dsimp only at h
  split at h <;> try contradiction
  try dsimp only at h
  split at h <;> try contradiction
  try dsimp only at h
  split at h <;> try contradiction
  try dsimp only at h
  split at h <;> try contradiction
  try dsimp only at h
  split at h <;> try contradiction
  try dsimp only at h
  split at h <;> try contradiction
  rename_i hround
  cases h
  exact hround

private theorem mem_slack (v : BimatrixVariable m n) :
    v ∈ bimatrixSlackVariables m n ↔ (ofLex v).2 = false := by
  constructor
  · rintro hv
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hv
    rw [← he]
    rfl
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨(ofLex v).1, Finset.mem_univ _, ?_⟩
    rw [← hv]
    exact toLex_ofLex v

/-- The distinguished source has exactly the all-false origin word. -/
@[simp] theorem encode_source (A B : Fin m → Fin n → ℤ) (d : Fin (m + n)) :
    encode (bimatrixSourcePort A B d) = List.replicate (width m n) false := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [encode, List.getElem_ofFn, List.getElem_replicate]
    split
    · rename_i hsmall
      have hv := mem_slack (variableAt (m := m) (n := n) ⟨i, hsmall⟩)
      change xor (decide (_ ∈ bimatrixSlackVariables m n)) _ = false
      simp only [hv]
      cases hb : (ofLex (variableAt (m := m) (n := n) ⟨i, hsmall⟩)).2 <;> simp
    · change xor (decide (_ = toLex (d, true))) (decide (_ = toLex (d, true))) = false
      simp

@[simp] theorem decode_origin (A B : Fin m → Fin n → ℤ) (d : Fin (m + n)) :
    decode A B d (List.replicate (width m n) false) = some (bimatrixSourcePort A B d) := by
  rw [← encode_source A B d, decode_encode]

/-- Extend a port operation to all binary words, fixing invalid encodings. -/
def transport {d : Fin (m + n)} (f : BimatrixPathPort A B d → BimatrixPathPort A B d)
    (word : List Bool) : List Bool :=
  match decode A B d word with
  | none => word
  | some port => encode (f port)

@[simp] theorem transport_encode {d : Fin (m + n)}
    (f : BimatrixPathPort A B d → BimatrixPathPort A B d) (port : BimatrixPathPort A B d) :
    transport f (encode port) = encode (f port) := by simp [transport]

theorem transport_invalid {d : Fin (m + n)}
    (f : BimatrixPathPort A B d → BimatrixPathPort A B d) {word : List Bool}
    (h : decode A B d word = none) : transport f word = word := by simp [transport, h]

/-- The total operation preserves width even on malformed and short words. -/
theorem transport_length {d : Fin (m + n)}
    (f : BimatrixPathPort A B d → BimatrixPathPort A B d) (word : List Bool) :
    (transport f word).length = word.length := by
  cases hd : decode A B d word with
  | none => simp [transport, hd]
  | some port =>
    rw [← encode_of_decode_eq_some hd]
    simp

/-- Canonical encoding preserves exactly the asymmetric End-of-Line condition. -/
theorem rawWitness_encode_iff {d : Fin (m + n)}
    (P S : BimatrixPathPort A B d → BimatrixPathPort A B d)
    (origin port : BimatrixPathPort A B d) :
    EndOfLine.RawWitness (transport P) (transport S) (encode origin) (encode port) ↔
      EndOfLine.RawWitness P S origin port := by
  simp only [EndOfLine.RawWitness, transport_encode, ne_eq, encode_injective.eq_iff]

/-- Invalid encodings cannot create either kind of asymmetric endpoint. -/
theorem not_rawWitness_of_invalid {d : Fin (m + n)}
    (P S : BimatrixPathPort A B d → BimatrixPathPort A B d)
    (origin word : List Bool) (h : decode A B d word = none) :
    ¬EndOfLine.RawWitness (transport P) (transport S) origin word := by
  simp only [EndOfLine.RawWitness, transport_invalid P h, transport_invalid S h,
    ne_eq, not_true_eq_false, and_false, or_self, not_false_eq_true]

/-- Every binary endpoint decodes to an endpoint of the underlying path. -/
theorem decode_of_rawWitness {d : Fin (m + n)}
    (P S : BimatrixPathPort A B d → BimatrixPathPort A B d)
    (origin : BimatrixPathPort A B d) (word : List Bool)
    (h : EndOfLine.RawWitness (transport P) (transport S) (encode origin) word) :
    ∃ port, decode A B d word = some port ∧ EndOfLine.RawWitness P S origin port := by
  cases hd : decode A B d word with
  | none => exact ((not_rawWitness_of_invalid P S _ _ hd) h).elim
  | some port =>
    refine ⟨port, rfl, ?_⟩
    rw [← encode_of_decode_eq_some hd] at h
    exact (rawWitness_encode_iff P S origin port).mp h

end GameTheory.Finite.BimatrixPathBinaryCodec
