import Complexitylib.Mathlib.NatBits
import GameTheory.Finite.BimatrixCertificate
import Mathlib.Tactic.Linarith

/-! Fixed-width fields and unary dimensions for signed rectangular bimatrix inputs. -/
namespace GameTheory.Complexity.Backend

/-- A total fixed-width field parser, also defined on malformed words. -/
def generalBinaryField (W index : ℕ) (word : List Bool) : List Bool :=
  (word.drop (index * W)).take W

/-- Unsigned value of a fixed-width field. -/
def generalNatField (W index : ℕ) (word : List Bool) : ℕ :=
  Nat.fromBitsLE (generalBinaryField W index word)

/-- Concatenate a specified number of equally wide binary fields. -/
def encodeGeneralFields (W : ℕ) : ℕ → (ℕ → ℕ) → List Bool
  | 0, _ => []
  | k + 1, f => Nat.toBitsLE W (f 0) ++ encodeGeneralFields W k (fun i => f (i + 1))

@[simp] theorem encodeGeneralFields_length (W k : ℕ) (f : ℕ → ℕ) :
    (encodeGeneralFields W k f).length = k * W := by
  induction k generalizing f with
  | zero => simp [encodeGeneralFields]
  | succ k ih => simp [encodeGeneralFields, ih, Nat.succ_mul, Nat.add_comm]

/-- Unary row dimension. -/
def generalRowRuler (input : List Bool) : List Bool := input.takeWhile id
/-- Unary column dimension following the row delimiter. -/
def generalColRuler (input : List Bool) : List Bool :=
  (input.drop ((generalRowRuler input).length + 1)).takeWhile id
/-- Unary payoff width following both dimension delimiters. -/
def generalBitsRuler (input : List Bool) : List Bool :=
  (input.drop ((generalRowRuler input).length + (generalColRuler input).length + 2)).takeWhile id
/-- Signed payoff blocks after the three unary headers. -/
def generalPayload (input : List Bool) : List Bool :=
  input.drop ((generalRowRuler input).length + (generalColRuler input).length +
    (generalBitsRuler input).length + 3)

/-- Serialized row dimension. -/
def generalRowCount (input : List Bool) : ℕ := (generalRowRuler input).length
/-- Serialized column dimension. -/
def generalColCount (input : List Bool) : ℕ := (generalColRuler input).length
/-- Serialized coefficient magnitude width. -/
def generalCoefficientBits (input : List Bool) : ℕ := (generalBitsRuler input).length

/-- Positive dimensions, positive coefficient width, and an exact payload length. -/
def GeneralInstanceValid (input : List Bool) : Prop :=
  let m := generalRowCount input
  let n := generalColCount input
  let h := generalCoefficientBits input
  0 < m ∧ 0 < n ∧ 0 < h ∧ input.length = m + n + h + 3 + 4 * m * n * h

instance (input : List Bool) : Decidable (GeneralInstanceValid input) := by
  unfold GeneralInstanceValid; infer_instance

/-- One unsigned magnitude block of a row-major signed payoff. -/
def generalPayoffField (columnPlayer positive : Bool) (input : List Bool) (i j : ℕ) :
    List Bool :=
  generalBinaryField (generalCoefficientBits input)
    (2 * ((if columnPlayer then generalRowCount input * generalColCount input else 0) +
      i * generalColCount input + j) + (if positive then 0 else 1)) (generalPayload input)

/-- Row-major signed integer payoff from its positive and negative magnitude blocks. -/
def decodeGeneralPayoff (columnPlayer : Bool) (input : List Bool) (i j : ℕ) : ℤ :=
  (Nat.fromBitsLE (generalPayoffField columnPlayer true input i j) : ℤ) -
    (Nat.fromBitsLE (generalPayoffField columnPlayer false input i j) : ℤ)

@[simp] theorem generalRowRuler_length_le (input : List Bool) :
    (generalRowRuler input).length ≤ input.length := (List.takeWhile_sublist _).length_le
@[simp] theorem generalColRuler_length_le (input : List Bool) :
    (generalColRuler input).length ≤ input.length := by
  exact ((List.takeWhile_sublist _).length_le).trans (by simp only [List.length_drop]; omega)
@[simp] theorem generalBitsRuler_length_le (input : List Bool) :
    (generalBitsRuler input).length ≤ input.length := by
  exact ((List.takeWhile_sublist _).length_le).trans (by simp only [List.length_drop]; omega)

/-- A field of a concatenated encoding is precisely its fixed-width block. -/
theorem generalBinaryField_encode (W k : ℕ) (f : ℕ → ℕ) (index : ℕ)
    (hi : index < k) :
    generalBinaryField W index (encodeGeneralFields W k f) = Nat.toBitsLE W (f index) := by
  induction k generalizing f index with
  | zero => omega
  | succ k ih =>
    cases index with
    | zero => simp [generalBinaryField, encodeGeneralFields]
    | succ index =>
      have hidx : index < k := by omega
      have hdrop : (Nat.toBitsLE W (f 0)).drop (W + index * W) = [] :=
        List.drop_eq_nil_iff.mpr (by simp)
      simpa [generalBinaryField, encodeGeneralFields, List.drop_append, Nat.succ_mul,
        hdrop, Nat.add_sub_cancel, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        ih (fun i => f (i + 1)) index hidx

/-- Bounded field values round-trip through binary encoding. -/
theorem generalNatField_encode (W k : ℕ) (f : ℕ → ℕ) (index : ℕ)
    (hi : index < k) (hf : f index < 2 ^ W) :
    generalNatField W index (encodeGeneralFields W k f) = f index := by
  rw [generalNatField, generalBinaryField_encode W k f index hi,
    Nat.fromBitsLE_toBitsLE hf]

/-- Every parsed field has at most the advertised bit width. -/
theorem generalNatField_lt (W index : ℕ) (word : List Bool) :
    generalNatField W index word < 2 ^ W := by
  have h := Nat.fromBitsLE_lt_pow_length (generalBinaryField W index word)
  have hl : (generalBinaryField W index word).length ≤ W := by
    simp only [generalBinaryField, List.length_take]; omega
  exact h.trans_le (Nat.pow_le_pow_right (by decide) hl)

/-- Both signed magnitudes are bounded, hence so is their difference. -/
theorem decodeGeneralPayoff_natAbs_lt (columnPlayer : Bool) (input : List Bool) (i j : ℕ) :
    (decodeGeneralPayoff columnPlayer input i j).natAbs < 2 ^ generalCoefficientBits input := by
  have hp := generalNatField_lt (generalCoefficientBits input)
    (2 * ((if columnPlayer then generalRowCount input * generalColCount input else 0) +
      i * generalColCount input + j)) (generalPayload input)
  have hn := generalNatField_lt (generalCoefficientBits input)
    (2 * ((if columnPlayer then generalRowCount input * generalColCount input else 0) +
      i * generalColCount input + j) + 1) (generalPayload input)
  change ((generalNatField (generalCoefficientBits input)
    (2 * ((if columnPlayer then generalRowCount input * generalColCount input else 0) +
      i * generalColCount input + j)) (generalPayload input) : ℤ) -
    (generalNatField (generalCoefficientBits input)
    (2 * ((if columnPlayer then generalRowCount input * generalColCount input else 0) +
      i * generalColCount input + j) + 1) (generalPayload input) : ℤ)).natAbs < _
  omega

private theorem trueRuler_eq (word : List Bool) :
    word.takeWhile id = List.replicate (word.takeWhile id).length true := by
  apply List.eq_replicate_iff.mpr
  exact ⟨rfl, List.all_eq_true.mp List.all_takeWhile⟩

/-- The row ruler consists entirely of true bits. -/
theorem generalRowRuler_eq (input : List Bool) :
    generalRowRuler input = List.replicate (generalRowRuler input).length true :=
  trueRuler_eq _
/-- The column ruler consists entirely of true bits. -/
theorem generalColRuler_eq (input : List Bool) :
    generalColRuler input = List.replicate (generalColRuler input).length true :=
  trueRuler_eq _
/-- The coefficient ruler consists entirely of true bits. -/
theorem generalBitsRuler_eq (input : List Bool) :
    generalBitsRuler input = List.replicate (generalBitsRuler input).length true :=
  trueRuler_eq _

/-- Canonical unary headers followed by the signed matrix payload. -/
def generalInstanceWord (m n h : ℕ) (payload : List Bool) : List Bool :=
  List.replicate m true ++ [false] ++ List.replicate n true ++ [false] ++
    List.replicate h true ++ [false] ++ payload

@[simp] theorem generalInstanceWord_row (m n h : ℕ) (payload : List Bool) :
    generalRowRuler (generalInstanceWord m n h payload) = List.replicate m true := by
  simp [generalRowRuler, generalInstanceWord, List.append_assoc]

@[simp] theorem generalInstanceWord_col (m n h : ℕ) (payload : List Bool) :
    generalColRuler (generalInstanceWord m n h payload) = List.replicate n true := by
  simp only [generalColRuler, generalInstanceWord_row, List.length_replicate]
  simp [generalInstanceWord, List.append_assoc, List.drop_append]

@[simp] theorem generalInstanceWord_bits (m n h : ℕ) (payload : List Bool) :
    generalBitsRuler (generalInstanceWord m n h payload) = List.replicate h true := by
  simp only [generalBitsRuler, generalInstanceWord_row, generalInstanceWord_col,
    List.length_replicate]
  simp [generalInstanceWord, List.append_assoc, List.drop_append,
    Nat.add_assoc]

@[simp] theorem generalInstanceWord_payload (m n h : ℕ) (payload : List Bool) :
    generalPayload (generalInstanceWord m n h payload) = payload := by
  simp only [generalPayload, generalInstanceWord_row, generalInstanceWord_col,
    generalInstanceWord_bits, List.length_replicate]
  simp only [generalInstanceWord, List.append_assoc, List.singleton_append]
  change (List.replicate m true ++ false ::
    (List.replicate n true ++ false :: (List.replicate h true ++ false :: payload))).drop
      (m + n + h + 3) = payload
  have hd (k r : ℕ) (rest : List Bool) :
      (List.replicate k true ++ false :: rest).drop (k + 1 + r) = rest.drop r := by
    rw [List.drop_append]
    have hnil : (List.replicate k true).drop (k + 1 + r) = [] :=
      List.drop_eq_nil_iff.mpr (by simp only [List.length_replicate]; omega)
    rw [hnil, List.nil_append]
    simp only [List.length_replicate]
    have he : k + 1 + r - k = r + 1 := by omega
    rw [he, List.drop_succ_cons]
  have he : m + n + h + 3 = m + 1 + (n + 1 + (h + 1)) := by omega
  rw [he, hd, hd]
  simpa using hd h 0 payload
/-- The row-major signed value represented by one payoff entry. -/
def generalPayoffValue (m n : ℕ) (A B : ℕ → ℕ → ℤ) (r : ℕ) : ℤ :=
  if r < m * n then A (r / n) (r % n)
  else B ((r - m * n) / n) ((r - m * n) % n)

/-- Separate the positive and negative magnitude of one row-major entry. -/
def generalPayoffMagnitude (m n : ℕ) (A B : ℕ → ℕ → ℤ) (index : ℕ) : ℕ :=
  let z := generalPayoffValue m n A B (index / 2)
  if index % 2 = 0 then z.toNat else (-z).toNat

/-- Serialize two independent signed matrices, with explicit unary dimensions and width. -/
def encodeGeneralInstance (m n h : ℕ) (A B : ℕ → ℕ → ℤ) : List Bool :=
  generalInstanceWord m n h
    (encodeGeneralFields h (4 * m * n) (generalPayoffMagnitude m n A B))

@[simp] theorem encodeGeneralInstance_row (m n h : ℕ) (A B : ℕ → ℕ → ℤ) :
    generalRowCount (encodeGeneralInstance m n h A B) = m := by
  simp [generalRowCount, encodeGeneralInstance]
@[simp] theorem encodeGeneralInstance_col (m n h : ℕ) (A B : ℕ → ℕ → ℤ) :
    generalColCount (encodeGeneralInstance m n h A B) = n := by
  simp [generalColCount, encodeGeneralInstance]
@[simp] theorem encodeGeneralInstance_bits (m n h : ℕ) (A B : ℕ → ℕ → ℤ) :
    generalCoefficientBits (encodeGeneralInstance m n h A B) = h := by
  simp [generalCoefficientBits, encodeGeneralInstance]
@[simp] theorem encodeGeneralInstance_length (m n h : ℕ) (A B : ℕ → ℕ → ℤ) :
    (encodeGeneralInstance m n h A B).length = m + n + h + 3 + 4 * m * n * h := by
  simp only [encodeGeneralInstance, generalInstanceWord, List.length_append,
    List.length_replicate, List.length_singleton, encodeGeneralFields_length]
  omega

theorem encodeGeneralInstance_valid (m n h : ℕ) (A B : ℕ → ℕ → ℤ)
    (hm : 0 < m) (hn : 0 < n) (hh : 0 < h) :
    GeneralInstanceValid (encodeGeneralInstance m n h A B) := by
  simp [GeneralInstanceValid, hm, hn, hh]

private theorem generalPayoffValue_index (m n : ℕ) (A B : ℕ → ℕ → ℤ)
    (columnPlayer : Bool) (i j : ℕ) (hi : i < m) (hj : j < n) :
    generalPayoffValue m n A B ((if columnPlayer then m * n else 0) + i * n + j) =
      (if columnPlayer then B else A) i j := by
  have hn : 0 < n := by omega
  have hr : i * n + j < m * n := by nlinarith
  have hd : (i * n + j) / n = i := by
    rw [Nat.mul_comm i n, Nat.mul_add_div hn, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hm : (i * n + j) % n = j := by
    rw [Nat.mul_comm i n, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  cases columnPlayer
  · simp [generalPayoffValue, hr, hd, hm]
  · have hnot : ¬ (m * n + i * n + j < m * n) := by omega
    have he : m * n + i * n + j - m * n = i * n + j := by omega
    simp [generalPayoffValue, hnot, he, hd, hm]

/-- Every in-range signed coefficient round-trips when its magnitude fits the width. -/
theorem decodeGeneralPayoff_encode (m n h : ℕ) (A B : ℕ → ℕ → ℤ)
    (columnPlayer : Bool) (i j : ℕ) (hi : i < m) (hj : j < n)
    (hz : ((if columnPlayer then B else A) i j).natAbs < 2 ^ h) :
    decodeGeneralPayoff columnPlayer (encodeGeneralInstance m n h A B) i j =
      (if columnPlayer then B else A) i j := by
  let r := (if columnPlayer then m * n else 0) + i * n + j
  have hr : r < 2 * m * n := by
    dsimp [r]; split <;> nlinarith
  have hp : generalPayoffMagnitude m n A B (2 * r) =
      ((if columnPlayer then B else A) i j).toNat := by
    simp only [generalPayoffMagnitude, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      Nat.mul_mod_right, ↓reduceIte]
    exact congrArg Int.toNat (generalPayoffValue_index m n A B columnPlayer i j hi hj)
  have hq : generalPayoffMagnitude m n A B (2 * r + 1) =
      (-((if columnPlayer then B else A) i j)).toNat := by
    simp only [generalPayoffMagnitude, Nat.mul_add_div (by decide : 0 < 2),
      Nat.mul_add_mod]
    norm_num only
    exact congrArg (fun z : ℤ => (-z).toNat)
      (generalPayoffValue_index m n A B columnPlayer i j hi hj)
  unfold decodeGeneralPayoff generalPayoffField
  simp only [encodeGeneralInstance_bits, encodeGeneralInstance_row, encodeGeneralInstance_col]
  simp only [encodeGeneralInstance, generalInstanceWord_payload]
  change (generalNatField h (2 * r) (encodeGeneralFields h (4 * m * n)
    (generalPayoffMagnitude m n A B)) : ℤ) -
    (generalNatField h (2 * r + 1) (encodeGeneralFields h (4 * m * n)
    (generalPayoffMagnitude m n A B)) : ℤ) = _
  rw [generalNatField_encode h _ _ _ (by nlinarith) (by rw [hp]; omega),
    generalNatField_encode h _ _ _ (by nlinarith) (by rw [hq]; omega), hp, hq]
  exact Int.toNat_sub_toNat_neg _

end GameTheory.Complexity.Backend

