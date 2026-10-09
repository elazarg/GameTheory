import GameTheoryComplexity.Backend.BinaryWordSubtraction
import Complexitylib.Classes.P.Pairing
import GameTheory.Math.BinaryExtraction

/-! Exact binary ratio extraction by bounded word arithmetic.
The precision ruler controls every iteration. A numerator exceeding its denominator
is clipped to the right endpoint, which selects the final binary cell.
A zero denominator retains the total scan: every extracted bit is one.
The exact ratio theorem requires a positive decoded denominator. -/
namespace GameTheory.Complexity.Backend.BinaryRatioExtraction
open _root_.Complexity _root_.Complexity.Cobham

private def clipped (num den : List Bool) : List Bool :=
  caseBit₀ (binaryCertificateLE ![num, den]) num den

private def step (v : Fin 4 → List Bool) : List Bool :=
  let doubled := false :: pairSnd (v 1)
  let next := binaryCertificateLE ![v 3, doubled]
  pair (next ++ pairFst (v 1)) (caseBit₀ next (binaryWordSub doubled (v 3)) doubled)

/-- The paired prefix and residual after a length-controlled scan. -/
def state (num den precision : List Bool) : List Bool :=
  recNotation (fun v : Fin 2 → List Bool => pair [] (clipped (v 0) (v 1)))
    step step precision ![num, den]

/-- Little-endian integer identifying the selected binary cell. -/
def prefixWord (num den precision : List Bool) : List Bool := pairFst (state num den precision)
/-- Unsigned residual numerator with the original denominator. -/
def remainderWord (num den precision : List Bool) : List Bool := pairSnd (state num den precision)

private theorem clipped_value (num den : List Bool) :
    Nat.fromBitsLE (clipped num den) = min (Nat.fromBitsLE num) (Nat.fromBitsLE den) := by
  rw [clipped, binaryCertificateLE_value]
  by_cases h : Nat.fromBitsLE num ≤ Nat.fromBitsLE den
  · simp [h, caseBit₀]
  · simp [h, caseBit₀, min_eq_right (by omega : Nat.fromBitsLE den ≤ Nat.fromBitsLE num)]

private theorem select_length (flag x y : List Bool) :
    (caseBit₀ flag x y).length ≤ max x.length y.length := by
  cases flag with
  | nil => exact le_max_right _ _
  | cons b flag => cases b <;> simp [caseBit₀]

private theorem fields_length (num den precision : List Bool) :
    ∃ p r, state num den precision = pair p r ∧ p.length = precision.length ∧
      r.length ≤ precision.length + num.length + den.length := by
  induction precision with
  | nil =>
    refine ⟨[], clipped num den, rfl, rfl, ?_⟩
    exact (select_length _ _ _).trans (by omega)
  | cons b clock ih =>
    obtain ⟨p, r, hs, hp, hr⟩ := ih
    let doubled := false :: r
    let next := binaryCertificateLE ![den, doubled]
    refine ⟨next ++ p, caseBit₀ next (binaryWordSub doubled den) doubled, ?_, ?_, ?_⟩
    · simp only [state, recNotation_cons, Bool.cond_self]
      change step ![clock, state num den clock, num, den] = _
      rw [hs]
      change pair (binaryCertificateLE ![den, false :: pairSnd (pair p r)] ++ pairFst (pair p r))
        (caseBit₀ (binaryCertificateLE ![den, false :: pairSnd (pair p r)])
          (binaryWordSub (false :: pairSnd (pair p r)) den) (false :: pairSnd (pair p r))) = _
      rw [pairFst_pair, pairSnd_pair]
    · change (binaryCertificateLE ![den, doubled] ++ p).length = _
      rw [List.length_append, binaryCertificateLE_length, hp, List.length_cons]
      omega
    · have hsub := binaryWordSub_length doubled den
      have hsel := select_length next (binaryWordSub doubled den) doubled
      have hd : doubled.length = r.length + 1 := rfl
      simp only [List.length_cons]
      omega

/-- The complete state has a linear bound even for malformed zero denominators. -/
theorem state_length (num den precision : List Bool) :
    (state num den precision).length ≤ 3 * precision.length + num.length + den.length + 2 := by
  obtain ⟨p, r, hs, hp, hr⟩ := fields_length num den precision
  rw [hs, pair_length, hp]
  omega

/-- The output contains exactly one bit per precision-ruler position. -/
theorem prefixWord_length (num den precision : List Bool) :
    (prefixWord num den precision).length = precision.length := by
  obtain ⟨p, r, hs, hp, _⟩ := fields_length num den precision
  simp only [prefixWord, hs, pairFst_pair, hp]

private theorem step_cobham : Cobham step := by
  have hp : Cobham fun v : Fin 4 → List Bool => pairFst (v 1) :=
    Cobham.comp (FP_subset_CobhamFP pairFst_mem_FP) fun _ : Fin 1 => .proj 1
  have hr : Cobham fun v : Fin 4 → List Bool => pairSnd (v 1) :=
    Cobham.comp (FP_subset_CobhamFP pairSnd_mem_FP) fun _ : Fin 1 => .proj 1
  have hd := appendFn (Cobham.const [false]) hr
  have hnext := Cobham.comp₂ binaryCertificateLE_cobham (.proj 3) hd
  exact Cobham.comp₂ Cobham.pairing (appendFn hnext hp)
    (Cobham.iteFn hnext (Cobham.comp₂ binaryWordSub_cobham hd (.proj 3)) hd)

/-- Ratio extraction has an actual polynomial-time word machine. -/
theorem state_cobham :
    Cobham fun v : Fin 3 → List Bool => state (v 0) (v 1) (v 2) := by
  have hinit : Cobham fun v : Fin 2 → List Bool => pair [] (clipped (v 0) (v 1)) :=
    Cobham.comp₂ Cobham.pairing Cobham.empty
      (Cobham.iteFn binaryCertificateLE_cobham (.proj 0) (.proj 1))
  have hbound : Cobham fun v : Fin 3 → List Bool =>
      v 0 ++ v 0 ++ v 0 ++ v 1 ++ v 2 ++ [false, false] :=
    appendFn (appendFn (appendFn (appendFn (appendFn (.proj 0) (.proj 0)) (.proj 0))
      (.proj 1)) (.proj 2)) (Cobham.const [false, false])
  have hrec := Cobham.boundedRec hinit step_cobham step_cobham hbound (fun r p => by
    have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> rfl
    rw [hp]
    change (state (p 0) (p 1) r).length ≤
      (r ++ r ++ r ++ p 0 ++ p 1 ++ [false, false]).length
    exact (state_length _ _ _).trans (by simp only [List.length_append,
      List.length_cons, List.length_nil]; omega))
  let args : Fin 3 → (Fin 3 → List Bool) → List Bool := ![fun v => v 2, fun v => v 0, fun v => v 1]
  have ha : ∀ i, Cobham (args i) := by intro i; fin_cases i <;> exact .proj _
  exact (Cobham.comp hrec ha).of_eq fun v => by
    have hp : Fin.tail (fun i => args i v) = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hp]
    rfl

theorem state_mem_FPn : FPn (fun v : Fin 3 → List Bool => state (v 0) (v 1) (v 2)) :=
  cobham_iff_FPn.mp state_cobham

/-- Extracting just the prefix preserves the polynomial-time certificate. -/
theorem prefixWord_cobham :
    Cobham fun v : Fin 3 → List Bool => prefixWord (v 0) (v 1) (v 2) :=
  Cobham.comp (FP_subset_CobhamFP pairFst_mem_FP) fun _ : Fin 1 => state_cobham

theorem prefixWord_mem_FPn : FPn (fun v : Fin 3 → List Bool => prefixWord (v 0) (v 1) (v 2)) :=
  cobham_iff_FPn.mp prefixWord_cobham

/-- Extracting the residual preserves the polynomial-time certificate. -/
theorem remainderWord_cobham :
    Cobham fun v : Fin 3 → List Bool => remainderWord (v 0) (v 1) (v 2) :=
  Cobham.comp (FP_subset_CobhamFP pairSnd_mem_FP) fun _ : Fin 1 => state_cobham

theorem remainderWord_mem_FPn :
    FPn (fun v : Fin 3 → List Bool => remainderWord (v 0) (v 1) (v 2)) :=
  cobham_iff_FPn.mp remainderWord_cobham

private theorem state_cons (num den clock : List Bool) (b : Bool) :
    state num den (b :: clock) =
      pair (binaryCertificateLE ![den, false :: remainderWord num den clock] ++
        prefixWord num den clock)
      (caseBit₀ (binaryCertificateLE ![den, false :: remainderWord num den clock])
        (binaryWordSub (false :: remainderWord num den clock) den)
        (false :: remainderWord num den clock)) := by
  simp only [state, recNotation_cons, Bool.cond_self]
  rfl

private theorem threshold_ratio (R D : ℕ) (hD : 0 < D) :
    decide (D ≤ 2 * R) = GameTheory.Math.binaryThreshold ((R : ℚ) / D) := by
  unfold GameTheory.Math.binaryThreshold
  congr 1
  apply propext
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  rw [le_div_iff₀ hDq]
  constructor
  · intro h
    have hq : (D : ℚ) ≤ 2 * (R : ℚ) := by exact_mod_cast h
    linarith
  · intro h
    have hq : (D : ℚ) ≤ 2 * (R : ℚ) := by linarith
    exact_mod_cast hq

/-- Exact prefix and residual for a clipped ratio with a positive denominator. -/
theorem value (num den precision : List Bool) (hden : 0 < Nat.fromBitsLE den) :
    let q : ℚ := (min (Nat.fromBitsLE num) (Nat.fromBitsLE den) : ℕ) / (Nat.fromBitsLE den : ℚ)
    Nat.fromBitsLE (prefixWord num den precision) =
      GameTheory.Math.binaryPrefix precision.length q ∧
    (Nat.fromBitsLE (remainderWord num den precision) : ℚ) / (Nat.fromBitsLE den : ℚ) =
      GameTheory.Math.binaryRemainder precision.length q ∧
    Nat.fromBitsLE (remainderWord num den precision) ≤ Nat.fromBitsLE den := by
  dsimp only
  induction precision with
  | nil =>
    simp only [prefixWord, remainderWord, state, recNotation, pairFst_pair, pairSnd_pair,
      clipped_value, List.length_nil, GameTheory.Math.binaryPrefix, GameTheory.Math.binaryRemainder]
    exact ⟨rfl, rfl, Nat.min_le_right _ _⟩
  | cons b clock ih =>
    obtain ⟨hp, hr, hbound⟩ := ih
    let R := Nat.fromBitsLE (remainderWord num den clock)
    let D := Nat.fromBitsLE den
    have hD : (0 : ℚ) < D := by exact_mod_cast hden
    have hbit : decide (D ≤ 2 * R) = GameTheory.Math.binaryThreshold
        (GameTheory.Math.binaryRemainder clock.length
          ((min (Nat.fromBitsLE num) D : ℕ) / (D : ℚ))) := by
      rw [threshold_ratio R D hden, hr]
    simp only [prefixWord, remainderWord, state_cons, pairFst_pair, pairSnd_pair]
    rw [binaryCertificateLE_value]
    simp only [Nat.fromBitsLE_cons, Bool.false_eq_true, ite_false, zero_add]
    change Nat.fromBitsLE ([decide (D ≤ 2 * R)] ++ prefixWord num den clock) = _ ∧
      (Nat.fromBitsLE (caseBit₀ [decide (D ≤ 2 * R)]
        (binaryWordSub (false :: remainderWord num den clock) den)
        (false :: remainderWord num den clock)) : ℚ) / D = _ ∧
      Nat.fromBitsLE (caseBit₀ [decide (D ≤ 2 * R)]
        (binaryWordSub (false :: remainderWord num den clock) den)
        (false :: remainderWord num den clock)) ≤ D
    by_cases hc : D ≤ 2 * R
    · have htrue : GameTheory.Math.binaryThreshold
          (GameTheory.Math.binaryRemainder clock.length
            ((min (Nat.fromBitsLE num) D : ℕ) / (D : ℚ))) = true := by simpa [hc] using hbit.symm
      simp only [hc, decide_true, caseBit₀, Bool.cond_true, ite_true,
        List.singleton_append, Nat.fromBitsLE_cons, binaryWordSub_value,
        Bool.false_eq_true, ite_false, zero_add]
      constructor
      · rw [List.length_cons, GameTheory.Math.binaryPrefix, htrue, hp]
        simp [Nat.add_comm]
      · constructor
        · rw [Nat.cast_sub hc, Nat.cast_mul, Nat.cast_ofNat, List.length_cons,
            GameTheory.Math.binaryRemainder, htrue]
          change (2 * (R : ℚ) - D) / D = 2 * _ - 1
          rw [← hr]
          simp [sub_div, mul_div_assoc, hD.ne', R, D]
        · change 2 * R - D ≤ D
          omega
    · have hfalse : GameTheory.Math.binaryThreshold
          (GameTheory.Math.binaryRemainder clock.length
            ((min (Nat.fromBitsLE num) D : ℕ) / (D : ℚ))) = false := by simpa [hc] using hbit.symm
      simp only [hc, decide_false, caseBit₀, Bool.cond_false, Bool.false_eq_true, ite_false,
        List.singleton_append, Nat.fromBitsLE_cons, zero_add]
      constructor
      · rw [List.length_cons, GameTheory.Math.binaryPrefix, hfalse, hp]
        simp
      · constructor
        · rw [Nat.cast_mul, Nat.cast_ofNat, List.length_cons,
            GameTheory.Math.binaryRemainder, hfalse]
          change (2 * (R : ℚ)) / D = 2 * _ - 0
          rw [← hr]
          ring
        · change 2 * R ≤ D
          omega

/-- The right endpoint and every clipped larger numerator select the final binary cell. -/
theorem prefixWord_endpoint (num den precision : List Bool)
    (hden : 0 < Nat.fromBitsLE den) (hclip : Nat.fromBitsLE den ≤ Nat.fromBitsLE num) :
    Nat.fromBitsLE (prefixWord num den precision) = 2 ^ precision.length - 1 := by
  have hn : (Nat.fromBitsLE den : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  simpa only [Nat.min_eq_right hclip, div_self hn, GameTheory.Math.binaryPrefix_one]
    using (value num den precision hden).1

end GameTheory.Complexity.Backend.BinaryRatioExtraction
