import GameTheoryComplexity.Backend.GeneralBimatrixEndpointMachine
import GameTheoryComplexity.Backend.GeneralBimatrixDictionary

/-! Automatic storage bounds for emission from a computed complementary dictionary.
The controller's working width covers all Cramer weights, probability masses and
payoff-unshift arithmetic. Clients supply the basis, without intermediate bounds. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec GameTheory.Math
open scoped BigOperators

private theorem cramerWidth_le_bird (k h : ℕ) :
    IntegerBasisBounds.width k h ≤ BirdIterationBounds.width k h := by
  unfold IntegerBasisBounds.width BirdIterationBounds.width
  nlinarith

private theorem shifted_bound (input : List Bool) (player : Bool) (i j : ℕ) :
    (decodeGeneralPayoff player input i j + ((2 : ℤ) ^ generalCoefficientBits input + 1)).natAbs ≤
      2 ^ (generalCoefficientBits input + 2) :=
  (payoff_add_pow_bound _ _ (decodeGeneralPayoff_natAbs_lt player input i j).le).le

private theorem cramerWeight_bound (input : List Bool) (basis : GeneralBimatrixShiftedBasis input)
    (v : BimatrixVariable (generalRowCount input) (generalColCount input)) :
    basis.cramerWeight v ≤
      2 ^ BirdIterationBounds.width (generalRowCount input + generalColCount input)
        (generalCoefficientBits input + 2) :=
  (basis.cramerWeight_lt (generalCoefficientBits input + 2)
    (fun i j => shifted_bound input false i.val j.val)
    (fun i j => shifted_bound input true i.val j.val) v).le.trans
      (Nat.pow_le_pow_right (by decide) (cramerWidth_le_bird _ _))

private theorem sum_natAbs_le (f : ℕ → ℤ) (t C : ℕ)
    (hf : ∀ i < t, (f i).natAbs ≤ C) :
    (∑ i ∈ Finset.range t, f i).natAbs ≤ t * C := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    exact (Int.natAbs_add_le _ _).trans
      ((Nat.add_le_add (ih (fun i hi => hf i (by omega))) (hf t (by omega))).trans_eq
        (by ring))

private theorem term_bound (input : List Bool) (basis : GeneralBimatrixShiftedBasis input)
    (det coeff width r : List Bool) (player : Bool)
    (hr : r.length < (generalActionRuler player input).length)
    (hf : ∀ i, binarySignedRowValue width coeff
      (i.val * (generalRowCount input + generalColCount input + 1)) =
      IntegerCramerComputation.signedNumerator basis.integerMatrix (fun _ => 1) i) :
    (binarySignedValue (generalBimatrixEndpointMassTermWord player (Fin.cons r
      ![input, membershipWord basis.basic, det, coeff, width]))).natAbs ≤
      2 ^ BirdIterationBounds.width (generalRowCount input + generalColCount input)
        (generalCoefficientBits input + 2) := by
  cases player
  · have hl : r.length < generalRowCount input + generalColCount input := by
      change r.length < generalRowCount input at hr
      omega
    have hv := generalBimatrixEndpointWeightWord_integer input basis det coeff width r
      ⟨r.length, hl⟩ rfl hf
    change (binarySignedValue (generalBimatrixEndpointWeightWord
      ![r, input, membershipWord basis.basic, det, coeff, width])).natAbs ≤ _
    rw [hv, Int.natAbs_natCast]
    exact cramerWeight_bound input basis _
  · have hl : generalRowCount input + r.length < generalRowCount input + generalColCount input := by
      change r.length < generalColCount input at hr
      omega
    have hv := generalBimatrixEndpointWeightWord_integer input basis det coeff width
      (generalRowRuler input ++ r) ⟨generalRowCount input + r.length, hl⟩
      (by rw [List.length_append]; rfl) hf
    change (binarySignedValue (generalBimatrixEndpointWeightWord
      ![generalRowRuler input ++ r, input, membershipWord basis.basic, det, coeff, width])).natAbs ≤ _
    rw [hv, Int.natAbs_natCast]
    exact cramerWeight_bound input basis _

private theorem prefix_bound (input : List Bool) (basis : GeneralBimatrixShiftedBasis input)
    (det coeff width : List Bool) (player : Bool) (t : ℕ)
    (ht : t ≤ (generalActionRuler player input).length)
    (hf : ∀ i, binarySignedRowValue width coeff
      (i.val * (generalRowCount input + generalColCount input + 1)) =
      IntegerCramerComputation.signedNumerator basis.integerMatrix (fun _ => 1) i) :
    (∑ i ∈ Finset.range t, binarySignedValue (generalBimatrixEndpointMassTermWord player
      (Fin.cons (List.replicate i false) ![input, membershipWord basis.basic, det, coeff, width]))).natAbs ≤
      (generalRowCount input + generalColCount input) *
        2 ^ BirdIterationBounds.width (generalRowCount input + generalColCount input)
          (generalCoefficientBits input + 2) := by
  apply (sum_natAbs_le _ _ _ (fun i hi => term_bound input basis det coeff width
    (List.replicate i false) player (by simpa only [List.length_replicate] using hi.trans_le ht) hf)).trans
  apply Nat.mul_le_mul_right
  cases player
  · change t ≤ generalRowCount input at ht
    omega
  · change t ≤ generalColCount input at ht
    omega

/-- The controller width removes all intermediate-capacity obligations from
endpoint serialization, including independently signed utility numerators. -/
theorem generalBimatrixEndpointMachineWord_eq_endpoint_of_workWidth
    (input : List Bool) (hi : GeneralInstanceValid input) (basis : GeneralBimatrixShiftedBasis input)
    (det coeff width : List Bool)
    (hw : width.length = BirdIterationBounds.workWidth
      (generalRowCount input + generalColCount input) (generalCoefficientBits input + 2))
    (hd : binarySignedValue det = IntegerCramerComputation.determinant basis.integerMatrix)
    (hf : ∀ i, binarySignedRowValue width coeff
      (i.val * (generalRowCount input + generalColCount input + 1)) =
      IntegerCramerComputation.signedNumerator basis.integerMatrix (fun _ => 1) i) :
    generalBimatrixEndpointMachineWord
      ![input, membershipWord basis.basic, det, coeff, width] = generalBimatrixEndpointWord input basis := by
  let k := generalRowCount input + generalColCount input
  let h := generalCoefficientBits input + 2
  let C := 2 ^ BirdIterationBounds.width k h
  have hk : 0 < k := by have hm := hi.1; dsimp [k]; omega
  have hpow : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hscale : k * C ≤ 2 ^ h * (k * C) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (k * C) hpow
  have hcapacity : 2 * k * C * 2 ^ h < 2 ^ (width.length - 1) := by
    rw [hw]
    exact BirdIterationBounds.workWidth_capacity k h
  have hmass_capacity : k * C < 2 ^ (width.length - 1) := by
    have hle : k * C ≤ 2 * k * C * 2 ^ h := calc
      k * C ≤ 2 ^ h * (k * C) := hscale
      _ ≤ 2 * (2 ^ h * (k * C)) := by omega
      _ = 2 * k * C * 2 ^ h := by ring
    exact hle.trans_lt hcapacity
  have hp : ∀ player, ∀ t ≤ (generalActionRuler player input).length,
      (∑ i ∈ Finset.range t, binarySignedValue (generalBimatrixEndpointMassTermWord player
        (Fin.cons (List.replicate i false) ![input, membershipWord basis.basic, det, coeff, width]))).natAbs <
        2 ^ (width.length - 1) := by
    intro player t ht
    exact (prefix_bound input basis det coeff width player t ht hf).trans_lt hmass_capacity
  have hwidth : 0 < width.length := by rw [hw]; exact BirdIterationBounds.workWidth_pos _ _
  have hm (player : Bool) :
      (binarySignedValue (generalBimatrixEndpointMassWord player
        ![input, membershipWord basis.basic, det, coeff, width])).natAbs ≤ k * C := by
    rw [generalBimatrixEndpointMassWord_value player _ hwidth (hp player)]
    exact prefix_bound input basis det coeff width player _ le_rfl hf
  have hd_bound : (binarySignedValue det).natAbs ≤ C := by
    rw [hd, IntegerCramerComputation.determinant_eq]
    exact (IntegerBasisBounds.determinant_natAbs_lt basis.integerMatrix h
      (basis.integerMatrix_bound h
        (fun i j => shifted_bound input false i.val j.val)
        (fun i j => shifted_bound input true i.val j.val))).le.trans
      (Nat.pow_le_pow_right (by decide) (cramerWidth_le_bird k h))
  have hshift : ((2 : ℤ) ^ generalCoefficientBits input + 1).natAbs ≤ 2 ^ h := by
    simpa only [zero_add] using
      (payoff_add_pow_bound 0 (generalCoefficientBits input) (by simp)).le
  apply generalBimatrixEndpointMachineWord_eq_endpoint input basis det coeff width hwidth hd hf hp
  intro player
  have htriangle := Int.natAbs_sub_le ((binarySignedValue det).natAbs : ℤ)
    (((2 : ℤ) ^ generalCoefficientBits input + 1) *
      binarySignedValue (generalBimatrixEndpointMassWord (!player)
        ![input, membershipWord basis.basic, det, coeff, width]))
  rw [Int.natAbs_natCast, Int.natAbs_mul] at htriangle
  have hle := htriangle.trans (Nat.add_le_add hd_bound
    (Nat.mul_le_mul hshift (hm (!player))))
  have hC : C ≤ k * C := by
    simpa using Nat.mul_le_mul_right C hk
  have htotal : C + 2 ^ h * (k * C) ≤ 2 * k * C * 2 ^ h := calc
    C + 2 ^ h * (k * C) ≤ k * C + 2 ^ h * (k * C) := Nat.add_le_add_right hC _
    _ ≤ 2 ^ h * (k * C) + 2 ^ h * (k * C) := Nat.add_le_add_right hscale _
    _ = 2 * k * C * 2 ^ h := by ring
  exact hle.trans_lt (htotal.trans_lt hcapacity)

/-- Feed the certified dictionary controller directly into certificate emission. -/
def generalBimatrixDictionaryEndpointWord (v : Fin 3 → List Bool) : List Bool :=
  generalBimatrixEndpointMachineWord ![v 0, v 1, generalBimatrixDictionaryDeterminant v,
    generalBimatrixDictionaryCoefficients v, generalBimatrixDictionaryWidth v]

theorem generalBimatrixDictionaryEndpointWord_cobham : Cobham generalBimatrixDictionaryEndpointWord := by
  let gs : Fin 5 → (Fin 3 → List Bool) → List Bool := fun i v =>
    ![v 0, v 1, generalBimatrixDictionaryDeterminant v,
      generalBimatrixDictionaryCoefficients v, generalBimatrixDictionaryWidth v] i
  have hg : ∀ i, Cobham (gs i) := by
    intro i
    fin_cases i
    · exact .proj 0
    · exact .proj 1
    · exact generalBimatrixDictionaryDeterminant_cobham
    · exact generalBimatrixDictionaryCoefficients_cobham
    · exact generalBimatrixDictionaryWidth_cobham
  exact (Cobham.comp (gs := gs) generalBimatrixEndpointMachineWord_cobham hg).of_eq fun _ => rfl

theorem generalBimatrixDictionaryEndpointWord_mem_FPn : FPn generalBimatrixDictionaryEndpointWord :=
  cobham_iff_FPn.mp generalBimatrixDictionaryEndpointWord_cobham

/-- Computing and emitting the dictionary preserves the supplied basis exactly.
No caller-supplied arithmetic width or intermediate bounds are required. -/
theorem generalBimatrixDictionaryEndpointWord_eq_endpoint (input : List Bool)
    (hi : GeneralInstanceValid input) (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool) :
    generalBimatrixDictionaryEndpointWord ![input, membershipWord basis.basic, entering] =
      generalBimatrixEndpointWord input basis := by
  let v : Fin 3 → List Bool := ![input, membershipWord basis.basic, entering]
  change generalBimatrixEndpointMachineWord ![input, membershipWord basis.basic,
    generalBimatrixDictionaryDeterminant v, generalBimatrixDictionaryCoefficients v,
      generalBimatrixDictionaryWidth v] = _
  apply generalBimatrixEndpointMachineWord_eq_endpoint_of_workWidth input hi basis
    (generalBimatrixDictionaryDeterminant v) (generalBimatrixDictionaryCoefficients v)
    (generalBimatrixDictionaryWidth v) (generalBimatrixDictionaryWidth_length v)
  · exact (generalBimatrixDictionaryDeterminant_value input basis entering).trans
      (IntegerCramerComputation.determinant_eq basis.integerMatrix).symm
  · intro i
    have hh := generalBimatrixDictionaryCoefficients_value input basis entering i 0
    simpa only [Fin.val_zero, Nat.add_zero, IntegerDictionaryComputation.coefficients_eq,
      Fin.cons_zero] using hh

/-- Every non-source complementary controller emits an answer accepted by the
unchanged serialized Nash relation. -/
theorem generalBimatrixDictionaryEndpointWord_accept (input : List Bool)
    (hi : GeneralInstanceValid input) (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool)
    (hc : ComplementaryLabels.IsComplementary basis.nonbasic)
    (hs : basis ≠ bimatrixSourceBasis
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))) :
    generalBimatrixRelation input
      (generalBimatrixDictionaryEndpointWord ![input, membershipWord basis.basic, entering]) := by
  rw [generalBimatrixDictionaryEndpointWord_eq_endpoint input hi basis entering]
  exact generalBimatrixEndpointWord_accept input hi basis hc hs

end GameTheory.Complexity.Backend
