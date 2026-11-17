module

public import GameTheoryComplexity.Backend.GeneralBimatrixVerifier
public import GameTheoryComplexity.Backend.BinaryCertificateFold

@[expose] public section

/-! Native polynomial-time certificates for the rectangular-game verifier.
Every loop is bounded by an explicitly encoded action ruler or field width. -/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

private theorem reindexProducer {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
    (hf : ComputableInPolyTime f (encPi encBits) encBits) (index : Fin m → Fin n) :
    ComputableInPolyTime (fun v : Fin n → List Bool => f (fun i => v (index i)))
      (encPi encBits) encBits := by
  apply hf.comp
  apply ComputableInPolyTime.pi
  intro i
  exact ComputableInPolyTime.pi_apply encBits (index i)

private theorem verifierInput_polyTime :
    ComputableInPolyTime (fun x : List Bool => x) encBits encBits := .id'

/-- The quadratic unary certificate-width ruler is polynomial-time. -/
@[fun_prop] theorem generalWidthRuler_polyTime :
    ComputableInPolyTime generalWidthRuler encBits encBits := by
  have hlen := ComputableInPolyTime.length_bits_comp verifierInput_polyTime
  have hleft := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (.const 2) hlen) (.const 2)
  have hright := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (.const 8) hlen) (.const 6)
  have hcount := ComputableInPolyTime.unary_mul' hleft hright
  exact ComputableInPolyTime.bitsAppend
    ((ComputableInPolyTime.bitsReplicate true).comp hcount) (.const [true])

/-- Select the row or column action ruler in polynomial time. -/
@[fun_prop] theorem generalActionRuler_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (fun v : Fin 1 → List Bool =>
      generalActionRuler columnPlayer (v 0)) (encPi encBits) encBits := by
  cases columnPlayer
  · exact generalRowRuler_polyTime
  · exact generalColRuler_polyTime

/-- Fixed-width extraction uses unary field and word lengths for its offset. -/
@[fun_prop] theorem generalCertificateFieldWord_polyTime :
    ComputableInPolyTime generalCertificateFieldWord (encPi encBits) encBits := by
  have hindex := ComputableInPolyTime.pi_apply encBits (0 : Fin 3)
  have hinput := ComputableInPolyTime.pi_apply encBits (1 : Fin 3)
  have hcert := ComputableInPolyTime.pi_apply encBits (2 : Fin 3)
  have hwidth := generalWidthRuler_polyTime.comp hinput
  have hwidthLen := ComputableInPolyTime.length_bits_comp hwidth
  have hoffset := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.length_bits_comp hindex) hwidthLen
  exact (hcert.bitsDropWithInput hoffset).bitsTakeWithInput hwidthLen

/-- Probability fields use the row ruler only for the column distribution. -/
@[fun_prop] theorem generalWeightWord_polyTime (columnWeights : Bool) :
    ComputableInPolyTime (generalWeightWord columnWeights) (encPi encBits) encBits := by
  have hrow := reindexProducer generalRowRuler_polyTime (![1] : Fin 1 → Fin 3)
  have hconditional : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => if columnWeights then generalRowRuler (v 1) else [])
      (encPi encBits) encBits := by
    cases columnWeights with
    | false => exact .const []
    | true => exact hrow
  have hheader := ComputableInPolyTime.bitsAppend (.const (List.replicate 6 true))
    (ComputableInPolyTime.bitsAppend hconditional (.pi_apply encBits (0 : Fin 3)))
  have hargs : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        ![List.replicate 6 true ++ (if columnWeights then generalRowRuler (v 1) else []) ++ v 0,
          v 1, v 2]) (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hheader
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
  exact generalCertificateFieldWord_polyTime.comp hargs

/-- One signed payoff slice preserves the exact matrix offsets and bit padding. -/
@[fun_prop] theorem generalPayoffWord_polyTime (columnPlayer positive : Bool) :
    ComputableInPolyTime (generalPayoffWord columnPlayer positive) (encPi encBits) encBits := by
  let m : (Fin 3 → List Bool) → List Bool := fun v => generalRowRuler (v 2)
  let n : (Fin 3 → List Bool) → List Bool := fun v => generalColRuler (v 2)
  let h : (Fin 3 → List Bool) → List Bool := fun v => generalBitsRuler (v 2)
  let cells : (Fin 3 → List Bool) → List Bool := fun v =>
    (if columnPlayer then List.replicate ((m v).length * (n v).length) true else []) ++
      List.replicate ((v 0).length * (n v).length) true ++ v 1
  let factor : (Fin 3 → List Bool) → List Bool := fun v => h v ++ h v
  have hinput : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![v 2]) (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .pi_apply encBits (2 : Fin 3)
  have hm0 := generalRowRuler_polyTime.comp hinput
  have hn0 := generalColRuler_polyTime.comp hinput
  have hh0 := generalBitsRuler_polyTime.comp hinput
  have hp0 := generalPayload_polyTime.comp hinput
  have hm : ComputableInPolyTime m (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hm0.tidy.of_enc_eq
    intro v
    rfl
  have hn : ComputableInPolyTime n (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hn0.tidy.of_enc_eq
    intro v
    rfl
  have hh : ComputableInPolyTime h (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hh0.tidy.of_enc_eq
    intro v
    rfl
  have hp : ComputableInPolyTime (fun v : Fin 3 → List Bool => generalPayload (v 2))
      (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hp0.tidy.of_enc_eq
    intro v
    rfl
  have hmlen := ComputableInPolyTime.length_bits_comp hm
  have hnlen := ComputableInPolyTime.length_bits_comp hn
  have hhLen := ComputableInPolyTime.length_bits_comp hh
  have hv0 := ComputableInPolyTime.pi_apply encBits (0 : Fin 3)
  have hv1 := ComputableInPolyTime.pi_apply encBits (1 : Fin 3)
  have hv0len := ComputableInPolyTime.length_bits_comp hv0
  have hv1len := ComputableInPolyTime.length_bits_comp hv1
  have hcolCount := ComputableInPolyTime.unary_mul' hmlen hnlen
  have hcolBlock0 := (ComputableInPolyTime.bitsReplicate true).comp hcolCount
  have hcolBlock : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => if columnPlayer then
        List.replicate ((m v).length * (n v).length) true else [])
      (encPi encBits) encBits := by
    cases columnPlayer with
    | false => exact .const []
    | true => simpa [Function.comp_def] using hcolBlock0
  have hrowCount := ComputableInPolyTime.unary_mul' hv0len hnlen
  have hrowBlock := (ComputableInPolyTime.bitsReplicate true).comp hrowCount
  have hcells := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hcolBlock hrowBlock) hv1
  have hfactorLen := ComputableInPolyTime.unary_add' hhLen hhLen
  have hcellsLen := ComputableInPolyTime.length_bits_comp hcells
  have hoffsetCount := ComputableInPolyTime.unary_mul' hcellsLen hfactorLen
  have hoffsetRep := (ComputableInPolyTime.bitsReplicate true).comp hoffsetCount
  have hsign : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => if positive then [] else h v)
      (encPi encBits) encBits := by
    cases positive with
    | false => simpa [Function.comp_def] using hh
    | true => exact .const []
  have hoffset := ComputableInPolyTime.bitsAppend hoffsetRep hsign
  have hdrop := hp.bitsDropWithInput (ComputableInPolyTime.length_bits_comp hoffset)
  have htake := hdrop.bitsTakeWithInput hhLen
  apply ComputableInPolyTime.of_tidy
  apply htake.tidy.of_enc_eq (g := generalPayoffWord columnPlayer positive)
  intro v
  rfl
/-- Multiplication of one signed tally and its opposite-player weight. -/
@[fun_prop] theorem generalWeightedTerm_polyTime (columnPlayer positive : Bool) :
    ComputableInPolyTime (generalWeightedTerm columnPlayer positive) (encPi encBits) encBits := by
  have hpayoffTable : ComputableInPolyTime
      (fun v : Fin 4 → List Bool =>
        ![if columnPlayer then v 0 else v 1, if columnPlayer then v 1 else v 0, v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · split
      · exact .pi_apply encBits (0 : Fin 4)
      · exact .pi_apply encBits (1 : Fin 4)
    · split
      · exact .pi_apply encBits (1 : Fin 4)
      · exact .pi_apply encBits (0 : Fin 4)
    · exact .pi_apply encBits 2
  have hpayoff := (generalPayoffWord_polyTime columnPlayer positive).comp hpayoffTable
  have hweightTable : ComputableInPolyTime (fun v : Fin 4 → List Bool => ![v 0, v 2, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
  have hweight := (generalWeightWord_polyTime (!columnPlayer)).comp hweightTable
  exact binaryWordMul_polyTime hpayoff hweight

@[fun_prop] theorem generalScoreWord_polyTime (columnPlayer positive : Bool) :
    ComputableInPolyTime (generalScoreWord columnPlayer positive) (encPi encBits) encBits := by
  let width : (Fin 3 → List Bool) → List Bool := fun params =>
    generalWidthRuler (params 1) ++
      List.replicate (2 * (generalBitsRuler (params 1)).length) true
  have hwidthRuler := generalWidthRuler_polyTime.comp (.pi_apply encBits (1 : Fin 3))
  have hbitsTable : ComputableInPolyTime (fun v : Fin 3 → List Bool => ![v 1])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .pi_apply encBits (1 : Fin 3)
  have hbitsRuler := generalBitsRuler_polyTime.comp hbitsTable
  have hdouble := ComputableInPolyTime.unary_mul' (.const 2)
    (ComputableInPolyTime.length_bits_comp hbitsRuler)
  have hwidth : ComputableInPolyTime width (encPi encBits) encBits := by
    simpa [width, Function.comp_def] using ComputableInPolyTime.bitsAppend
      hwidthRuler ((ComputableInPolyTime.bitsReplicate true).comp hdouble)
  have hclock := reindexProducer (generalActionRuler_polyTime (!columnPlayer))
    (![1] : Fin 1 → Fin 3)
  have hclock' : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => generalActionRuler (!columnPlayer) (v 1))
      (encPi encBits) encBits := by
    simpa [reindexProducer, Function.comp_def] using hclock
  have hparams : ComputableInPolyTime (fun v : Fin 3 → List Bool => v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact .pi_apply encBits i
  have hbound (suffix : List Bool) (params : Fin 3 → List Bool) :
      (generalWeightedTerm columnPlayer positive (Fin.cons suffix params)).length ≤
        (width params).length := by
    have h := generalWeightedTerm_length_le columnPlayer positive (Fin.cons suffix params)
    have hi : (Fin.cons suffix params : Fin 4 → List Bool) 2 = params 1 := rfl
    rw [hi] at h
    simp only [width, List.length_append, List.length_replicate]
    omega
  change ComputableInPolyTime
    (fun v : Fin 3 → List Bool => binaryIndexedSum (generalWeightedTerm columnPlayer positive)
      (generalActionRuler (!columnPlayer) (v 1)) v) (encPi encBits) encBits
  exact binaryIndexedSum_polyTime (p := 3) (Input := Fin 3 → List Bool)
    (input := encPi encBits) (term := generalWeightedTerm columnPlayer positive)
    (width := width) (clock := fun v => generalActionRuler (!columnPlayer) (v 1))
    (params := fun v => v) (generalWeightedTerm_polyTime columnPlayer positive)
    hwidth hbound hclock' hparams

@[fun_prop] theorem generalWeightSumWord_polyTime (columnWeights : Bool) :
    ComputableInPolyTime (generalWeightSumWord columnWeights) (encPi encBits) encBits := by
  let width : (Fin 2 → List Bool) → List Bool := fun params => generalWidthRuler (params 0)
  have hwidth := generalWidthRuler_polyTime.comp (.pi_apply encBits (0 : Fin 2))
  have hclock := reindexProducer (generalActionRuler_polyTime columnWeights)
    (![0] : Fin 1 → Fin 2)
  have hparams : ComputableInPolyTime (fun v : Fin 2 → List Bool => v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact .pi_apply encBits i
  have hbound (suffix : List Bool) (params : Fin 2 → List Bool) :
      (generalWeightWord columnWeights (Fin.cons suffix params)).length ≤
        (width params).length := by
    exact generalWeightWord_length_le columnWeights (Fin.cons suffix params)
  change ComputableInPolyTime
    (fun v : Fin 2 → List Bool => binaryIndexedSum (generalWeightWord columnWeights)
      (generalActionRuler columnWeights (v 0)) v) (encPi encBits) encBits
  exact binaryIndexedSum_polyTime (p := 2) (Input := Fin 2 → List Bool)
    (input := encPi encBits) (term := generalWeightWord columnWeights) (width := width)
    (clock := fun v => generalActionRuler columnWeights (v 0)) (params := fun v => v)
    (generalWeightWord_polyTime columnWeights) hwidth hbound hclock hparams

@[fun_prop] theorem generalActionCheck_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (generalActionCheck columnPlayer) (encPi encBits) encBits := by
  have hpos := generalScoreWord_polyTime columnPlayer true
  have hneg := generalScoreWord_polyTime columnPlayer false
  have hutility (positive : Bool) : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        generalCertificateFieldWord
          ![List.replicate ((if columnPlayer then 4 else 2) + (if positive then 0 else 1)) true,
            v 1, v 2]) (encPi encBits) encBits := by
    have htable : ComputableInPolyTime
        (fun v : Fin 3 → List Bool =>
          ![List.replicate ((if columnPlayer then 4 else 2) + (if positive then 0 else 1)) true,
            v 1, v 2]) (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .const (List.replicate
          ((if columnPlayer then 4 else 2) + (if positive then 0 else 1)) true)
      · exact .pi_apply encBits 1
      · exact .pi_apply encBits 2
    exact generalCertificateFieldWord_polyTime.comp htable
  have hutilityTrue := hutility true
  have hutilityFalse := hutility false
  have hleftTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![generalScoreWord columnPlayer true v,
        generalCertificateFieldWord
          ![List.replicate ((if columnPlayer then 4 else 2) + 1) true, v 1, v 2]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hpos
    · exact hutilityFalse
  have hleft := binaryCertificateAdd_polyTime.comp hleftTable
  have hrightTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![generalScoreWord columnPlayer false v,
        generalCertificateFieldWord
          ![List.replicate (if columnPlayer then 4 else 2) true, v 1, v 2]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hneg
    · exact hutilityTrue
  have hright := binaryCertificateAdd_polyTime.comp hrightTable
  have hleTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![binaryCertificateAdd ![generalScoreWord columnPlayer true v,
          generalCertificateFieldWord
            ![List.replicate ((if columnPlayer then 4 else 2) + 1) true, v 1, v 2]],
        binaryCertificateAdd ![generalScoreWord columnPlayer false v,
          generalCertificateFieldWord
            ![List.replicate (if columnPlayer then 4 else 2) true, v 1, v 2]]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hleft
    · exact hright
  have hle := binaryCertificateLE_polyTime.comp hleTable
  have hsupport := generalWeightWord_polyTime columnPlayer
  have heqEmptyTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![generalWeightWord columnPlayer v, []])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hsupport
    · exact .const []
  have heqEmpty := certificateEqualWord_polyTime.comp heqEmptyTable
  have heqScore := certificateEqualWord_polyTime.comp hleTable
  have horTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        (certificateEqualWord (generalWeightWord columnPlayer v) [],
          certificateEqualWord
            (binaryCertificateAdd ![generalScoreWord columnPlayer true v,
              generalCertificateFieldWord
                ![List.replicate ((if columnPlayer then 4 else 2) + 1) true, v 1, v 2]])
            (binaryCertificateAdd ![generalScoreWord columnPlayer false v,
              generalCertificateFieldWord
                ![List.replicate (if columnPlayer then 4 else 2) true, v 1, v 2]])))
      (encPi encBits) (encPair encBits encBits) :=
    ComputableInPolyTime.pair heqEmpty heqScore
  have hor := orFlag_polyTime.comp horTable
  have hfinalTable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        (binaryCertificateLE ![binaryCertificateAdd ![generalScoreWord columnPlayer true v,
              generalCertificateFieldWord
                ![List.replicate ((if columnPlayer then 4 else 2) + 1) true, v 1, v 2]],
            binaryCertificateAdd ![generalScoreWord columnPlayer false v,
              generalCertificateFieldWord
                ![List.replicate (if columnPlayer then 4 else 2) true, v 1, v 2]]],
          orFlag (certificateEqualWord (generalWeightWord columnPlayer v) [])
            (certificateEqualWord
              (binaryCertificateAdd ![generalScoreWord columnPlayer true v,
                generalCertificateFieldWord
                  ![List.replicate ((if columnPlayer then 4 else 2) + 1) true, v 1, v 2]])
              (binaryCertificateAdd ![generalScoreWord columnPlayer false v,
                generalCertificateFieldWord
                  ![List.replicate (if columnPlayer then 4 else 2) true, v 1, v 2]]))))
      (encPi encBits) (encPair encBits encBits) :=
    ComputableInPolyTime.pair hle hor
  have hcert := andFlag_polyTime.comp hfinalTable
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq
  intro v
  rfl

@[fun_prop] theorem generalAllChecks_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (generalAllChecks columnPlayer) (encPi encBits) encBits := by
  have hclock := reindexProducer (generalActionRuler_polyTime columnPlayer)
    (![0] : Fin 1 → Fin 2)
  have hparams : ComputableInPolyTime (fun v : Fin 2 → List Bool => v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact .pi_apply encBits i
  have hchecks := certificateAll_polyTime (p := 2) (Input := Fin 2 → List Bool)
    (input := encPi encBits) (term := generalActionCheck columnPlayer)
    (clock := fun v : Fin 2 → List Bool => generalActionRuler columnPlayer (v 0))
    (params := fun v : Fin 2 → List Bool => v)
    (generalActionCheck_polyTime columnPlayer) hclock hparams
  change ComputableInPolyTime
    (fun v : Fin 2 → List Bool =>
      certificateAll (generalActionCheck columnPlayer) (generalActionRuler columnPlayer (v 0)) v)
    (encPi encBits) encBits
  exact hchecks

@[fun_prop] theorem generalValidCertificateVerdict_polyTime :
    ComputableInPolyTime generalValidCertificateVerdict (encPi encBits) encBits := by
  have hfield (i : ℕ) : ComputableInPolyTime
      (fun v : Fin 2 → List Bool =>
        generalCertificateFieldWord ![List.replicate i true, v 0, v 1])
      (encPi encBits) encBits := by
    have htable : ComputableInPolyTime
        (fun v : Fin 2 → List Bool => ![List.replicate i true, v 0, v 1])
        (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro j
      fin_cases j
      · exact .const (List.replicate i true)
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
    exact generalCertificateFieldWord_polyTime.comp htable
  have hf0 := hfield 0
  have hf1 := hfield 1
  have hrow := reindexProducer generalRowRuler_polyTime (![0] : Fin 1 → Fin 2)
  have hcol := reindexProducer generalColRuler_polyTime (![0] : Fin 1 → Fin 2)
  have hwidth := generalWidthRuler_polyTime.comp (.pi_apply encBits (0 : Fin 2))
  have hrowLen := ComputableInPolyTime.length_bits_comp hrow
  have hcolLen := ComputableInPolyTime.length_bits_comp hcol
  have hwidthLen := ComputableInPolyTime.length_bits_comp hwidth
  have hheader := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add' hrowLen hcolLen) (.const 6)
  have htotal := ComputableInPolyTime.unary_mul' hheader hwidthLen
  have hcertLen := ComputableInPolyTime.length_bits_comp (.pi_apply encBits (1 : Fin 2))
  have heq' := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hcertLen.tidy.prod htotal.tidy))
  have heq : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => decide ((v 1).length =
        ((generalRowRuler (v 0)).length + (generalColRuler (v 0)).length + 6) *
          (generalWidthRuler (v 0)).length)) (encPi encBits) encBool := by
    simpa [Function.comp_def] using heq'
  have hlengthFlag := ComputableInPolyTime.bitsCons heq (.const [])
  have heqEmpty0Table : ComputableInPolyTime
      (fun v : Fin 2 → List Bool =>
        ![generalCertificateFieldWord ![List.replicate 0 true, v 0, v 1], []])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hf0
    · exact .const []
  have heqEmpty1Table : ComputableInPolyTime
      (fun v : Fin 2 → List Bool =>
        ![generalCertificateFieldWord ![List.replicate 1 true, v 0, v 1], []])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hf1
    · exact .const []
  have hnot0 := notFlag_polyTime.comp (certificateEqualWord_polyTime.comp heqEmpty0Table)
  have hnot1 := notFlag_polyTime.comp (certificateEqualWord_polyTime.comp heqEmpty1Table)
  have hsumFalse := generalWeightSumWord_polyTime false
  have hsumTrue := generalWeightSumWord_polyTime true
  have heqFalseTable : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![generalWeightSumWord false v,
        generalCertificateFieldWord ![List.replicate 0 true, v 0, v 1]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hsumFalse
    · exact hf0
  have heqTrueTable : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![generalWeightSumWord true v,
        generalCertificateFieldWord ![List.replicate 1 true, v 0, v 1]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    fin_cases j
    · exact hsumTrue
    · exact hf1
  have heqFalse := certificateEqualWord_polyTime.comp heqFalseTable
  have heqTrue := certificateEqualWord_polyTime.comp heqTrueTable
  have hallFalse := generalAllChecks_polyTime false
  have hallTrue := generalAllChecks_polyTime true
  have andC {f g : (Fin 2 → List Bool) → List Bool}
      (hf : ComputableInPolyTime f (encPi encBits) encBits)
      (hg : ComputableInPolyTime g (encPi encBits) encBits) :
      ComputableInPolyTime (fun v => andFlag (f v) (g v)) (encPi encBits) encBits :=
    andFlag_polyTime.comp (hf.prod hg)
  have h6 := andC hallFalse hallTrue
  have h5 := andC heqTrue h6
  have h4 := andC heqFalse h5
  have h3 := andC hnot1 h4
  have h2 := andC hnot0 h3
  have h1 := andC hlengthFlag h2
  apply ComputableInPolyTime.of_tidy
  apply h1.tidy.of_enc_eq
  intro v
  simp only [generalValidCertificateVerdict, List.length_append, List.length_replicate,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

@[fun_prop] theorem generalInstanceFlag_polyTime :
    ComputableInPolyTime generalInstanceFlag encBits encBits := by
  have hinput : ComputableInPolyTime (fun input : List Bool => ![input])
      encBits (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact verifierInput_polyTime
  have hrow := generalRowRuler_polyTime.comp hinput
  have hcol := generalColRuler_polyTime.comp hinput
  have hbits := generalBitsRuler_polyTime.comp hinput
  have hrowLen := ComputableInPolyTime.length_bits_comp hrow
  have hcolLen := ComputableInPolyTime.length_bits_comp hcol
  have hbitsLen := ComputableInPolyTime.length_bits_comp hbits
  have hrowCol := ComputableInPolyTime.unary_mul' hrowLen hcolLen
  have hprod := ComputableInPolyTime.unary_mul' hrowCol hbitsLen
  have hprod4 := ComputableInPolyTime.unary_mul' (.const 4) hprod
  have hbase := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add' hrowLen hcolLen) hbitsLen) (.const 3)
  have htotal := ComputableInPolyTime.unary_add' hbase hprod4
  have hinputLen := ComputableInPolyTime.length_bits_comp verifierInput_polyTime
  have heq' := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hinputLen.tidy.prod htotal.tidy))
  have heq : ComputableInPolyTime
      (fun input : List Bool => decide (input.length =
        (generalRowRuler input).length + (generalColRuler input).length +
          (generalBitsRuler input).length + 3 +
            4 * (generalRowRuler input).length * (generalColRuler input).length *
              (generalBitsRuler input).length)) encBits encBool := by
    apply ComputableInPolyTime.of_tidy
    apply heq'.tidy.of_enc_eq
    intro input
    simp only [Function.comp_apply, Matrix.cons_val_zero]
    congr 1
    ring_nf
  have hlengthFlag := ComputableInPolyTime.bitsCons heq (.const [])
  have hempty : ComputableInPolyTime (fun _ : List Bool => ([] : List Bool))
      encBits encBits := .const []
  have hrowTable : ComputableInPolyTime
      (fun x : List Bool => (generalRowRuler ((![x] : Fin 1 → List Bool) 0), ([] : List Bool)))
      encBits (encPair encBits encBits) := ComputableInPolyTime.pair hrow hempty
  have hcolTable : ComputableInPolyTime
      (fun x : List Bool => (generalColRuler ((![x] : Fin 1 → List Bool) 0), ([] : List Bool)))
      encBits (encPair encBits encBits) := ComputableInPolyTime.pair hcol hempty
  have hbitsTable : ComputableInPolyTime
      (fun x : List Bool => (generalBitsRuler ((![x] : Fin 1 → List Bool) 0), ([] : List Bool)))
      encBits (encPair encBits encBits) := ComputableInPolyTime.pair hbits hempty
  have hnotRow := notFlag_polyTime.comp (eqFlag_polyTime.comp hrowTable)
  have hnotCol := notFlag_polyTime.comp (eqFlag_polyTime.comp hcolTable)
  have hnotBits := notFlag_polyTime.comp (eqFlag_polyTime.comp hbitsTable)
  have hthird := andFlag_polyTime.comp (hnotBits.prod hlengthFlag)
  have hsecond := andFlag_polyTime.comp (hnotCol.prod hthird)
  have hfirst := andFlag_polyTime.comp (hnotRow.prod hsecond)
  apply ComputableInPolyTime.of_tidy
  apply hfirst.tidy.of_enc_eq
  intro input
  simp only [generalInstanceFlag, Function.comp_apply, generalInstanceLengthRuler_length,
    generalRowCount, generalColCount, generalCoefficientBits, Matrix.cons_val_zero]

@[fun_prop] theorem generalBimatrixVerdict_polyTime :
    ComputableInPolyTime generalBimatrixVerdict (encPi encBits) encBits := by
  have hin : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hcert := generalValidCertificateVerdict_polyTime
  have hinFlag := generalInstanceFlag_polyTime.comp hin
  have hleft := andFlag_polyTime.comp (hinFlag.prod hcert)
  have hnot := notFlag_polyTime.comp hinFlag
  have hempty : ComputableInPolyTime (fun _ : Fin 2 → List Bool => ([] : List Bool))
      (encPi encBits) encBits := .const []
  have heqTable : ComputableInPolyTime (fun v : Fin 2 → List Bool => (v 1, []))
      (encPi encBits) (encPair encBits encBits) :=
    ComputableInPolyTime.pair (.pi_apply encBits 1) hempty
  have heq := eqFlag_polyTime.comp heqTable
  have hright := andFlag_polyTime.comp (hnot.prod heq)
  have hfinal := orFlag_polyTime.comp (hleft.prod hright)
  apply ComputableInPolyTime.of_tidy
  apply hfinal.tidy.of_enc_eq
  intro v
  simp only [generalBimatrixVerdict, Function.comp_apply]
