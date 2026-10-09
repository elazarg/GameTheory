import GameTheoryComplexity.Backend.BrouwerNashProgramCorrectness
import GameTheoryComplexity.Backend.BrouwerNashAnswerMachine
import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BimatrixProgramEmission

/-! Scalar coefficient and singleton-kind selectors compose with certified table writers
to reduce continuous Brouwer search to the canonical rectangular Nash relation. Every accepted
game answer is decoded through the actual sampled program and binary-cell answer machine. -/

namespace GameTheory.Complexity.Backend.BrouwerNashReduction
open _root_.Complexity _root_.Complexity.CircuitCode _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixGateProgram
open BrouwerNashLayout BrouwerNashProgram

section
variable (source tape : List Bool) (raw₀ raw₁ : RawCircuit)
local notation "b" => List.length (pairFst source)
local notation "k" => dimension b raw₀.length raw₁.length
local notation "g" => program b raw₀ raw₁

/-- Exact written fields preserve every accepted answer through the canonical program. -/
theorem answer_sound_of_fields
    (hsize : (BimatrixProgramCodec.dimension tape).length = k)
    (rulers : Fin 2 → List Bool) (hdepth : (rulers 0).length = b)
    (hruler : (rulers 1).length = k)
    (hbaseline : BimatrixProgramCodec.baseline tape =
      binarySignedValue (BrouwerNashRewardMachine.reward rulers))
    (hcoeff : ∀ i r (hi : i < k) (hr : r < k * 2),
      binarySignedRowValue (BimatrixProgramCodec.width tape)
        (BimatrixProgramCodec.coefficientTape tape) (i * (k * 2) + r) =
          (g ⟨i, hi⟩).coefficients ⟨r, hr⟩)
    (hkind : ∀ i (hi : i < k),
      (if (BimatrixProgramCodec.kindFlags tape)[i]?.getD false then GateKind.comparator
        else GateKind.affine) = (g ⟨i, hi⟩).kind)
    (hraw : ∀ flag : Fin 2, (if flag.val = 0 then raw₀ else raw₁).WellFormed (arity b))
    (hquery : ∀ flag : Fin 2, ∀ x y : ℕ, x ≤ 2 ^ b → y ≤ 2 ^ b →
      (if flag.val = 0 then raw₀ else raw₁).eval?
        (Nat.toBitsLE (b + 1) x ++ Nat.toBitsLE (b + 1) y) =
          some (bitOf (encodeGridColor (spernerColor source x y)) flag))
    (answer : List Bool)
    (ha : generalBimatrixRelation (BimatrixProgramMachine.instanceWord tape) answer) :
    brouwerRelation source (BrouwerNashAnswerMachine.answerWord ![source, tape, answer]) := by
  have hk : 2 ≤ (BimatrixProgramCodec.dimension tape).length := by
    rw [hsize]
    dsimp [dimension, units]
    omega
  have hv := BimatrixProgramCorrectness.accepted_valid tape answer (by omega) ha
  unfold BimatrixProgramCodec.decode at hv
  rw [hsize, hbaseline] at hv
  have hg : (fun i : Fin k => ({
      coefficients := fun r => binarySignedRowValue (BimatrixProgramCodec.width tape)
        (BimatrixProgramCodec.coefficientTape tape) (i.val * (k * 2) + r.val)
      kind := if (BimatrixProgramCodec.kindFlags tape)[i.val]?.getD false
        then .comparator else .affine } : Gate k)) = g := by
    funext i
    cases hgi : g i
    apply congrArg₂ GameTheory.Finite.BimatrixGateProgram.Gate.mk
    · funext r
      have he := hcoeff i.val r.val i.isLt r.isLt
      simpa only [hgi] using he
    · have he := hkind i.val i.isLt
      simpa only [hgi] using he
  rw [hg] at hv
  let c := decodeGeneralCertificate (k * 2) (k * 2)
    (generalCertificateWidth (BimatrixProgramMachine.instanceWord tape).length) answer
  have hres := BrouwerNashProgramCorrectness.reward_source_residual b raw₀ raw₁
    source rfl rulers hdepth hruler c hv hraw hquery
  have hd : 0 < Nat.fromBitsLE (BrouwerNashAnswerMachine.denominatorWord tape answer) := by
    rw [BrouwerNashAnswerMachine.denominatorWord_value]
    exact hv.1
  have hcoordinate (axis : Fin 2) :
      BrouwerNashAnswerMachine.coordinate (axis.val = 1) tape answer =
        BrouwerNashProgramCorrectness.coordinateValue b raw₀ raw₁ c axis := by
    rw [BrouwerNashAnswerMachine.coordinate_eq_clamp _ _ _ hk hd]
    simp only [hsize]
    fin_cases axis <;> rfl
  have hx := hcoordinate 0
  have hy := hcoordinate 1
  change BrouwerNashAnswerMachine.coordinate false tape answer = _ at hx
  change BrouwerNashAnswerMachine.coordinate true tape answer = _ at hy
  apply BrouwerNashAnswerMachine.answerWord_sound source tape answer hk ha
  · rw [hx, hy]
    exact hres.1
  · rw [hx, hy]
    exact hres.2

end

private theorem decoded_prefix_length (code : List Bool) (raw : RawCircuit)
    (hd : RawCircuit.decode? code = some raw) : (circuitUnaryPrefix code).length = raw.length := by
  have he := (RawCircuit.decode?_eq_some_iff code raw).mp hd
  rw [he, RawCircuit.encode, circuitUnaryPrefix_encode, List.length_replicate]

private def kindWord (query : (Fin 2 → List Bool) → List Bool)
    (ruler source : List Bool) : List Bool := binarySignedTable query ruler [false] ![source]

private theorem kindWord_mem_FP {query : (Fin 2 → List Bool) → List Bool}
    (hq : FPn query) {ruler : List Bool → List Bool} (hr : ruler ∈ FP) :
    (fun source => kindWord query (ruler source) source) ∈ FP := by
  apply CobhamFP_subset_FP
  exact (Cobham.comp₃ (binarySignedTable_cobham (cobham_iff_FPn.mpr hq))
    (FP_subset_CobhamFP hr) (Cobham.const [false]) (.proj 0)).of_eq fun _ => rfl

private theorem kindWord_at (query : (Fin 2 → List Bool) → List Bool)
    (ruler source : List Bool) (i : ℕ) (hi : i < ruler.length) (bit : Bool)
    (he : query ![ruler.drop (ruler.length - i), source] = [bit]) :
    (kindWord query ruler source)[i]?.getD false = bit := by
  have hf := binarySignedTable_field query ruler [false] ![source] i hi
  change ((kindWord query ruler source).drop (i * 1)).take 1 =
    binarySignedFixed [false] (query ![ruler.drop (ruler.length - i), source]) at hf
  rw [he, binarySignedFixed_eq_of_length [false] [bit] rfl] at hf
  have h := congrArg (fun word : List Bool => word[0]?.getD false) hf
  simpa using h
section Assembly
variable (codes : Fin 2 → List Bool → List Bool)
variable (query : (Fin 3 → List Bool) → List Bool)
variable (kindQuery : (Fin 2 → List Bool) → List Bool)
local notation "d" => BrouwerNashHeaders.sourceFn BrouwerNashHeaders.dimensionRuler codes
local notation "w" => BrouwerNashHeaders.sourceFn BrouwerNashHeaders.widthRuler codes
local notation "h" => BrouwerNashHeaders.sourceFn BrouwerNashHeaders.baselineWord codes

/-- Certified scalar and kind selectors supply an actual every-answer search reduction. -/
theorem exists_reduction_of_selectors
    (hcodes : ∀ flag, codes flag ∈ FP)
    (hcompiled : ∀ flag source, ∃ raw : RawCircuit,
      RawCircuit.decode? (codes flag source) = some raw ∧
      raw.WellFormed (arity (pairFst source).length) ∧
      ∀ x y, x ≤ 2 ^ (pairFst source).length → y ≤ 2 ^ (pairFst source).length →
        raw.eval? (Nat.toBitsLE ((pairFst source).length + 1) x ++
          Nat.toBitsLE ((pairFst source).length + 1) y) =
            some (bitOf (encodeGridColor (spernerColor source x y)) flag))
    (hq : FPn query) (hkq : FPn kindQuery)
    (hcoeff : ∀ source raw₀ raw₁,
      RawCircuit.decode? (codes 0 source) = some raw₀ →
      RawCircuit.decode? (codes 1 source) = some raw₁ →
      ∀ (i : Fin (dimension (pairFst source).length raw₀.length raw₁.length))
        (r : Fin (dimension (pairFst source).length raw₀.length raw₁.length * 2)),
      binarySignedValue (query ![(d source).drop ((d source).length - i.val),
        (d source ++ d source).drop ((d source).length * 2 - r.val), source]) =
          (program (pairFst source).length raw₀ raw₁ i).coefficients r)
    (hkind : ∀ source raw₀ raw₁,
      RawCircuit.decode? (codes 0 source) = some raw₀ →
      RawCircuit.decode? (codes 1 source) = some raw₁ →
      ∀ i : Fin (dimension (pairFst source).length raw₀.length raw₁.length),
        kindQuery ![(d source).drop ((d source).length - i.val), source] =
          [decide ((program (pairFst source).length raw₀ raw₁ i).kind = .comparator)]) :
    Nonempty (SearchReduction brouwerRelation generalBimatrixRelation) := by
  let kinds := fun source => kindWord kindQuery (d source) source
  let tape := BimatrixProgramEmission.programWord d w h kinds query
  have hdFP := BrouwerNashHeaders.sourceFn_mem_FP
    BrouwerNashHeaders.dimensionRuler_cobham codes hcodes
  have hwFP := BrouwerNashHeaders.sourceFn_mem_FP
    BrouwerNashHeaders.widthRuler_cobham codes hcodes
  have hhFP := BrouwerNashHeaders.sourceFn_mem_FP
    BrouwerNashHeaders.baselineWord_cobham codes hcodes
  have htape : tape ∈ FP := BimatrixProgramEmission.programWord_mem_FP
    hdFP hwFP hhFP (kindWord_mem_FP hkq hdFP) hq
  let instanceMap := BimatrixProgramMachine.instanceWord ∘ tape
  have hiFP : instanceMap ∈ FP := mem_FP_comp (f := tape)
    (g := BimatrixProgramMachine.instanceWord) htape BimatrixProgramMachine.instanceWord_mem_FP
  refine ⟨{
    instanceMap := instanceMap
    instanceMap_mem_FP := hiFP
    decode := fun v => BrouwerNashAnswerMachine.answerWord ![v 0, tape (v 0), v 1]
    decode_mem_FPn := ?_
    sound := ?_ }⟩
  · apply cobham_iff_FPn.mp
    exact (Cobham.comp₃ BrouwerNashAnswerMachine.answerWord_cobham (.proj 0)
      (Cobham.comp (FP_subset_CobhamFP htape) fun _ : Fin 1 =>
        (Cobham.proj 0 : Cobham fun v : Fin 2 → List Bool => v 0)) (.proj 1)).of_eq
      fun _ => rfl
  · intro source answer ha
    obtain ⟨raw₀, hd₀, hw₀, he₀⟩ := hcompiled 0 source
    obtain ⟨raw₁, hd₁, hw₁, he₁⟩ := hcompiled 1 source
    let b := (pairFst source).length
    let K := dimension b raw₀.length raw₁.length
    let G := program b raw₀ raw₁
    have hd : (d source).length = K := by
      have hd := BrouwerNashHeaders.dimensionRuler_length ![source, codes 0 source, codes 1 source]
      change (d source).length = dimension b
        (circuitUnaryPrefix (codes 0 source)).length
        (circuitUnaryPrefix (codes 1 source)).length at hd
      rwa [decoded_prefix_length _ _ hd₀, decoded_prefix_length _ _ hd₁] at hd
    have hf := BimatrixProgramEmission.programWord_fields d w h kinds query source
    have hsize : (BimatrixProgramCodec.dimension (tape source)).length = K :=
      (congrArg List.length hf.1).trans hd
    change generalBimatrixRelation (BimatrixProgramMachine.instanceWord (tape source)) answer at ha
    change brouwerRelation source
      (BrouwerNashAnswerMachine.answerWord ![source, tape source, answer])
    let rulers : Fin 2 → List Bool := ![pairFst source, d source]
    have hdepth : (rulers 0).length = b := rfl
    have hruler : (rulers 1).length = K := by
      dsimp only [rulers, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact hd
    refine answer_sound_of_fields source (tape source) raw₀ raw₁ hsize
      rulers hdepth hruler ?_ ?_ ?_ ?_ ?_ answer ha
    · rw [BimatrixProgramCodec.baseline, hf.2.2.1]
      rfl
    · intro i r hi hr
      rw [hf.2.1, hf.2.2.2.2]
      have hiD : i < (d source).length := hd.symm ▸ hi
      have hrD : r < (d source).length * 2 := hd.symm ▸ hr
      have hp := BimatrixProgramEmission.coefficients_field query ![d source, w source, source]
        i r (by simpa only [Matrix.cons_val_zero] using hiD)
          (by simpa only [Matrix.cons_val_zero] using hrD)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hp
      change ((BimatrixProgramEmission.coefficients query ![d source, w source, source]).drop
        ((i * ((d source).length * 2) + r) * (w source).length)).take (w source).length = _ at hp
      rw [hd] at hp
      unfold binarySignedRowValue
      rw [hp]
      have he := hcoeff source raw₀ raw₁ hd₀ hd₁ ⟨i, hi⟩ ⟨r, hr⟩
      rw [hd] at he
      apply (binarySignedFixed_value (w source) _ ?_ ?_).trans he
      · change 0 < (BrouwerNashHeaders.widthRuler
          ![source, codes 0 source, codes 1 source]).length
        rw [BrouwerNashHeaders.widthRuler_length]
        omega
      · rw [he]
        apply BrouwerNashHeaders.widthRuler_fits ![source, codes 0 source, codes 1 source]
        change ((G ⟨i, hi⟩).coefficients ⟨r, hr⟩).natAbs ≤ 100 * (d source).length
        rw [hd]
        have hb := coefficients_bound b raw₀ raw₁ ⟨i, hi⟩ ⟨r, hr⟩
        rw [← Int.natCast_natAbs] at hb
        exact_mod_cast hb
    · intro i hi
      rw [hf.2.2.2.1]
      have hiD : i < (d source).length := hd.symm ▸ hi
      have he := hkind source raw₀ raw₁ hd₀ hd₁ ⟨i, hi⟩
      have hat := kindWord_at kindQuery (d source) source i hiD _ he
      change (if (kindWord kindQuery (d source) source)[i]?.getD false then _ else _) = _
      rw [hat]
      cases hc : (G ⟨i, hi⟩).kind <;> simp
    · intro flag
      fin_cases flag
      · exact hw₀
      · exact hw₁
    · intro flag
      fin_cases flag
      · exact he₀
      · exact he₁

end Assembly
end GameTheory.Complexity.Backend.BrouwerNashReduction
