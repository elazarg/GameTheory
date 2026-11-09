module

public import GameTheoryComplexity.Backend.BrouwerNashProgramCorrectness
public import GameTheoryComplexity.Backend.BrouwerNashAnswerMachine
public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BimatrixProgramEmission
public import GameTheoryComplexity.Backend.GeneralBimatrixTotality

@[expose] public section

/-! Scalar coefficient and singleton-kind selectors compose with certified table writers
to reduce continuous Brouwer search to the canonical rectangular Nash relation. Every accepted
game answer is decoded through the actual sampled program and binary-cell answer machine. -/

namespace GameTheory.Complexity.Backend.BrouwerNashReduction
open Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits
open Cslib.BitString
open GameTheory.Finite GameTheory.Finite.BimatrixGateProgram
open BrouwerNashLayout BrouwerNashProgram

section
variable (source tape : List Bool) (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
local notation "b" => List.length (CircuitWords.first source)
local notation "k" => dimension b raw₀.length raw₁.length
local notation "g" => program b raw₀ raw₁

/-- Exact written fields preserve every accepted answer through the canonical program. -/
theorem answer_sound_of_fields
    (hsize : (BimatrixProgramCodec.dimension tape).length = k)
    (precision size : List Bool) (hdepth : precision.length = b)
    (hruler : size.length = k)
    (hbaseline : BimatrixProgramCodec.baseline tape =
      binarySignedValue (BrouwerNashRewardMachine.reward precision size))
    (hcoeff : ∀ i r (hi : i < k) (hr : r < k * 2),
      binarySignedRowValue (BimatrixProgramCodec.width tape)
        (BimatrixProgramCodec.coefficientTape tape) (i * (k * 2) + r) =
          (g ⟨i, hi⟩).coefficients ⟨r, hr⟩)
    (hkind : ∀ i (hi : i < k),
      (if (BimatrixProgramCodec.kindFlags tape)[i]?.getD false then GateKind.comparator
        else GateKind.affine) = (g ⟨i, hi⟩).kind)
    (hraw : ∀ flag : Fin 2, Program.IsCodeFrom CircuitFormat.signature (arity b) 0
      (if flag.val = 0 then raw₀ else raw₁))
    (hne : ∀ flag : Fin 2, (if flag.val = 0 then raw₀ else raw₁) ≠ [])
    (hquery : ∀ flag : Fin 2, ∀ x y : ℕ, x ≤ 2 ^ b → y ≤ 2 ^ b →
      CircuitFormat.evalOutput (lowBits (b + 1) x ++ lowBits (b + 1) y)
        (if flag.val = 0 then raw₀ else raw₁)
        (arity b + (if flag.val = 0 then raw₀ else raw₁).length - 1) =
          (encodeGridColor (spernerColor source x y)).getD flag.val false)
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
  simp only [List.getD_eq_getElem?_getD] at hv
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
    source rfl precision size hdepth hruler c hv hraw hne hquery
  have hd : 0 < ofBits (BrouwerNashAnswerMachine.denominatorWord tape answer) := by
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

private def kindWord (query : List Bool → List Bool → List Bool)
    (ruler source : List Bool) : List Bool :=
  (List.range ruler.length).flatMap fun i =>
    binarySignedFixed [false] (query source (ruler.drop (ruler.length - i)))

private theorem kindWord_polyTime
    {query : List Bool → List Bool → List Bool}
    (hq : ComputableInPolyTime (fun p : List Bool × List Bool => query p.1 p.2)
      (encPair encBits encBits) encBits)
    {ruler : List Bool → List Bool} (hr : ComputableInPolyTime ruler encBits encBits) :
    ComputableInPolyTime (fun source => kindWord query (ruler source) source)
      encBits encBits := by
  have hi := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.range).comp
    (ComputableInPolyTime.length_bits_comp hr)
  change ComputableInPolyTime (fun source =>
    (List.range (ruler source).length).flatMap fun i =>
      binarySignedFixed [false] (query source ((ruler source).drop ((ruler source).length - i))))
    encBits encBits
  refine ComputableInPolyTime.flatMapToBitsWithInput
    (f := fun (source : List Bool) (i : ℕ) =>
      binarySignedFixed [false]
        (query source ((ruler source).drop ((ruler source).length - i)))) hi ?_
  have hs : ComputableInPolyTime (fun p : List Bool × ℕ => p.1)
      (encPair encBits encUnary) encBits := .fst encBits encUnary
  have hj : ComputableInPolyTime (fun p : List Bool × ℕ => p.2)
      (encPair encBits encUnary) encUnary := .snd encBits encUnary
  have hr' := hr.comp hs
  have ho := ComputableInPolyTime.bitsDropWithInput hr'
    (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.length_bits_comp hr') hj)
  exact binarySignedFixed_polyTime (.const [false]) (hq.comp (hs.prod ho))

private theorem kindWord_at (query : List Bool → List Bool → List Bool)
    (ruler source : List Bool) (i : ℕ) (hi : i < ruler.length) (bit : Bool)
    (he : query source (ruler.drop (ruler.length - i)) = [bit]) :
    (kindWord query ruler source)[i]?.getD false = bit := by
  have hf := GameTheory.Math.FixedBlockList.block_flatMap_fixed
    (List.range ruler.length)
    (fun j => binarySignedFixed [false] (query source (ruler.drop (ruler.length - j))))
    1 (fun _ _ => binarySignedFixed_length _ _) i
    (by simpa only [List.length_range] using hi)
  simp only [List.getElem_range, Nat.mul_one] at hf
  change ((kindWord query ruler source).drop i).take 1 = _ at hf
  rw [he, binarySignedFixed_eq_of_length [false] [bit] rfl] at hf
  have h := congrArg (fun word : List Bool => word[0]?.getD false) hf
  simpa using h

section Assembly
variable (codes : Fin 2 → List Bool → List Bool)
variable (query : List Bool → List Bool → List Bool → List Bool)
variable (kindQuery : List Bool → List Bool → List Bool)
local notation "d" => BrouwerNashHeaders.sourceFn BrouwerNashHeaders.dimensionRuler codes
local notation "w" => BrouwerNashHeaders.sourceFn BrouwerNashHeaders.widthRuler codes
local notation "h" => BrouwerNashHeaders.sourceFn BrouwerNashHeaders.baselineWord codes

/-- Certified scalar and kind selectors supply an actual every-answer search reduction. -/
theorem exists_reduction_of_selectors
    (hcodes : ∀ flag, ComputableInPolyTime (codes flag) encBits encBits)
    (hcompiled : ∀ flag source,
      ∃ gates : List (CircuitFormat.signature.Op × List ℕ),
        ∃ output : Fin (2 * ((CircuitWords.first source).length + 1) + gates.length),
          CircuitFormat.decode? (codes flag source) = some gates ∧
          Program.IsCodeFrom CircuitFormat.signature
            (2 * ((CircuitWords.first source).length + 1)) 0 gates ∧ gates ≠ [] ∧
          output.val = 2 * ((CircuitWords.first source).length + 1) + gates.length - 1 ∧
          ∀ x y, x ≤ 2 ^ (CircuitWords.first source).length →
            y ≤ 2 ^ (CircuitWords.first source).length →
            CircuitFormat.evalOutput
              (lowBits ((CircuitWords.first source).length + 1) x ++
                lowBits ((CircuitWords.first source).length + 1) y) gates output.val =
              (encodeGridColor (spernerColor source x y)).getD flag.val false)
    (hq : ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => query p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBits)
    (hkq : ComputableInPolyTime (fun p : List Bool × List Bool => kindQuery p.1 p.2)
      (encPair encBits encBits) encBits)
    (hcoeff : ∀ source raw₀ raw₁,
      CircuitFormat.decode? (codes 0 source) = some raw₀ →
      CircuitFormat.decode? (codes 1 source) = some raw₁ →
      ∀ (i : Fin (dimension (CircuitWords.first source).length raw₀.length raw₁.length))
        (r : Fin (dimension (CircuitWords.first source).length raw₀.length raw₁.length * 2)),
      binarySignedValue (query source ((d source).drop ((d source).length - i.val))
        ((d source ++ d source).drop ((d source).length * 2 - r.val))) =
          (program (CircuitWords.first source).length raw₀ raw₁ i).coefficients r)
    (hkind : ∀ source raw₀ raw₁,
      CircuitFormat.decode? (codes 0 source) = some raw₀ →
      CircuitFormat.decode? (codes 1 source) = some raw₁ →
      ∀ i : Fin (dimension (CircuitWords.first source).length raw₀.length raw₁.length),
        kindQuery source ((d source).drop ((d source).length - i.val)) =
          [decide ((program (CircuitWords.first source).length raw₀ raw₁ i).kind = .comparator)]) :
    SearchReducible encBits encBits brouwerRelation generalBimatrixRelation := by
  let kinds := fun source => kindWord kindQuery (d source) source
  let tape := BimatrixProgramEmission.programWord d w h kinds query
  have hdPT : ComputableInPolyTime d encBits encBits :=
    BrouwerNashHeaders.dimensionRuler_polyTime (.id') (hcodes 0) (hcodes 1)
  have hwPT : ComputableInPolyTime w encBits encBits :=
    BrouwerNashHeaders.widthRuler_polyTime (.id') (hcodes 0) (hcodes 1)
  have hhPT : ComputableInPolyTime h encBits encBits :=
    BrouwerNashHeaders.baselineWord_polyTime (.id') (hcodes 0) (hcodes 1)
  have htape : ComputableInPolyTime tape encBits encBits :=
    BimatrixProgramEmission.programWord_polyTime hdPT hwPT hhPT
      (kindWord_polyTime hkq hdPT) hq
  let instanceMap := fun source => BimatrixProgramMachine.instanceWord (tape source)
  have hiPT : ComputableInPolyTime instanceMap encBits encBits :=
    BimatrixProgramMachine.instanceWord_polyTime htape
  apply SearchReducible.of_isTotalSearch
    (f := instanceMap)
    (g := fun p : List Bool × List Bool =>
      BrouwerNashAnswerMachine.answerWord ![p.1, tape p.1, p.2])
    generalBimatrixRelation_total hiPT
  · have hargs : ComputableInPolyTime
        (fun p : List Bool × List Bool => ![p.1, tape p.1, p.2])
        (encPair encBits encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .fst encBits encBits
      · exact htape.comp (.fst encBits encBits)
      · exact .snd encBits encBits
    have hcert := BrouwerNashAnswerMachine.answerWord_polyTime.comp hargs
    exact hcert
  · intro source answer ha
    obtain ⟨raw₀, output₀, hd₀, hw₀, hn₀, hl₀, he₀⟩ := hcompiled 0 source
    obtain ⟨raw₁, output₁, hd₁, hw₁, hn₁, hl₁, he₁⟩ := hcompiled 1 source
    let b := (CircuitWords.first source).length
    let K := dimension b raw₀.length raw₁.length
    let G := program b raw₀ raw₁
    have hd := BrouwerNashHeaders.sourceDimension_length_of_decode
      codes source raw₀ raw₁ hd₀ hd₁
    have hf := BimatrixProgramEmission.programWord_fields d w h kinds query source
    have hsize : (BimatrixProgramCodec.dimension (tape source)).length = K :=
      (congrArg List.length hf.1).trans hd
    change generalBimatrixRelation (BimatrixProgramMachine.instanceWord (tape source)) answer at ha
    change brouwerRelation source
      (BrouwerNashAnswerMachine.answerWord ![source, tape source, answer])
    let precision := CircuitWords.first source
    have hdepth : precision.length = b := rfl
    have hruler : (d source).length = K := hd
    refine answer_sound_of_fields source (tape source) raw₀ raw₁ hsize
      precision (d source) hdepth hruler ?_ ?_ ?_ ?_ ?_ ?_ answer ha
    · rw [BimatrixProgramCodec.baseline, hf.2.2.1]
      rfl
    · intro i r hi hr
      rw [hf.2.1, hf.2.2.2.2]
      have hiD : i < (d source).length := by simpa only [hd] using hi
      have hrD : r < (d source).length * 2 := by simpa only [hd] using hr
      have hp := BimatrixProgramEmission.coefficients_field query source (d source) (w source)
        i r hiD hrD
      change ((BimatrixProgramEmission.coefficients query source (d source) (w source)).drop
        ((i * ((d source).length * 2) + r) * (w source).length)).take (w source).length = _ at hp
      rw [hd] at hp
      unfold binarySignedRowValue
      rw [hp]
      have he := hcoeff source raw₀ raw₁ hd₀ hd₁ ⟨i, hi⟩ ⟨r, hr⟩
      rw [hd] at he
      apply (binarySignedFixed_value (w source) _ ?_ ?_).trans he
      · change 0 < (BrouwerNashHeaders.widthRuler source (codes 0 source) (codes 1 source)).length
        rw [BrouwerNashHeaders.widthRuler_length]
        omega
      · rw [he]
        apply BrouwerNashHeaders.widthRuler_fits source (codes 0 source) (codes 1 source)
        change ((G ⟨i, hi⟩).coefficients ⟨r, hr⟩).natAbs ≤ 100 * (d source).length
        rw [hd]
        have hb := coefficients_bound b raw₀ raw₁ ⟨i, hi⟩ ⟨r, hr⟩
        rw [← Int.natCast_natAbs] at hb
        exact_mod_cast hb
    · intro i hi
      rw [hf.2.2.2.1]
      have hiD : i < (d source).length := by simpa only [hd] using hi
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
      · exact hn₀
      · exact hn₁
    · intro flag
      fin_cases flag
      · simpa only [hl₀, arity, Fin.val_zero, ite_true] using he₀
      · simpa only [hl₁, arity, Fin.val_one, Nat.one_ne_zero, ite_false] using he₁

end Assembly
end GameTheory.Complexity.Backend.BrouwerNashReduction
