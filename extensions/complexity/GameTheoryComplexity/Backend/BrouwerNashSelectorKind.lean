import GameTheoryComplexity.Backend.BrouwerNashKindCorrectness
import GameTheoryComplexity.Backend.BrouwerNashGlobalCorrectness
import GameTheoryComplexity.Backend.BrouwerNashColorQuery
import GameTheoryComplexity.Backend.BrouwerNashQueryRegions

/-! The canonical combined comparator flag for the allocated Brouwer feedback program. -/
namespace GameTheory.Complexity.Backend.BrouwerNashSelectorKind
open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode
open BrouwerNashLayout BrouwerNashProgram

/-- Combine the disjoint non-color and color comparator flags. -/
def kindWord (v : Fin 5 → List Bool) : List Bool :=
  orBit (BrouwerNashSampleKind.kindWord v) (BrouwerNashColorQuery.kindWord v)

/-- The complete flag selector has an actual Cobham certificate. -/
theorem kindWord_cobham : Cobham kindWord :=
  Cobham.orFn BrouwerNashSampleKind.kindWord_cobham
    BrouwerNashColorQuery.kindWord_cobham

theorem kindWord_mem_FPn : FPn kindWord := cobham_iff_FPn.mp kindWord_cobham

private theorem or_false_right (a : Bool) : orBit [a] [false] = [a] := by cases a <;> rfl
private theorem or_false_left (a : Bool) : orBit [false] [a] = [a] := by cases a <;> rfl

section Correctness
variable (out action source code₀ code₁ : List Bool)
local notation "b" => List.length (pairFst source)
local notation "e₀" => List.length (circuitUnaryPrefix code₀)
local notation "e₁" => List.length (circuitUnaryPrefix code₁)

private theorem minimumBase_le_width : minimumBase b e₀ e₁ ≤ sampleWidth b e₀ e₁ := by
  dsimp only [minimumBase, colorBase, weightBase, sampleWidth]
  omega

private theorem color_zero_outside_allocated
    (ho : out.length < globalCount b ∨ globalCount b + 41 * sampleWidth b e₀ e₁ ≤ out.length) :
    BrouwerNashColorQuery.kindWord ![out, action, source, code₀, code₁] = [false] := by
  apply BrouwerNashColorQuery.kindWord_zero_of_outside
  intro t
  change ¬(sampleBase b e₀ e₁ t + colorBase b ≤ out.length ∧
    out.length < sampleBase b e₀ e₁ t + minimumBase b e₀ e₁)
  intro hin
  have hm := Nat.mul_le_mul_right (sampleWidth b e₀ e₁)
    (show t.val + 1 ≤ 41 from Nat.succ_le_of_lt t.isLt)
  rw [Nat.add_mul, one_mul] at hm
  have hw := minimumBase_le_width source code₀ code₁
  dsimp only [sampleBase] at hin
  rcases ho with hbefore | hafter <;> omega

private theorem color_zero_at_noncolor (t : Fin 41) (i : ℕ)
    (hi : i < sampleWidth b e₀ e₁) (ho : out.length = sampleBase b e₀ e₁ t + i)
    (hno : i < colorBase b ∨ minimumBase b e₀ e₁ ≤ i) :
    BrouwerNashColorQuery.kindWord ![out, action, source, code₀, code₁] = [false] := by
  apply BrouwerNashColorQuery.kindWord_zero_of_outside
  intro t'
  change ¬(sampleBase b e₀ e₁ t' + colorBase b ≤ out.length ∧
    out.length < sampleBase b e₀ e₁ t' + minimumBase b e₀ e₁)
  intro hin
  have hw := minimumBase_le_width source code₀ code₁
  have hin' : sampleBase b e₀ e₁ t' ≤ out.length ∧
      out.length < sampleBase b e₀ e₁ t' + sampleWidth b e₀ e₁ := by omega
  have ht := BrouwerNashQueryRegions.sampleOutput_interval_unique b e₀ e₁ out.length i
    t t' hi ho hin'
  subst t'
  rcases hno with hbefore | hafter <;> omega

private theorem color_at_sample (raw₀ raw₁ : RawCircuit)
    (h₀ : e₀ = raw₀.length) (h₁ : e₁ = raw₁.length)
    (hw₀ : raw₀.WellFormed (arity b)) (hw₁ : raw₁.WellFormed (arity b))
    (t : Fin 41) (i : ℕ)
    (ho : out.length = sampleBase b raw₀.length raw₁.length t + i)
    (hlo : colorBase b ≤ i) (hhi : i < minimumBase b raw₀.length raw₁.length) :
    BrouwerNashColorQuery.kindWord ![out, action, source, code₀, code₁] =
      [decide ((sampleGate b raw₀ raw₁ t i).kind =
        GameTheory.Finite.BimatrixGateProgram.GateKind.comparator)] := by
  let w := cornerWidth b raw₀.length raw₁.length
  have hw : 0 < w := by dsimp [w, cornerWidth, arity]; omega
  let localIndex := i - colorBase b
  have hlocal : localIndex < 4 * w := by
    dsimp only [localIndex, w, minimumBase] at *
    omega
  let corner : Fin 4 := ⟨localIndex / w,
    Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hlocal)⟩
  let offset := localIndex % w
  have hoff : offset < w := Nat.mod_lt _ hw
  have he : i = colorBase b + corner.val * w + offset := by
    have hsplit := Nat.mod_add_div localIndex w
    change i = colorBase b + (localIndex / w) * w + localIndex % w
    rw [Nat.mul_comm w] at hsplit
    have hsum : colorBase b + localIndex = i := Nat.add_sub_of_le hlo
    omega
  rw [he, sampleGate_colorRegion b raw₀ raw₁ t corner offset hoff]
  apply BrouwerNashColorQuery.kindWord_eq_colorRegion_of_lengths
    ![out, action, source, code₀, code₁] raw₀ raw₁ h₀ h₁ hw₀ hw₁ t corner offset hoff
  change out.length = sampleBase b raw₀.length raw₁.length t + colorBase b +
    corner.val * w + offset
  omega

/-- At every program output, the combined flag equals the canonical gate's comparator kind. -/
theorem kindWord_value (raw₀ raw₁ : RawCircuit)
    (h₀ : e₀ = raw₀.length) (h₁ : e₁ = raw₁.length)
    (hw₀ : raw₀.WellFormed (arity b)) (hw₁ : raw₁.WellFormed (arity b))
    (i : Fin (dimension b raw₀.length raw₁.length)) (ho : out.length = i.val) :
    kindWord ![out, action, source, code₀, code₁] =
      [decide ((program b raw₀ raw₁ i).kind =
        GameTheory.Finite.BimatrixGateProgram.GateKind.comparator)] := by
  by_cases hg : i.val < globalCount b
  · have houtside : out.length < globalCount b ∨
        globalCount b + 41 * sampleWidth b e₀ e₁ ≤ out.length := Or.inl (by omega)
    rw [kindWord, BrouwerNashKindCorrectness.sampleKind_zero _ _ _ _ _ houtside,
      color_zero_outside_allocated _ _ _ _ _ houtside]
    rw [program, ite_eq_left hg, BrouwerNashGlobalQuery.globalGate_kind]
    rfl
  let w := sampleWidth b raw₀.length raw₁.length
  have hw : 0 < w := by dsimp [w, sampleWidth]; omega
  let offset := i.val - globalCount b
  by_cases hs : offset / w < 41
  · let t : Fin 41 := ⟨offset / w, hs⟩
    let localIndex := offset % w
    have hi : localIndex < w := Nat.mod_lt _ hw
    have hp : i.val = sampleBase b raw₀.length raw₁.length t + localIndex := by
      have hsplit := Nat.mod_add_div offset w
      change i.val = globalCount b + (offset / w) * w + offset % w
      rw [Nat.mul_comm w] at hsplit
      have hsum : globalCount b + offset = i.val := Nat.add_sub_of_le (by omega)
      omega
    have href : sampleRef b raw₀.length raw₁.length t localIndex = i := by
      apply Fin.ext
      rw [sampleRef, slot_val _ _ _ _ (sample_lt_dimension _ _ _ t localIndex hi)]
      exact hp.symm
    rw [← href, program_sample b raw₀ raw₁ t localIndex hi]
    have hout : out.length = sampleBase b raw₀.length raw₁.length t + localIndex := by omega
    have hicode : localIndex < sampleWidth b e₀ e₁ := by simpa only [h₀, h₁] using hi
    have hocode : out.length = sampleBase b e₀ e₁ t + localIndex := by
      simpa only [h₀, h₁] using hout
    by_cases hno : localIndex < colorBase b ∨ minimumBase b raw₀.length raw₁.length ≤ localIndex
    · rw [kindWord, BrouwerNashKindCorrectness.sampleKind_at_sample _ _ _ _ _ raw₀ raw₁
        t localIndex h₀ h₁ hi hout hno,
        color_zero_at_noncolor _ _ _ _ _ t localIndex hicode hocode
          (by simpa only [h₀, h₁] using hno)]
      exact or_false_right _
    · have hlo : colorBase b ≤ localIndex := by omega
      have hhi : localIndex < minimumBase b raw₀.length raw₁.length := by omega
      have hafter : weightBase b ≤ localIndex := by dsimp only [colorBase] at hlo; omega
      rw [kindWord, BrouwerNashKindCorrectness.sampleKind_false_of_weightBase _ _ _ _ _
        t localIndex hicode hocode hafter,
        color_at_sample _ _ _ _ _ raw₀ raw₁ h₀ h₁ hw₀ hw₁ t localIndex hout hlo hhi]
      exact or_false_left _
  · have hafter : globalCount b + 41 * sampleWidth b e₀ e₁ ≤ out.length := by
      have hmul := Nat.mul_le_of_le_div w 41 offset (show 41 ≤ offset / w by omega)
      dsimp only [offset, w] at hmul
      rw [h₀, h₁]
      omega
    have houtside : out.length < globalCount b ∨
        globalCount b + 41 * sampleWidth b e₀ e₁ ≤ out.length := Or.inr hafter
    rw [kindWord, BrouwerNashKindCorrectness.sampleKind_zero _ _ _ _ _ houtside,
      color_zero_outside_allocated _ _ _ _ _ houtside]
    unfold program
    rw [ite_eq_right hg]
    rw [dite_eq_right hs]
    rfl
end Correctness
end GameTheory.Complexity.Backend.BrouwerNashSelectorKind
