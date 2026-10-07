import GameTheoryComplexity.Backend.SATTableScanner
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal.StringOps
import Complexitylib.Classes.P.Pairing
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.List.Fold

/-! String registers for the clause-incidence scanner. Fixed-arity tuple packing
retains unary counters exactly, avoiding truncation when the source is scanned. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Read one register from a fixed-arity packed tuple. -/
def incidenceRegister (input : List Bool) (i : ℕ) : List Bool :=
  pairSnd ((pairFst^[i]) input)

/-- Encode the reverse scanner's Boolean registers and unary counters. -/
def encodeIncidenceState (s : IncidenceState) : List Bool :=
  encodeVec ![[s.waiting], [s.saved], List.replicate s.clauseIndex true,
    List.replicate s.variableCount true, [s.sign], [s.seenData], [s.seenClause], [s.hit]]

private theorem incidenceRegister_cobham {n : ℕ} {source : (Fin n → List Bool) → List Bool}
    (hs : Cobham source) (i : ℕ) : Cobham fun v => incidenceRegister (source v) i := by
  have hf : Cobham fun v : Fin 1 → List Bool => pairFst (v 0) :=
    FP_subset_CobhamFP pairFst_mem_FP
  have ht : Cobham fun v : Fin 1 → List Bool => pairSnd (v 0) :=
    FP_subset_CobhamFP pairSnd_mem_FP
  have hi : ∀ i : ℕ, Cobham fun v => (pairFst^[i]) (source v) := by
    intro i
    induction i with
    | zero => exact hs
    | succ i ih =>
        exact (Cobham.comp hf fun _ => ih).of_eq fun v => by
          simp only [Function.iterate_succ_apply']
  exact (Cobham.comp ht fun _ => hi i).of_eq fun _ => rfl

/-- One reverse input bit updates the packed scanner registers. Parameters are
the packed state, unary variable index, sign flag, and unary clause index. -/
def incidenceWordStep (bit : Bool) (v : Fin 4 → List Bool) : List Bool :=
  let r := incidenceRegister (v 0)
  let litSep := andBit (r 0) (bif bit then [false] else r 1)
  let clauseSep := andBit (r 0) (bif bit then notBit (r 1) else [false])
  let separator := orBit litSep clauseSep
  let data := andBit (r 0) (bif bit then r 1 else notBit (r 1))
  let finish := orBit (r 7) (andBit (r 5)
    (andBit (eqFlag (r 3) (v 1))
      (andBit (eqFlag (r 4) (v 2)) (eqFlag (r 2) (v 3)))))
  encodeVec ![
    notBit (r 0), caseBit₀ (r 0) (r 1) [bit],
    caseBit₀ (andBit clauseSep (r 6)) (true :: r 2) (r 2),
    caseBit₀ separator [] (caseBit₀ (andBit data (r 5)) (true :: r 3) (r 3)),
    caseBit₀ data [bit] (r 4),
    caseBit₀ separator [false] (caseBit₀ data [true] (r 5)),
    caseBit₀ clauseSep [true] (r 6),
    caseBit₀ separator finish (r 7)]

/-- The packed register transition is a member of Cobham's polynomial-time algebra. -/
theorem incidenceWordStep_cobham (bit : Bool) : Cobham (incidenceWordStep bit) := by
  let r : ℕ → (Fin 4 → List Bool) → List Bool := fun i v => incidenceRegister (v 0) i
  have hr (i : ℕ) : Cobham (r i) := incidenceRegister_cobham (Cobham.proj 0) i
  let litSep := fun v => andBit (r 0 v) (bif bit then [false] else r 1 v)
  let clauseSep := fun v => andBit (r 0 v) (bif bit then notBit (r 1 v) else [false])
  let separator := fun v => orBit (litSep v) (clauseSep v)
  let data := fun v => andBit (r 0 v) (bif bit then r 1 v else notBit (r 1 v))
  have hl : Cobham litSep := by
    cases bit
    · exact Cobham.andFn (hr 0) (hr 1)
    · exact Cobham.andFn (hr 0) (Cobham.const [false])
  have hc : Cobham clauseSep := by
    cases bit
    · exact Cobham.andFn (hr 0) (Cobham.const [false])
    · exact Cobham.andFn (hr 0) (Cobham.notFn (hr 1))
  have hs : Cobham separator := Cobham.orFn hl hc
  have hd : Cobham data := by
    cases bit
    · exact Cobham.andFn (hr 0) (Cobham.notFn (hr 1))
    · exact Cobham.andFn (hr 0) (hr 1)
  have heq (i j : Fin 4) : Cobham fun v => eqFlag (r i.val v) (v j) :=
    eqFlag_mem (hr i.val) (Cobham.proj j)
  have hfinish : Cobham fun v => orBit (r 7 v) (andBit (r 5 v)
      (andBit (eqFlag (r 3 v) (v 1))
        (andBit (eqFlag (r 4 v) (v 2)) (eqFlag (r 2 v) (v 3))))) :=
    Cobham.orFn (hr 7) (Cobham.andFn (hr 5)
      (Cobham.andFn (heq 3 1) (Cobham.andFn (eqFlag_mem (hr 4) (Cobham.proj 2)) (heq 2 3))))
  have hinc (i : ℕ) : Cobham fun v => true :: r i v :=
    (Cobham.comp (Cobham.bit true) fun _ => hr i).of_eq fun _ => rfl
  unfold incidenceWordStep
  apply Cobham.comp encodeVec_mem
  intro i
  fin_cases i
  · exact Cobham.notFn (hr 0)
  · exact Cobham.iteFn (hr 0) (hr 1) (Cobham.const [bit])
  · exact Cobham.iteFn (Cobham.andFn hc (hr 6)) (hinc 2) (hr 2)
  · exact Cobham.iteFn hs Cobham.empty (Cobham.iteFn (Cobham.andFn hd (hr 5)) (hinc 3) (hr 3))
  · exact Cobham.iteFn hd (Cobham.const [bit]) (hr 4)
  · exact Cobham.iteFn hs (Cobham.const [false]) (Cobham.iteFn hd (Cobham.const [true]) (hr 5))
  · exact Cobham.iteFn hc (Cobham.const [true]) (hr 6)
  · exact Cobham.iteFn hs hfinish (hr 7)

/-- The string equality flag represents the ordinary decidable equality test. -/
theorem eqFlag_as_bool (a b : List Bool) : eqFlag a b = [decide (a = b)] := by
  by_cases h : a = b
  · simp only [h, decide_true]
    exact (eqFlag_eq_true_iff b b).mpr rfl
  · rcases eqFlag_flag a b with hflag | hflag
    · exact False.elim (h ((eqFlag_eq_true_iff a b).mp hflag))
    · simpa only [h, decide_false] using hflag

@[simp] theorem incidenceRegister_encodeVec {n : ℕ}
    (v : Fin n → List Bool) (i : Fin n) : incidenceRegister (encodeVec v) i.val = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [incidenceRegister, encodeVec_succ]
      · simpa only [incidenceRegister, Fin.val_succ, Function.iterate_succ_apply,
          encodeVec_succ, pairFst_pair, Fin.tail] using ih (Fin.tail v) j

/-- Packed string execution agrees exactly with the semantic incidence registers. -/
theorem incidenceWordStep_encode (s : IncidenceState) (varIndex clauseIndex : ℕ)
    (sign bit : Bool) :
    incidenceWordStep bit ![encodeIncidenceState s, List.replicate varIndex true,
      [sign], List.replicate clauseIndex true] =
    encodeIncidenceState (s.step varIndex sign clauseIndex bit) := by
  rcases s with ⟨waiting, saved, clause, count, currentSign, seen, started, hit⟩
  cases waiting <;> cases saved <;> cases bit <;> cases seen <;> cases started <;>
    simp [incidenceWordStep, encodeIncidenceState, incidenceRegister, encodeVec,
      Function.iterate_succ_apply, IncidenceState.step, IncidenceState.token,
      IncidenceState.finish, andBit, orBit, notBit, caseBit₀, eqFlag_as_bool,
      List.replicate_succ] <;> split_ifs <;> simp_all

private theorem incidenceState_step_bounds (s : IncidenceState) (varIndex clauseIndex : ℕ)
    (sign bit : Bool) :
    (s.step varIndex sign clauseIndex bit).clauseIndex ≤ s.clauseIndex + 1 ∧
      (s.step varIndex sign clauseIndex bit).variableCount ≤ s.variableCount + 1 := by
  rcases s with ⟨waiting, saved, clause, count, currentSign, seen, started, hit⟩
  cases waiting <;> cases saved <;> cases bit <;> cases seen <;> cases started <;>
    simp [IncidenceState.step, IncidenceState.token, IncidenceState.finish]

/-- The semantic state reached by the reverse incidence scan. -/
def incidenceScanState (varIndex clauseIndex : ℕ) (sign : Bool)
    (input : List Bool) : IncidenceState :=
  input.foldr (fun bit s => s.step varIndex sign clauseIndex bit) {}

private theorem incidenceScanState_bounds (varIndex clauseIndex : ℕ) (sign : Bool)
    (input : List Bool) :
    (incidenceScanState varIndex clauseIndex sign input).clauseIndex ≤ input.length ∧
      (incidenceScanState varIndex clauseIndex sign input).variableCount ≤ input.length := by
  induction input with
  | nil => simp [incidenceScanState]
  | cons bit input ih =>
      have hs := incidenceState_step_bounds
        (incidenceScanState varIndex clauseIndex sign input) varIndex clauseIndex sign bit
      change (incidenceScanState varIndex clauseIndex sign input |>.step varIndex sign clauseIndex bit).clauseIndex ≤ input.length + 1 ∧
        (incidenceScanState varIndex clauseIndex sign input |>.step varIndex sign clauseIndex bit).variableCount ≤ input.length + 1
      omega

private theorem encodeIncidenceState_length_le (s : IncidenceState) :
    (encodeIncidenceState s).length ≤ 4 * s.clauseIndex + 8 * s.variableCount + 753 := by
  simp [encodeIncidenceState, encodeVec]
  omega

/-- A linear state-width ruler. -/
@[irreducible] def incidenceWidth (input : List Bool) : List Bool :=
  List.replicate (768 * (input.length + 1)) true

@[simp] theorem incidenceWidth_length (input : List Bool) :
    (incidenceWidth input).length = 768 * (input.length + 1) := by
  rw [incidenceWidth, List.length_replicate]

private theorem incidenceWidth_cobham : Cobham fun v : Fin 1 → List Bool => incidenceWidth (v 0) := by
  exact (Cobham.comp₂ Cobham.smash (Cobham.const (List.replicate 768 true))
    (Cobham.bit false)).of_eq fun _ => by
      change Complexity.smash (List.replicate 768 true) (false :: _) = _
      rw [incidenceWidth, Complexity.smash, List.length_replicate, List.length_cons]

/-- Apply one bit transition with a polynomial-width clamp; the clamp is inactive
on encoded states reached by a genuine source scan. -/
def incidenceClampedStep (bit : Bool) (v : Fin 6 → List Bool) : List Bool :=
  (incidenceWordStep bit ![v 1, v 2, v 3, v 4]).take (incidenceWidth (v 5)).length

/-- A bounded recursion implementing the reverse incidence scan. -/
def incidenceWordLoop (input : List Bool) (params : Fin 4 → List Bool) : List Bool :=
  recNotation (fun _ => encodeIncidenceState {})
    (incidenceClampedStep false) (incidenceClampedStep true) input params

private theorem incidenceClampedStep_cobham (bit : Bool) : Cobham (incidenceClampedStep bit) := by
  have hword := Cobham.comp (incidenceWordStep_cobham bit)
    (gs := fun i => fun v : Fin 6 → List Bool =>
      (![v 1, v 2, v 3, v 4] : Fin 4 → List Bool) i) (by
        intro i
        fin_cases i
        · exact Cobham.proj 1
        · exact Cobham.proj 2
        · exact Cobham.proj 3
        · exact Cobham.proj 4)
  have hwidth : Cobham fun v : Fin 6 → List Bool => incidenceWidth (v 5) :=
    (Cobham.comp incidenceWidth_cobham fun _ => Cobham.proj 5).of_eq fun _ => rfl
  exact (Cobham.takeFn hwidth hword).of_eq fun _ => rfl

private theorem incidenceWordLoop_length_le (input : List Bool) (params : Fin 4 → List Bool) :
    (incidenceWordLoop input params).length ≤ (incidenceWidth (params 3)).length := by
  cases input with
  | nil =>
      have h := encodeIncidenceState_length_le ({} : IncidenceState)
      change (encodeIncidenceState {}).length ≤ _
      rw [incidenceWidth_length]
      norm_num at h
      omega
  | cons bit input =>
      cases bit
      all_goals
        change (incidenceClampedStep _ (Fin.cons input (Fin.cons (incidenceWordLoop input params) params))).length ≤ _
        rw [incidenceClampedStep, List.length_take]
        have hp : (Fin.cons input (Fin.cons (incidenceWordLoop input params) params) : Fin 6 → List Bool) 5 = params 3 := rfl
        rw [hp]
        omega

/-- Polynomial-time scanning on encoded query vectors. -/
def incidenceWordScan (v : Fin 4 → List Bool) : List Bool := incidenceWordLoop (v 3) v

theorem incidenceWordScan_cobham : Cobham incidenceWordScan := by
  have hwidth : Cobham fun v : Fin 5 → List Bool => incidenceWidth (v 4) :=
    (Cobham.comp incidenceWidth_cobham fun _ => Cobham.proj 4).of_eq fun _ => rfl
  have hrec := Cobham.boundedRec (Cobham.const (encodeIncidenceState {}))
    (incidenceClampedStep_cobham false) (incidenceClampedStep_cobham true) hwidth
    (fun input params => incidenceWordLoop_length_le input params)
  have h := Cobham.comp hrec (gs := fun i => fun v : Fin 4 → List Bool =>
    (![v 3, v 0, v 1, v 2, v 3] : Fin 5 → List Bool) i) (by
      intro i
      fin_cases i
      · exact Cobham.proj 3
      · exact Cobham.proj 0
      · exact Cobham.proj 1
      · exact Cobham.proj 2
      · exact Cobham.proj 3)
  apply h.of_eq
  intro v
  change incidenceWordLoop (v 3) (Fin.tail ![v 3, v 0, v 1, v 2, v 3]) =
    incidenceWordLoop (v 3) v
  congr 1
  ext i
  fin_cases i <;> rfl

private theorem incidenceScanState_length_le (varIndex clauseIndex : ℕ) (sign : Bool)
    (input : List Bool) :
    (encodeIncidenceState (incidenceScanState varIndex clauseIndex sign input)).length ≤
      (incidenceWidth input).length := by
  have hs := incidenceScanState_bounds varIndex clauseIndex sign input
  have he := encodeIncidenceState_length_le (incidenceScanState varIndex clauseIndex sign input)
  rw [incidenceWidth_length]
  omega

/-- The width clamp preserves every genuine semantic scan state. -/
theorem incidenceWordLoop_encode (varIndex clauseIndex : ℕ) (sign : Bool)
    (input source : List Bool) (hsource : input.length ≤ source.length) :
    incidenceWordLoop input ![List.replicate varIndex true, [sign],
      List.replicate clauseIndex true, source] =
      encodeIncidenceState (incidenceScanState varIndex clauseIndex sign input) := by
  induction input with
  | nil => rfl
  | cons bit input ih =>
      have hi : input.length ≤ source.length := by simpa using Nat.le_trans (Nat.le_succ _) hsource
      have hb (b : Bool) :
          (encodeIncidenceState (incidenceScanState varIndex clauseIndex sign (b :: input))).length ≤
            (incidenceWidth source).length := by
        have h := incidenceScanState_length_le varIndex clauseIndex sign (b :: input)
        have hi' : input.length + 1 ≤ source.length := by simpa only [List.length_cons] using hsource
        simp only [incidenceWidth_length, List.length_cons] at h ⊢
        omega
      simp only [incidenceWordLoop, recNotation_cons]
      cases bit <;> simp only [Bool.cond_true, Bool.cond_false, incidenceClampedStep]
      all_goals
        change (incidenceWordStep _ ![incidenceWordLoop input ![List.replicate varIndex true,
          [sign], List.replicate clauseIndex true, source], List.replicate varIndex true,
          [sign], List.replicate clauseIndex true]).take (incidenceWidth source).length = _
        rw [ih hi, incidenceWordStep_encode]
        change (encodeIncidenceState (incidenceScanState varIndex clauseIndex sign (_ :: input))).take
          (incidenceWidth source).length = _
        apply List.take_of_length_le
        exact hb _

/-- Finish the first literal and include the tautological padded-clause case. -/
def incidenceVerdictWord (v : Fin 4 → List Bool) : List Bool :=
  let r := incidenceRegister (incidenceWordScan v)
  let finish := orBit (r 7) (andBit (r 5)
    (andBit (eqFlag (r 3) (v 0))
      (andBit (eqFlag (r 4) (v 1)) (eqFlag (r 2) (v 2)))))
  orBit finish (orBit (notBit (r 6)) (notBit (lenLeFlag (r 2) (v 2))))

/-- The incidence decision runs in polynomial time on encoded query vectors. -/
theorem incidenceVerdictWord_cobham : Cobham incidenceVerdictWord := by
  let r : ℕ → (Fin 4 → List Bool) → List Bool := fun i v =>
    incidenceRegister (incidenceWordScan v) i
  have hr (i : ℕ) : Cobham (r i) := incidenceRegister_cobham incidenceWordScan_cobham i
  exact Cobham.orFn
    (Cobham.orFn (hr 7) (Cobham.andFn (hr 5)
      (Cobham.andFn (eqFlag_mem (hr 3) (Cobham.proj 0))
        (Cobham.andFn (eqFlag_mem (hr 4) (Cobham.proj 1)) (eqFlag_mem (hr 2) (Cobham.proj 2))))))
    (Cobham.orFn (Cobham.notFn (hr 6)) (Cobham.notFn (lenLeFlag_mem (hr 2) (Cobham.proj 2))))

/-- The string length flag represents the ordinary decidable comparison. -/
theorem lenLeFlag_as_bool (a b : List Bool) :
    lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  by_cases h : b.length ≤ a.length
  · simp only [h, decide_true]
    exact (lenLeFlag_eq_true_iff a b).mpr h
  · rcases lenLeFlag_flag a b with hflag | hflag
    · exact False.elim (h ((lenLeFlag_eq_true_iff a b).mp hflag))
    · simpa only [h, decide_false] using hflag

/-- The polynomial-time verdict is exactly the semantic literal-incidence scanner. -/
theorem incidenceVerdictWord_eq (varIndex clauseIndex : ℕ) (sign : Bool) (input : List Bool) :
    incidenceVerdictWord ![List.replicate varIndex true, [sign],
      List.replicate clauseIndex true, input] = [scanIncidence varIndex sign clauseIndex input] := by
  unfold incidenceVerdictWord incidenceWordScan scanIncidence
  change (let r := incidenceRegister (incidenceWordLoop input
    ![List.replicate varIndex true, [sign], List.replicate clauseIndex true, input]);
    orBit (orBit (r 7) (andBit (r 5)
      (andBit (eqFlag (r 3) (List.replicate varIndex true))
        (andBit (eqFlag (r 4) [sign]) (eqFlag (r 2) (List.replicate clauseIndex true))))))
      (orBit (notBit (r 6)) (notBit (lenLeFlag (r 2) (List.replicate clauseIndex true))))) = _
  rw [incidenceWordLoop_encode varIndex clauseIndex sign input input (le_refl _)]
  have hstate : incidenceScanState varIndex clauseIndex sign input =
      input.reverse.foldl (IncidenceState.step varIndex sign clauseIndex) {} := by
    simp only [incidenceScanState, List.foldr_eq_foldl_reverse]
  rw [hstate]
  generalize input.reverse.foldl (IncidenceState.step varIndex sign clauseIndex) {} = s
  rcases s with ⟨waiting, saved, clause, count, currentSign, seen, started, hit⟩
  simp [encodeIncidenceState, incidenceRegister, encodeVec, Function.iterate_succ_apply,
    eqFlag_as_bool, lenLeFlag_as_bool, IncidenceState.finish,
    andBit, orBit, notBit, caseBit₀]
  split_ifs <;> simp_all

/-- An actual deterministic polynomial-time implementation witnesses the incidence query. -/
theorem incidenceVerdictWord_mem_FPn : FPn incidenceVerdictWord :=
  Cobham.cobham_iff_FPn.mp incidenceVerdictWord_cobham

end GameTheory.Complexity.Backend
