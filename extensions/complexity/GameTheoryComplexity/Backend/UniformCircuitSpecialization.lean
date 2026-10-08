import GameTheoryComplexity.Backend.CircuitPrefixCompiler
import Complexitylib.Classes.P.DecisionFn
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Containment

/-! Polynomial-time Boolean computations admit uniformly generated serialized
circuits with a fixed word prefix hardwired. The generator retains the family
tag, while the prefix compiler operates on its underlying positive-arity code. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode

private def prefixFamilyGenerator (gen : List Bool → List Bool) (z : List Bool) :
    List Bool :=
  true :: restrictCircuitCode (pairFst z) (pairSnd z)
    (gen (unaryList ((pairSnd z ++ pairFst z).length))).tail

private theorem prefixFamilyGenerator_mem_FP {gen : List Bool → List Bool}
    (hg : gen ∈ FP) : prefixFamilyGenerator gen ∈ FP := by
  have hruler := mem_FP_comp (appendFn_mem_FP pairSnd_mem_FP pairFst_mem_FP)
    unaryLength_mem_FP
  have hcode : (fun z => gen (unaryList ((pairSnd z ++ pairFst z).length))) ∈ FP :=
    mem_FP_comp hruler hg
  have htail : (fun z => (gen (unaryList ((pairSnd z ++ pairFst z).length))).tail) ∈ FP := by
    apply CobhamFP_subset_FP
    exact Cobham.tailFn (FP_subset_CobhamFP hcode)
  have hrestrict := restrictCircuitCodeFn_mem_FP pairFst_mem_FP pairSnd_mem_FP htail
  have hfull := appendFn_mem_FP (constFn_mem_FP [true]) hrestrict
  exact hfull

/-- A polynomial-time Boolean computation has a polynomial-time circuit generator
whose paired ruler and seed fix the prefix and leave exactly the ruler's width live. -/
theorem exists_prefixCircuitGenerator (b : List Bool → Bool)
    (hb : (fun x => [b x]) ∈ FP) :
    ∃ gen : List Bool → List Bool, gen ∈ FP ∧ ∀ ruler seed vertex,
      0 < ruler.length → vertex.length = ruler.length →
      evalFamilyCode (gen (pair ruler seed)) vertex = some (b (seed ++ vertex)) := by
  let L : Language := {x | b x = true}
  have hL : L ∈ P := mem_P_of_decisionFn_bool hb (fun _ => Iff.rfl)
  obtain ⟨F, _, hdec, _, gen, hgen, hcode⟩ := P_subset_UniformPPoly hL
  have heval (x : List Bool) : F.evalList x = b x := by
    have h := hdec.evalList x
    change F.evalList x = true ↔ b x = true at h
    cases hf : F.evalList x <;> cases hb : b x <;> simp_all
  refine ⟨prefixFamilyGenerator gen, prefixFamilyGenerator_mem_FP (FL_subset_FP hgen), ?_⟩
  intro ruler seed vertex hn hi
  have hpos : 0 < (seed ++ ruler).length := by simp only [List.length_append]; omega
  obtain ⟨n, hlen⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hg : gen (unaryList ((seed ++ ruler).length)) =
      true :: encodeCircuit (F.circuit (n + 1)) := by
    rw [hcode, hlen, CircuitFamily.encodeAt_succ]
  have harg : (seed ++ vertex).length = n + 1 := by
    simpa only [List.length_append, hi] using hlen
  have hfamily := evalFamilyCode_encodeAt_length F (seed ++ vertex)
  rw [harg, CircuitFamily.encodeAt_succ] at hfamily
  have hv : vertex ≠ [] := List.length_pos_iff.mp (by omega)
  have hseed : seed ++ vertex ≠ [] := List.length_pos_iff.mp (by simp [hi]; omega)
  simp only [prefixFamilyGenerator, pairFst_pair, pairSnd_pair, hg, List.tail_cons]
  simp only [evalFamilyCode, List.isEmpty_iff, hv, ↓reduceIte]
  rw [hi, restrictCircuitCode_eval _ _ _ _ hn hi]
  simp only [evalFamilyCode, List.isEmpty_iff, hseed, ↓reduceIte] at hfamily
  simpa only [List.length_append, hi, heval, ← harg] using hfamily

end GameTheory.Complexity.Backend
