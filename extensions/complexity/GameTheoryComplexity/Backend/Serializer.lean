import GameTheoryComplexity.Backend.Complexitylib
import Complexitylib.Classes.P.Cobham.Vec
import Complexitylib.Classes.P.Cobham.Internal.FstBlock
import Complexitylib.Classes.P.Cobham.Internal.SndBlock
import Complexitylib.Classes.P.Cobham.Internal.Reorder
import Complexitylib.Classes.P.Cobham.Internal.Cat
import Complexitylib.Classes.P.Cobham.Internal.ConsBit
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.PairWithInput
import Complexitylib.Classes.P.UnaryLength

/-! Polynomial-time serialization of a unary security parameter and Boolean samples.
The certificate witnesses an actual deterministic machine on encoded two-component
inputs, rather than treating a bound on output length as a runtime guarantee.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Normalize the first component to unary, delimit it, and retain the sample payload. -/
def serializeBoolean (v : Fin 2 → List Bool) : List Bool :=
  List.replicate (v 0).length true ++ [false] ++ v 1

/-- An actual polynomial-time string function implements the serializer on encoded tuples. -/
theorem serializeBoolean_mem_FPn : FPn serializeBoolean := by
  let a : List Bool → List Bool := fun z => List.replicate (pairSnd z).length true
  let b : List Bool → List Bool := fun z => false :: pairSnd (pairFst z)
  have ha : a ∈ FP := mem_FP_comp sndBlock_mem_FP unaryLength_mem_FP
  have hb : b ∈ FP :=
    mem_FP_comp (mem_FP_comp fstBlock_mem_FP sndBlock_mem_FP) (cons_mem_FP false)
  have h1 : (fun z => pair (b z) z) ∈ FP := mem_FP_pairWithInput hb
  have h2 : (fun w => pair (a (pairSnd w)) w) ∈ FP :=
    mem_FP_pairWithInput (mem_FP_comp sndBlock_mem_FP ha)
  have h12 : (fun z => pair (a z) (pair (b z) z)) ∈ FP := by
    simpa only [Function.comp_def, pairSnd_pair] using mem_FP_comp h1 h2
  have hr : (fun z => pair (a z) (b z)) ∈ FP := by
    simpa only [Function.comp_def, reorder_pair_pair] using mem_FP_comp h12 reorder_mem_FP
  refine ⟨catBlocks ∘ (fun z => pair (a z) (b z)), mem_FP_comp hr catBlocks_mem_FP, ?_⟩
  intro v
  simp [a, b, serializeBoolean, Function.comp, encodeVec, List.append_assoc]
  rfl

/-- The actual tuple presented to the serializer contains the unary parameter
and the samples in their original order. -/
def booleanTuple (sampleDegree κ : ℕ) (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    Fin 2 → List Bool :=
  ![List.replicate κ true, List.ofFn draws]

/-- The certified machine computes precisely the input consumed by the sample test. -/
theorem serializeBoolean_booleanTuple (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    serializeBoolean (booleanTuple sampleDegree κ draws) = booleanInput sampleDegree κ draws := by
  simp [serializeBoolean, booleanTuple, booleanInput]

/-- The fixed-arity encoding has an exact linear size formula. -/
theorem booleanTuple_encode_length (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    (encodeVec (booleanTuple sampleDegree κ draws)).length = κ + 2 * (κ + 1) ^ sampleDegree + 6 := by
  simp [encodeVec, booleanTuple, Fin.tail]
  omega

/-- The encoded tuple has polynomial length in the unary security parameter. -/
theorem booleanTuple_encode_length_bound (sampleDegree κ : ℕ)
    (draws : Fin ((κ + 1) ^ sampleDegree) → Bool) :
    (encodeVec (booleanTuple sampleDegree κ draws)).length ≤
      24 * (κ + 1) ^ (sampleDegree + 1) := by
  have hlength := booleanInput_length_bound sampleDegree κ draws
  have hpow : 1 ≤ (κ + 1) ^ (sampleDegree + 1) := one_le_pow₀ (by omega)
  rw [booleanTuple_encode_length]
  rw [booleanInput_length] at hlength
  omega

/-- One deterministic machine serializes every sample degree and every security
parameter. Its actual execution has a polynomial bound in the parameter, uniformly
over all sample tuples; the polynomial may depend on the fixed sample degree. -/
theorem exists_uniform_booleanSerializer :
    ∃ (n : ℕ) (machine : TM n), ∀ sampleDegree : ℕ, ∃ bound : Polynomial ℕ,
      ∀ (κ : ℕ) (draws : Fin ((κ + 1) ^ sampleDegree) → Bool),
        ∃ (final : Cfg n machine.Q) (time : ℕ),
          time ≤ bound.eval κ ∧
          machine.reachesIn time
            (machine.initCfg (encodeVec (booleanTuple sampleDegree κ draws))) final ∧
          machine.halted final ∧ final.output.HasOutput (booleanInput sampleDegree κ draws) := by
  obtain ⟨g, hg, hspec⟩ := serializeBoolean_mem_FPn
  obtain ⟨degree, n, machine, steps, hcompute, hbig⟩ := hg
  obtain ⟨p, hp⟩ := hbig.pow_polynomial_bound
  refine ⟨n, machine, fun sampleDegree => ?_⟩
  let bound : Polynomial ℕ :=
    p.comp (Polynomial.C 24 * (Polynomial.X + Polynomial.C 1) ^ (sampleDegree + 1))
  refine ⟨bound, fun κ draws => ?_⟩
  obtain ⟨final, time, htime, hreach, hhalt, houtput⟩ :=
    hcompute (encodeVec (booleanTuple sampleDegree κ draws))
  refine ⟨final, time, ?_, hreach, hhalt, ?_⟩
  · calc
      time ≤ steps (encodeVec (booleanTuple sampleDegree κ draws)).length := htime
      _ ≤ p.eval (encodeVec (booleanTuple sampleDegree κ draws)).length := hp _
      _ ≤ p.eval (24 * (κ + 1) ^ (sampleDegree + 1)) :=
        polynomial_eval_mono_nat p (booleanTuple_encode_length_bound sampleDegree κ draws)
      _ = bound.eval κ := by simp [bound, Polynomial.eval_comp]
  · simpa only [hspec, serializeBoolean_booleanTuple] using houtput

end GameTheory.Complexity.Backend
