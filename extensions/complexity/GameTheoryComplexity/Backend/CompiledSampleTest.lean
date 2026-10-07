import GameTheoryComplexity.Backend.Composition
import GameTheoryComplexity.Backend.Serializer

/-! A single probabilistic machine implements canonical Boolean serialization and testing.
The implementation is fixed across security parameters and sample tuples; its
parameter-polynomial clock preserves the complete sample-test acceptance law.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Every canonical machine test has a single uniform polynomial-time machine
implementing serialization and testing together. The security clock is independent
of the observed samples, and immediate rejection is covered as well. -/
theorem exists_composed_booleanMachine {ng : ℕ} (machine : NTM ng)
    (clock : PolynomialClock machine) :
    ∃ (n : ℕ) (composite : NTM n), composite.IsPPT ∧
      ∀ sampleDegree : ℕ, ∃ bound : Polynomial ℕ,
        ∀ (κ : ℕ) (draws : Fin ((κ + 1) ^ sampleDegree) → Bool),
          (∀ choices : Fin (bound.eval κ) → Bool,
            composite.halted (composite.trace (bound.eval κ) choices
              (composite.initCfg (encodeVec (booleanTuple sampleDegree κ draws))))) ∧
          machineLaw composite (encodeVec (booleanTuple sampleDegree κ draws)) (bound.eval κ) =
            (booleanMachineTest machine clock sampleDegree).accept κ draws := by
  obtain ⟨f, hf, hspec⟩ := serializeBoolean_mem_FPn
  obtain ⟨n, composite, p, hppt, hhalt, hlaw⟩ := exists_preprocessing_machine hf machine clock
  refine ⟨n, composite, hppt, fun sampleDegree => ?_⟩
  let bound : Polynomial ℕ :=
    p.comp (Polynomial.C 24 * (Polynomial.X + Polynomial.C 1) ^ (sampleDegree + 1))
  refine ⟨bound, fun κ draws => ?_⟩
  let input := encodeVec (booleanTuple sampleDegree κ draws)
  have hle : p.eval input.length ≤ bound.eval κ := by
    have hbound : bound.eval κ = p.eval (24 * (κ + 1) ^ (sampleDegree + 1)) := by
      simp only [bound, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
    rw [hbound]
    exact polynomial_eval_mono_nat p (booleanTuple_encode_length_bound sampleDegree κ draws)
  constructor
  · intro choices
    have heq := composite.trace_mono hle
      (choices := fun i => choices ⟨i.val, by omega⟩) (choices' := choices)
      (c := composite.initCfg input) (fun _ => rfl) (hhalt input _)
    rw [heq]
    exact hhalt input _
  · have hencoded : f input = booleanInput sampleDegree κ draws :=
      (hspec _).trans (serializeBoolean_booleanTuple sampleDegree κ draws)
    have h := (machineLaw_of_le_of_halts composite input hle (hhalt input)).trans (hlaw input)
    rw [hencoded] at h
    exact h

end GameTheory.Complexity.Backend
