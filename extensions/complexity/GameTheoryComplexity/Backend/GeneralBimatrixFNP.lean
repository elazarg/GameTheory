module

public import GameTheoryComplexity.Backend.GeneralBimatrixProblem
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierMachine
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness
public import Complexity.Computability.Complexity.Classes.TFNP

@[expose] public section

/-! Native polynomial verification of exact signed rectangular bimatrix Nash
certificates. Both the complete input and witness are machine arguments. -/

namespace GameTheory.Complexity.Backend
open Turing.MultiTapeTM Cslib.Complexity WordOperations

/-- The executable verifier agrees with the canonical certificate relation. -/
theorem generalBimatrixVerdict_accept_iff_relation (input certificate : List Bool) :
    generalBimatrixVerdict ![input, certificate] = [true] ↔
      generalBimatrixRelation input certificate :=
  generalBimatrixVerdict_eq_true_iff input certificate

/-- Boolean acceptance by the exact binary verifier, including malformed games. -/
def generalBimatrixAccepts (input certificate : List Bool) : Bool :=
  (generalBimatrixVerdict ![input, certificate]).headD false

/-- Native argument framing charges the complete input and certificate. -/
@[fun_prop] theorem generalBimatrixAccepts_polyTime
    {α : Type} {enc : α ↪ List Bool} {input certificate : α → List Bool}
    (hi : ComputableInPolyTime input enc encBits)
    (hc : ComputableInPolyTime certificate enc encBits) :
    ComputableInPolyTime (fun a => generalBimatrixAccepts (input a) (certificate a))
      enc encBool := by
  have hargs : ComputableInPolyTime (fun a => ![input a, certificate a])
      enc (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hi
    · exact hc
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  exact hhead.comp (generalBimatrixVerdict_polyTime.comp hargs)

/-- The native Boolean verdict decides the same canonical Nash relation. -/
theorem generalBimatrixAccepts_accept (input certificate : List Bool) :
    generalBimatrixAccepts input certificate = true ↔
      generalBimatrixRelation input certificate := by
  rw [← generalBimatrixVerdict_accept_iff_relation]
  simp only [generalBimatrixAccepts, generalBimatrixVerdict, WordOperations.orFlag,
    List.headD_cons, List.cons.injEq, and_true]

/-- Exact signed rectangular Nash search has native bounded verification. -/
theorem generalBimatrixRelation_mem_FNP : generalBimatrixRelation ∈ FNP encBits := by
  refine ⟨generalBimatrixRelation_polyBalanced, fun p => generalBimatrixAccepts p.1 p.2,
    generalBimatrixAccepts_polyTime (ComputableInPolyTime.fst encBits encBits)
      (ComputableInPolyTime.snd encBits encBits), fun input certificate => ?_⟩
  exact (generalBimatrixAccepts_accept input certificate).symm

end GameTheory.Complexity.Backend
