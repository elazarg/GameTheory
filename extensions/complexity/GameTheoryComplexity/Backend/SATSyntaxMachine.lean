import Complexitylib.SAT.Tseitin.Machine.Internal.Validation
import Complexitylib.SAT.Tseitin.Machine.Internal.ValidationFramed
import Complexitylib.Classes.P.Cobham
import Complexitylib.Asymptotics.PolyBound

/-! Polynomial-time syntax validation for the concrete SAT bit encoding.
The existing finite-state validator writes one Boolean output bit and halts in
exactly the input length plus two machine transitions.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.SAT _root_.Complexity.SAT.ThreeSAT.Machine

/-- One-bit characteristic word for successful CNF decoding. -/
def satSyntaxWord (input : List Bool) : List Bool := [(CNF.decode? input).isSome]

@[simp] theorem satSyntaxWord_eq (input : List Bool) :
    satSyntaxWord input = [(CNF.decode? input).isSome] := rfl

/-- The concrete finite-state validator computes the full one-bit syntax word. -/
theorem satSyntaxWord_computesInTime :
    (validationTM (n := 0)).ComputesInTime satSyntaxWord (fun n => n + 2) := by
  intro input
  let work₀ : Fin 0 → Tape := fun _ => ⟨1, (Tape.init []).cells⟩
  let output₀ : Tape := ⟨1, (Tape.init []).cells⟩
  let started : Cfg 0 (validationTM (n := 0)).Q :=
    { state := (validationTM (n := 0)).qstart
      input := ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩
      work := work₀
      output := output₀ }
  have hstep : (validationTM (n := 0)).step ((validationTM (n := 0)).initCfg input) =
      some started := rfl
  obtain ⟨c, hreach, hhalt, hpost⟩ :=
    validationTM_started_framed_reachesIn_internal input work₀ output₀
      (fun i => Fin.elim0 i) TM.outAcc_nil_init
  refine ⟨c, input.length + 2, le_rfl, .step hstep hreach, hhalt, ?_⟩
  rcases hpost with ⟨_, _, _, _, _, hcell, htail⟩
  constructor
  · intro i hi
    have hi0 : i = 0 := by simpa [satSyntaxWord] using hi
    subst i
    simpa [satSyntaxWord, validEncoding_eq_decode?_isSome_internal] using hcell
  · exact htail 2 (by decide)

/-- The syntax word has an actual polynomial-time deterministic-machine certificate. -/
theorem satSyntaxWord_mem_FP : satSyntaxWord ∈ FP := by
  obtain ⟨d, hd⟩ := (PolyBound.id.add (PolyBound.const 2)).bigO
  exact ⟨d, 0, validationTM, fun n => n + 2, satSyntaxWord_computesInTime, hd⟩

/-- The machine certificate can be used in Cobham constructions of payoff serializers. -/
theorem satSyntaxWord_cobham :
    Cobham (fun v : Fin 1 → List Bool => satSyntaxWord (v 0)) :=
  FP_subset_CobhamFP satSyntaxWord_mem_FP

end GameTheory.Complexity.Backend
