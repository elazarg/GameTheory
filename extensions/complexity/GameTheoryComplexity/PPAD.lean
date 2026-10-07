import GameTheoryComplexity.Backend.RawEndOfLineReduction

/-! Polynomial search classification through the standard asymmetric End-of-Line
relation. Verifiability and balance are independent of solution-preserving
reductions, so membership includes the source's FNP certificate. -/

namespace GameTheory.Complexity

open _root_.Complexity
open Backend

/-- Polynomially verified search problems reducing to standard End-of-Line. -/
def PPAD : Set (List Bool → List Bool → Prop) :=
  {R | R ∈ FNP ∧ Nonempty (SearchReduction R rawEndOfLineRelation)}

/-- Every PPAD problem has short, efficiently verified witnesses and is total. -/
theorem PPAD.mem_TFNP {R : List Bool → List Bool → Prop} (h : R ∈ PPAD) : R ∈ TFNP := by
  obtain ⟨a⟩ := h.2
  exact a.mem_TFNP h.1 rawEndOfLineRelation_mem_TFNP

/-- A certified reduction transports membership when source FNP is supplied. -/
theorem PPAD.of_reduction {R T : List Bool → List Bool → Prop}
    (a : SearchReduction R T) (hR : R ∈ FNP) (hT : T ∈ PPAD) : R ∈ PPAD := by
  obtain ⟨b⟩ := hT.2
  exact ⟨hR, ⟨a.trans b⟩⟩

/-- Every PPAD problem reduces to a hard relation. -/
def PPADHard (R : List Bool → List Bool → Prop) : Prop :=
  ∀ T, T ∈ PPAD → Nonempty (SearchReduction T R)

/-- A complete relation belongs to PPAD and receives all of its search reductions. -/
def PPADComplete (R : List Bool → List Bool → Prop) : Prop :=
  R ∈ PPAD ∧ PPADHard R

/-- Standard End-of-Line is complete for the class it defines. -/
theorem rawEndOfLineRelation_PPADComplete : PPADComplete rawEndOfLineRelation :=
  ⟨⟨rawEndOfLineRelation_mem_FNP, ⟨SearchReduction.refl _⟩⟩, fun _ h => h.2⟩

/-- Consistent-edge endpoint search is PPAD-hard through a certified identity
instance map and source-aware solution decoder. Membership requires a separate
efficient circuit-instance normalization theorem. -/
theorem endOfLineRelation_PPADHard : PPADHard endOfLineRelation := by
  intro T hT
  obtain ⟨a⟩ := hT.2
  exact ⟨a.trans rawToEndpointReduction⟩

end GameTheory.Complexity
