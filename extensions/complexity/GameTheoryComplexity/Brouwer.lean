import GameTheoryComplexity.Backend.BrouwerReduction
import GameTheoryComplexity.Backend.BrouwerVerifier

/-! PPAD-completeness of approximate fixed-point search for succinct continuous
triangular maps of the unit square. Answers encode arbitrary rational output
grid points at denominator six times the grid size. The acceptance tolerance is
the actual coordinate residual at that point, not distance to an exact fixed
point. Color circuits determine the locally evaluable continuous interpolation. -/

namespace GameTheory.Complexity

open _root_.Complexity Backend GameTheory.Math.Brouwer

/-- Every serialized instance represents a globally continuous map. -/
theorem brouwerInstance_continuous (input : List Bool) :
    Continuous (normalizedGridMap (spernerColor input) (2 ^ (pairFst input).length)) :=
  continuous_normalizedGridMap _ _

/-- Canonical boundary colors make every represented map preserve the unit square. -/
theorem brouwerInstance_mem_unitSquare (input : List Bool) {p : ℝ × ℝ}
    (hp : InRealGridSquare 1 p) :
    InRealGridSquare 1
      (normalizedGridMap (spernerColor input) (2 ^ (pairFst input).length) p) :=
  normalizedGridMap_mem_unitSquare
    (GameTheory.Math.Sperner.standardGridColor_boundary _ _ (Nat.two_pow_pos _))
    (Nat.two_pow_pos _) hp

/-- Polynomially verified continuous residual search reduces to standard End-of-Line. -/
theorem brouwerRelation_mem_PPAD : brouwerRelation ∈ PPAD :=
  PPAD.of_reduction brouwerToSpernerReduction brouwerRelation_mem_FNP
    spernerRelation_mem_PPAD

/-- Every PPAD search problem reduces to continuous residual search. -/
theorem brouwerRelation_PPADHard : PPADHard brouwerRelation := by
  intro T hT
  obtain ⟨a⟩ := spernerRelation_PPADHard T hT
  exact ⟨a.trans spernerToBrouwerReduction⟩

/-- Approximate fixed-point search for the succinct continuous square maps is PPAD-complete. -/
theorem brouwerRelation_PPADComplete : PPADComplete brouwerRelation :=
  ⟨brouwerRelation_mem_PPAD, brouwerRelation_PPADHard⟩

/-- All instances have short, efficiently verified rational-point answers. -/
theorem brouwerRelation_mem_TFNP : brouwerRelation ∈ TFNP :=
  PPAD.mem_TFNP brouwerRelation_mem_PPAD

/-- Canonical boundary enforcement gives a point answer for every serialized input. -/
theorem brouwerRelation_total (input : List Bool) : ∃ word, brouwerRelation input word :=
  brouwerRelation_mem_TFNP.2 input

end GameTheory.Complexity
