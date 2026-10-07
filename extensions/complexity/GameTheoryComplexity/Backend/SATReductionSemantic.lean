import GameTheory.Core.SatisfiabilityGameReduction
import GameTheory.Core.SatisfiabilityGameEncoding
import GameTheory.Finite.BimatrixTableProblem
import GameTheoryComplexity.Backend.SATGame

/-! The SAT reduction emits an explicit symmetric integer payoff table. Its
membership equivalence uses canonical mixed Nash and actual table decoding;
polynomial machine certificates are supplied separately. -/

noncomputable section

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Probability
open GameTheory.SatisfiabilityGame
open GameTheory.Finite.BimatrixTable

/-- The polynomially padded gadget's number of actions. -/
def satTableDimension (input : List Bool) : ℕ :=
  3 * (input.length + 1) + (input.length + 1) + 1

/-- Every table entry is computed from the explicit indexed game actions. -/
def satTablePayoff (input : List Bool) (i j : ℕ) : ℤ :=
  payoffInt (satIncidence input)
    (actionAt (input.length + 1) (input.length + 1) i)
    (actionAt (input.length + 1) (input.length + 1) j)

/-- The entire dense payoff table, including its dimension header. -/
def satTableReduction (input : List Bool) : List Bool :=
  encodeTable (satTableDimension input) (satTablePayoff input)

theorem satTableDimension_eq (input : List Bool) :
    satTableDimension input = 4 * (input.length + 1) + 1 := by
  unfold satTableDimension
  omega

/-- The explicit encoding's fixed-width tallies contain every gadget payoff. -/
theorem satTablePayoff_bound (input : List Bool) (i j : ℕ) :
    (satTablePayoff input i j).natAbs ≤ satTableDimension input + 2 := by
  have h := sat_payoffInt_bounds input
    (actionAt (input.length + 1) (input.length + 1) i)
    (actionAt (input.length + 1) (input.length + 1) j)
  change -((input.length : ℤ) + 3) ≤ satTablePayoff input i j ∧
    satTablePayoff input i j ≤ (input.length : ℤ) + 3 at h
  have hb : |satTablePayoff input i j| ≤ (satTableDimension input + 2 : ℕ) := by
    apply abs_le.mpr
    unfold satTableDimension
    constructor <;> omega
  rw [← Int.natCast_natAbs] at hb
  exact_mod_cast hb

/-- The dense reduction word has the explicit cubic table-encoding length. -/
theorem satTableReduction_length (input : List Bool) :
    (satTableReduction input).length = satTableDimension input + 1 +
      satTableDimension input * satTableDimension input * (2 * (satTableDimension input + 2)) :=
  encodeTable_length _ _ (fun i _ j _ => satTablePayoff_bound input i j)

/-- Encoded SAT membership is canonical payoff-constrained Nash existence in the gadget. -/
theorem sat_mem_iff_gadget_hasNash (input : List Bool) :
    input ∈ _root_.Complexity.SAT.language ↔
      (game (satIncidence input)).HasNashWithPayoffAtLeast (fun _ => 1) := by
  rw [sat_language_iff_satisfies, satisfiable_iff_hasNash_threshold]

/-- The indexed integer table is the gadget payoff renamed by its action enumeration. -/
theorem satTablePayoff_eq_renamed (input : List Bool) :
    (fun i j : Fin (satTableDimension input) => (satTablePayoff input i j : ℝ)) =
      (fun i j => payoff (satIncidence input)
        ((actionEquiv (input.length + 1) (input.length + 1)).symm i)
        ((actionEquiv (input.length + 1) (input.length + 1)).symm j)) := by
  funext i j
  have hi := actionAt_eq_symm (n := input.length + 1) (m := input.length + 1) i
  have hj := actionAt_eq_symm (n := input.length + 1) (m := input.length + 1) j
  simp only [satTablePayoff, payoff]
  rw [hi, hj]

/-- SAT reduces semantically to the actual language of decoded explicit payoff tables. -/
theorem sat_mem_iff_reduction_mem (input : List Bool) :
    input ∈ _root_.Complexity.SAT.language ↔
      satTableReduction input ∈ unitPayoffLanguage := by
  rw [sat_mem_iff_gadget_hasNash input]
  change (game (satIncidence input)).HasNashWithPayoffAtLeast (fun _ => 1) ↔
    (decodedGame (encodeTable (satTableDimension input) (satTablePayoff input))).HasNashWithPayoffAtLeast
      (fun _ => 1)
  rw [decodedGame_encodeTable _ _ (fun i _ j _ => satTablePayoff_bound input i j)]
  let A : Fin (satTableDimension input) → Fin (satTableDimension input) → ℝ :=
    fun i j => satTablePayoff input i j
  change (game (satIncidence input)).HasNashWithPayoffAtLeast (fun _ => 1) ↔
    (MatrixGame.bimatrixGame A (fun i j => A j i)).HasNashWithPayoffAtLeast (fun _ => 1)
  have hA : A = _ := satTablePayoff_eq_renamed input
  rw [hA]
  exact MatrixGame.hasNashWithPayoffAtLeast_map_equiv
    (actionEquiv (input.length + 1) (input.length + 1)) (payoff (satIncidence input))

end GameTheory.Complexity.Backend
