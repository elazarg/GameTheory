import GameTheoryComplexity.Backend.BrouwerProblem
import GameTheoryComplexity.Backend.BrouwerPointMachine
import GameTheoryComplexity.Backend.BrouwerResidualMachine
import Complexitylib.Classes.P.NormalForm

/-! A polynomial-time verifier locates a rational point, queries the three
corner colors, and checks its exact affine residual. It validates both the
point fields and the outer input pair before accepting the continuous-map
approximate fixed-point relation. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner GameTheory.Math.Brouwer

private theorem routingLEFlag_flag (x y : List Bool) :
    routingLEFlag x y = [true] ∨ routingLEFlag x y = [false] := by
  rw [routingLEFlag_value]
  by_cases h : Nat.fromBitsLE x ≤ Nat.fromBitsLE y <;> simp [h]

/-- Validate the two fixed-width numerators against the closed-square bound. -/
def brouwerPointAcceptFlag (ruler word : List Bool) : List Bool :=
  andBit (lenEqFlag word (brouwerPointRuler ruler ++ brouwerPointRuler ruler))
    (andBit (routingLEFlag (brouwerPointXBits ruler word) (brouwerPointBoundBits ruler))
      (routingLEFlag (brouwerPointYBits ruler word) (brouwerPointBoundBits ruler)))

theorem brouwerPointAcceptFlag_flag (ruler word : List Bool) :
    brouwerPointAcceptFlag ruler word = [true] ∨
      brouwerPointAcceptFlag ruler word = [false] := andBit_flag _ _

theorem brouwerPointAcceptFlag_accept (ruler word : List Bool) :
    brouwerPointAcceptFlag ruler word = [true] ↔
      ∃ p, decodeBrouwerPoint ruler.length word = some p := by
  rw [brouwerPointAcceptFlag,
    andBit_eq_true_iff (lenEqFlag_flag _ _) (andBit_flag _ _),
    andBit_eq_true_iff (routingLEFlag_flag _ _) (routingLEFlag_flag _ _),
    lenEqFlag_eq_true_iff, routingLEFlag_value, routingLEFlag_value]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq, brouwerPointBoundBits_value,
    List.length_append, brouwerPointRuler_length, brouwerPointXBits, brouwerPointYBits]
  have hwidth : pointCoordinateWidth ruler.length + pointCoordinateWidth ruler.length =
      pointWordWidth ruler.length := by simp [pointWordWidth, two_mul]
  rw [hwidth]
  unfold decodeBrouwerPoint
  dsimp only
  split_ifs with h
  · simp [h]
  · simp [h]

theorem brouwerPointAcceptFlagFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => brouwerPointAcceptFlag (ruler z) (word z)) ∈ FP := by
  have hpr := brouwerPointRulerFn_mem_FP hr
  have hwidth := appendFn_mem_FP hpr hpr
  have hlen : (fun z => lenEqFlag (word z)
      (brouwerPointRuler (ruler z) ++ brouwerPointRuler (ruler z))) ∈ FP :=
    andBitFn_mem_FP (lenLeFlagFn_mem_FP hw hwidth) (lenLeFlagFn_mem_FP hwidth hw)
  exact andBitFn_mem_FP hlen
    (andBitFn_mem_FP
      (routingLEFlagFn_mem_FP (brouwerPointXBitsFn_mem_FP hr hw)
        (brouwerPointBoundBitsFn_mem_FP hr))
      (routingLEFlagFn_mem_FP (brouwerPointYBitsFn_mem_FP hr hw)
        (brouwerPointBoundBitsFn_mem_FP hr)))

private def brouwerResidualFlag (input word : List Bool) : List Bool :=
  let ruler := pairFst input
  let triangle := brouwerLocateWord ruler word
  let query := evaluateCircuitVector (pairSnd input)
  residualVerdict
    (brouwerOffsetBits ruler (brouwerPointXBits ruler word))
    (brouwerOffsetBits ruler (brouwerPointYBits ruler word))
    (gridCornerColor ruler query triangle 0)
    (gridCornerColor ruler query triangle 1)
    (gridCornerColor ruler query triangle 2)

private theorem brouwerResidualFlag_flag (input word : List Bool) :
    brouwerResidualFlag input word = [true] ∨
      brouwerResidualFlag input word = [false] := residualVerdict_flag _ _ _ _ _

private theorem brouwerResidualFlag_accept {input word : List Bool} {p : ℕ × ℕ}
    (hd : decodeBrouwerPoint (pairFst input).length word = some p) :
    brouwerResidualFlag input word = [true] ↔
      |(sixthDisplacement (spernerColor input) (2 ^ (pairFst input).length) p.1 p.2).1|
        ≤ 1 / 6 ∧
      |(sixthDisplacement (spernerColor input) (2 ^ (pairFst input).length) p.1 p.2).2|
        ≤ 1 / 6 := by
  obtain ⟨_, hx, hy, hxx, hyy⟩ := decodeBrouwerPoint_properties hd
  have hv := sixthTriangle_valid (Nat.two_pow_pos _) hx hy
  have hxx' : Nat.fromBitsLE (brouwerPointXBits (pairFst input) word) = p.1 := by
    simpa only [brouwerPointXBits, brouwerPointRuler_length] using hxx
  have hyy' : Nat.fromBitsLE (brouwerPointYBits (pairFst input) word) = p.2 := by
    simpa only [brouwerPointYBits, brouwerPointRuler_length] using hyy
  let rx : Fin 7 := ⟨sixthOffset (2 ^ (pairFst input).length) p.1,
    by have h := (sixthCellIndex_bounds (Nat.two_pow_pos _) hx).2.1; omega⟩
  let ry : Fin 7 := ⟨sixthOffset (2 ^ (pairFst input).length) p.2,
    by have h := (sixthCellIndex_bounds (Nat.two_pow_pos _) hy).2.1; omega⟩
  have hex : brouwerOffsetBits (pairFst input) (brouwerPointXBits (pairFst input) word) =
      encodeResidualOffset rx := by
    rw [brouwerOffsetBits_eq _ _ (by simpa [hxx'] using hx), hxx']
    rfl
  have hey : brouwerOffsetBits (pairFst input) (brouwerPointYBits (pairFst input) word) =
      encodeResidualOffset ry := by
    rw [brouwerOffsetBits_eq _ _ (by simpa [hyy'] using hy), hyy']
    rfl
  unfold brouwerResidualFlag
  dsimp only
  rw [brouwerLocateWord_eq hd,
    gridCornerColor_encode _ _ _ 0 hv, gridCornerColor_encode _ _ _ 1 hv,
    gridCornerColor_encode _ _ _ 2 hv, hex, hey, residualVerdict_accept]
  change SixthGridSmallResidual rx ry _ _ _ ↔ _
  unfold SixthGridSmallResidual sixthGridDisplacement sixthDisplacement sixthWeights
  dsimp only [rx, ry]
  split_ifs <;> rfl

/-- Validate point fields and their exact map residual. -/
def brouwerVerdict (input word : List Bool) : List Bool :=
  andBit (brouwerPointAcceptFlag (pairFst input) word) (brouwerResidualFlag input word)

theorem brouwerVerdict_flag (input word : List Bool) :
    brouwerVerdict input word = [true] ∨ brouwerVerdict input word = [false] :=
  andBit_flag _ _

theorem brouwerVerdict_accept (input word : List Bool) :
    brouwerVerdict input word = [true] ↔ brouwerRelation input word := by
  rw [brouwerVerdict,
    andBit_eq_true_iff (brouwerPointAcceptFlag_flag _ _)
      (brouwerResidualFlag_flag _ _),
    brouwerPointAcceptFlag_accept, brouwerRelation_local_iff]
  constructor
  · rintro ⟨⟨p, hd⟩, hr⟩
    exact ⟨p, hd, (brouwerResidualFlag_accept hd).mp hr⟩
  · rintro ⟨p, hd, hr⟩
    exact ⟨⟨p, hd⟩, (brouwerResidualFlag_accept hd).mpr hr⟩

private theorem verdict_pair_mem_FP :
    (fun z => brouwerVerdict (pairFst z) (pairSnd z)) ∈ FP := by
  have hr := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hw := pairSnd_mem_FP
  have ht := brouwerLocateWordFn_mem_FP hr hw
  have h₀ := gridCornerColorUniformFn_mem_FP 0 hr hs ht _ evaluateCircuitVector_pair_mem_FP
  have h₁ := gridCornerColorUniformFn_mem_FP 1 hr hs ht _ evaluateCircuitVector_pair_mem_FP
  have h₂ := gridCornerColorUniformFn_mem_FP 2 hr hs ht _ evaluateCircuitVector_pair_mem_FP
  exact andBitFn_mem_FP (brouwerPointAcceptFlagFn_mem_FP hr hw)
    (residualVerdictFn_mem_FP
      (brouwerOffsetBitsFn_mem_FP hr (brouwerPointXBitsFn_mem_FP hr hw))
      (brouwerOffsetBitsFn_mem_FP hr (brouwerPointYBitsFn_mem_FP hr hw)) h₀ h₁ h₂)

/-- Reject malformed outer pairs before checking their approximate fixed point. -/
def brouwerPairedVerdict (z : List Bool) : List Bool :=
  andBit (eqFlag z (pair (pairFst z) (pairSnd z)))
    (brouwerVerdict (pairFst z) (pairSnd z))

theorem brouwerPairedVerdict_mem_FP : brouwerPairedVerdict ∈ FP :=
  andBitFn_mem_FP
    (eqFlagFn_mem_FP id_mem_FP (pairFn_mem_FP pairFst_mem_FP pairSnd_mem_FP))
    verdict_pair_mem_FP

theorem exists_brouwerPairedVerdict_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime brouwerPairedVerdict bound.eval :=
  mem_FP_iff_computesInTime_polynomial.mp brouwerPairedVerdict_mem_FP

theorem brouwerPairedVerdict_accept (z : List Bool) :
    brouwerPairedVerdict z = [true] ↔ z ∈ pairLang brouwerRelation := by
  rw [brouwerPairedVerdict,
    andBit_eq_true_iff (eqFlag_flag _ _) (brouwerVerdict_flag _ _),
    eqFlag_eq_true_iff, brouwerVerdict_accept]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨pairFst z, pairSnd z, hz, h⟩
  · rintro ⟨input, word, rfl, h⟩
    simp only [pairFst_pair, pairSnd_pair]
    exact ⟨trivial, h⟩

/-- Linear witness balance and the polynomial-time verifier give FNP membership. -/
theorem brouwerRelation_mem_FNP : brouwerRelation ∈ FNP := by
  refine ⟨brouwerRelation_polyBalanced,
    mem_P_of_decisionFn brouwerPairedVerdict_mem_FP ?_⟩
  intro z
  rw [← brouwerPairedVerdict_accept]
  rcases andBit_flag (eqFlag z (pair (pairFst z) (pairSnd z)))
    (brouwerVerdict (pairFst z) (pairSnd z)) with h | h <;>
    simp [brouwerPairedVerdict, h]

end GameTheory.Complexity.Backend
