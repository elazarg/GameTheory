import GameTheoryComplexity.Backend.BrouwerProblem
import GameTheoryComplexity.Backend.BrouwerPointMachine
import GameTheoryComplexity.Sperner

/-! Point answers are located in their containing triangle before decoding.
Conversely, a trichromatic triangle supplies its rational fixed barycenter.
Both maps operate on binary fields, without enumerating the exponential grid. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity GameTheory.Math.Sperner GameTheory.Math.Brouwer

/-- Every accepted rational point locates a valid trichromatic triangle. -/
theorem brouwerLocate_sound (input word : List Bool) (h : brouwerRelation input word) :
    spernerRelation input (brouwerLocate input word) := by
  obtain ⟨p, hd, hx, hy⟩ := (brouwerRelation_local_iff input word).mp h
  have hp := decodeBrouwerPoint_properties hd
  have ht := sixthTriangle_valid (Nat.two_pow_pos _) hp.2.1 hp.2.2.1
  refine ⟨sixthTriangle (2 ^ (pairFst input).length) p.1 p.2, ?_, ?_⟩
  · change decodeGridNode _ (brouwerLocateWord (pairFst input) word) = _
    rw [brouwerLocateWord_eq hd]
    exact decodeGridNode_encode _ _ (fun t he => by cases he; exact ht)
  · exact weightedDisplacement_small_implies_trichromatic _ _ _ _ _ _
      (sixthWeights_sum _ _ _) hx hy

/-- Every Sperner answer emits an accepted point with an actual zero residual. -/
theorem brouwerBarycenter_sound (input word : List Bool) (h : spernerRelation input word) :
    brouwerRelation input (brouwerBarycenter input word) := by
  obtain ⟨t, hd, hc⟩ := h
  have ht := decodeGridNode_valid hd t rfl
  have hp := sixthBarycenterNumerators_bounds ht
  apply (brouwerRelation_local_iff _ _).mpr
  refine ⟨sixthBarycenterNumerators t, ?_, ?_⟩
  · change decodeBrouwerPoint _ (brouwerBarycenterWord (pairFst input) word) = _
    rw [brouwerBarycenterWord_eq hd]
    exact decodeBrouwerPoint_encode _ _ hp.1 hp.2
  · rw [sixthDisplacement_barycenter _ ht,
      (triangleBarycenterDisplacement_eq_zero_iff _ _).mpr hc]
    norm_num

/-- The continuous point relation receives Sperner hardness, preserving every point answer. -/
def spernerToBrouwerReduction : SearchReduction spernerRelation brouwerRelation where
  instanceMap := id
  instanceMap_mem_FP := id_mem_FP
  decode := fun v => brouwerLocate (v 0) (v 1)
  decode_mem_FPn := brouwerLocate_mem_FPn
  sound := brouwerLocate_sound

/-- Computing a Sperner triangle supplies a rational point for continuous residual search. -/
def brouwerToSpernerReduction : SearchReduction brouwerRelation spernerRelation where
  instanceMap := id
  instanceMap_mem_FP := id_mem_FP
  decode := fun v => brouwerBarycenter (v 0) (v 1)
  decode_mem_FPn := brouwerBarycenter_mem_FPn
  sound := brouwerBarycenter_sound

end GameTheory.Complexity.Backend
