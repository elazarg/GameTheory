module

public import GameTheoryComplexity.Backend.BrouwerProblem
public import GameTheoryComplexity.Backend.BrouwerPointMachine
public import GameTheoryComplexity.Sperner

@[expose] public section

/-! Point answers are located in their containing triangle before decoding.
Conversely, a trichromatic triangle supplies its rational fixed barycenter.
Both maps operate on binary fields, without enumerating the exponential grid. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime GameTheory.Math.Sperner GameTheory.Math.Brouwer

/-- Every accepted rational point locates a valid trichromatic triangle. -/
theorem brouwerLocate_sound (input word : List Bool) (h : brouwerRelation input word) :
    spernerRelation input (brouwerLocate input word) := by
  obtain ⟨p, hd, hx, hy⟩ := (brouwerRelation_local_iff input word).mp h
  have hp := decodeBrouwerPoint_properties hd
  have ht := sixthTriangle_valid (Nat.two_pow_pos _) hp.2.1 hp.2.2.1
  refine ⟨sixthTriangle (2 ^ (CircuitWords.first input).length) p.1 p.2, ?_, ?_⟩
  · change decodeGridNode _ (brouwerLocateWord (CircuitWords.first input) word) = _
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
  · change decodeBrouwerPoint _ (brouwerBarycenterWord (CircuitWords.first input) word) = _
    rw [brouwerBarycenterWord_eq hd]
    exact decodeBrouwerPoint_encode _ _ hp.1 hp.2
  · rw [sixthDisplacement_barycenter _ ht,
      (triangleBarycenterDisplacement_eq_zero_iff _ _).mpr hc]
    norm_num

/-- Every continuous residual answer decodes to a Sperner answer under a native reduction. -/
theorem spernerToBrouwerReduction :
    Cslib.Complexity.SearchReducible encBits encBits spernerRelation brouwerRelation := by
  have htotal : Cslib.Complexity.IsTotalSearch brouwerRelation := by
    intro input
    obtain ⟨word, hw⟩ := GameTheory.Complexity.spernerRelation_total input
    exact ⟨brouwerBarycenter input word, brouwerBarycenter_sound input word hw⟩
  apply Cslib.Complexity.SearchReducible.of_isTotalSearch
    (f := id) (g := fun p : List Bool × List Bool => brouwerLocate p.1 p.2)
    htotal (id' (encIn := encBits))
    (brouwerLocate_polyTime (fst encBits encBits) (snd encBits encBits))
  intro input word hw
  exact brouwerLocate_sound input word hw

/-- Every Sperner triangle yields a continuous residual answer under a native reduction. -/
theorem brouwerToSpernerReduction :
    Cslib.Complexity.SearchReducible encBits encBits brouwerRelation spernerRelation := by
  apply Cslib.Complexity.SearchReducible.of_isTotalSearch
    (f := id) (g := fun p : List Bool × List Bool => brouwerBarycenter p.1 p.2)
    GameTheory.Complexity.spernerRelation_total (id' (encIn := encBits))
    (brouwerBarycenter_polyTime (fst encBits encBits) (snd encBits encBits))
  intro input word hw
  exact brouwerBarycenter_sound input word hw

end GameTheory.Complexity.Backend
