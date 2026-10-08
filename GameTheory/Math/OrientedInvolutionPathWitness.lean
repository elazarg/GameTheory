import GameTheory.Math.OrientedInvolutionPath
import GameTheory.Math.EndOfLineNormalization

/-! Raw End-of-Line witnesses on alternating involution paths.
Source pointer consistency rules out an outgoing inconsistency at the origin;
every remaining witness is an incident-edge fixed point away from that source. -/
namespace GameTheory.Math.OrientedInvolutionPath
variable {α : Type*}

/-- For a source-calibrated alternating path, a raw witness is exactly a
terminal distinct from the source. -/
theorem rawWitness_iff (flip turn : α → α) (color : α → Bool)
    (hflip : Function.Involutive flip) (hturn : Function.Involutive turn)
    (hflip_ne : ∀ x, flip x ≠ x)
    (hflip_color : ∀ x, color (flip x) = !(color x))
    (hturn_color : ∀ x, turn x ≠ x → color (turn x) = !(color x))
    (origin : α) (hfixed : turn origin = origin) (hcolor : color origin = true) (x : α) :
    EndOfLine.RawWitness (predecessor flip turn color) (successor flip turn color) origin x ↔
      turn x = x ∧ x ≠ origin := by
  have hsource := (source_pointers flip turn color hflip hflip_ne hflip_color origin hfixed hcolor).2.2
  constructor
  · intro hw
    refine ⟨(inverse_failure_iff flip turn color hflip hturn hflip_ne hflip_color hturn_color x).mp
      (hw.elim Or.inl (fun h => Or.inr h.2)), ?_⟩
    intro hx
    subst x
    exact hw.elim (fun h => h hsource) (fun h => h.1 rfl)
  · rintro ⟨ht, hn⟩
    exact EndOfLine.endpoint_rawWitness _ _ hn
      ((isEndpoint_iff flip turn color hflip hturn hflip_ne hflip_color hturn_color x).mpr ht)

end GameTheory.Math.OrientedInvolutionPath
