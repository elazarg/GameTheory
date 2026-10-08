import GameTheory.Math.EndOfLine

/-! End-of-Line pointers obtained from two alternating involutions.
One involution exchanges the two sides of an edge and never fixes a point.
The other exchanges incident edges except at endpoints. A Boolean coloring
orients their alternating path components without assuming computational cost.
-/

namespace GameTheory.Math.OrientedInvolutionPath

variable {α : Type*}

/-- The outgoing pointer alternates between the two involutions according to color. -/
def successor (flip turn : α → α) (color : α → Bool) (x : α) : α :=
  if color x then flip x else turn x

/-- The incoming pointer uses the complementary involution. -/
def predecessor (flip turn : α → α) (color : α → Bool) (x : α) : α :=
  if color x then turn x else flip x

variable (flip turn : α → α) (color : α → Bool)
  (hflip : Function.Involutive flip) (hturn : Function.Involutive turn)
  (hflip_ne : ∀ x, flip x ≠ x)
  (hflip_color : ∀ x, color (flip x) = !(color x))
  (hturn_color : ∀ x, turn x ≠ x → color (turn x) = !(color x))

include hflip hturn hflip_ne hflip_color hturn_color

omit hflip_ne in
/-- The incoming pointer inverts every nonendpoint outgoing pointer. -/
theorem predecessor_successor (x : α) (hx : turn x ≠ x) :
    predecessor flip turn color (successor flip turn color x) = x := by
  cases hc : color x
  · simp only [successor, hc, Bool.false_eq_true, ↓reduceIte, predecessor,
      hturn_color x hx, Bool.not_false, hturn x]
  · simp only [successor, hc, ↓reduceIte, predecessor, hflip_color x,
      Bool.not_true, Bool.false_eq_true, hflip x]

omit hflip_ne in
/-- The outgoing pointer inverts every nonendpoint incoming pointer. -/
theorem successor_predecessor (x : α) (hx : turn x ≠ x) :
    successor flip turn color (predecessor flip turn color x) = x := by
  cases hc : color x
  · simp only [predecessor, hc, Bool.false_eq_true, ↓reduceIte, successor,
      hflip_color x, Bool.not_false, hflip x]
  · simp only [predecessor, hc, ↓reduceIte, successor, hturn_color x hx,
      Bool.not_true, Bool.false_eq_true, hturn x]

/-- A colored edge exists out of every interior point and every true-colored endpoint. -/
theorem hasSuccessor_iff (x : α) :
    EndOfLine.HasSuccessor (predecessor flip turn color) (successor flip turn color) x ↔
      color x = true ∨ turn x ≠ x := by
  cases hc : color x
  · by_cases hx : turn x = x
    · simp [EndOfLine.HasSuccessor, successor, hc, hx]
    · have hi := predecessor_successor flip turn color hflip hturn hflip_color hturn_color x hx
      exact iff_of_true ⟨by simpa [successor, hc] using hx, hi⟩ (Or.inr hx)
  · have hi : predecessor flip turn color (successor flip turn color x) = x := by
      simp [successor, predecessor, hc, hflip_color x, hflip x]
    exact iff_of_true ⟨by simpa [successor, hc] using hflip_ne x, hi⟩ (Or.inl rfl)

/-- A colored edge exists into every interior point and every false-colored endpoint. -/
theorem hasPredecessor_iff (x : α) :
    EndOfLine.HasPredecessor (predecessor flip turn color) (successor flip turn color) x ↔
      color x = false ∨ turn x ≠ x := by
  cases hc : color x
  · have hi : successor flip turn color (predecessor flip turn color x) = x := by
      simp [successor, predecessor, hc, hflip_color x, hflip x]
    exact iff_of_true ⟨by simpa [predecessor, hc] using hflip_ne x, hi⟩ (Or.inl rfl)
  · by_cases hx : turn x = x
    · simp [EndOfLine.HasPredecessor, predecessor, hc, hx]
    · have hi := successor_predecessor flip turn color hflip hturn hflip_color hturn_color x hx
      exact iff_of_true ⟨by simpa [predecessor, hc] using hx, hi⟩ (Or.inr hx)

/-- Exactly the fixed points of the incident-edge involution are graph endpoints. -/
theorem isEndpoint_iff (x : α) :
    EndOfLine.IsEndpoint (predecessor flip turn color) (successor flip turn color) x ↔
      turn x = x := by
  rw [EndOfLine.IsEndpoint, hasSuccessor_iff flip turn color hflip hturn hflip_ne
      hflip_color hturn_color, hasPredecessor_iff flip turn color hflip hturn hflip_ne
      hflip_color hturn_color]
  cases color x <;> simp

/-- A failed pointer inverse occurs precisely at an incident-edge fixed point. -/
theorem inverse_failure_iff (x : α) :
    (predecessor flip turn color (successor flip turn color x) ≠ x ∨
      successor flip turn color (predecessor flip turn color x) ≠ x) ↔ turn x = x := by
  by_cases hx : turn x = x
  · cases hc : color x <;>
      simp [successor, predecessor, hc, hx, hflip_color x, hflip x, hflip_ne x]
  · rw [predecessor_successor flip turn color hflip hturn hflip_color hturn_color x hx,
      successor_predecessor flip turn color hflip hturn hflip_color hturn_color x hx]
    simp [hx]

omit hturn hturn_color in
/-- A true-colored fixed point is a source with a nontrivial outgoing edge. -/
theorem source_pointers (origin : α) (hfixed : turn origin = origin)
    (hcolor : color origin = true) :
    predecessor flip turn color origin = origin ∧
      successor flip turn color origin ≠ origin ∧
      predecessor flip turn color (successor flip turn color origin) = origin := by
  refine ⟨by simp [predecessor, hcolor, hfixed], ?_, ?_⟩
  · simpa only [successor, hcolor, ↓reduceIte] using hflip_ne origin
  · simp [successor, predecessor, hcolor, hflip_color origin, hflip origin]

/-- Finite alternating paths with a known source have another incident-edge fixed point. -/
theorem exists_fixedPoint_ne_origin [Fintype α] [DecidableEq α]
    (origin : α) (hfixed : turn origin = origin) (hcolor : color origin = true) :
    ∃ x, x ≠ origin ∧ turn x = x := by
  obtain ⟨hp, hs, hlink⟩ := source_pointers flip turn color hflip hflip_ne hflip_color
    origin hfixed hcolor
  obtain ⟨x, hx, he⟩ := EndOfLine.exists_endpoint_ne_origin
    (predecessor flip turn color) (successor flip turn color) origin hp hs hlink
  exact ⟨x, hx, (isEndpoint_iff flip turn color hflip hturn hflip_ne hflip_color
    hturn_color x).mp he⟩

end GameTheory.Math.OrientedInvolutionPath
