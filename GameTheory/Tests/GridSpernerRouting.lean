import GameTheory.Math.GridSpernerRoutingBoundary
import Mathlib.Tactic.IntervalCases

/-! Boundary entrance controls preserve disconnected endpoints while removing
only the known source witness. A power-of-two outer square cuts partial tiles. -/

namespace GameTheory.Tests.GridSpernerRouting

open GameTheory.Math.GridWire GameTheory.Math.Sperner GameTheory.Math.EndOfLine

private def fixtureS : ℕ → ℕ
  | 0 => 1
  | 2 => 3
  | 4 => 5
  | 5 => 4
  | i => i

private def fixtureP : ℕ → ℕ
  | 1 => 0
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | i => i

private theorem fixtureP_bound : ∀ i, i<8 → fixtureP i<8 := by
  intro i hi
  interval_cases i <;> decide

private theorem fixtureS_bound : ∀ i, i<8 → fixtureS i<8 := by
  intro i hi
  interval_cases i <;> decide

private def answer (t : GridTriangle) : Prop :=
  Trichromatic (gridSpernerRoutingColor 8 fixtureP fixtureS 2048 (corner t 0).1 (corner t 0).2)
    (gridSpernerRoutingColor 8 fixtureP fixtureS 2048 (corner t 1).1 (corner t 1).2)
    (gridSpernerRoutingColor 8 fixtureP fixtureS 2048 (corner t 2).1 (corner t 2).2)

private instance (t : GridTriangle) : Decidable (answer t) :=
  inferInstanceAs (Decidable (Trichromatic _ _ _))

example : ¬answer ⟨8,8,false⟩ := by decide

example : answer ⟨8,44,false⟩ ∧ answer ⟨8,80,false⟩ ∧ answer ⟨8,116,false⟩ := by decide

example : ¬answer ⟨8,152,false⟩ ∧ ¬answer ⟨8,188,false⟩ := by decide

example {t : GridTriangle} (hv : ValidTriangle 2048 t) (ht : answer t) :
    t.x=8 ∧ (t.y/36=1 ∨ t.y/36=2 ∨ t.y/36=3) := by
  obtain ⟨hx,hi,hne,he⟩ := gridSpernerRouting_endpoint_label
    (by decide) (by decide) (by decide) (by decide) (by decide)
    fixtureP_bound fixtureS_bound (by decide) (by decide) hv ht
  refine ⟨hx,?_⟩
  generalize hz : t.y/36=k at hi hne he ⊢
  interval_cases k <;> simp_all [IsEndpoint,HasPredecessor,HasSuccessor,fixtureP,fixtureS]

example (y : ℕ) (upper : Bool) (hy : y<2048) : ¬answer ⟨2047,y,upper⟩ := by
  intro ht
  have hb := gridSpernerRouting_trichromatic_strict
    (n:=8) (M:=2048) (P:=fixtureP) (S:=fixtureS) (by decide) (by decide)
    (t:=⟨2047,y,upper⟩) ⟨by change 2047<2048; decide,hy⟩ ht
  dsimp only at hb
  omega

example (x : ℕ) (upper : Bool) (hx : x<2048) : ¬answer ⟨x,2047,upper⟩ := by
  intro ht
  have hb := gridSpernerRouting_trichromatic_strict
    (n:=8) (M:=2048) (P:=fixtureP) (S:=fixtureS) (by decide) (by decide)
    (t:=⟨x,2047,upper⟩) ⟨hx,by change 2047<2048; decide⟩ ht
  dsimp only at hb
  omega

example : gridSpernerRoutingColor 8 fixtureP fixtureS 2048 0 0=0 ∧
    gridSpernerRoutingColor 8 fixtureP fixtureS 2048 2048 0=1 ∧
    gridSpernerRoutingColor 8 fixtureP fixtureS 2048 0 2048=2 ∧
    gridSpernerRoutingColor 8 fixtureP fixtureS 2048 2048 2048=2 := by decide

end GameTheory.Tests.GridSpernerRouting

