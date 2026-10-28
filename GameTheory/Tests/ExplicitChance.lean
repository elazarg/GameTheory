module

/-
# Explicit Nature and embedded chance

A public player move followed by a separate fair draw satisfies the explicit
chance certificate. Combining that move and draw in one stochastic transition
fails the certificate, even though it is a valid execution protocol.
-/

public import GameTheory.Protocol.ExplicitChance
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

noncomputable section

namespace GameTheory.Tests.ExplicitChance

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

/-- One player move, then a fair Nature draw, then termination. -/
@[reducible] def separated : ExecutionProtocol Unit where
  State := Option (Option Bool)
  Action _ := Unit
  init := none
  active state _ := state = none
  available _ _ := Set.univ
  terminal state := ∃ bit, state = some (some bit)
  step state _ := match state with
    | none => PMF.pure (some none)
    | some none => (uniformLaw Bool).map (fun bit => some (some bit))
    | some (some bit) => PMF.pure (some (some bit))
  progress := by
    intro state nonterminal
    cases state with
    | none => exact ⟨fun _ => some (), fun _ => ⟨rfl, Set.mem_univ _⟩⟩
    | some result =>
        cases result with
        | none => exact ⟨fun _ => none, fun _ => by simp⟩
        | some bit => exact False.elim (nonterminal ⟨bit, rfl⟩)

/-- Explicit chance allows nondegenerate random transitions at Nature states. -/
theorem separated_hasExplicitChance : separated.HasExplicitChance := by
  intro history active joint
  obtain ⟨who, active⟩ := active
  obtain ⟨state, trace⟩ := history
  change state = none at active
  subst state
  exact ⟨some none, rfl⟩

/-- The same player move instead contains the fair draw inside its transition. -/
@[reducible] def embedded : ExecutionProtocol Unit :=
  { separated with
    step := fun state joint =>
      if state = none then (uniformLaw Bool).map (fun bit => some (some bit))
      else separated.step state joint }

private def playerMove : {joint : Unit → Option Unit // embedded.Legal none joint} :=
  ⟨fun _ => some (), ⟨by simp, fun _ => ⟨rfl, Set.mem_univ _⟩⟩⟩

/-- Both hidden draw outcomes are possible after the player's one legal move. -/
private theorem embedded_supported (bit : Bool) :
    some (some bit) ∈ (embedded.step none playerMove).support := by
  simp only [embedded, ite_true, PMF.support_map]
  exact ⟨bit, mem_support_uniformLaw bit, rfl⟩

/-- A native stochastic player transition is rejected by the certificate. -/
theorem embedded_not_hasExplicitChance : ¬ embedded.HasExplicitChance := by
  apply embedded.not_hasExplicitChance_of_distinct_supported embedded.initHistory
    ⟨(), rfl⟩ playerMove (first := some (some false)) (second := some (some true))
  · simp
  · exact embedded_supported false
  · exact embedded_supported true

/-- The separated representation genuinely has both Nature outcomes. -/
theorem separated_chance_has_two_outcomes :
    ∃ joint : {joint : Unit → Option Unit // separated.Legal (some none) joint},
      some (some false) ∈ (separated.step (some none) joint).support ∧
        some (some true) ∈ (separated.step (some none) joint).support := by
  refine ⟨⟨fun _ => none, ⟨by simp, fun _ => by simp⟩⟩, ?_, ?_⟩
  all_goals
    rw [show separated.step (some none) _ =
      (uniformLaw Bool).map (fun bit => some (some bit)) from rfl, PMF.support_map]
  · exact ⟨false, mem_support_uniformLaw false, rfl⟩
  · exact ⟨true, mem_support_uniformLaw true, rfl⟩

end GameTheory.Tests.ExplicitChance
