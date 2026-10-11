import GameTheory.Analysis.ComponentCompletion
noncomputable section
namespace GameTheory.Tests.ComponentCompletion
open GameTheory GameTheory.Math.Probability

private abbrev form : GameForm Bool :=
  GameForm.deterministic { Strategy := fun _ : Bool => ℕ, Outcome := Bool → ℕ } id

private def utility (outcome : Bool → ℕ) (who : Bool) : ℝ :=
  if who then -(outcome who : ℝ) else (outcome who : ℝ)

private def component (_who : Bool) (part : Bool) : PMF ℕ := PMF.pure (if part then 1 else 0)

private theorem component_integrable (choice : Bool → Bool) (who : Bool) :
    PayoffIntegrable (form.mixed.play fun player => component player (choice player))
      (fun outcome => utility outcome who) := by
  change PayoffIntegrable (form.mixed.play (form.purify (fun player => if choice player then 1
    else 0))) _
  rw [GameForm.mixed_play_purify]
  exact payoffIntegrable_pure _ _

/-- Finite component menus suffice with infinite underlying strategies and outcomes,
and utilities unbounded over the entire outcome carrier. -/
theorem best_component_mixtures :
    ∃ weights : Bool → PMF Bool, ∀ who (alternative : PMF Bool),
      expectedUtility utility who (form.mixed.play
        (Profile.update (sig := form.sig.mixed) (fun player => (weights player).bind (component
          player))
          who (alternative.bind (component who)))) ≤
        expectedUtility utility who (form.mixed.play fun player => (weights player).bind
          (component player)) :=
  exists_component_bestResponses (F := form) utility component component_integrable

/-- Distinct agents can share mixture weights without narrowing the underlying game carriers. -/
theorem shared_weight_mixtures :
    ∃ weights : Unit → PMF Bool, ∀ (alternative : Unit → PMF Bool) (groupIndex : Unit),
      ∑ who ∈ Finset.univ.filter (fun _ : Bool => () = groupIndex),
        (expectedUtility utility who (form.mixed.play
            (Profile.update (sig := form.sig.mixed)
              (fun player => (weights ()).bind (component player))
              who ((alternative ()).bind (component who)))) -
          expectedUtility utility who (form.mixed.play fun player => (weights ()).bind (component
            player))) ≤ 0 := by
  have witness :=  exists_bestResponses_with_shared_mixture_weights (F := form) (Part := fun _ :
    Unit => Bool)
    (fun _ => ()) utility component component_integrable (fun _ _ => 1) (fun _ =>
      continuousOn_const)
  simpa only [one_mul] using witness

end GameTheory.Tests.ComponentCompletion
