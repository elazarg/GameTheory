import CS.TraceLanguage

set_option autoImplicit false

namespace CS
namespace Transition

variable {α β σ τ : Type*}

/-- Forward simulation between same-labeled transition systems. -/
structure ForwardSimulation
    (step₁ : α → σ → σ → Prop)
    (step₂ : α → τ → τ → Prop)
    (R : σ → τ → Prop) : Prop where
  step :
    ∀ {a : α} {s s' : σ} {t : τ},
      R s t → step₁ a s s' → ∃ t', step₂ a t t' ∧ R s' t'

namespace ForwardSimulation

theorem reachBy
    {step₁ : α → σ → σ → Prop}
    {step₂ : α → τ → τ → Prop}
    {R : σ → τ → Prop}
    (sim : ForwardSimulation step₁ step₂ R)
    {w : List α} {s s' : σ} {t : τ}
    (hR : R s t)
    (h : ReachBy step₁ w s s') :
    ∃ t', ReachBy step₂ w t t' ∧ R s' t' := by
  induction h generalizing t with
  | nil s =>
      exact ⟨t, ReachBy.nil t, hR⟩
  | @cons a rest s u s' hs hrest ih =>
      rcases sim.step hR hs with ⟨t1, ht1, hR1⟩
      rcases ih hR1 with ⟨t2, h2, hR2⟩
      exact ⟨t2, ReachBy.cons ht1 h2, hR2⟩

theorem tracesFrom_subset
    {step₁ : α → σ → σ → Prop}
    {step₂ : α → τ → τ → Prop}
    {R : σ → τ → Prop}
    (sim : ForwardSimulation step₁ step₂ R)
    {s : σ} {t : τ}
    (hR : R s t) :
    Trace.TracesFrom step₁ s ⊆ Trace.TracesFrom step₂ t := by
  intro w hw
  rcases hw with ⟨s', hs'⟩
  rcases sim.reachBy hR hs' with ⟨t', ht', _⟩
  exact ⟨t', ht'⟩

end ForwardSimulation

/-- Bisimulation between same-labeled transition systems. -/
structure Bisimulation
    (step₁ : α → σ → σ → Prop)
    (step₂ : α → τ → τ → Prop)
    (R : σ → τ → Prop) : Prop where
  forth : ForwardSimulation step₁ step₂ R
  back : ForwardSimulation step₂ step₁ (fun t s => R s t)

namespace Bisimulation

theorem tracesFrom_eq
    {step₁ : α → σ → σ → Prop}
    {step₂ : α → τ → τ → Prop}
    {R : σ → τ → Prop}
    (bis : Bisimulation step₁ step₂ R)
    {s : σ} {t : τ}
    (hR : R s t) :
    Trace.TracesFrom step₁ s = Trace.TracesFrom step₂ t := by
  apply Set.Subset.antisymm
  · exact bis.forth.tracesFrom_subset hR
  · exact bis.back.tracesFrom_subset hR

end Bisimulation

/-- Homomorphic simulation by state/label maps. -/
structure HomSimulation
    (step₁ : α → σ → σ → Prop)
    (step₂ : β → τ → τ → Prop) where
  stateMap : σ → τ
  labelMap : α → β
  step :
    ∀ {a : α} {s s' : σ},
      step₁ a s s' → step₂ (labelMap a) (stateMap s) (stateMap s')

namespace HomSimulation

theorem reachBy_map
    {step₁ : α → σ → σ → Prop}
    {step₂ : β → τ → τ → Prop}
    (sim : HomSimulation step₁ step₂)
    {w : List α} {s t : σ}
    (h : ReachBy step₁ w s t) :
    ReachBy step₂ (w.map sim.labelMap) (sim.stateMap s) (sim.stateMap t) := by
  induction h with
  | nil s =>
      simp
  | @cons a rest s u t hs hrest ih =>
      simpa using ReachBy.cons (sim.step hs) ih

end HomSimulation

end Transition
end CS
