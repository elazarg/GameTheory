import GameTheory.Model.SemanticForm
import Semantics.Simulation

/-!
# GameTheory.Model.Simulation

Semantic simulation and bisimulation notions for source-language operational
semantics compiled into `InfoModel`.

`NativeInfoHomSimulation` is the general map-based notion:
- source labels may differ from compiled joint actions
- source states map into compiled latent states
- public and player-local observations are preserved

`NativeInfoBisimulation` is the same-label strong form:
- source labels are already compiled joint actions
- source states are equivalent to compiled latent states
- source and compiled steps are logically equivalent
- public and player-local observations are preserved
-/

namespace GameTheory

open Semantics.Transition

variable {ι : Type}

/-- Map-based simulation from a native source semantics into a compiled
`InfoModel`. -/
structure NativeInfoHomSimulation
    {α σ τ : Type} {Act : ι → Type}
    (step : α → σ → σ → Prop)
    (s0 : σ)
    (I : InfoModel ι τ Act)
    (publicView : σ → I.Public)
    (observe : (i : ι) → σ → I.Obs i) where
  stateMap : σ → τ
  labelMap : α → I.JointAction
  init : stateMap s0 = I.init
  step :
    ∀ {a : α} {s t : σ},
      step a s t →
      I.step (labelMap a) (stateMap s) (stateMap t)
  publicView_eq :
    ∀ s, I.publicView (stateMap s) = publicView s
  observe_eq :
    ∀ i s, I.observe i (stateMap s) = observe i s

namespace NativeInfoHomSimulation

variable {α σ τ : Type} {Act : ι → Type}
variable {step : α → σ → σ → Prop}
variable {s0 : σ}
variable {I : InfoModel ι τ Act}
variable {publicView : σ → I.Public}
variable {observe : (i : ι) → σ → I.Obs i}

/-- Trace-level reachability transport induced by a native-info simulation. -/
theorem reachBy_map
    (sim : NativeInfoHomSimulation step s0 I publicView observe)
    {w : List α} {s t : σ}
    (h : ReachBy step w s t) :
    ReachBy I.step (w.map sim.labelMap) (sim.stateMap s) (sim.stateMap t) := by
  let hsim : Semantics.Transition.HomSimulation step I.step :=
    { stateMap := sim.stateMap
      labelMap := sim.labelMap
      step := by
        intro a s t hs
        exact sim.step hs }
  simpa using Semantics.Transition.HomSimulation.reachBy_map hsim h

end NativeInfoHomSimulation

/-- Same-label bisimulation from a native source semantics into a compiled
`InfoModel`. This is the strong structural notion used when compilation keeps
the joint action labels unchanged. -/
structure NativeInfoBisimulation
    {σ τ : Type} {Act : ι → Type}
    {I : InfoModel ι τ Act}
    (step : I.JointAction → σ → σ → Prop)
    (s0 : σ)
    (publicView : σ → I.Public)
    (observe : (i : ι) → σ → I.Obs i) where
  stateEquiv : σ ≃ τ
  init : stateEquiv s0 = I.init
  step_iff :
    ∀ {a : I.JointAction} {s t : σ},
      step a s t ↔ I.step a (stateEquiv s) (stateEquiv t)
  publicView_eq :
    ∀ s, I.publicView (stateEquiv s) = publicView s
  observe_eq :
    ∀ i s, I.observe i (stateEquiv s) = observe i s

namespace NativeInfoBisimulation

variable {σ τ : Type} {Act : ι → Type}
variable {I : InfoModel ι τ Act}
variable {step : I.JointAction → σ → σ → Prop}
variable {s0 : σ}
variable {publicView : σ → I.Public}
variable {observe : (i : ι) → σ → I.Obs i}

/-- Forget the backward direction and view a bisimulation as a homomorphic
simulation. -/
def toHomSimulation
    (bis : NativeInfoBisimulation step s0 publicView observe) :
    NativeInfoHomSimulation step s0 I publicView observe where
  stateMap := bis.stateEquiv
  labelMap := id
  init := bis.init
  step := fun hs => (bis.step_iff).1 hs
  publicView_eq := bis.publicView_eq
  observe_eq := bis.observe_eq

/-- Same-label reachability transport induced by a native-info bisimulation. -/
theorem reachBy_map
    (bis : NativeInfoBisimulation step s0 publicView observe)
    {w : List I.JointAction} {s t : σ}
    (h : ReachBy step w s t) :
    ReachBy I.step w (bis.stateEquiv s) (bis.stateEquiv t) := by
  simpa [NativeInfoBisimulation.toHomSimulation] using
    (NativeInfoHomSimulation.reachBy_map (sim := bis.toHomSimulation) h)

end NativeInfoBisimulation

end GameTheory
