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
    {α σ : Type}
    (step : α → σ → σ → Prop)
    (s0 : σ)
    {M : LSM ι}
    (I : InfoModel M)
    (publicView : σ → I.Public)
    (observe : (i : ι) → σ → I.Obs i) where
  stateMap : σ → M.State
  labelMap : α → JointAction M
  init : stateMap s0 = M.init
  step :
    ∀ {a : α} {s t : σ},
      step a s t →
      M.step (labelMap a) (stateMap s) (stateMap t)
  publicView_eq :
    ∀ s, I.publicView (stateMap s) = publicView s
  observe_eq :
    ∀ i s, I.observe i (stateMap s) = observe i s

namespace NativeInfoHomSimulation

variable {α σ : Type}
variable {step : α → σ → σ → Prop}
variable {s0 : σ}
variable {M : LSM ι} {I : InfoModel M}
variable {publicView : σ → I.Public}
variable {observe : (i : ι) → σ → I.Obs i}

/-- Trace-level reachability transport induced by a native-info simulation. -/
theorem reachBy_map
    (sim : NativeInfoHomSimulation step s0 I publicView observe)
    {w : List α} {s t : σ}
    (h : ReachBy step w s t) :
    ReachBy M.step (w.map sim.labelMap) (sim.stateMap s) (sim.stateMap t) := by
  let hsim : Semantics.Transition.HomSimulation step M.step :=
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
    {σ : Type}
    {M : LSM ι}
    (step : JointAction M → σ → σ → Prop)
    (s0 : σ)
    (I : InfoModel M)
    (publicView : σ → I.Public)
    (observe : (i : ι) → σ → I.Obs i) where
  stateEquiv : σ ≃ M.State
  init : stateEquiv s0 = M.init
  step_iff :
    ∀ {a : JointAction M} {s t : σ},
      step a s t ↔ M.step a (stateEquiv s) (stateEquiv t)
  publicView_eq :
    ∀ s, I.publicView (stateEquiv s) = publicView s
  observe_eq :
    ∀ i s, I.observe i (stateEquiv s) = observe i s

namespace NativeInfoBisimulation

variable {σ : Type}
variable {M : LSM ι}
variable {step : JointAction M → σ → σ → Prop}
variable {s0 : σ}
variable {I : InfoModel M}
variable {publicView : σ → I.Public}
variable {observe : (i : ι) → σ → I.Obs i}

/-- Forget the backward direction and view a bisimulation as a homomorphic
simulation. -/
def toHomSimulation
    (bis : NativeInfoBisimulation step s0 I publicView observe) :
    NativeInfoHomSimulation step s0 I publicView observe where
  stateMap := bis.stateEquiv
  labelMap := id
  init := bis.init
  step := fun hs => (bis.step_iff).1 hs
  publicView_eq := bis.publicView_eq
  observe_eq := bis.observe_eq

/-- Same-label reachability transport induced by a native-info bisimulation. -/
theorem reachBy_map
    (bis : NativeInfoBisimulation step s0 I publicView observe)
    {w : List (JointAction M)} {s t : σ}
    (h : ReachBy step w s t) :
    ReachBy M.step w (bis.stateEquiv s) (bis.stateEquiv t) := by
  simpa [NativeInfoBisimulation.toHomSimulation] using
    (NativeInfoHomSimulation.reachBy_map (sim := bis.toHomSimulation) h)

end NativeInfoBisimulation

end GameTheory
