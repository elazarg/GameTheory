import GameTheory.Languages.FOSG.Information
import GameTheory.Theorems.Kuhn.KuhnModel

/-!
# FOSG -> ObsModelCore bridge

This file exposes a factored-observation stochastic game as an `ObsModelCore`
execution model. The bridge state stores the current world together with each
player's current FOSG information state.

The action alphabet is `Option (Act i)`: active players choose `some ai`,
inactive players are expected to choose `none`. Illegal joint action profiles
fall back to a self-loop; later theorem wrappers should quantify only over
profiles that stay in the legal fragment.
-/

namespace GameTheory

open Math.ProbabilityMassFunction

namespace FOSG

namespace ObsModelCoreBridge

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- Bridge state: current world together with every player's current FOSG
information state. -/
structure State (G : FOSG ι W Act PrivObs PubObs) where
  world : W
  info : ∀ i, G.InfoState i

namespace State

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Initial bridge state. -/
def init (G : FOSG ι W Act PrivObs PubObs) : State G where
  world := G.init
  info := fun _ => []

@[simp] theorem world_init :
    (State.init G).world = G.init := rfl

@[simp] theorem info_init (i : ι) :
    (State.init G).info i = [] := rfl

end State

/-- One-step player-visible increment determined by a realized FOSG transition,
without bundling it into a `History.Step`. -/
def playerViewIncrement
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (w : W) (a : G.LegalAction w) (w' : W) :
    List (PlayerEvent G i) :=
  match a.1 i with
  | some ai => [.act ai, .obs (G.privObs i w a w') (G.pubObs w a w')]
  | none => [.obs (G.privObs i w a w') (G.pubObs w a w')]

@[simp] theorem playerViewIncrement_of_some
    {G : FOSG ι W Act PrivObs PubObs}
    (i : ι) (w : W) (a : G.LegalAction w) (w' : W) {ai : Act i}
    (h : a.1 i = some ai) :
    playerViewIncrement G i w a w' =
      [.act ai, .obs (G.privObs i w a w') (G.pubObs w a w')] := by
  simp [playerViewIncrement, h]

@[simp] theorem playerViewIncrement_of_none
    {G : FOSG ι W Act PrivObs PubObs}
    (i : ι) (w : W) (a : G.LegalAction w) (w' : W)
    (h : a.1 i = none) :
    playerViewIncrement G i w a w' =
      [.obs (G.privObs i w a w') (G.pubObs w a w')] := by
  simp [playerViewIncrement, h]

/-- Advance a bridge state along a realized legal FOSG transition. -/
def advance
    (G : FOSG ι W Act PrivObs PubObs)
    (s : State G) (a : JointAction Act) (hleg : G.legal s.world a) (w' : W) :
    State G where
  world := w'
  info := fun i => s.info i ++ playerViewIncrement G i s.world ⟨a, hleg⟩ w'

@[simp] theorem advance_world
    {G : FOSG ι W Act PrivObs PubObs}
    (s : State G) (a : JointAction Act) (hleg : G.legal s.world a) (w' : W) :
    (advance G s a hleg w').world = w' := rfl

@[simp] theorem advance_info
    {G : FOSG ι W Act PrivObs PubObs}
    (s : State G) (a : JointAction Act) (hleg : G.legal s.world a) (w' : W) (i : ι) :
    (advance G s a hleg w').info i =
      s.info i ++ playerViewIncrement G i s.world ⟨a, hleg⟩ w' := rfl

/-- The `ObsModelCore` observation type for player `i` is exactly the player's
current FOSG information state. -/
abbrev Obs
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  G.InfoState i

/-- The `ObsModelCore` action type: `some ai` for a real move, `none` for
inactivity. -/
abbrev LocalAct
    (_G : FOSG ι W Act PrivObs PubObs) (i : ι) (_ : Obs _G i) : Type :=
  Option (Act i)

/-- The core execution-model bridge from FOSG to `ObsModelCore`. -/
noncomputable def toObsModelCore
    (G : FOSG ι W Act PrivObs PubObs) :
    ObsModelCore ι (State G) (Obs G) (LocalAct G) where
  infoState := fun _ => InfoStateCore.identity _
  observe := fun i s => s.info i
  machine :=
    { init := State.init G
      step := fun s a => by
        classical
        exact if hleg : G.legal s.world a then
          (G.transition s.world ⟨a, hleg⟩).map (advance G s a hleg)
        else
          PMF.pure s }

@[simp] theorem toObsModelCore_init_world
    (G : FOSG ι W Act PrivObs PubObs) :
    ((toObsModelCore G).init).world = G.init := rfl

@[simp] theorem toObsModelCore_observe
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) (s : State G) :
    (toObsModelCore G).observe i s = s.info i := rfl

@[simp] theorem toObsModelCore_step_legal
    (G : FOSG ι W Act PrivObs PubObs)
    (s : State G) (a : ∀ i, Option (Act i))
    (hleg : G.legal s.world a) :
    (toObsModelCore G).step s a =
      (G.transition s.world ⟨a, hleg⟩).map (advance G s a hleg) := by
  classical
  change (toObsModelCore G).machine.step s a =
    (G.transition s.world ⟨a, hleg⟩).map (advance G s a hleg)
  simp [toObsModelCore, hleg]

@[simp] theorem toObsModelCore_step_illegal
    (G : FOSG ι W Act PrivObs PubObs)
    (s : State G) (a : ∀ i, Option (Act i))
    (hleg : ¬ G.legal s.world a) :
    (toObsModelCore G).step s a = PMF.pure s := by
  classical
  change (toObsModelCore G).machine.step s a = PMF.pure s
  simp [toObsModelCore, hleg]

@[simp] theorem toObsModelCore_currentObs
    (G : FOSG ι W Act PrivObs PubObs) (i : ι)
    (v : (toObsModelCore G).InfoState i) :
    (toObsModelCore G).currentObs i v = v := rfl

/-- After one legal step in the bridge model, the observed local state is the
previous FOSG information state extended by the realized one-step increment. -/
theorem observe_advance_eq_append
    {G : FOSG ι W Act PrivObs PubObs}
    (s : State G) (a : JointAction Act) (hleg : G.legal s.world a) (w' : W) (i : ι) :
    (toObsModelCore G).observe i (advance G s a hleg w') =
      (toObsModelCore G).observe i s ++
        playerViewIncrement G i s.world ⟨a, hleg⟩ w' := by
  rfl

end ObsModelCoreBridge

end FOSG

end GameTheory
