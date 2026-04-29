import GameTheory.Core.KernelGame
import GameTheory.Core.GameMorphism
import GameTheory.Languages.InfoModel.InfoGame
import GameTheory.Languages.InfoModel.Simulation
import GameTheory.Languages.MultiRound.SOS
import Math.PMFProduct
import Math.Probability

/-!
# GameTheory.Languages.MultiRound.Compile

Compilation-facing semantic core for sequential/protocol languages.

This file provides a small repeated-step semantics:
- `PreKernelStep`: one semantic step (state, local views, joint controls)
- `StepwiseGame`: initial distribution + finite horizon + terminal utility
- `toKernelGame`: collapse to a `KernelGame`

Language-native protocol syntax should compile into this layer, and then
further into the generic semantic targets when theorem transport is needed.
-/

namespace GameTheory

open Math.Probability

open scoped BigOperators
open Math.PMFProduct

section Core

variable {ι : Type} [Fintype ι]

/-- One semantic step: each controller observes a view of state, samples an action,
and all actions combine into a stochastic next state. -/
structure PreKernelStep (ι : Type) [Fintype ι] where
  State : Type
  View : ι → Type
  Act : ι → Type
  [fAct : ∀ i, Fintype (Act i)]
  observe : State → (i : ι) → View i
  combine : State → (∀ i, Act i) → PMF State

attribute [instance] PreKernelStep.fAct

/-- A policy chooses a distribution over actions from each controller view. -/
abbrev Policy (K : PreKernelStep ι) : Type :=
  (i : ι) → K.View i → PMF (K.Act i)

namespace PreKernelStep

variable (K : PreKernelStep ι)

open Classical in
/-- Joint action law at state `s` induced by policy `π` (independent local sampling). -/
noncomputable def jointActDist (π : Policy K) (s : K.State) : PMF (∀ i, K.Act i) :=
  pmfPi (fun i => π i (K.observe s i))

/-- One-step state-transition kernel induced by policy `π`. -/
noncomputable def stepKernel (π : Policy K) : Kernel K.State K.State :=
  fun s => (K.jointActDist π s).bind (K.combine s)

end PreKernelStep

/-- A finite-horizon sequential game built from a repeated semantic step. -/
structure StepwiseGame (ι : Type) [Fintype ι] where
  Step : PreKernelStep ι
  init : PMF Step.State
  horizon : Nat
  utility : Step.State → Payoff ι

namespace StepwiseGame

variable (G : StepwiseGame ι)

/-- Run distribution after `horizon` repeated steps under policy `π`. -/
noncomputable def runDist (π : Policy G.Step) : PMF G.Step.State :=
  Nat.rec G.init (fun _ acc => acc.bind (G.Step.stepKernel π)) G.horizon

@[simp] theorem runDist_zero (π : Policy G.Step) (h0 : G.horizon = 0) :
    G.runDist π = G.init := by
  simp [runDist, h0]

/-- Collapse a sequential game into its profile-to-outcome kernel semantics. -/
noncomputable def toKernelGame : KernelGame ι where
  Strategy := fun i => G.Step.View i → PMF (G.Step.Act i)
  Outcome := G.Step.State
  utility := G.utility
  outcomeKernel := fun π => G.runDist π

@[simp] theorem toKernelGame_outcomeKernel (π : Policy G.Step) :
    G.toKernelGame.outcomeKernel π = G.runDist π := rfl

end StepwiseGame

section DeterministicPolicy

variable {A : ι → Type} [∀ i, Fintype (A i)]

open Classical in
/-- Product of point masses is a point mass at the joint assignment. -/
theorem pmfPi_pure (σ : ∀ i, A i) :
    pmfPi (fun i => (PMF.pure (σ i) : PMF (A i))) = PMF.pure σ := by
  classical
  ext s
  by_cases hs : s = σ
  · subst hs
    simp [pmfPi_apply]
  · have hneq : ¬ ∀ i, s i = σ i := by
      intro hall
      apply hs
      funext i
      exact hall i
    obtain ⟨i, hi⟩ := not_forall.mp hneq
    have hfactor0 : (if s i = σ i then (1 : ENNReal) else 0) = 0 := by
      simp [hi]
    have hprod0 :
        (∏ x : ι, (if s x = σ x then (1 : ENNReal) else 0)) = 0 := by
      calc
        (∏ x : ι, (if s x = σ x then (1 : ENNReal) else 0))
            = (if s i = σ i then (1 : ENNReal) else 0) *
              (Finset.prod (Finset.univ.erase i)
                (fun x => (if s x = σ x then (1 : ENNReal) else 0))) := by
                simpa [Finset.mem_univ] using
                  (Finset.mul_prod_erase
                    (s := (Finset.univ : Finset ι))
                    (f := fun x => (if s x = σ x then (1 : ENNReal) else 0))
                    (a := i) (by simp)).symm
        _ = 0 := by simp [hfactor0]
    simpa [pmfPi_apply, PMF.pure_apply, hs] using hprod0

variable (K : PreKernelStep ι)

/-- Deterministic (pure) policy from a joint action assignment. -/
noncomputable def constPurePolicy (σ : ∀ i, K.Act i) : Policy K :=
  fun i _ => PMF.pure (σ i)

@[simp] theorem stepKernel_constPure (σ : ∀ i, K.Act i) (s : K.State) :
    K.stepKernel (constPurePolicy K σ) s = K.combine s σ := by
  simp [PreKernelStep.stepKernel, PreKernelStep.jointActDist, constPurePolicy, pmfPi_pure]

end DeterministicPolicy

section KernelEmbedding

/-- A `KernelGame` as a 1-step sequential game with trivial views. -/
noncomputable def KernelGame.toOneStepStepwise (ι : Type) [Fintype ι]
    (Gk : KernelGame ι) [∀ i, Fintype (Gk.Strategy i)] : StepwiseGame ι where
  Step := {
    State := Option Gk.Outcome
    View := fun _ => PUnit
    Act := Gk.Strategy
    observe := fun _ _ => PUnit.unit
    combine := fun s σ =>
      match s with
      | none => (Gk.outcomeKernel σ).bind (fun ω => PMF.pure (some ω))
      | some ω => PMF.pure (some ω)
  }
  init := PMF.pure none
  horizon := 1
  utility := fun s =>
    match s with
    | none => fun _ => 0
    | some ω => Gk.utility ω

@[simp] theorem KernelGame.toOneStepStepwise_runDist_constPure
    (ι : Type) [Fintype ι]
    (Gk : KernelGame ι)
    [∀ i, Fintype (Gk.Strategy i)]
    (σ : KernelGame.Profile Gk) :
    (KernelGame.toOneStepStepwise ι Gk).runDist
      (constPurePolicy (KernelGame.toOneStepStepwise ι Gk).Step σ) =
      (Gk.outcomeKernel σ).bind (fun ω => PMF.pure (some ω)) := by
  simp [KernelGame.toOneStepStepwise, StepwiseGame.runDist,
    PreKernelStep.stepKernel, PreKernelStep.jointActDist, constPurePolicy, pmfPi_pure]

/-- Refinement morphism: a `KernelGame` `Gk` injects into its one-step
stepwise compilation via `some` on outcomes and constant-pure-policy on
strategies. Built via the `Morphism.ofOutcomeEmbedding` recipe. -/
noncomputable def KernelGame.toOneStepStepwise_morphism
    (ι : Type) [Fintype ι]
    (Gk : KernelGame ι)
    [∀ i, Fintype (Gk.Strategy i)] :
    KernelGame.Morphism Gk (KernelGame.toOneStepStepwise ι Gk).toKernelGame :=
  KernelGame.Morphism.ofOutcomeEmbedding
    (stratMap := fun _i s => fun _ : PUnit => PMF.pure s)
    (embed := some)
    (h_outcome := fun σ => by
      change (KernelGame.toOneStepStepwise ι Gk).runDist
          (constPurePolicy _ σ)
        = (Gk.outcomeKernel σ).map some
      rw [KernelGame.toOneStepStepwise_runDist_constPure]
      rfl)
    (h_util := fun _ω => rfl)

end KernelEmbedding

end Core

end GameTheory

namespace GameTheory.MultiRound

open Math.Probability

variable {n : Nat} {S V A Sig : Type}

/-- Compile a sequential protocol directly into the generic `InfoModel` layer.

The compiled model uses the native SOS configurations as states:
- `signal` states wait for nature's joint signal realization
- `action` states wait for the players' joint action
- `terminal` states have no outgoing transitions

Public visibility is the current execution phase and round index; private
visibility is the current round view when the protocol is waiting for actions,
and `none` otherwise. -/
def compileInfoOn (G : MultiRoundGame n S V A Sig) :
    GameTheory.InfoModel (Fin n) (Config G) (fun _ => A) where
  init := initialConfig G
  step := Step G
  Public := PublicPhase
  publicView := publicPhase
  Obs := fun _ => Option V
  observe := observe G

/-- A protocol SOS step is definitionally the compiled machine step. -/
theorem compile_step_iff
    (G : MultiRoundGame n S V A Sig)
    (a : JointControl n A)
    (src dst : Config G) :
    (compileInfoOn G).step a src dst ↔ Step G a src dst := by
  rfl

/-- Native SOS reachability is definitionally the same as reachability in the
compiled latent-state machine. -/
theorem compile_reach_iff
    (G : MultiRoundGame n S V A Sig)
    (ha : List (JointControl n A))
    (src dst : Config G) :
    Semantics.Transition.ReachBy (compileInfoOn G).step ha src dst ↔
      ReachBy G ha src dst := by
  rfl

/-- The compiled private observation agrees with the native SOS observation. -/
theorem compile_observe_eq_observe
    (G : MultiRoundGame n S V A Sig)
    (i : Fin n) (c : Config G) :
    (compileInfoOn G).observe i c = observe G i c := by
  rfl

/-- The compiled public view agrees with the native SOS public phase. -/
theorem compile_publicView_eq_publicPhase
    (G : MultiRoundGame n S V A Sig)
    (c : Config G) :
    (compileInfoOn G).publicView c = publicPhase c := by
  rfl

/-- The compiled `InfoModel` is definitionally bisimilar to the native
protocol SOS: states are identical, labels are identical joint controls, and
public/private observations coincide. -/
def nativeInfoBisimulation (G : MultiRoundGame n S V A Sig) :
    GameTheory.NativeInfoBisimulation (I := compileInfoOn G)
      (Step G)
      (initialConfig G)
      publicPhase
      (observe G) where
  stateEquiv := Equiv.refl _
  init := rfl
  step_iff := by
    intro a s t
    rfl
  publicView_eq := by
    intro s
    rfl
  observe_eq := by
    intro i s
    rfl

end GameTheory.MultiRound
