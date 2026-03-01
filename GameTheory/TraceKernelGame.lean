import GameTheory.KernelGame
import GameTheory.PMFProduct

/-!
# GameTheory.TraceKernelGame

Minimal trace-style sequential semantics:

- `PreKernelStep`: one semantic step (state, views, controls, combine kernel)
- `SequentialGame`: initial distribution + finite horizon + terminal utility
- `toKernelGame`: collapse sequential semantics to a `KernelGame`

This is a semantics-first layer: EFG/MAID-style syntax can map into it.
-/

namespace GameTheory

open scoped BigOperators

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
structure SequentialGame (ι : Type) [Fintype ι] where
  Step : PreKernelStep ι
  init : PMF Step.State
  horizon : Nat
  utility : Step.State → Payoff ι

namespace SequentialGame

variable (G : SequentialGame ι)

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

end SequentialGame

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
noncomputable def KernelGame.toOneStepSequential (ι : Type) [Fintype ι]
    (Gk : KernelGame ι) [∀ i, Fintype (Gk.Strategy i)] : SequentialGame ι where
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

@[simp] theorem KernelGame.toOneStepSequential_runDist_constPure
    (ι : Type) [Fintype ι]
    (Gk : KernelGame ι)
    [∀ i, Fintype (Gk.Strategy i)]
    (σ : KernelGame.Profile Gk) :
    (KernelGame.toOneStepSequential ι Gk).runDist
      (constPurePolicy (KernelGame.toOneStepSequential ι Gk).Step σ) =
      (Gk.outcomeKernel σ).bind (fun ω => PMF.pure (some ω)) := by
  simp [KernelGame.toOneStepSequential, SequentialGame.runDist,
    PreKernelStep.stepKernel, PreKernelStep.jointActDist, constPurePolicy, pmfPi_pure]

end KernelEmbedding

end Core

end GameTheory
