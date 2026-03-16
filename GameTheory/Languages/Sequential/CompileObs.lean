import GameTheory.Languages.Sequential.SOS
import GameTheory.Theorems.Kuhn.ObsModel

/-!
# GameTheory.Languages.Sequential.CompileObs

Compilation of sequential protocol semantics into the `ObsModel` layer.

The compiled `ObsModel` treats each protocol step as a stochastic transition:
signal phases sample from the round's signal distribution, and action phases
apply the players' joint control deterministically.

## Main definitions

- `compileObsModel G` : the observation model for a sequential protocol
-/

namespace GameTheory.Sequential

open GameTheory

variable {n : Nat} {S V A Sig : Type}

/-- Stochastic step for a sequential protocol: given a configuration and joint
player actions, produce a distribution over successor configurations.

At signal phases, this samples from the round's signal distribution.
At action phases, this applies the transition deterministically.
At terminal states, the state is absorbing. -/
noncomputable def configStepPMF (G : Protocol n S V A Sig)
    (cfg : Config G)
    (acts : Fin n → Option A) :
    PMF (Config G) :=
  match cfg with
  | .signal k s =>
      match G.rounds[k]? with
      | some r => (r.signal s).map (fun sig => Config.action k s sig)
      | none   => PMF.pure (.signal k s)
  | .action k s _sig =>
      match G.rounds[k]? with
      | some r =>
          let next := r.transition s acts
          match G.rounds[k + 1]? with
          | some _ => PMF.pure (.signal (k + 1) next)
          | none   => PMF.pure (.terminal next)
      | none => PMF.pure (.action k s _sig)
  | .terminal s =>
      PMF.pure (.terminal s)

/-- Compile a sequential protocol into the observation model layer.

- **States**: protocol configurations (`Config G`)
- **Players**: `Fin n`
- **Observations**: player-local view (`Option V`, constant type across obs)
- **Actions**: optional actions per player (constant across observations)
- **Step**: stochastic resolution via `configStepPMF`
-/
noncomputable def compileObsModel (G : Protocol n S V A Sig) :
    ObsModel (Fin n) (Config G)
      (fun _ => Option V)
      (fun (_ : Fin n) (_ : Option V) => Option A) where
  infoState := fun _ => InfoStateSpec.list _
  observe := fun i cfg => observe G i cfg
  machine := {
    init := initialConfig G
    step := fun cfg acts => configStepPMF G cfg acts
  }

/-- The compiled ObsModel step is consistent with the native SOS:
the stochastic step assigns nonzero probability exactly to the states
reachable via the native `Step` relation. -/
private theorem pure_ne_zero_iff {α : Type*} (a b : α) :
    (PMF.pure a) b ≠ 0 ↔ b = a := by
  rw [ne_eq, PMF.pure_apply]
  constructor
  · intro h; by_contra hne; exact h (if_neg hne)
  · intro h; subst h; simp

theorem compileObsModel_step_consistent (G : Protocol n S V A Sig)
    (acts : JointControl n A)
    (cfg cfg' : Config G) :
    (configStepPMF G cfg acts) cfg' ≠ 0 ↔ Step G acts cfg cfg' := by
  constructor
  · -- Forward: nonzero PMF → Step
    intro hne
    match cfg with
    | .signal k s =>
      simp only [configStepPMF] at hne
      match hr : G.rounds[k]? with
      | some r =>
        simp only [hr] at hne
        -- map f μ at b ≠ 0 means ∃ a, μ a ≠ 0 ∧ f a = b
        have hmem := (PMF.mem_support_iff _ _).mpr hne
        rw [PMF.mem_support_map_iff] at hmem
        obtain ⟨sig, hsig, heq⟩ := hmem
        subst heq
        exact Step.sample hr ((PMF.mem_support_iff _ _).mp hsig)
      | none =>
        simp only [hr] at hne
        have := (pure_ne_zero_iff _ _).mp hne
        subst this
        exact Step.signal_stuck hr
    | .action k s sig =>
      simp only [configStepPMF] at hne
      match hr : G.rounds[k]? with
      | some r =>
        simp only [hr] at hne
        match hr' : G.rounds[k + 1]? with
        | some rNext =>
          simp only [hr'] at hne
          have := (pure_ne_zero_iff _ _).mp hne
          subst this
          exact Step.act_more hr rfl hr'
        | none =>
          simp only [hr'] at hne
          have := (pure_ne_zero_iff _ _).mp hne
          subst this
          exact Step.act_last hr rfl hr'
      | none =>
        simp only [hr] at hne
        have := (pure_ne_zero_iff _ _).mp hne
        subst this
        exact Step.action_stuck hr
    | .terminal s =>
      simp only [configStepPMF] at hne
      have := (pure_ne_zero_iff _ _).mp hne
      subst this
      exact Step.terminal
  · -- Backward: Step → nonzero PMF
    intro hstep
    match hstep with
    | .sample hr hsig =>
      simp only [configStepPMF, hr]
      exact (PMF.mem_support_iff _ _).mp
        ((PMF.mem_support_map_iff _ _ _).mpr
          ⟨_, (PMF.mem_support_iff _ _).mpr hsig, rfl⟩)
    | .act_more hr htrans hr' =>
      subst htrans
      simp [configStepPMF, hr, hr', PMF.pure_apply]
    | .act_last hr htrans hr' =>
      subst htrans
      simp [configStepPMF, hr, hr', PMF.pure_apply]
    | .terminal =>
      simp [configStepPMF, PMF.pure_apply]
    | .signal_stuck hr =>
      simp [configStepPMF, hr, PMF.pure_apply]
    | .action_stuck hr =>
      simp [configStepPMF, hr, PMF.pure_apply]

/-- At every configuration, `configStepPMF` is mass-invariant with respect to
the joint action: if two action vectors both assign nonzero probability to the
same successor, then the full step distributions are equal.

- **Signal phase**: the step samples from the round's signal distribution and
  ignores the action vector entirely, so any two action vectors yield the same
  PMF.
- **Action phase**: the step is `PMF.pure` of a deterministic successor, so if
  two action vectors reach the same target the pure PMFs coincide.
- **Terminal phase**: absorbing — `PMF.pure` of the current state, independent
  of actions. -/
theorem configStepPMF_mass_invariant (G : Protocol n S V A Sig)
    (cfg : Config G) (acts₁ acts₂ : Fin n → Option A) (t : Config G)
    (h₁ : (configStepPMF G cfg acts₁) t ≠ 0)
    (h₂ : (configStepPMF G cfg acts₂) t ≠ 0) :
    configStepPMF G cfg acts₁ = configStepPMF G cfg acts₂ := by
  match cfg with
  | .signal k s =>
    simp only [configStepPMF] at h₁ h₂ ⊢
  | .action k s sig =>
    simp only [configStepPMF] at h₁ h₂ ⊢
    match hr : G.rounds[k]? with
    | some r =>
      simp only [hr] at h₁ h₂ ⊢
      match hr' : G.rounds[k + 1]? with
      | some _ =>
        simp only [hr'] at h₁ h₂ ⊢
        exact congrArg PMF.pure ((pure_ne_zero_iff _ _).mp h₁ |>.symm.trans
          ((pure_ne_zero_iff _ _).mp h₂))
      | none =>
        simp only [hr'] at h₁ h₂ ⊢
        exact congrArg PMF.pure ((pure_ne_zero_iff _ _).mp h₁ |>.symm.trans
          ((pure_ne_zero_iff _ _).mp h₂))
    | none =>
      simp only [hr] at h₁ h₂ ⊢
  | .terminal s =>
    simp only [configStepPMF] at h₁ h₂ ⊢

/-- Compile a sequential protocol into the `ObsModelCore` layer using the
identity info-state model (observations are their own information states).

- **States**: protocol configurations (`Config G`)
- **Players**: `Fin n`
- **Observations**: player-local view (`Option V`)
- **Actions**: optional actions per player
- **InfoState**: identity — observation = info state
- **Step**: stochastic resolution via `configStepPMF`
-/
noncomputable def compileObsCoreModel (G : Protocol n S V A Sig) :
    ObsModelCore (Fin n) (Config G)
      (fun _ => Option V)
      (fun (_ : Fin n) (_ : Option V) => Option A) where
  infoState := fun _ => InfoStateCore.identity _
  observe := fun i cfg => observe G i cfg
  machine := {
    init := initialConfig G
    step := fun cfg acts => configStepPMF G cfg acts
  }

/-- The compiled `ObsModelCore` for a sequential protocol. -/
noncomputable abbrev compiledCoreObs (G : Protocol n S V A Sig) :=
  compileObsCoreModel G

end GameTheory.Sequential
