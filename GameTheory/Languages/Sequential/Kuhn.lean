import GameTheory.Languages.Sequential.CompileObs
import GameTheory.Languages.Sequential.CompileObsLin
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.Sequential.Kuhn

Kuhn's theorem for compiled sequential protocols.

## Main results

- `kuhn_behavioral_to_mixed_core` : B→M on `ObsModelCore` (under `NoNontrivialInfoStateRepeat`)
- `stepMassInvariant_compiledCore` : `StepMassInvariant` holds for the compiled core model
- `kuhn_mixed_to_behavioral_compiledLin` : M→B on linearized `ObsModelCore`
  (under `ActionPosteriorLocal`, which follows from perfect recall)
- `kuhn_mixed_to_behavioral_native` : M→B with native `Protocol.eval` on the RHS
  (under `Protocol.FullRecall`)

## Architecture

**B→M** uses the simultaneous-action `ObsModelCore` compilation (`compiledCoreObs`).
The `NoNontrivialInfoStateRepeat` condition ensures behavioral strategies can be
decomposed into product mixed strategies.

**M→B** uses the **linearized** `ObsModelCore` compilation (`compiledLinObs`), which
splits each simultaneous action phase into per-player sub-steps. This ensures
`StepSupportFactorization` holds (one player per step), which is required by the
core M→B proof but fails for simultaneous-action models.

The structural conditions `StepMassInvariant` and `StepSupportFactorization` hold
automatically for the linearized model. The remaining condition,
`ActionPosteriorLocal`, requires a protocol-level recall condition.
-/

namespace GameTheory.Languages.Sequential

open GameTheory.Sequential
open GameTheory.Theorems

variable {n : Nat} {S V A Sig : Type}

section KuhnCore

variable (G : Protocol n S V A Sig)

/-- The compiled ObsModelCore for a sequential protocol. -/
noncomputable abbrev compiledCoreObs' (G : Protocol n S V A Sig) :=
  GameTheory.Sequential.compiledCoreObs G

/-- **Kuhn B→M for compiled sequential protocol core model**: behavioral
strategies can be realized as product mixed strategies, given the
no-nontrivial-info-state-repeat condition. -/
theorem kuhn_behavioral_to_mixed_core
    [Fintype (Option A)]
    [∀ i, Fintype ((compiledCoreObs' G).InfoState i)]
    [∀ i, Fintype ((compiledCoreObs' G).LocalStrategy i)]
    (hNR : (compiledCoreObs' G).NoNontrivialInfoStateRepeat)
    (β : ObsModelCore.BehavioralProfile (compiledCoreObs' G)) (k : Nat) :
    (compiledCoreObs' G).runDist k β =
      ((compiledCoreObs' G).behavioralToMixedJoint β).bind
        ((compiledCoreObs' G).runDistPure k) :=
  ObsModelCore.kuhn_behavioral_to_mixed hNR β k

/-- The compiled `ObsModelCore` for a sequential protocol satisfies
`StepMassInvariant`: if two pure profiles can reach the same next state from
the same trace in one step, then the one-step mass is equal.

This follows from `configStepPMF_mass_invariant`: the step PMF at signal
phases does not depend on player actions at all, and at action/terminal phases
the step is deterministic (`PMF.pure`), so if both profiles reach the same
target the full distributions coincide. -/
theorem stepMassInvariant_compiledCore
    [Fintype (Option A)]
    (G : Protocol n S V A Sig) :
    ObsModelCore.StepMassInvariant (compiledCoreObs' G) := by
  intro ss t π₁ π₂ h₁ h₂
  have eq₁ := ObsModelCore.pureStep_eq π₁ ss
  have eq₂ := ObsModelCore.pureStep_eq π₂ ss
  rw [eq₁] at h₁ ⊢
  rw [eq₂] at h₂ ⊢
  have hmass := configStepPMF_mass_invariant G
    (ObsModelCore.lastState (compiledCoreObs' G) ss)
    _ _ t h₁ h₂
  exact congrFun (congrArg DFunLike.coe hmass) t

end KuhnCore

section KuhnLinearized

variable [DecidableEq (Fin n)] [Fintype (Fin n)]
variable (G : Protocol n S V A Sig)

/-- The compiled linearized ObsModelCore for a sequential protocol. -/
noncomputable abbrev compiledLinObs' (G : Protocol n S V A Sig) :=
  GameTheory.Sequential.compiledLinObs G

/-- **Kuhn M→B for linearized sequential protocols**: under action-posterior
locality, product mixed strategies can be realized by behavioral strategies.

The linearized model satisfies `StepMassInvariant` and `StepSupportFactorization`
structurally. The remaining condition, `ActionPosteriorLocal`, requires a
protocol-level recall condition (e.g. perfect recall). -/
theorem kuhn_mixed_to_behavioral_compiledLin
    [Fintype A] [Nonempty A]
    [∀ i, Fintype ((compiledLinObs' G).InfoState i)]
    [∀ i, Fintype ((compiledLinObs' G).LocalStrategy i)]
    (hAPL : ∀ i, ObsModelCore.ActionPosteriorLocal (compiledLinObs' G) i)
    (μ : ∀ i, PMF ((compiledLinObs' G).LocalStrategy i))
    (k : Nat) :
    ∃ β : ObsModelCore.BehavioralProfile (compiledLinObs' G),
      (compiledLinObs' G).runDist k β =
        (Math.PMFProduct.pmfPi μ).bind ((compiledLinObs' G).runDistPure k) :=
  ObsModelCore.kuhn_mixed_to_behavioral_semantic
    (stepMassInvariant_compiledLin G)
    (stepSupportFactorization_compiledLin G)
    hAPL μ k

set_option linter.unusedFintypeInType false in
/-- Full recall (view + action) implies `ActionPosteriorLocal` on the linearized model.

The proof route is: FullRecall → `ObsLocalFeasibility` → (+ MI) → APL, using
`ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility`.

With the identity info state, `projectStates i ss` captures only the *last*
observation. Under view-only `PerfectRecall`, two traces with the same last
observation have matching view histories — but the *action* histories may differ.
`FullRecall` additionally requires that same view at round `k` determines past
own-actions, which ensures that the actions encoded in both traces at player `i`'s
turns agree, making `ObsLocalFeasibility` hold. -/
theorem actionPosteriorLocal_of_fullRecall
    [Fintype A] [Nonempty A]
    [∀ i, Fintype ((compiledLinObs' G).InfoState i)]
    [∀ i, Fintype ((compiledLinObs' G).LocalStrategy i)]
    (hFR : G.FullRecall) (i : Fin n) :
    ObsModelCore.ActionPosteriorLocal (compiledLinObs' G) i :=
  ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
    (stepMassInvariant_compiledLin G) i
    (obsLocalFeasibility_of_fullRecall G hFR i)

set_option linter.unusedFintypeInType false in
/-- **Kuhn M→B for sequential protocols under full recall**: product mixed
strategies can be realized by behavioral strategies.

Combines: linearized compilation (structural MI + SF), FullRecall → APL,
and the core M→B theorem. -/
theorem kuhn_mixed_to_behavioral_fullRecall
    [Fintype A] [Nonempty A]
    [∀ i, Fintype ((compiledLinObs' G).InfoState i)]
    [∀ i, Fintype ((compiledLinObs' G).LocalStrategy i)]
    (hFR : G.FullRecall)
    (μ : ∀ i, PMF ((compiledLinObs' G).LocalStrategy i))
    (k : Nat) :
    ∃ β : ObsModelCore.BehavioralProfile (compiledLinObs' G),
      (compiledLinObs' G).runDist k β =
        (Math.PMFProduct.pmfPi μ).bind ((compiledLinObs' G).runDistPure k) :=
  kuhn_mixed_to_behavioral_compiledLin G
    (fun i => actionPosteriorLocal_of_fullRecall G hFR i) μ k

-- ============================================================================
-- Native M→B: stated on Protocol.eval
-- ============================================================================

/-- Extract the terminal state from a trace of the linearized model. -/
private noncomputable def extractState (G : Protocol n S V A Sig) :
    List (LinConfig G) → S :=
  fun ss => ((compiledLinObs G).lastState ss).state

set_option linter.unusedFintypeInType false in
/-- **Kuhn M→B (native)**: under full recall, every product mixed strategy profile
can be realized by a behavioral strategy profile on the linearized compiled model,
with the same outcome distribution as `Protocol.eval`.

The behavioral profile lives on the compiled model. The RHS is the native
protocol evaluation: `(pmfPi μ).bind (Protocol.eval G)`. -/
theorem kuhn_mixed_to_behavioral_native
    [DecidableEq V] [Fintype V] [Fintype A] [Nonempty A]
    (hFR : G.FullRecall)
    (μ : (i : Fin n) → PMF (PureStrategy V A))
    (k : Nat) (hk : k ≥ G.rounds.length * (n + 2)) :
    ∃ β : ObsModelCore.BehavioralProfile (compiledLinObs' G),
      ((compiledLinObs' G).runDist k β).bind
        (fun ss => PMF.pure (extractState G ss)) =
      (Math.PMFProduct.pmfPi μ).bind (fun σ => G.eval σ) := by
  obtain ⟨β, hβ⟩ := kuhn_mixed_to_behavioral_fullRecall G hFR
    (liftMixedProfile (G := G) μ) k
  refine ⟨β, ?_⟩
  -- Apply .bind extract to hβ
  have hlhs : ((compiledLinObs' G).runDist k β).bind
      (fun ss => PMF.pure (extractState G ss)) =
    ((Math.PMFProduct.pmfPi (liftMixedProfile (G := G) μ)).bind
      ((compiledLinObs' G).runDistPure k)).bind
        (fun ss => PMF.pure (extractState G ss)) := by
    rw [hβ]
  rw [hlhs, PMF.bind_bind]
  -- Replace pmfPi (liftMixedProfile μ) with pushforward (pmfPi μ) liftPureProfile
  rw [liftMixedProfile_joint (G := G) μ]
  -- pushforward (pmfPi μ) liftPureProfile = (pmfPi μ).bind (fun σ => pure (liftPureProfile σ))
  simp only [Math.ProbabilityMassFunction.pushforward, PMF.bind_bind, PMF.pure_bind]
  -- Now both sides: (pmfPi μ).bind (fun σ => ...)
  congr 1; funext σ
  exact runDistPure_eq_eval G σ k hk

-- ============================================================================
-- Fully native M→B: stated entirely on Protocol types
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- **Kuhn M→B (fully native)**: under full recall and view-determines-round,
every product mixed strategy profile can be realized by a behavioral strategy
profile with the same outcome distribution.

Both LHS and RHS use native Sequential types — no compiled model in the statement.
The compiled model is used internally to construct the behavioral profile
via the core M→B theorem. -/
theorem kuhn_mixed_to_behavioral_sequential
    [DecidableEq V] [Fintype V] [Fintype A] [Nonempty A]
    [Nonempty (Fin G.rounds.length)]
    (hFR : G.FullRecall)
    (hVRD : G.ViewDeterminesRound)
    (μ : (i : Fin n) → PMF (PureStrategy V A)) :
    ∃ σ : BehavioralProfile n V A,
      G.evalMixed σ = (Math.PMFProduct.pmfPi μ).bind (fun π => G.eval π) := by
  -- Step 1: Get compiled behavioral profile β from core M→B
  set k := G.rounds.length * (n + 2)
  obtain ⟨β, hβ⟩ := kuhn_mixed_to_behavioral_fullRecall G hFR
    (liftMixedProfile (G := G) μ) k
  -- Step 2: Descend to native behavioral profile using ViewDeterminesRound
  set σ := descendBehavioralProfileVRD hVRD β
  refine ⟨σ, ?_⟩
  -- Step 3: Connect LHS via behavioral adequacy
  -- G.evalMixed σ = runDist k (liftBehavioral σ) .bind (pure ∘ extractState)
  rw [← runDist_liftBehavioral_extractState_eq_evalMixed (G := G) σ k (by omega)]
  -- Step 4: runDist k (liftBehavioral σ) = runDist k β (via agreement + congr)
  have hcongr : (compiledLinObs G).runDist k (liftBehavioralProfile σ) =
      (compiledLinObs G).runDist k β := by
    symm
    exact ObsModelCore.runDist_congr
      (fun m i ss hss => liftBehavioralProfile_descendVRD_agree hVRD β m i ss hss) k
  rw [hcongr]
  -- Step 5: Apply hβ and connect RHS via pure adequacy (same as kuhn_mixed_to_behavioral_native)
  rw [show ((compiledLinObs G).runDist k β).bind
      (fun ss => PMF.pure ((compiledLinObs G).lastState ss).state) =
    ((Math.PMFProduct.pmfPi (liftMixedProfile (G := G) μ)).bind
      ((compiledLinObs' G).runDistPure k)).bind
        (fun ss => PMF.pure ((compiledLinObs G).lastState ss).state) from by
    rw [hβ]]
  rw [PMF.bind_bind, liftMixedProfile_joint (G := G) μ]
  simp only [Math.ProbabilityMassFunction.pushforward, PMF.bind_bind, PMF.pure_bind]
  congr 1; funext π
  exact runDistPure_eq_eval G π k (by omega)

end KuhnLinearized

end GameTheory.Languages.Sequential
