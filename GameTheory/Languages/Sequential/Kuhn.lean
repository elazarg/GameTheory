import GameTheory.Languages.Sequential.CompileObs
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.Sequential.Kuhn

Kuhn's theorem for compiled sequential protocols.

Both directions go through the `ObsModel` layer, which automatically provides
the `StepActionDeterminism` / `StepSupportFactorization` needed by the core
proof (via its snapshot-refined information states).

## Main results

- `kuhn_behavioral_to_mixed_of_compiled` : B→M direction (no recall needed)
- `kuhn_mixed_to_behavioral_of_compiled` : M→B direction (under PSPR)
- `kuhn_behavioral_to_mixed_core` : B→M on `ObsModelCore` (under `NoNontrivialInfoStateRepeat`)
- `stepMassInvariant_compiledCore` : `StepMassInvariant` holds for the compiled core model
-/

namespace GameTheory.Languages.Sequential

open GameTheory.Sequential
open GameTheory.Theorems

variable {n : Nat} {S V A Sig : Type}

section Kuhn

variable (G : Protocol n S V A Sig)

/-- The compiled ObsModel for a sequential protocol. -/
noncomputable abbrev compiledObs (G : Protocol n S V A Sig) :=
  GameTheory.Sequential.compileObsModel G

/-- **Kuhn B→M for compiled sequential protocols**: behavioral strategies can be
realized as product mixed strategies.

This requires finiteness of the compiled information-state type; the default
list-backed summary used by `compileObsModel` does not provide that instance
automatically. -/
theorem kuhn_behavioral_to_mixed_of_compiled
    [Fintype (Option A)]
    [∀ i, Fintype ((compiledObs G).InfoState i)]
    (β : ObsModel.BehavioralProfile (compiledObs G)) (k : Nat) :
    (compiledObs G).runDist k β =
      ((compiledObs G).behavioralToMixedJoint β).bind
        ((compiledObs G).runDistPure k) :=
  ObsModel.kuhn_behavioral_to_mixed β k

/-- **Kuhn M→B for compiled sequential protocols**: under per-step player recall,
product mixed strategies can be realized by behavioral strategies. -/
theorem kuhn_mixed_to_behavioral_of_compiled
    [Fintype (Option A)]
    [∀ i, Fintype ((compiledObs G).InfoState i)]
    [Nonempty (Option A)]
    (hPSPR : ObsModel.PerStepPlayerRecall (compiledObs G))
    (μ : ∀ i, PMF ((compiledObs G).LocalStrategy i))
    (k : Nat) :
    ∃ β : ObsModel.BehavioralProfile (compiledObs G),
      (compiledObs G).runDist k β =
        (Math.PMFProduct.pmfPi μ).bind ((compiledObs G).runDistPure k) :=
  ObsModel.kuhn_mixed_to_behavioral_pspr hPSPR μ k

end Kuhn

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

end GameTheory.Languages.Sequential
