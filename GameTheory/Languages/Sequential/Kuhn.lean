import GameTheory.Languages.Sequential.CompileObs
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.Sequential.Kuhn

Kuhn reduction lemmas for compiled sequential protocols via the `ObsModel` layer.

This file connects sequential protocol semantics to Kuhn's theorem by:
1. Compiling protocols to `ObsModel` via `compileObsModel`
2. Assuming the finiteness / recall conditions needed by the generic theorem
3. Applying ObsModel-level Kuhn corollaries honestly

## Main results

- `kuhn_behavioral_to_mixed_of_compiled` : B→M direction (no recall needed)
- `kuhn_mixed_to_behavioral_of_compiled` : M→B direction (under PSPR)
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

end GameTheory.Languages.Sequential
