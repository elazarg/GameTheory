import GameTheory.Languages.Sequential.Compile
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Theorems.Sequential

Target-side reduction lemmas for compiled sequential protocols.

This file is intentionally thin. It packages the structural equivalence between
native protocol SOS and the compiled `InfoModel` presentation, so later ports of
Kuhn/Zermelo-style theorems can depend on one semantic interface.
-/

namespace GameTheory.Theorems.Sequential

open GameTheory.Sequential
open GameTheory.Theorems

variable {n : Nat} {S V A Sig : Type}

/-- The compiled protocol machine has exactly the native SOS transition relation. -/
theorem step_iff
    (G : GameTheory.Protocol n S V A Sig)
    (a : JointControl n A)
    (src dst : Config G) :
    (compileLSM G).step a src dst ↔ Step G a src dst :=
  compile_step_iff G a src dst

/-- Reachability in the compiled machine is exactly native SOS reachability. -/
theorem reach_iff
    (G : GameTheory.Protocol n S V A Sig)
    (ha : List (JointControl n A))
    (src dst : Config G) :
    Semantics.Transition.ReachBy (compileLSM G |>.stepExists) ha src dst ↔
      ReachBy G ha src dst :=
  compile_reach_iff G ha src dst

/-- The compiled information model exposes the native public phase. -/
theorem publicView_eq
    (G : GameTheory.Protocol n S V A Sig)
    (c : Config G) :
    (compileInfoOn G).publicView c = publicPhase c :=
  compile_publicView_eq_publicPhase G c

/-- The compiled information model exposes the native local observation. -/
theorem observe_eq
    (G : GameTheory.Protocol n S V A Sig)
    (i : Fin n) (c : Config G) :
    (compileInfoOn G).observe i c = observe G i c :=
  compile_observe_eq_observe G i c

/-- Mixed-to-behavioral Kuhn reduction for the compiled sequential semantics.

This is the honest reduction boundary currently available: once a sequential
protocol has been compiled into an `InfoModel` together with a stochastic
`Execution.Dynamics`, the generic mixed-to-behavioral theorem applies directly
under the same finiteness and perfect-recall obligations required by the
generic theorem. -/
theorem kuhn_mixed_to_behavioral_of_compiled
    (G : GameTheory.Protocol n S V A Sig)
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    [∀ i, Finite ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := compileInfoOn G) i)]
    [∀ i, Fintype (Option ((compileLSM G).Act i))]
    (hPR : (compileInfoOn G).PerfectRecall) :
    KuhnMixedToBehavioralViaOutcome
      (Execution.BehavioralProfile (compileInfoOn G))
      (InfoModel.MixedProfile (I := compileInfoOn G))
      (Execution.PureProfile (compileInfoOn G))
      (compileInfoOn G).Outcome
      (InfoModel.mixedJoint (I := compileInfoOn G))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  simpa using
    (GameTheory.Theorems.kuhn_mixed_to_behavioral
      (I := compileInfoOn G) (D := D) (k := k) hPR)

/-- Full Kuhn reduction for the compiled sequential semantics.

This packages the generic `InfoModel` Kuhn theorem without adding any
language-specific proof burden beyond supplying the compiled dynamics and the
generic theorem's own finiteness/perfect-recall hypotheses. -/
theorem kuhn_complete_of_compiled
    (G : GameTheory.Protocol n S V A Sig)
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    [∀ i, Fintype ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := compileInfoOn G) i)]
    [∀ i, Fintype (Option ((compileLSM G).Act i))]
    (hPR : (compileInfoOn G).PerfectRecall) :
    KuhnCompleteViaOutcome
      (Execution.BehavioralProfile (compileInfoOn G))
      (InfoModel.MixedProfile (I := compileInfoOn G))
      (Execution.PureProfile (compileInfoOn G))
      (compileInfoOn G).Outcome
      (mixedOfBehavioralCanonical (I := compileInfoOn G))
      (InfoModel.mixedJoint (I := compileInfoOn G))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  simpa using
    (GameTheory.Theorems.kuhn_complete
      (I := compileInfoOn G) (D := D) (k := k) hPR)

end GameTheory.Theorems.Sequential
