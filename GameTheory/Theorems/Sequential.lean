import GameTheory.Languages.Sequential.Compile

/-!
# GameTheory.Theorems.Sequential

Target-side reduction lemmas for compiled sequential protocols.

This file is intentionally thin. It packages the structural equivalence between
native protocol SOS and the compiled `InfoModel` presentation, so later ports of
Kuhn/Zermelo-style theorems can depend on one semantic interface.
-/

namespace GameTheory.Theorems.Sequential

open GameTheory.Sequential

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

/-- Placeholder reduction target for future Kuhn-style ports on compiled
sequential protocols. The substantive theorem port should refine this into the
appropriate behavioral/mixed equivalence statement. -/
def KuhnReductionTarget
    (G : GameTheory.Protocol n S V A Sig) : Prop :=
  ∀ _ : Config G, True

end GameTheory.Theorems.Sequential
