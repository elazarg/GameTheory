import GameTheory.Languages.FOSG.Compile
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# GameTheory.Languages.Bridges.FOSG.SerialExec

Canonical execution kernel for the rebuilt FOSG -> augmented-EFG bridge.

The first version deliberately uses native FOSG histories as the kernel state.
This keeps the semantic spine aligned with `G.runDist` while the EFG
presentation layer is rebuilt.  If a later EFG tree needs serialized
microstates, they should be introduced as a private presentation refinement
with a theorem back to this kernel, not as a second public semantics.
-/

namespace GameTheory

open Math.Probability

namespace FOSG
namespace AugmentedEFGBridge
namespace SerialExec

variable {ι W : Type} [DecidableEq ι] [Fintype ι]
variable {Act : ι → Type} [∀ i, Fintype (Option (Act i))]
variable {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)
variable [Fintype W]
variable [DecidablePred G.terminal]

/-- The canonical bridge execution state is a native FOSG history.

This is intentionally small.  The EFG bridge may later present this process
using serialized decision nodes, but the theorem-facing state is the original
history whose law is already `G.runDist`. -/
abbrev State : Type :=
  G.History

/-- Erase a bridge execution state to the native FOSG history it represents. -/
abbrev erase (s : State G) : G.History :=
  s

/-- Initial execution state. -/
abbrev root : State G :=
  History.nil G

/-- Original-step execution law. -/
noncomputable def runOriginal
    (k : Nat) (σ : G.LegalBehavioralProfile) : PMF (State G) :=
  G.runDist k σ

@[simp] theorem runOriginal_zero
    (σ : G.LegalBehavioralProfile) :
    runOriginal (G := G) 0 σ = PMF.pure (root G) := by
  simp [runOriginal, root]

/-- Gate theorem for the bridge spine: erasing `SerialExec` execution recovers
the native FOSG run distribution. -/
theorem runOriginal_erases_to_native
    (k : Nat) (σ : G.LegalBehavioralProfile) :
    PMF.map (erase (G := G)) (runOriginal (G := G) k σ) =
      G.runDist k σ := by
  simpa [runOriginal, erase] using
    (PMF.map_id (p := G.runDist k σ))

end SerialExec
end AugmentedEFGBridge
end FOSG
end GameTheory
