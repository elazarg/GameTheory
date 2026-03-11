import GameTheory.Languages.MAID.CompileObs
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.MAID.Kuhn

Kuhn reduction lemmas for compiled MAIDs via the `ObsModel` layer.

This file connects MAID frontier semantics to Kuhn's theorem by:
1. Compiling MAIDs to `ObsModel` via `compileObsModel`
2. Assuming the finiteness / recall conditions needed by the generic theorem
3. Applying ObsModel-level Kuhn corollaries honestly

## Main results

- `kuhn_behavioral_to_mixed_of_compiled` : B→M direction (no recall needed)
- `kuhn_mixed_to_behavioral_of_compiled` : M→B direction (under PSPR)
-/

namespace GameTheory.Languages.MAID

open _root_.MAID
open GameTheory.Theorems
open ObsModel

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

section Kuhn

variable (S : Struct Player n) (sem : Sem S)

/-- The compiled ObsModel for a MAID. -/
noncomputable abbrev compiledObs (S : Struct Player n) (sem : Sem S) :=
  compileObsModel S sem

/-- **Kuhn B→M for compiled MAIDs**: behavioral strategies can be realized as
product mixed strategies.

This requires finiteness of the compiled information-state type; the default
list-backed summary used by `compileObsModel` does not provide that instance
automatically. -/
theorem kuhn_behavioral_to_mixed_of_compiled
    [∀ p, Fintype (Option (FrontierAct S p))]
    [∀ p, Fintype ((compiledObs S sem).InfoState p)]
    (β : BehavioralProfile (compiledObs S sem)) (k : Nat) :
    (compiledObs S sem).runDist k β =
      ((compiledObs S sem).behavioralToMixedJoint β).bind
        ((compiledObs S sem).runDistPure k) :=
  kuhn_behavioral_to_mixed β k

/-- **Kuhn M→B for compiled MAIDs**: under per-step player recall,
product mixed strategies can be realized by behavioral strategies. -/
theorem kuhn_mixed_to_behavioral_of_compiled
    [∀ p, Fintype (Option (FrontierAct S p))]
    [∀ p, Fintype ((compiledObs S sem).InfoState p)]
    [∀ p, Nonempty (Option (FrontierAct S p))]
    (hPSPR : PerStepPlayerRecall (compiledObs S sem))
    (μ : ∀ p, PMF ((compiledObs S sem).LocalStrategy p))
    (k : Nat) :
    ∃ β : BehavioralProfile (compiledObs S sem),
      (compiledObs S sem).runDist k β =
        (Math.PMFProduct.pmfPi μ).bind ((compiledObs S sem).runDistPure k) :=
  kuhn_mixed_to_behavioral_pspr hPSPR μ k

end Kuhn

end GameTheory.Languages.MAID
