import GameTheory.Theorems.Kuhn.ObsModel
import GameTheory.Theorems.Kuhn.BehavioralToMixedCore

/-! # Behavioral -> Mixed direction of Kuhn's theorem for `ObsModel`

This file is a thin migration wrapper.

The generic B->M theorem now lives on `ObsModelCore`; the stronger `ObsModel`
surface only adds the snapshot structure needed to prove that the core-side
`HorizonSeparation` hypothesis holds automatically. Existing clients can keep
using `ObsModel.kuhn_behavioral_to_mixed`, but the proof is delegated to the
core theorem.
-/

set_option autoImplicit false

namespace ObsModel

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModel ι σ Obs Act}

section CoreInstances

variable [hInfo : ∀ i, Fintype (O.InfoState i)]

noncomputable instance infoStateFintype_toCore :
    ∀ i, Fintype (O.toCore.InfoState i) := by
  intro i
  simpa [ObsModel.toCore, ObsModelCore.InfoState, ObsModel.InfoState] using
    (hInfo i)

end CoreInstances

section Definitions

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

open Classical in
/-- Convert a behavioral profile to per-player mixed strategies by taking the
independent product over information states for each player. -/
noncomputable abbrev behavioralToMixed
    (β : BehavioralProfile O) : ∀ i, PMF (O.LocalStrategy i) :=
  O.toCore.behavioralToMixed β

open Classical in
/-- The full product mixed strategy: first over information states per player,
then over players. -/
noncomputable abbrev behavioralToMixedJoint
    [∀ i, Fintype (O.LocalStrategy i)]
    (β : BehavioralProfile O) : PMF (PureProfile O) :=
  O.toCore.behavioralToMixedJoint β

end Definitions

section HorizonSeparation

/-- Snapshot-refined information states cannot recur at different horizons. -/
theorem horizonSeparation_toCore (O : ObsModel ι σ Obs Act) :
    O.toCore.HorizonSeparation := by
  intro i ss ss' hEq hlt
  have hlen : ss.length = ss'.length := by
    simpa [O.stateDepth_projectStates i ss, O.stateDepth_projectStates i ss'] using
      congrArg (O.stateDepth i) hEq
  omega

end HorizonSeparation

section MainTheorem

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Kuhn's theorem, B->M direction for `ObsModel`.**
Every behavioral profile has the same bounded trace distribution as the
product mixed strategy. No recall conditions are needed. -/
theorem kuhn_behavioral_to_mixed
    [∀ i, Fintype (O.LocalStrategy i)]
    (β : BehavioralProfile O) (k : Nat) :
    O.runDist k β =
      (O.behavioralToMixedJoint β).bind (fun π => O.runDistPure k π) := by
  simpa [ObsModel.runDist, ObsModel.runDistPure, ObsModel.behavioralToMixedJoint,
    ObsModel.behavioralToMixed, ObsModel.toCore] using
    (ObsModelCore.kuhn_behavioral_to_mixed (O := O.toCore)
      (hSep := O.horizonSeparation_toCore) β k)

end MainTheorem

end ObsModel
