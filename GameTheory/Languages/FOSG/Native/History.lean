/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Languages.Bridges.FOSG.ObsModelCore
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.Execution
import GameTheory.Concepts.Transport.Corners
import GameTheory.Languages.Kuhn.BehavioralToMixedCore
import GameTheory.Languages.Kuhn.MixedToBehavioralCore

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)

noncomputable local instance infoStateFintype_toObsModelCore
    [∀ i, Fintype (G.InfoState i)] :
    ∀ i, Fintype ((toObsModelCore G).InfoState i) := by
  intro i
  simpa [ObsModelCoreBridge.toObsModelCore, ObsModelCore.InfoState] using
    (inferInstance : Fintype (G.InfoState i))


/-- Execution states for the FOSG Kuhn semantics: current world plus current
player information states. -/
abbrev ExecutionState : Type := ObsModelCoreBridge.State G

/-- Pure local strategy type used by the FOSG Kuhn execution semantics. `none`
denotes inactivity. -/
abbrev KuhnLocalStrategy (i : ι) : Type :=
  (toObsModelCore G).LocalStrategy i

/-- Pure profile type used by the FOSG Kuhn execution semantics. -/
abbrev KuhnPureProfile : Type :=
  (toObsModelCore G).PureProfile

/-- Behavioral profile type used by the FOSG Kuhn execution semantics. -/
abbrev KuhnBehavioralProfile : Type :=
  (toObsModelCore G).BehavioralProfile

/-- Bounded run distribution on FOSG execution-state traces. -/
noncomputable abbrev runDist
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (k : Nat) (β : KuhnBehavioralProfile (G := G)) :
    PMF (List (ExecutionState (G := G))) :=
  (toObsModelCore G).runDist k β

/-- Bounded pure-profile run distribution on FOSG execution-state traces. -/
noncomputable abbrev runDistPure
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (k : Nat) (π : KuhnPureProfile (G := G)) :
    PMF (List (ExecutionState (G := G))) :=
  (toObsModelCore G).runDistPure k π

/-- Independent product mixed strategy induced by a Kuhn-semantic behavioral
profile. -/
noncomputable abbrev executionBehavioralToMixedJoint
    [Fintype ι] [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (KuhnLocalStrategy (G := G) i)]
    (β : KuhnBehavioralProfile (G := G)) :
    PMF (KuhnPureProfile (G := G)) :=
  (toObsModelCore G).behavioralToMixedJoint β

/-- Nonrepetition condition used in the behavioral-to-mixed direction. -/
abbrev NoNontrivialInfoStateRepeat
    [Fintype ι] [∀ i, Fintype (Option (Act i))] : Prop :=
  (toObsModelCore G).NoNontrivialInfoStateRepeat

/-- Semantic step-mass invariance condition used in the mixed-to-behavioral
direction. -/
abbrev StepMassInvariant
    [Fintype ι] [∀ i, Fintype (Option (Act i))] : Prop :=
  ObsModelCore.StepMassInvariant (toObsModelCore G)

/-- Semantic step-support factorization condition used in the
mixed-to-behavioral direction. -/
abbrev StepSupportFactorization
    [Fintype ι] [∀ i, Fintype (Option (Act i))] : Prop :=
  ObsModelCore.StepSupportFactorization (toObsModelCore G)

/-- Semantic posterior-locality condition used in the mixed-to-behavioral
direction. -/
abbrev ActionPosteriorLocal
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (i : ι) : Prop :=
  ObsModelCore.ActionPosteriorLocal (toObsModelCore G) i

/-- Stronger semantic obs-locality condition that implies both support
factorization and posterior locality. -/
abbrev ObsLocalFeasibilityFull
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (i : ι) : Prop :=
  ObsModelCore.ObsLocalFeasibilityFull (toObsModelCore G) i

/-- **Kuhn's theorem, behavioral -> mixed direction for FOSGs, at the bounded
execution semantics.**

This is the FOSG-facing API for the execution-level theorem: under the standard
bounded nonrepetition condition on visited information states, the Kuhn
execution semantics induced by a behavioral profile coincides with the product
mixed strategy obtained by independently sampling pure local strategies. -/
theorem behavioral_to_mixed_runDist
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (KuhnLocalStrategy (G := G) i)]
    (hNontriv : NoNontrivialInfoStateRepeat (G := G))
    (β : KuhnBehavioralProfile (G := G)) (k : Nat) :
    runDist (G := G) k β =
      (executionBehavioralToMixedJoint (G := G) β).bind
        (fun π => runDistPure (G := G) k π) := by
  simpa [runDist, runDistPure, executionBehavioralToMixedJoint,
    NoNontrivialInfoStateRepeat] using
    (ObsModelCore.kuhn_behavioral_to_mixed (O := toObsModelCore G)
      (hNontriv := hNontriv) β k)

/-- **Kuhn's theorem, mixed -> behavioral direction for FOSGs, under semantic
step conditions.**

If the FOSG Kuhn execution semantics satisfies the semantic step-mass
invariance, support factorization, and posterior-locality conditions, then
every product mixed strategy over pure local strategies is behaviorally
realizable with the same bounded execution distribution. -/
theorem mixed_to_behavioral_semantic
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : StepMassInvariant (G := G))
    (hFactor : StepSupportFactorization (G := G))
    (hLocal : ∀ i, ActionPosteriorLocal (G := G) i)
    (μ : ∀ i, PMF (KuhnLocalStrategy (G := G) i))
    (k : Nat) :
    ∃ β : KuhnBehavioralProfile (G := G),
      runDist (G := G) k β =
        (Math.PMFProduct.pmfPi μ).bind (fun π => runDistPure (G := G) k π) := by
  simpa [runDist, runDistPure, StepMassInvariant, StepSupportFactorization,
    ActionPosteriorLocal] using
    let hLocalCore : ∀ i, (toObsModelCore G).ActionPosteriorLocal i := by
      intro i
      simpa [ActionPosteriorLocal] using hLocal i
    (ObsModelCore.kuhn_mixed_to_behavioral_semantic (O := toObsModelCore G)
      hMass hFactor hLocalCore μ k)

/-- **Kuhn's theorem, mixed -> behavioral direction for FOSGs, via full
semantic obs-locality.**

This is the stronger semantic FOSG formulation: step-mass invariance together
with full obs-local feasibility already suffices to realize any product mixed
strategy by a behavioral profile with the same bounded execution
distribution. -/
theorem mixed_to_behavioral_of_obsLocal
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : StepMassInvariant (G := G))
    (hObsLocal : ∀ i, ObsLocalFeasibilityFull (G := G) i)
    (μ : ∀ i, PMF (KuhnLocalStrategy (G := G) i))
    (k : Nat) :
    ∃ β : KuhnBehavioralProfile (G := G),
      runDist (G := G) k β =
        (Math.PMFProduct.pmfPi μ).bind (fun π => runDistPure (G := G) k π) := by
  simpa [runDist, runDistPure, StepMassInvariant, ObsLocalFeasibilityFull] using
    let hObsLocalCore : ∀ i, (toObsModelCore G).ObsLocalFeasibilityFull i := by
      intro i
      simpa [ObsLocalFeasibilityFull] using hObsLocal i
    (ObsModelCore.kuhn_mixed_to_behavioral_of_obsLocal (O := toObsModelCore G)
      hMass hObsLocalCore μ k)

/-- Native FOSG pure-strategy type. -/
abbrev PureStrategy (i : ι) : Type :=
  _root_.GameTheory.FOSG.PureStrategy G i

/-- Native FOSG mixed-strategy profile: independently, each player samples a
pure strategy for all of its information states. -/
abbrev MixedProfile : Type :=
  ∀ i, PMF (PureStrategy (G := G) i)

noncomputable instance mixedProfilePureStrategyFintype
    [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy, _root_.GameTheory.FOSG.PureStrategy]
  infer_instance

/-- Native FOSG behavioral-profile type. -/
abbrev BehavioralProfile : Type :=
  _root_.GameTheory.FOSG.BehavioralProfile G

/-- Native joint law induced by an independent per-player mixed profile. -/
noncomputable abbrev mixedProfileJoint
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (G := G)) : PMF (_root_.GameTheory.FOSG.PureProfile G) :=
  Math.PMFProduct.pmfPi μ

/-- Lift a native FOSG pure strategy into the Kuhn execution core. -/
noncomputable def liftPureStrategy
    (i : ι) (π : PureStrategy (G := G) i) : KuhnLocalStrategy (G := G) i := by
  intro v
  exact π v

/-- Lift a native FOSG pure profile into the Kuhn execution core. -/
noncomputable def liftPureProfile
    (π : _root_.GameTheory.FOSG.PureProfile G) : KuhnPureProfile (G := G) :=
  fun i => liftPureStrategy (G := G) i (π i)

/-- Lift a native independent mixed profile into the Kuhn execution core. -/
noncomputable def liftMixedProfile
    (μ : MixedProfile (G := G)) : ∀ i, PMF (KuhnLocalStrategy (G := G) i) :=
  fun i => Math.ProbabilityMassFunction.pushforward (μ i) (liftPureStrategy (G := G) i)

/-- Product sampling commutes with the native-to-core pure-profile lift. -/
theorem liftMixedProfile_joint
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (G := G)) :
    Math.PMFProduct.pmfPi (liftMixedProfile (G := G) μ) =
      Math.ProbabilityMassFunction.pushforward
        (mixedProfileJoint (G := G) μ) (liftPureProfile (G := G)) := by
  classical
  rw [mixedProfileJoint]
  change Math.PMFProduct.pmfPi
      (fun i => Math.ProbabilityMassFunction.pushforward (μ i) (liftPureStrategy (G := G) i)) =
    Math.ProbabilityMassFunction.pushforward (Math.PMFProduct.pmfPi μ)
      (fun π => fun i => liftPureStrategy (G := G) i (π i))
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun i => liftPureStrategy (G := G) i)).symm

/-- Native product mixed strategy induced by independently sampling a pure
strategy at each information state for each player. -/
noncomputable def behavioralToMixed
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]
    (β : BehavioralProfile (G := G)) : ∀ i, PMF (PureStrategy (G := G) i) :=
  by
    classical
    intro i
    exact Math.PMFProduct.pmfPi (β i)

/-- Native joint mixed strategy over pure profiles. -/
noncomputable def behavioralToMixedJoint
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]
    (β : BehavioralProfile (G := G)) : PMF (_root_.GameTheory.FOSG.PureProfile G) :=
  by
    classical
    exact Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)

open Classical in
/-- **Kuhn's theorem, mixed -> behavioral direction for FOSGs, over native
independent per-player mixed strategies.**

Under the semantic step-mass invariance, support factorization, and
posterior-locality assumptions, every native independent mixed profile
is realized by a behavioral profile with the same bounded execution-state
trace distribution. -/
theorem mixed_to_behavioral_runDist
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : StepMassInvariant (G := G))
    (hFactor : StepSupportFactorization (G := G))
    (hLocal : ∀ i, ActionPosteriorLocal (G := G) i)
    (μ : MixedProfile (G := G))
    (k : Nat) :
    ∃ β : KuhnBehavioralProfile (G := G),
      runDist (G := G) k β =
        (mixedProfileJoint (G := G) μ).bind
          (fun π => runDistPure (G := G) k (liftPureProfile (G := G) π)) := by
  obtain ⟨β, hβ⟩ :=
    mixed_to_behavioral_semantic (G := G) hMass hFactor hLocal
      (liftMixedProfile (G := G) μ) k
  refine ⟨β, ?_⟩
  rw [hβ, liftMixedProfile_joint (G := G) μ]
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
  rfl

open Classical in
/-- **Kuhn's theorem, mixed -> behavioral direction for FOSGs, over native
independent per-player mixed strategies, via full semantic obs-locality.**

This is the obs-locality convenience form of `mixed_to_behavioral_runDist`. -/
theorem mixed_to_behavioral_runDist_of_obsLocal
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : StepMassInvariant (G := G))
    (hObsLocal : ∀ i, ObsLocalFeasibilityFull (G := G) i)
    (μ : MixedProfile (G := G))
    (k : Nat) :
    ∃ β : KuhnBehavioralProfile (G := G),
      runDist (G := G) k β =
        (mixedProfileJoint (G := G) μ).bind
          (fun π => runDistPure (G := G) k (liftPureProfile (G := G) π)) := by
  obtain ⟨β, hβ⟩ :=
    mixed_to_behavioral_of_obsLocal (G := G) hMass hObsLocal
      (liftMixedProfile (G := G) μ) k
  refine ⟨β, ?_⟩
  rw [hβ, liftMixedProfile_joint (G := G) μ]
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
  rfl

/-! ### Native-history mixed-to-behavioral semantics

The bridge model above stores only the current world and player information
states.  For outcome statements over realized FOSG histories we use a second
`ObsModelCore` whose machine state is the native history itself. -/

/-- Native-history Kuhn execution model for a FOSG.

The state is a realized FOSG history. Legal joint moves append a realized
outcome to the history; illegal joint moves self-loop. Terminal histories
self-loop because `G.legal` is false at terminal states. -/
noncomputable def toHistoryObsModelCore
    (G : FOSG ι W Act PrivObs PubObs) :
    ObsModelCore ι G.History (fun i => G.InfoState i) (fun i _ => Option (Act i)) where
  infoState := fun _ => InfoStateCore.identity _
  observe := fun i h => h.playerView i
  machine :=
    { init := History.nil G
      step := fun h a => by
        classical
        exact if hleg : G.legal h.lastState a then
          (G.transition h.lastState ⟨a, hleg⟩).map
            (fun dst => h.extendByOutcome ⟨a, hleg⟩ dst)
        else
          PMF.pure h }

namespace HistoryNative

variable (G : FOSG ι W Act PrivObs PubObs)

noncomputable instance historyInfoStateFintype
    [∀ i, Fintype (G.InfoState i)] :
    ∀ i, Fintype ((toHistoryObsModelCore G).InfoState i) := by
  intro i
  simpa [toHistoryObsModelCore, ObsModelCore.InfoState] using
    (inferInstance : Fintype (G.InfoState i))

end HistoryNative

end Kuhn

end FOSG

end GameTheory
