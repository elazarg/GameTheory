import GameTheory.Languages.Bridges.FOSG.ObsModelCore
import GameTheory.Languages.FOSG.Execution
import GameTheory.Theorems.Kuhn.BehavioralToMixedCore
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore

/-!
# Kuhn's Theorem for FOSGs

This file exposes the behavioral-to-mixed direction of Kuhn's theorem for
factored-observation stochastic games by transporting the existing
`ObsModelCore` theorem across the FOSG bridge.

The theorem is stated in terms of FOSG-specific execution states and profiles,
not in terms of the bridge implementation.
-/

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- FOSG execution states for the Kuhn semantics: current world plus current
player information states. -/
abbrev State
    (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ObsModelCoreBridge.State G

/-- FOSG local information states used by the Kuhn execution model. -/
abbrev InfoState
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  G.InfoState i

/-- Pure local strategy type for the FOSG Kuhn semantics. `none` denotes
inactivity. -/
abbrev LocalStrategy
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  (toObsModelCore G).LocalStrategy i

section CoreInstances

variable (G : FOSG ι W Act PrivObs PubObs)
variable [∀ i, Fintype (G.InfoState i)]

noncomputable instance infoStateFintype_toObsModelCore :
    ∀ i, Fintype ((toObsModelCore G).InfoState i) := by
  intro i
  simpa [ObsModelCoreBridge.toObsModelCore, ObsModelCore.InfoState, Kuhn.InfoState] using
    (inferInstance : Fintype (G.InfoState i))

end CoreInstances

/-- Pure profile for the FOSG Kuhn semantics. -/
abbrev PureProfile
    (G : FOSG ι W Act PrivObs PubObs) : Type :=
  (toObsModelCore G).PureProfile

/-- Behavioral profile for the FOSG Kuhn semantics. -/
abbrev BehavioralProfile
    (G : FOSG ι W Act PrivObs PubObs) : Type :=
  (toObsModelCore G).BehavioralProfile

/-- Bounded run distribution on FOSG execution-state traces. -/
noncomputable abbrev runDist
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (k : Nat) (β : BehavioralProfile G) :
    PMF (List (State G)) :=
  (toObsModelCore G).runDist k β

/-- Bounded pure-profile run distribution on FOSG execution-state traces. -/
noncomputable abbrev runDistPure
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (k : Nat) (π : PureProfile G) :
    PMF (List (State G)) :=
  (toObsModelCore G).runDistPure k π

/-- Independent product mixed strategy induced by a behavioral profile. -/
noncomputable abbrev behavioralToMixedJoint
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalStrategy G i)]
    (β : BehavioralProfile G) :
    PMF (PureProfile G) :=
  (toObsModelCore G).behavioralToMixedJoint β

/-- FOSG-side statement of the nontrivial-information-state nonrepetition
condition used in the behavioral-to-mixed direction. -/
abbrev NoNontrivialInfoStateRepeat
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] : Prop :=
  (toObsModelCore G).NoNontrivialInfoStateRepeat

/-- FOSG-side name for the semantic step-mass invariance condition used in the
mixed-to-behavioral direction. -/
abbrev StepMassInvariant
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] : Prop :=
  ObsModelCore.StepMassInvariant (toObsModelCore G)

/-- FOSG-side name for the semantic step-support factorization condition used
in the mixed-to-behavioral direction. -/
abbrev StepSupportFactorization
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] : Prop :=
  ObsModelCore.StepSupportFactorization (toObsModelCore G)

/-- FOSG-side name for the semantic posterior-locality condition used in the
mixed-to-behavioral direction. -/
abbrev ActionPosteriorLocal
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (i : ι) : Prop :=
  ObsModelCore.ActionPosteriorLocal (toObsModelCore G) i

/-- FOSG-side name for the stronger semantic locality condition that implies
both support factorization and posterior locality in the mixed-to-behavioral
direction. -/
abbrev ObsLocalFeasibilityFull
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (i : ι) : Prop :=
  ObsModelCore.ObsLocalFeasibilityFull (toObsModelCore G) i

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Kuhn's theorem, behavioral -> mixed direction for FOSGs.**

Under the standard bounded nonrepetition condition on visited information
states, every behavioral profile on a FOSG induces the same bounded execution
distribution as the corresponding independent product mixed strategy. -/
theorem behavioral_to_mixed
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalStrategy G i)]
    (hNontriv : NoNontrivialInfoStateRepeat G)
    (β : BehavioralProfile G) (k : Nat) :
    runDist G k β =
      (behavioralToMixedJoint G β).bind (fun π => runDistPure G k π) := by
  letI : ∀ i, Fintype ((toObsModelCore G).InfoState i) :=
    infoStateFintype_toObsModelCore (G := G)
  simpa [runDist, runDistPure, behavioralToMixedJoint, NoNontrivialInfoStateRepeat] using
    (ObsModelCore.kuhn_behavioral_to_mixed (O := toObsModelCore G)
      (hNontriv := hNontriv) β k)

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Kuhn's theorem, mixed -> behavioral direction for FOSGs, stated at the
semantic level.**

If the FOSG execution semantics satisfies the core step-mass invariance,
support-factorization, and posterior-locality conditions, then every product
distribution over pure local strategies is behaviorally realizable with the
same bounded execution distribution. -/
theorem mixed_to_behavioral_semantic
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : StepMassInvariant G)
    (hFactor : StepSupportFactorization G)
    (hLocal : ∀ i, ActionPosteriorLocal G i)
    (μ : ∀ i, PMF (LocalStrategy G i))
    (k : Nat) :
    ∃ β : BehavioralProfile G,
      runDist G k β = (Math.PMFProduct.pmfPi μ).bind (fun π => runDistPure G k π) := by
  letI : ∀ i, Fintype ((toObsModelCore G).InfoState i) :=
    infoStateFintype_toObsModelCore (G := G)
  simpa [runDist, runDistPure, StepMassInvariant, StepSupportFactorization,
    ActionPosteriorLocal] using
    (ObsModelCore.kuhn_mixed_to_behavioral_semantic (O := toObsModelCore G)
      hMass hFactor hLocal μ k)

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Kuhn's theorem, mixed -> behavioral direction for FOSGs, via full
semantic obs-locality.**

This is the stronger semantic FOSG formulation: step-mass invariance together
with full obs-local feasibility already suffices to realize any product mixed
strategy by a behavioral profile with the same bounded execution
distribution. -/
theorem mixed_to_behavioral_of_obsLocal
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : StepMassInvariant G)
    (hObsLocal : ∀ i, ObsLocalFeasibilityFull G i)
    (μ : ∀ i, PMF (LocalStrategy G i))
    (k : Nat) :
    ∃ β : BehavioralProfile G,
      runDist G k β = (Math.PMFProduct.pmfPi μ).bind (fun π => runDistPure G k π) := by
  letI : ∀ i, Fintype ((toObsModelCore G).InfoState i) :=
    infoStateFintype_toObsModelCore (G := G)
  simpa [runDist, runDistPure, StepMassInvariant, ObsLocalFeasibilityFull] using
    (ObsModelCore.kuhn_mixed_to_behavioral_of_obsLocal (O := toObsModelCore G)
      hMass hObsLocal μ k)

namespace Native

open scoped BigOperators

variable (G : FOSG ι W Act PrivObs PubObs)

/-- Native FOSG pure-strategy type. -/
abbrev PureStrategy (i : ι) : Type :=
  _root_.GameTheory.FOSG.PureStrategy G i

/-- Native FOSG behavioral-profile type. -/
abbrev BehavioralProfile : Type :=
  _root_.GameTheory.FOSG.BehavioralProfile G

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

section Step

variable [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]

noncomputable local instance pureStrategyFintype
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy]
  infer_instance

noncomputable local instance pureProfileFintype
    : Fintype (_root_.GameTheory.FOSG.PureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.PureProfile, PureStrategy]
  infer_instance

section Raw

variable [∀ i, DecidableEq (Act i)]

omit [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem stepActionProb_pureToBehavioral
    (π : _root_.GameTheory.FOSG.PureProfile G) (pref : G.History) (e : G.Step) :
    G.stepActionProb (G.pureToBehavioral π) pref e =
      ∏ i, match e.ownAction? i with
        | some ai => if π i (pref.playerView i) = ai then 1 else 0
        | none => 1 := by
  classical
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  cases hact : e.ownAction? i with
  | none =>
      simp
  | some ai =>
      rw [FOSG.pureToBehavioral_apply]
      by_cases hEq : π i (pref.playerView i) = ai
      · simp [PMF.pure_apply, hEq]
      · have hEq' : ¬ ai = π i (pref.playerView i) := by
          simpa [eq_comm] using hEq
        simp [PMF.pure_apply, hEq, hEq']

/-- One-step Kuhn marginal at the raw dependent function type. -/
theorem marginal_stepActionProb_raw
    (β : BehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
      (Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)) ρ *
        (∏ i, match e.ownAction? i with
          | some ai => if ρ i (pref.playerView i) = ai then 1 else 0
          | none => 1) =
      G.stepActionProb β pref e := by
  classical
  have hprod :
      (∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        (Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)) ρ *
          (∏ i, match e.ownAction? i with
            | some ai => if ρ i (pref.playerView i) = ai then 1 else 0
            | none => 1)) =
      ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        ∏ i,
          (behavioralToMixed (G := G) β i) (ρ i) *
            (match e.ownAction? i with
              | some ai => if ρ i (pref.playerView i) = ai then 1 else 0
              | none => 1) := by
    refine Finset.sum_congr rfl ?_
    intro ρ _
    rw [Math.PMFProduct.pmfPi_apply, ← Finset.prod_mul_distrib]
  rw [hprod]
  rw [show (∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        ∏ i,
          (behavioralToMixed (G := G) β i) (ρ i) *
            (match e.ownAction? i with
              | some ai => if ρ i (pref.playerView i) = ai then 1 else 0
              | none => 1)) =
      ∏ i, ∑ πi : PureStrategy (G := G) i,
        (behavioralToMixed (G := G) β i) πi *
          (match e.ownAction? i with
            | some ai => if πi (pref.playerView i) = ai then 1 else 0
            | none => 1) by
      simpa [PureProfile] using
        (@Fintype.prod_sum ι ENNReal _ _ _ (fun i => PureStrategy (G := G) i) _
          (fun i πi =>
            (behavioralToMixed (G := G) β i) πi *
              (match e.ownAction? i with
                | some ai => if πi (pref.playerView i) = ai then 1 else 0
                | none => 1))).symm]
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  cases hact : e.ownAction? i with
  | none =>
      have hsum :
          (∑ πi : PureStrategy (G := G) i, (behavioralToMixed (G := G) β i) πi) = 1 := by
        have := PMF.tsum_coe (behavioralToMixed (G := G) β i)
        simpa [behavioralToMixed, PureStrategy, tsum_fintype,
          Math.PMFProduct.pmfPi_apply] using this
      simp [hsum]
  | some ai =>
      have hcoord :
          ∑ πi : (G.InfoState i → Act i),
            (if πi (pref.playerView i) = ai then (behavioralToMixed (G := G) β i) πi else 0) =
              β i (pref.playerView i) ai := by
        simpa [behavioralToMixed] using
          Math.PMFProduct.pmfPi_coord_mass (β i) (pref.playerView i) ai
      simpa [hact, mul_ite, mul_one, mul_zero] using hcoord

end Raw

/-- One-step Kuhn marginal in the native FOSG profile type. -/
theorem marginal_stepActionProb
    (β : BehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ π : _root_.GameTheory.FOSG.PureProfile G,
      behavioralToMixedJoint (G := G) β π *
        G.stepActionProb (G.pureToBehavioral π) pref e =
      G.stepActionProb β pref e := by
  classical
  rw [show (∑ π : _root_.GameTheory.FOSG.PureProfile G,
        behavioralToMixedJoint (G := G) β π *
          G.stepActionProb (G.pureToBehavioral π) pref e) =
      ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        (Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)) ρ *
          (∏ i, match e.ownAction? i with
            | some ai => if ρ i (pref.playerView i) = ai then 1 else 0
            | none => 1) by
      refine Finset.sum_congr rfl ?_
      intro ρ _
      rw [stepActionProb_pureToBehavioral (G := G) ρ pref e]
      rfl]
  simpa using marginal_stepActionProb_raw (G := G) β pref e

/-- One-step Kuhn marginal for realized step weights in native FOSG semantics. -/
theorem marginal_stepProb
    (β : BehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ π : _root_.GameTheory.FOSG.PureProfile G,
      behavioralToMixedJoint (G := G) β π *
        G.stepProb (G.pureToBehavioral π) pref e =
      G.stepProb β pref e := by
  let p : ENNReal := (G.transition e.src e.act) e.dst
  calc
    ∑ π : _root_.GameTheory.FOSG.PureProfile G,
        behavioralToMixedJoint (G := G) β π *
          G.stepProb (G.pureToBehavioral π) pref e
      = ∑ π : _root_.GameTheory.FOSG.PureProfile G,
          (behavioralToMixedJoint (G := G) β π *
            G.stepActionProb (G.pureToBehavioral π) pref e) * p := by
              simp [p, mul_assoc]
    _ = (∑ π : _root_.GameTheory.FOSG.PureProfile G,
          behavioralToMixedJoint (G := G) β π *
            G.stepActionProb (G.pureToBehavioral π) pref e) * p := by
              rw [Finset.sum_mul]
    _ = G.stepActionProb β pref e * p := by
          rw [marginal_stepActionProb (G := G) β pref e]
    _ = G.stepProb β pref e := by
          simp [p]

end Step

end Native

end Kuhn

end FOSG

end GameTheory
