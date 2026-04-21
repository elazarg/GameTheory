import GameTheory.Languages.Bridges.FOSG.ObsModelCore
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.Execution
import GameTheory.Theorems.Kuhn.BehavioralToMixedCore
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore

/-!
# Kuhn's Theorem for FOSGs

This file has two layers:

- `Kuhn.Bridge` exposes the existing `ObsModelCore` Kuhn theorems through the
  FOSG bridge.
- `Kuhn` itself contains native FOSG behavioral-to-mixed results stated
  directly in terms of FOSG histories, terminal laws, and expected utilities.
-/

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

namespace Bridge

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
  simpa [ObsModelCoreBridge.toObsModelCore, ObsModelCore.InfoState] using
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

end Bridge

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
private theorem stepActionProb_pureToBehavioral
    (π : _root_.GameTheory.FOSG.PureProfile G) (pref : G.History) (e : G.Step) :
    G.stepActionProb (G.pureToBehavioral π) pref e =
      ∏ i, if π i (pref.playerView i) = e.ownAction? i then 1 else 0 := by
  classical
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [FOSG.pureToBehavioral_apply]
  by_cases hEq : π i (pref.playerView i) = e.ownAction? i
  · simp [PMF.pure_apply, hEq]
  · have hEq' : e.ownAction? i ≠ π i (pref.playerView i) := by
      simpa [eq_comm] using hEq
    simp [PMF.pure_apply, hEq, hEq']

/-- One-step Kuhn marginal at the raw dependent function type. -/
private theorem marginal_stepActionProb_raw
    (β : BehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
      (Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)) ρ *
        (∏ i, if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0) =
      G.stepActionProb β pref e := by
  classical
  have hprod :
      (∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        (Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)) ρ *
          (∏ i, if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0)) =
      ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        ∏ i,
          (behavioralToMixed (G := G) β i) (ρ i) *
            (if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro ρ _
    rw [Math.PMFProduct.pmfPi_apply, ← Finset.prod_mul_distrib]
  rw [hprod]
  rw [show (∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        ∏ i,
          (behavioralToMixed (G := G) β i) (ρ i) *
            (if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0)) =
      ∏ i, ∑ πi : PureStrategy (G := G) i,
        (behavioralToMixed (G := G) β i) πi *
          (if πi (pref.playerView i) = e.ownAction? i then 1 else 0) by
      simpa [PureProfile] using
        (@Fintype.prod_sum ι ENNReal _ _ _ (fun i => PureStrategy (G := G) i) _
          (fun i πi =>
            (behavioralToMixed (G := G) β i) πi *
              (if πi (pref.playerView i) = e.ownAction? i then 1 else 0))).symm]
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  have hcoord :
      ∑ πi : PureStrategy (G := G) i,
        (behavioralToMixed (G := G) β i) πi *
          (if πi (pref.playerView i) = e.ownAction? i then 1 else 0) =
            β i (pref.playerView i) (e.ownAction? i) := by
    simpa [behavioralToMixed, mul_ite, mul_one, mul_zero] using
      Math.PMFProduct.pmfPi_coord_mass (β i) (pref.playerView i) (e.ownAction? i)
  simpa using hcoord

end Raw

/-- One-step Kuhn marginal in the native FOSG profile type. -/
private theorem marginal_stepActionProb
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
          (∏ i, if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0) by
      refine Finset.sum_congr rfl ?_
      intro ρ _
      rw [stepActionProb_pureToBehavioral (G := G) ρ pref e]
      rfl]
  simpa using marginal_stepActionProb_raw (G := G) β pref e

/-- One-step Kuhn marginal for realized step weights in native FOSG semantics. -/
private theorem marginal_stepProb
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

section ScalarIndependence

variable [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]

noncomputable local instance pureStrategyFintypeScalar
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy]
  infer_instance

noncomputable local instance pureProfileFintypeScalar
    : Fintype (_root_.GameTheory.FOSG.PureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.PureProfile, PureStrategy]
  infer_instance

/-- Swap coordinates between two pure profiles according to a predicate on
player-information-state coordinates. -/
private noncomputable def swapProfileBy
    (P : ∀ i, G.InfoState i → Prop)
    (π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G) :
    _root_.GameTheory.FOSG.PureProfile G := by
  classical
  exact fun i v => if P i v then π₁ i v else π₂ i v

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
private theorem swapProfileBy_involutive
    (P : ∀ i, G.InfoState i → Prop) :
    Function.Involutive
      (fun (p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G) =>
        (swapProfileBy (G := G) P p.1 p.2,
          swapProfileBy (G := G) P p.2 p.1)) := by
  classical
  intro ⟨π₁, π₂⟩
  apply Prod.ext
  · funext i v
    by_cases hv : P i v <;> simp [swapProfileBy, hv]
  · funext i v
    by_cases hv : P i v <;> simp [swapProfileBy, hv]

open Classical in
private theorem swapBy_weight_eq
    (P : ∀ i, G.InfoState i → Prop)
    (β : BehavioralProfile (G := G))
    (π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G) :
    behavioralToMixedJoint (G := G) β (swapProfileBy (G := G) P π₁ π₂) *
      behavioralToMixedJoint (G := G) β (swapProfileBy (G := G) P π₂ π₁) =
    behavioralToMixedJoint (G := G) β π₁ *
      behavioralToMixedJoint (G := G) β π₂ := by
  simp only [behavioralToMixedJoint, behavioralToMixed,
    Math.PMFProduct.pmfPi_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext i
  simp only [swapProfileBy]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext v
  by_cases hv : P i v <;> simp [hv, mul_comm]

/-- Scalar independence under the native FOSG product mixed measure: if `f`
depends only on coordinates where `P` holds, and `g` depends only on the
complementary coordinates, then `E[f * g] = E[f] * E[g]`. -/
private theorem scalar_indep
    (P : ∀ i, G.InfoState i → Prop)
    (β : BehavioralProfile (G := G))
    (f g : _root_.GameTheory.FOSG.PureProfile G → ENNReal)
    (hf : ∀ π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G,
      (∀ i (v : G.InfoState i), P i v → π₁ i v = π₂ i v) →
        f π₁ = f π₂)
    (hg : ∀ π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G,
      (∀ i (v : G.InfoState i), ¬ P i v → π₁ i v = π₂ i v) →
        g π₁ = g π₂) :
    ∑ π, behavioralToMixedJoint (G := G) β π * (f π * g π) =
      (∑ π, behavioralToMixedJoint (G := G) β π * f π) *
      (∑ π, behavioralToMixedJoint (G := G) β π * g π) := by
  set ν : PMF (_root_.GameTheory.FOSG.PureProfile G) := behavioralToMixedJoint (G := G) β
  have hf_swap :
      ∀ π₁ π₂, f (swapProfileBy (G := G) P π₁ π₂) = f π₁ := by
    intro π₁ π₂
    apply hf
    intro i v hv
    simp [swapProfileBy, hv]
  have hg_swap :
      ∀ π₁ π₂, g (swapProfileBy (G := G) P π₁ π₂) = g π₂ := by
    intro π₁ π₂
    apply hg
    intro i v hv
    simp [swapProfileBy, hv]
  let W := fun π => ν π
  let Fsame : _root_.GameTheory.FOSG.PureProfile G ×
      _root_.GameTheory.FOSG.PureProfile G → ENNReal :=
    fun p => W p.1 * W p.2 * (f p.1 * g p.1)
  let Fcross : _root_.GameTheory.FOSG.PureProfile G ×
      _root_.GameTheory.FOSG.PureProfile G → ENNReal :=
    fun p => W p.1 * W p.2 * (f p.1 * g p.2)
  let e : _root_.GameTheory.FOSG.PureProfile G ×
      _root_.GameTheory.FOSG.PureProfile G →
      _root_.GameTheory.FOSG.PureProfile G ×
        _root_.GameTheory.FOSG.PureProfile G :=
    fun p => (swapProfileBy (G := G) P p.1 p.2,
      swapProfileBy (G := G) P p.2 p.1)
  have he : Function.Involutive e := swapProfileBy_involutive (G := G) P
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro ⟨π₁, π₂⟩
    simp only [Fcross, Fsame, e, W]
    rw [swapBy_weight_eq (G := G) P β π₁ π₂, hf_swap π₁ π₂, hg_swap π₁ π₂]
  have hFsame_eq_Fcross :
      ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fsame p =
        ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fcross p := by
    calc
      ∑ p, Fsame p = ∑ p, Fsame (e p) :=
        (Math.PMFProduct.sum_univ_eq_sum_univ_of_involutive e he Fsame).symm
      _ = ∑ p, Fcross p := by
        congr 1
        funext p
        exact (hpoint p).symm
  have hFsame_expand :
      ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fsame p =
        (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by
    have h1 :
        ∀ (a b : _root_.GameTheory.FOSG.PureProfile G),
          Fsame (a, b) = (ν a * (f a * g a)) * ν b := fun a b => by
            simp [Fsame, W]
            ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum, ← Finset.sum_mul]
  have hFcross_expand :
      ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fcross p =
        (∑ π, ν π * f π) * (∑ π, ν π * g π) := by
    have h1 :
        ∀ (a b : _root_.GameTheory.FOSG.PureProfile G),
          Fcross (a, b) = (ν a * f a) * (ν b * g b) := fun a b => by
            simp [Fcross, W]
            ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hsum_one : (∑ π : _root_.GameTheory.FOSG.PureProfile G, ν π) = 1 := by
    have := PMF.tsum_coe ν
    rwa [tsum_fintype] at this
  calc
    ∑ π, ν π * (f π * g π) = (∑ π, ν π * (f π * g π)) * 1 := by ring
    _ = (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by rw [hsum_one]
    _ = ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fsame p := hFsame_expand.symm
    _ = ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fcross p := hFsame_eq_Fcross
    _ = (∑ π, ν π * f π) * (∑ π, ν π * g π) := hFcross_expand

section StepCorollaries

/-- Scalar independence specialized to the realized one-step weight at a given
history. If `f` depends only on coordinates in `P`, and the current
information states of `h` all lie outside `P`, then `f` is independent of the
next-step realized weight. -/
private theorem scalar_indep_stepProb
    (P : ∀ i, G.InfoState i → Prop)
    (β : BehavioralProfile (G := G))
    (f : _root_.GameTheory.FOSG.PureProfile G → ENNReal)
    (h : G.History) (e : G.Step)
    (hf : ∀ π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G,
      (∀ i (v : G.InfoState i), P i v → π₁ i v = π₂ i v) →
        f π₁ = f π₂)
    (hP : ∀ i, ¬ P i (h.playerView i)) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      (f π * G.stepProb (G.pureToBehavioral π) h e) =
        (∑ π, behavioralToMixedJoint (G := G) β π * f π) *
          G.stepProb β h e := by
  classical
  have hg : ∀ π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G,
      (∀ i (v : G.InfoState i), ¬ P i v → π₁ i v = π₂ i v) →
        G.stepProb (G.pureToBehavioral π₁) h e =
          G.stepProb (G.pureToBehavioral π₂) h e := by
    intro π₁ π₂ hag
    rw [G.stepProb_eq_stepActionProb_mul_transition,
      G.stepProb_eq_stepActionProb_mul_transition]
    congr 1
    unfold FOSG.stepActionProb
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [FOSG.pureToBehavioral_apply, FOSG.pureToBehavioral_apply]
    have hEq : π₁ i (h.playerView i) = π₂ i (h.playerView i) := hag i _ (hP i)
    simp [PMF.pure_apply, hEq]
  calc
    ∑ π, behavioralToMixedJoint (G := G) β π *
        (f π * G.stepProb (G.pureToBehavioral π) h e)
      = (∑ π, behavioralToMixedJoint (G := G) β π * f π) *
          (∑ π, behavioralToMixedJoint (G := G) β π *
            G.stepProb (G.pureToBehavioral π) h e) := by
              exact scalar_indep (G := G) P β f
                (fun π => G.stepProb (G.pureToBehavioral π) h e) hf hg
    _ = (∑ π, behavioralToMixedJoint (G := G) β π * f π) *
          G.stepProb β h e := by
            rw [marginal_stepProb (G := G) β h e]

end StepCorollaries

end ScalarIndependence

section HistoryMarginal

variable [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]

noncomputable local instance pureStrategyFintypeHistory
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy]
  infer_instance

noncomputable local instance pureProfileFintypeHistory
    : Fintype (_root_.GameTheory.FOSG.PureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.PureProfile, PureStrategy]
  infer_instance

/-- Information-state coordinates that already appeared on a proper prefix of
`h`. -/
private def SeenBefore
    (h : G.History) (i : ι) (v : G.InfoState i) : Prop :=
  ∃ h' : G.History, h'.IsPrefix h ∧ h' ≠ h ∧ h'.playerView i = v

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
private theorem stepChainFrom_prefix
    {w : W} {es : List G.Step} {e : G.Step}
    (hchain : G.StepChainFrom w (es ++ [e])) :
    G.StepChainFrom w es := by
  induction es generalizing w with
  | nil =>
      trivial
  | cons e₀ es ih =>
      rcases hchain with ⟨hsrc, htail⟩
      exact And.intro hsrc (ih htail)

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
private theorem stepChainFrom_last_src
    {w : W} {es : List G.Step} {e : G.Step}
    (hchain : G.StepChainFrom w (es ++ [e])) :
    e.src = G.lastStateFrom w es := by
  induction es generalizing w with
  | nil =>
      simpa [StepChainFrom, lastStateFrom] using hchain.1
  | cons e₀ es ih =>
      rcases hchain with ⟨hsrc, htail⟩
      simpa [lastStateFrom] using ih htail

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
private theorem seenBefore_mono_appendStep
    {h : G.History} {e : G.Step} {hsrc : e.src = h.lastState}
    {i : ι} {v : G.InfoState i}
    (hSeen : SeenBefore (G := G) h i v) :
    SeenBefore (G := G) (h.appendStep e hsrc) i v := by
  rcases hSeen with ⟨h', hpref, hne, hv⟩
  refine ⟨h', History.prefix_trans hpref ?_, ?_, hv⟩
  · exact ⟨[e], by simp [History.appendStep]⟩
  · intro hEq
    have hpref' : (h.appendStep e hsrc).IsPrefix h := by
      simpa [hEq] using hpref
    rcases hpref' with ⟨s, hs⟩
    have hlen := congrArg List.length hs
    simp [History.appendStep] at hlen

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
private theorem seenBefore_current_appendStep
    (h : G.History) (e : G.Step) (hsrc : e.src = h.lastState) (i : ι) :
    SeenBefore (G := G) (h.appendStep e hsrc) i (h.playerView i) := by
  refine ⟨h, ?_, ?_, rfl⟩
  · exact ⟨[e], by simp [History.appendStep]⟩
  · intro hEq
    have hlen := congrArg (fun h' : G.History => h'.steps.length) hEq
    simp [History.appendStep] at hlen

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
private theorem not_seenBefore_current
    (h : G.History) (i : ι) :
    ¬ SeenBefore (G := G) h i (h.playerView i) := by
  intro hSeen
  rcases hSeen with ⟨h', hpref, hne, hv⟩
  exact History.playerView_ne_of_properPrefix (G := G) i hpref hne hv

omit [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
private theorem stepProb_pure_congr_at_history
    {π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G}
    (h : G.History) (e : G.Step)
    (hag : ∀ i, π₁ i (h.playerView i) = π₂ i (h.playerView i)) :
    G.stepProb (G.pureToBehavioral π₁) h e =
      G.stepProb (G.pureToBehavioral π₂) h e := by
  classical
  rw [G.stepProb_eq_stepActionProb_mul_transition,
    G.stepProb_eq_stepActionProb_mul_transition]
  congr 1
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [FOSG.pureToBehavioral_apply, FOSG.pureToBehavioral_apply]
  simp [PMF.pure_apply, hag i]

omit [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
/-- Pure-history weight depends only on the information-state coordinates that
appear on proper prefixes of the history. -/
private theorem prob_pure_congr_of_agreeOnSeenBefore
    {π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G}
    (h : G.History)
    (hag : ∀ i (v : G.InfoState i), SeenBefore (G := G) h i v → π₁ i v = π₂ i v) :
    History.prob (G.pureToBehavioral π₁) h =
      History.prob (G.pureToBehavioral π₂) h := by
  classical
  let H :
      ∀ (es : List G.Step) (hchain : G.StepChainFrom G.init es),
        (∀ i (v : G.InfoState i),
          SeenBefore (G := G) ({ steps := es, chain := hchain } : G.History) i v →
            π₁ i v = π₂ i v) →
          History.prob (G.pureToBehavioral π₁)
              ({ steps := es, chain := hchain } : G.History) =
            History.prob (G.pureToBehavioral π₂)
              ({ steps := es, chain := hchain } : G.History) := by
    intro es
    induction es using List.reverseRecOn with
    | nil =>
        intro hchain hag'
        simp [History.prob]
    | append_singleton es e ih =>
        intro hchain hag'
        let prefChain : G.StepChainFrom G.init es :=
          stepChainFrom_prefix (G := G) hchain
        let pref : G.History := ⟨es, prefChain⟩
        have hsrc : e.src = pref.lastState := by
          simpa [pref, History.lastState] using stepChainFrom_last_src (G := G) hchain
        have hh :
            ({ steps := es ++ [e], chain := hchain } : G.History) = pref.appendStep e hsrc := by
          apply History.ext
          simp [pref, History.appendStep]
        rw [hh] at hag' ⊢
        have hPref :
            History.prob (G.pureToBehavioral π₁) pref =
              History.prob (G.pureToBehavioral π₂) pref := by
          apply ih prefChain
          intro i v hSeen
          exact hag' i v (seenBefore_mono_appendStep (G := G) hSeen)
        have hStep :
            G.stepProb (G.pureToBehavioral π₁) pref e =
            G.stepProb (G.pureToBehavioral π₂) pref e := by
          apply stepProb_pure_congr_at_history (G := G) pref e
          intro i
          exact hag' i _ (seenBefore_current_appendStep (G := G) pref e hsrc i)
        rw [History.prob_appendStep, History.prob_appendStep, hPref, hStep]
  exact H h.steps h.chain hag

/-- Native FOSG behavioral-to-mixed equality for realized-history weights. -/
private theorem marginal_prob
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      History.prob (G.pureToBehavioral π) h =
        History.prob β h := by
  classical
  let H :
      ∀ (es : List G.Step) (hchain : G.StepChainFrom G.init es),
        ∑ π, behavioralToMixedJoint (G := G) β π *
          History.prob (G.pureToBehavioral π) ({ steps := es, chain := hchain } : G.History) =
            History.prob β ({ steps := es, chain := hchain } : G.History) := by
    intro es
    induction es using List.reverseRecOn with
    | nil =>
        intro hchain
        simp [History.prob]
        have := PMF.tsum_coe (behavioralToMixedJoint (G := G) β)
        rwa [tsum_fintype] at this
    | append_singleton es e ih =>
        intro hchain
        let prefChain : G.StepChainFrom G.init es :=
          stepChainFrom_prefix (G := G) hchain
        let pref : G.History := ⟨es, prefChain⟩
        have hsrc : e.src = pref.lastState := by
          simpa [pref, History.lastState] using stepChainFrom_last_src (G := G) hchain
        have hh :
            ({ steps := es ++ [e], chain := hchain } : G.History) = pref.appendStep e hsrc := by
          apply History.ext
          simp [pref, History.appendStep]
        rw [hh]
        calc
          ∑ π, behavioralToMixedJoint (G := G) β π *
              History.prob (G.pureToBehavioral π) (pref.appendStep e hsrc)
            = ∑ π, behavioralToMixedJoint (G := G) β π *
                (History.prob (G.pureToBehavioral π) pref *
                  G.stepProb (G.pureToBehavioral π) pref e) := by
                    refine Finset.sum_congr rfl ?_
                    intro π _
                    rw [History.prob_appendStep]
          _ = (∑ π, behavioralToMixedJoint (G := G) β π *
                History.prob (G.pureToBehavioral π) pref) *
                G.stepProb β pref e := by
                  exact scalar_indep_stepProb (G := G)
                    (P := SeenBefore (G := G) pref) β
                    (fun π => History.prob (G.pureToBehavioral π) pref)
                    pref e
                    (fun π₁ π₂ hag =>
                      prob_pure_congr_of_agreeOnSeenBefore (G := G) pref hag)
                    (fun i => not_seenBefore_current (G := G) pref i)
          _ = History.prob β pref * G.stepProb β pref e := by
                rw [ih prefChain]
          _ = History.prob β (pref.appendStep e hsrc) := by
                rw [History.prob_appendStep]
  exact H h.steps h.chain

end HistoryMarginal

section TerminalCorollaries

variable [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]
variable [DecidablePred G.terminal]

noncomputable local instance pureStrategyFintypeTerminal
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy]
  infer_instance

noncomputable local instance pureProfileFintypeTerminal
    : Fintype (_root_.GameTheory.FOSG.PureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.PureProfile, PureStrategy]
  infer_instance

/-- Native FOSG behavioral-to-mixed equality for terminal-history mass. -/
private theorem marginal_terminalWeight
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      History.terminalWeight (G := G) (G.pureToBehavioral π) h =
        History.terminalWeight (G := G) β h := by
  by_cases hterm : G.terminal h.lastState
  · have hsum :
        (∑ π, behavioralToMixedJoint (G := G) β π *
          History.terminalWeight (G := G) (G.pureToBehavioral π) h) =
          ∑ π, behavioralToMixedJoint (G := G) β π *
            History.prob (G.pureToBehavioral π) h := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalWeight_of_terminal (G := G)
                (σ := G.pureToBehavioral π) hterm]
    rw [History.terminalWeight_of_terminal (G := G) β hterm, hsum, marginal_prob]
  · rw [History.terminalWeight_of_not_terminal (G := G) β hterm]
    have hsum :
        (∑ π, behavioralToMixedJoint (G := G) β π *
          History.terminalWeight (G := G) (G.pureToBehavioral π) h) =
          ∑ π, behavioralToMixedJoint (G := G) β π * 0 := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalWeight_of_not_terminal (G := G)
                (σ := G.pureToBehavioral π) hterm]
    rw [hsum]
    simp

/-- Native FOSG distribution preservation on any finite event of terminal
histories. The induced product mixed strategy assigns the same total
terminal-history mass to every finite set of histories as the behavioral
profile. -/
private theorem marginal_terminalMassOn
    (β : BehavioralProfile (G := G)) (hs : Finset G.History) :
    (∑ π, behavioralToMixedJoint (G := G) β π *
      History.terminalMassOn (G := G) (G.pureToBehavioral π) hs) =
      History.terminalMassOn (G := G) β hs := by
  calc
    ∑ π, behavioralToMixedJoint (G := G) β π *
        History.terminalMassOn (G := G) (G.pureToBehavioral π) hs
      = ∑ π, Finset.sum hs (fun h =>
          behavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π) h) := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalMassOn, Finset.mul_sum]
    _ = Finset.sum hs (fun h => ∑ π,
          behavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π) h) := by
              rw [Finset.sum_comm]
    _ = History.terminalMassOn (G := G) β hs := by
          rw [History.terminalMassOn]
          refine Finset.sum_congr rfl ?_
          intro h hh
          exact marginal_terminalWeight (G := G) β h

/-- Native FOSG terminal-law preservation on finite events. This packages the
behavioral-to-mixed terminal distribution equality as equality of the native
terminal-history event-mass functional. -/
private theorem marginal_terminalLaw
    (β : BehavioralProfile (G := G)) :
    (fun hs =>
      ∑ π, behavioralToMixedJoint (G := G) β π *
        History.terminalLaw (G := G) (G.pureToBehavioral π) hs) =
      History.terminalLaw (G := G) β := by
  funext hs
  simpa [History.terminalLaw] using marginal_terminalMassOn (G := G) β hs

/-- Pointwise real-valued terminal-mass preservation. This is the `toReal`
version of `marginal_terminalWeight`, suitable for expected-utility
calculations. -/
private theorem marginal_terminalWeight_toReal
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
      (History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal =
      (History.terminalWeight (G := G) β h).toReal := by
  calc
    ∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
        (History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal
      = ∑ π,
          (behavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [ENNReal.toReal_mul]
    _ = (∑ π,
          behavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal := by
          symm
          apply ENNReal.toReal_sum
          intro π _
          exact ENNReal.mul_ne_top
            (PMF.apply_ne_top (behavioralToMixedJoint (G := G) β) π)
            (History.terminalWeight_ne_top (G := G) (σ := G.pureToBehavioral π) h)
    _ = (History.terminalWeight (G := G) β h).toReal := by
          rw [marginal_terminalWeight (G := G) β h]

/-- `terminalWeight` specialized to the classical decidability instance, used
internally to keep private utility lemmas free of hidden section-instance
arguments. -/
private noncomputable def terminalWeightClassical
    [Fintype G.History]
    (σ : BehavioralProfile (G := G)) (h : G.History) : ENNReal :=
  @History.terminalWeight ι W _ Act PrivObs PubObs _ G (Classical.decPred G.terminal) σ h

omit [DecidablePred G.terminal] in
/-- Native FOSG preservation of the terminal-history utility sum under the
product mixed strategy induced by a behavioral profile. -/
private theorem marginal_terminalUtilitySum
    [Fintype G.History]
    (β : BehavioralProfile (G := G)) (i : ι) :
    ∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
      (∑ h : G.History,
        (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal *
          History.utility h i) =
      ∑ h : G.History,
        (terminalWeightClassical (G := G) β h).toReal * History.utility h i := by
  classical
  letI : DecidablePred G.terminal := Classical.decPred G.terminal
  calc
    ∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
        ∑ h : G.History,
          (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal *
            History.utility h i
      = ∑ π, ∑ h : G.History,
          ((behavioralToMixedJoint (G := G) β π).toReal *
            (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal) *
              History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro π _
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro h _
                simp [mul_assoc]
    _ = ∑ h : G.History, ∑ π,
          ((behavioralToMixedJoint (G := G) β π).toReal *
            (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal) *
              History.utility h i := by
                rw [Finset.sum_comm]
    _ = ∑ h : G.History,
          (∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
            (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal) *
              History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro h _
                rw [← Finset.sum_mul]
    _ = ∑ h : G.History,
          (terminalWeightClassical (G := G) β h).toReal * History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro h _
                simpa using
                  congrArg (fun x => x * History.utility h i)
                    (marginal_terminalWeight_toReal (G := G) β h)

omit [DecidablePred G.terminal] in
/-- **Native Kuhn theorem for FOSGs at realized histories.**

Sampling a pure profile ex ante from the independent product mixed strategy
induced by a behavioral profile preserves the weight of every realized FOSG
history. -/
theorem behavioral_to_mixed_prob
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      History.prob (G.pureToBehavioral π) h =
        History.prob β h :=
  marginal_prob (G := G) β h

/-- **Native Kuhn theorem for FOSGs at terminal histories.**

The product mixed strategy induced by a behavioral profile preserves the
terminal weight of every realized terminal history. -/
theorem behavioral_to_mixed_terminalWeight
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      History.terminalWeight (G := G) (G.pureToBehavioral π) h =
        History.terminalWeight (G := G) β h :=
  marginal_terminalWeight (G := G) β h

/-- **Native Kuhn theorem for finite terminal events in a FOSG.**

The product mixed strategy induced by a behavioral profile assigns the same
total terminal mass to every finite set of realized histories. -/
theorem behavioral_to_mixed_terminalMassOn
    (β : BehavioralProfile (G := G)) (hs : Finset G.History) :
    (∑ π, behavioralToMixedJoint (G := G) β π *
      History.terminalMassOn (G := G) (G.pureToBehavioral π) hs) =
      History.terminalMassOn (G := G) β hs :=
  marginal_terminalMassOn (G := G) β hs

/-- **Native Kuhn theorem for the terminal law of a FOSG.**

The product mixed strategy induced by a behavioral profile preserves the native
terminal-history law exactly. -/
theorem behavioral_to_mixed_terminalLaw
    (β : BehavioralProfile (G := G)) :
    (fun hs =>
      ∑ π, behavioralToMixedJoint (G := G) β π *
        History.terminalLaw (G := G) (G.pureToBehavioral π) hs) =
      History.terminalLaw (G := G) β :=
  marginal_terminalLaw (G := G) β

/-- **Native Kuhn theorem for FOSG expected utility.**

The product mixed strategy induced by a legal behavioral profile preserves
expected utility for every player in the induced `KernelGame`. -/
theorem behavioral_to_mixed_eu
    [Fintype G.History]
    (hNorm : G.HasNormalizedTerminalLaw)
    (β : G.LegalBehavioralProfile) (i : ι) :
    ∑ π, (behavioralToMixedJoint (G := G) β.toProfile π).toReal *
      (∑ h : G.History,
        (History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal *
          History.utility h i) =
      (G.toKernelGame hNorm).eu β i := by
  have hEqWeight :
      ∀ (σ : BehavioralProfile (G := G)) (h : G.History),
        terminalWeightClassical (G := G) σ h = History.terminalWeight (G := G) σ h := by
    intro σ h
    classical
    unfold terminalWeightClassical History.terminalWeight
    by_cases hterm : G.terminal h.lastState <;> simp [hterm]
  rw [G.toKernelGame_eu_eq hNorm β i]
  have hMain := marginal_terminalUtilitySum (G := G) β.toProfile i
  simpa [hEqWeight] using hMain

end TerminalCorollaries

end Kuhn

end FOSG

end GameTheory
