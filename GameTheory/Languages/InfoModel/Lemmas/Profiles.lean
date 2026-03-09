import GameTheory.Languages.InfoModel.SemanticForm
import GameTheory.Languages.InfoModel.Lemmas.ExecutionSupport
import Math.PMFProduct
import Math.ProbabilityMassFunction

namespace GameTheory
namespace InfoModel

open Execution
open Math.PMFProduct

variable {ι σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)

abbrev LocalPure (i : ι) : Type :=
  I.LocalTrace i → Option (Act i)

/-- Mixed profiles over pure local policies (model-level notion). -/
abbrev MixedProfile : Type := ∀ i, PMF (LocalPure (I := I) i)

/-- Product-joint pure-profile law induced by per-controller mixed strategies. -/
noncomputable def mixedJoint
    [Fintype ι]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (μ : MixedProfile (I := I)) : PMF (PureProfile I) := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  exact pmfPi μ

open Classical in
/-- `mixedJoint` is injective in the mixed profile argument. -/
theorem mixedJoint_injective
    [Fintype ι]
    [∀ i, Fintype (LocalPure (I := I) i)]
    {μ₁ μ₂ : MixedProfile (I := I)}
    (h : mixedJoint (I := I) μ₁ = mixedJoint (I := I) μ₂) :
    μ₁ = μ₂ := by
  letI : DecidableEq ι := Classical.decEq ι
  funext i
  have hi := congrArg
    (fun ν => Math.ProbabilityMassFunction.pushforward ν (fun π : PureProfile I => π i)) h
  have hi' :
      Math.ProbabilityMassFunction.pushforward (pmfPi μ₁) (fun π : PureProfile I => π i) =
      Math.ProbabilityMassFunction.pushforward (pmfPi μ₂) (fun π : PureProfile I => π i) := by
    simpa [mixedJoint] using hi
  calc
    μ₁ i = Math.ProbabilityMassFunction.pushforward (pmfPi μ₁) (fun π : PureProfile I => π i) := by
      simpa using (pmfPi_push_coord (σ := μ₁) (j := i)).symm
    _ = Math.ProbabilityMassFunction.pushforward (pmfPi μ₂) (fun π : PureProfile I => π i) := hi'
    _ = μ₂ i := by
      simpa using (pmfPi_push_coord (σ := μ₂) (j := i))

/-- Canonical mixed evaluation (sample pure profile, then evaluate). -/
noncomputable def evalMixedCanonical
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [Fintype ι]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (k : Nat) (μ : MixedProfile (I := I)) : PMF I.Outcome :=
  (mixedJoint (I := I) μ).bind (D.evalPure k)

/-- Coordinate query on pure profiles. -/
def pureActionAt (i : ι) (v : I.LocalTrace i)
    (π : PureProfile I) : Option (Act i) :=
  π i v

/-- Canonical realization from mixed profile by coordinate marginals. -/
noncomputable def realizeBehavioralCanonical
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (I := I)) : BehavioralProfile I :=
  fun i v => Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f v)

/-- Behavioral → Mixed: each player's mixed strategy is the product measure over
all local-trace coordinates. -/
noncomputable def behavioralToMixed
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    (b : BehavioralProfile I) : MixedProfile (I := I) := by
  classical
  exact fun i => pmfPi (fun v : I.LocalTrace i => b i v)

/-- Round-trip identity: realizing the behavioral profile recovers the original. -/
theorem realize_behavioralToMixed
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    (b : BehavioralProfile I) :
    realizeBehavioralCanonical (I := I) (behavioralToMixed (I := I) b) = b := by
  classical
  funext i v
  simp only [realizeBehavioralCanonical, behavioralToMixed,
    Math.ProbabilityMassFunction.pushforward]
  conv_lhs =>
    arg 2; ext f
    simp only [Function.comp, Equiv.curry, Equiv.coe_fn_mk]
  change pushforward (pmfPi fun w => b i w)
    (fun f => f v) = b i v
  rw [pmfPi_push_coord]

/-- Pure step simplification: `jointActionDist` under `pureToBehavioral` is a point mass. -/
theorem jointActionDist_pure
    [DecidableEq ι]
    [Fintype ι]
    [∀ i, Fintype (Option (Act i))]
    (π : PureProfile I) (ss : List σ) :
    Execution.Dynamics.jointActionDist (I := I) (pureToBehavioral I π) ss =
      PMF.pure (fun i => π i (I.projectStates i ss)) := by
  simpa [Execution.Dynamics.jointActionDist, pureToBehavioral] using
    (pmfPi_pure (σ := fun i => π i (I.projectStates i ss)))

/-- Pure step unfolding: `stepDist` under `pureToBehavioral` simplifies. -/
theorem stepDist_pure
    (D : Execution.Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (π : PureProfile I) (ss : List σ) :
    D.stepDist (pureToBehavioral I π) ss =
      let s := (ss.getLast?).getD I.init
      D.nextState (fun i => π i (I.projectStates i ss)) s := by
  simp [Execution.Dynamics.stepDist, jointActionDist_pure, PMF.pure_bind]

/-- Pure explicit-step unfolding: `stepActionStateDist` under `pureToBehavioral`
records the current queried action profile without additional randomness. -/
theorem stepActionStateDist_pure
    (D : Execution.Dynamics I)
    [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (π : PureProfile I) (ss : List σ) :
    D.stepActionStateDist (pureToBehavioral I π) ss =
      let s := (ss.getLast?).getD I.init
      let a : I.JointAction := fun i => π i (I.projectStates i ss)
      Math.ProbabilityMassFunction.pushforward
        (D.nextState a s)
        (fun t => (a, t)) := by
  simp [Execution.Dynamics.stepActionStateDist, jointActionDist_pure, PMF.pure_bind]

section Restricted

variable [∀ i, DecidableEq (I.LocalTrace i)]

/-- Covered local-history coordinates for a finite cover `H`. -/
abbrev RestrictedLocalCoord
    (H : ∀ i, Finset (I.LocalTrace i)) (i : ι) : Type :=
  {v : I.LocalTrace i // v ∈ H i}

/-- Pure local policy restricted to the covered coordinates. -/
abbrev RestrictedLocalPure
    (H : ∀ i, Finset (I.LocalTrace i)) (i : ι) : Type :=
  RestrictedLocalCoord (I := I) H i → Option (Act i)

/-- Joint pure profile restricted to a finite local-history cover. -/
abbrev RestrictedPureProfile
    (H : ∀ i, Finset (I.LocalTrace i)) : Type :=
  ∀ i, RestrictedLocalPure (I := I) H i

/-- Behavioral profile restricted to a finite local-history cover. -/
abbrev RestrictedBehavioralProfile
    (H : ∀ i, Finset (I.LocalTrace i)) : Type :=
  ∀ i, RestrictedLocalCoord (I := I) H i → PMF (Option (Act i))

/-- Mixed profile over restricted pure local policies. -/
abbrev RestrictedMixedProfile
    (H : ∀ i, Finset (I.LocalTrace i)) : Type :=
  ∀ i, PMF (RestrictedLocalPure (I := I) H i)

/-- Extend a restricted local pure policy by playing `none` outside the cover. -/
def extendRestrictedLocalPure
    (H : ∀ i, Finset (I.LocalTrace i)) (i : ι)
    (f : RestrictedLocalPure (I := I) H i) :
    LocalPure (I := I) i :=
  fun v =>
    if hv : v ∈ H i then
      f ⟨v, hv⟩
    else
      none

/-- Restrict a full local pure policy to a finite cover. -/
def restrictLocalPure
    (H : ∀ i, Finset (I.LocalTrace i)) (i : ι)
    (f : LocalPure (I := I) i) :
    RestrictedLocalPure (I := I) H i :=
  fun v => f v.1

/-- Extend a restricted pure profile by playing `none` outside the cover. -/
def extendRestrictedPureProfile
    (H : ∀ i, Finset (I.LocalTrace i))
    (π : RestrictedPureProfile (I := I) H) :
    PureProfile I :=
  fun i => extendRestrictedLocalPure (I := I) H i (π i)

/-- Restrict a full pure profile to a finite cover. -/
def restrictPureProfile
    (H : ∀ i, Finset (I.LocalTrace i))
    (π : PureProfile I) :
    RestrictedPureProfile (I := I) H :=
  fun i => restrictLocalPure (I := I) H i (π i)

/-- Extend a restricted behavioral profile by playing `none` outside the cover. -/
noncomputable def extendRestrictedBehavioralProfile
    (H : ∀ i, Finset (I.LocalTrace i))
    (b : RestrictedBehavioralProfile (I := I) H) :
    BehavioralProfile I :=
  fun i v =>
    if hv : v ∈ H i then
      b i ⟨v, hv⟩
    else
      PMF.pure none

/-- Restrict a full behavioral profile to a finite cover. -/
def restrictBehavioralProfile
    (H : ∀ i, Finset (I.LocalTrace i))
    (b : BehavioralProfile I) :
    RestrictedBehavioralProfile (I := I) H :=
  fun i v => b i v.1

/-- Extend a restricted mixed profile to the full local-policy space by
pushforward along the pure-policy extension map. -/
noncomputable def extendRestrictedMixedProfile
    (H : ∀ i, Finset (I.LocalTrace i))
    (μ : RestrictedMixedProfile (I := I) H) :
    MixedProfile (I := I) :=
  fun i =>
    Math.ProbabilityMassFunction.pushforward
      (μ i) (extendRestrictedLocalPure (I := I) H i)

/-- Restrict a full mixed profile to the covered coordinates. -/
noncomputable def restrictMixedProfile
    (H : ∀ i, Finset (I.LocalTrace i))
    (μ : MixedProfile (I := I)) :
    RestrictedMixedProfile (I := I) H :=
  fun i =>
    Math.ProbabilityMassFunction.pushforward
      (μ i) (restrictLocalPure (I := I) H i)

/-- Product-joint law induced by a restricted mixed profile, pushed forward to
full pure profiles via extension outside the finite cover. -/
noncomputable def restrictedMixedJointRaw
    (H : ∀ i, Finset (I.LocalTrace i))
    [Fintype ι]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    (μ : RestrictedMixedProfile (I := I) H) :
    PMF (RestrictedPureProfile (I := I) H) := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  exact pmfPi μ

/-- Product-joint law induced by a restricted mixed profile, pushed forward to
full pure profiles via extension outside the finite cover. -/
noncomputable def restrictedMixedJoint
    (H : ∀ i, Finset (I.LocalTrace i))
    [Fintype ι]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    (μ : RestrictedMixedProfile (I := I) H) :
    PMF (PureProfile I) := by
  exact Math.ProbabilityMassFunction.pushforward
    (restrictedMixedJointRaw (I := I) H μ) (extendRestrictedPureProfile (I := I) H)

/-- Extending each restricted local-policy marginal and then taking the full
joint law agrees with pushing the restricted joint law forward along
`extendRestrictedPureProfile`. -/
theorem mixedJoint_extendRestrictedMixedProfile_eq_restrictedMixedJoint
    (H : ∀ i, Finset (I.LocalTrace i))
    [Fintype ι]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    (μ : RestrictedMixedProfile (I := I) H) :
    mixedJoint (I := I) (extendRestrictedMixedProfile (I := I) H μ) =
      restrictedMixedJoint (I := I) H μ := by
  classical
  rw [mixedJoint, restrictedMixedJoint]
  exact (pmfPi_push_coordwise μ
    (fun i => extendRestrictedLocalPure (I := I) H i)).symm

/-- Restricted mixed evaluation against full pure-profile observables is just
evaluation after pushing the raw restricted joint law forward along
`extendRestrictedPureProfile`. -/
theorem restrictedMixedJointRaw_bind_eq_restrictedMixedJoint_bind
    (H : ∀ i, Finset (I.LocalTrace i))
    [Fintype ι]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    {β : Type*}
    (μ : RestrictedMixedProfile (I := I) H)
    (f : PureProfile I → PMF β) :
    (restrictedMixedJointRaw (I := I) H μ).bind
        (fun π => f (extendRestrictedPureProfile (I := I) H π)) =
      (restrictedMixedJoint (I := I) H μ).bind f := by
  simp [restrictedMixedJoint, Math.ProbabilityMassFunction.pushforward,
    PMF.bind_bind]

/-- Pushing forward `mixedJoint μ` by "restrict then extend" is the same as
taking the joint law of the coordinatewise pushed-forward marginals. -/
theorem mixedJoint_extendRestrict_eq_pushforward
    (H : ∀ i, Finset (I.LocalTrace i))
    [Fintype ι]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (μ : MixedProfile (I := I)) :
    mixedJoint (I := I)
        (extendRestrictedMixedProfile (I := I) H
          (restrictMixedProfile (I := I) H μ)) =
      Math.ProbabilityMassFunction.pushforward
        (mixedJoint (I := I) μ)
        (fun π => extendRestrictedPureProfile (I := I) H
          (restrictPureProfile (I := I) H π)) := by
  classical
  have hcoord :
      (fun i =>
        Math.ProbabilityMassFunction.pushforward
          (Math.ProbabilityMassFunction.pushforward (μ i)
            (restrictLocalPure (I := I) H i))
          (extendRestrictedLocalPure (I := I) H i))
        =
      (fun i =>
        Math.ProbabilityMassFunction.pushforward (μ i)
          ((extendRestrictedLocalPure (I := I) H i) ∘
            (restrictLocalPure (I := I) H i))) := by
    funext i
    rw [Math.ProbabilityMassFunction.pushforward_comp]
  calc
    mixedJoint (I := I)
        (extendRestrictedMixedProfile (I := I) H
          (restrictMixedProfile (I := I) H μ))
        =
      pmfPi (fun i =>
        Math.ProbabilityMassFunction.pushforward (μ i)
          ((extendRestrictedLocalPure (I := I) H i) ∘
            (restrictLocalPure (I := I) H i))) := by
          rw [mixedJoint]
          change pmfPi
            (fun i =>
              Math.ProbabilityMassFunction.pushforward
                (Math.ProbabilityMassFunction.pushforward (μ i)
                  (restrictLocalPure (I := I) H i))
                (extendRestrictedLocalPure (I := I) H i)) =
            pmfPi (fun i =>
              Math.ProbabilityMassFunction.pushforward (μ i)
                ((extendRestrictedLocalPure (I := I) H i) ∘
                  (restrictLocalPure (I := I) H i)))
          rw [hcoord]
    _ =
      Math.ProbabilityMassFunction.pushforward
        (mixedJoint (I := I) μ)
        (fun π => extendRestrictedPureProfile (I := I) H
          (restrictPureProfile (I := I) H π)) := by
          rw [mixedJoint]
          exact (pmfPi_push_coordwise μ
            (fun i => (extendRestrictedLocalPure (I := I) H i) ∘
              (restrictLocalPure (I := I) H i))).symm

/-- Canonical behavioral realization from a restricted mixed profile, extended
outside the cover by the deterministic `none` action. -/
noncomputable def restrictedRealizeBehavioralCanonical
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (Option (Act i))]
    (μ : RestrictedMixedProfile (I := I) H) :
    BehavioralProfile I :=
  extendRestrictedBehavioralProfile (I := I) H <|
    fun i v =>
      Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f v)

/-- Behavioral-to-mixed lifting over a restricted finite local-history cover. -/
noncomputable def restrictedBehavioralToMixed
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (Option (Act i))]
    (b : RestrictedBehavioralProfile (I := I) H) :
    RestrictedMixedProfile (I := I) H := by
  classical
  exact fun i => pmfPi (fun v : RestrictedLocalCoord (I := I) H i => b i v)

/-- Restricting an extended local pure policy recovers the original. -/
theorem restrict_extend_localPure
    (H : ∀ i, Finset (I.LocalTrace i)) (i : ι)
    (f : RestrictedLocalPure (I := I) H i) :
    restrictLocalPure (I := I) H i
      (extendRestrictedLocalPure (I := I) H i f) = f := by
  funext v
  simp [restrictLocalPure, extendRestrictedLocalPure, v.2]

/-- Restricting an extended pure profile recovers the original. -/
theorem restrict_extend_pureProfile
    (H : ∀ i, Finset (I.LocalTrace i))
    (π : RestrictedPureProfile (I := I) H) :
    restrictPureProfile (I := I) H
      (extendRestrictedPureProfile (I := I) H π) = π := by
  funext i
  exact restrict_extend_localPure (I := I) H i (π i)

/-- Restricting an extended behavioral profile recovers the original. -/
theorem restrict_extend_behavioralProfile
    (H : ∀ i, Finset (I.LocalTrace i))
    (b : RestrictedBehavioralProfile (I := I) H) :
    restrictBehavioralProfile (I := I) H
      (extendRestrictedBehavioralProfile (I := I) H b) = b := by
  funext i v
  simp [restrictBehavioralProfile, extendRestrictedBehavioralProfile, v.2]

/-- The extension of a restricted pure profile agrees with the restricted value
on covered coordinates. -/
theorem extendRestrictedPureProfile_apply_mem
    (H : ∀ i, Finset (I.LocalTrace i))
    (π : RestrictedPureProfile (I := I) H)
    (i : ι) (v : I.LocalTrace i) (hv : v ∈ H i) :
    extendRestrictedPureProfile (I := I) H π i v = π i ⟨v, hv⟩ := by
  simp [extendRestrictedPureProfile, extendRestrictedLocalPure, hv]

/-- The extension of a restricted behavioral profile agrees with the restricted
value on covered coordinates. -/
theorem extendRestrictedBehavioralProfile_apply_mem
    (H : ∀ i, Finset (I.LocalTrace i))
    (b : RestrictedBehavioralProfile (I := I) H)
    (i : ι) (v : I.LocalTrace i) (hv : v ∈ H i) :
    extendRestrictedBehavioralProfile (I := I) H b i v = b i ⟨v, hv⟩ := by
  simp [extendRestrictedBehavioralProfile, hv]

/-- Round-trip identity on the restricted cover: realizing the behavioral
profile produced from `restrictedBehavioralToMixed` recovers the original. -/
theorem restricted_realize_behavioralToMixed
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (Option (Act i))]
    (b : RestrictedBehavioralProfile (I := I) H) :
    restrictBehavioralProfile (I := I) H
      (restrictedRealizeBehavioralCanonical (I := I) H
        (restrictedBehavioralToMixed (I := I) H b)) = b := by
  classical
  funext i v
  simp only [restrictBehavioralProfile, restrictedRealizeBehavioralCanonical,
    restrictedBehavioralToMixed, extendRestrictedBehavioralProfile]
  suffices
      Math.ProbabilityMassFunction.pushforward
        (pmfPi (fun w : RestrictedLocalCoord (I := I) H i => b i w))
        (fun f => f v) = b i v by
    simpa only [SetLike.coe_mem, ↓reduceDIte, Subtype.coe_eta] using this
  simpa [Math.ProbabilityMassFunction.pushforward] using
    (pmfPi_push_coord (σ := fun w : RestrictedLocalCoord (I := I) H i => b i w) (j := v))

end Restricted

end InfoModel
end GameTheory
