import GameTheory.Model.SemanticForm
import Semantics.Execution
import Math.PMFProduct
import Math.ProbabilityMassFunction

namespace GameTheory
namespace InfoModel

open Execution
open Math.PMFProduct

variable {ι : Type}
variable {M : LSM ι} (I : InfoModel M)

abbrev LocalPure (i : ι) : Type :=
  I.LocalTrace i → Option (M.Act i)

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
    [Fintype ι]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (k : Nat) (μ : MixedProfile (I := I)) : PMF I.Outcome :=
  (mixedJoint (I := I) μ).bind (D.evalPure k)

/-- Coordinate query on pure profiles. -/
def pureActionAt (i : ι) (v : I.LocalTrace i)
    (π : PureProfile I) : Option (M.Act i) :=
  π i v

/-- Canonical realization from mixed profile by coordinate marginals. -/
noncomputable def realizeBehavioralCanonical
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : MixedProfile (I := I)) : BehavioralProfile I :=
  fun i v => Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f v)

/-- Behavioral → Mixed: each player's mixed strategy is the product measure over
    all (label, local-trace) coordinates. -/
noncomputable def behavioralToMixed
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) : MixedProfile (I := I) := by
  classical
  exact fun i => pmfPi (fun v : I.LocalTrace i => σ i v)

/-- Round-trip identity: realizing the behavioral profile recovers the original. -/
theorem realize_behavioralToMixed
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) :
    realizeBehavioralCanonical (I := I) (behavioralToMixed (I := I) σ) = σ := by
  classical
  funext i v
  simp only [realizeBehavioralCanonical, behavioralToMixed,
    Math.ProbabilityMassFunction.pushforward]
  conv_lhs =>
    arg 2; ext f
    simp only [Function.comp, Equiv.curry, Equiv.coe_fn_mk]
  change pushforward (pmfPi fun w => σ i w)
    (fun f => f v) = σ i v
  rw [pmfPi_push_coord]

/-- Pure step simplification: `jointActionDist` under `pureToBehavioral` is a point mass. -/
theorem jointActionDist_pure
    [Fintype ι]
    [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I) (ss : List M.State) :
    Execution.Dynamics.jointActionDist (I := I) (pureToBehavioral I π) ss =
      PMF.pure (fun i => π i (I.projectStates i ss)) := by
  simp [Execution.Dynamics.jointActionDist, pureToBehavioral, pmfPi_pure]

/-- Pure step unfolding: `stepDist` under `pureToBehavioral` simplifies. -/
theorem stepDist_pure
    (D : Execution.Dynamics I) [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I) (ss : List M.State) :
    D.stepDist (pureToBehavioral I π) ss =
      let s := (ss.getLast?).getD M.init
      (D.labelKernel s).bind (fun ℓ =>
        Math.ProbabilityMassFunction.pushforward
          (D.nextState ℓ (fun i => π i (I.projectStates i ss)) s)
          (fun t => (ℓ, t))) := by
  simp only [Execution.Dynamics.stepDist, jointActionDist_pure]
  congr 1; funext ℓ
  simp [PMF.pure_bind]

/-- Pure explicit-step unfolding: `stepActionStateDist` under `pureToBehavioral`
records the current queried action profile without additional randomness. -/
theorem stepActionStateDist_pure
    (D : Execution.Dynamics I) [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I) (ss : List M.State) :
    D.stepActionStateDist (pureToBehavioral I π) ss =
      let s := (ss.getLast?).getD M.init
      let a : ∀ i, Option (M.Act i) := fun i => π i (I.projectStates i ss)
      (D.labelKernel s).bind (fun ℓ =>
        Math.ProbabilityMassFunction.pushforward
          (D.nextState ℓ a s)
          (fun t => ((ℓ, a), t))) := by
  simp only [Execution.Dynamics.stepActionStateDist, jointActionDist_pure]
  congr 1
  funext ℓ
  simp [PMF.pure_bind]

end InfoModel
end GameTheory
