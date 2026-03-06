import Math.PMFProduct
import Math.ProbabilityMassFunction
import GameTheory.Model.Lemmas.StepIndependence
import GameTheory.Model.Lemmas.PerfectRecall

namespace GameTheory
namespace Theorems

open Math
open Math.PMFProduct

/-- Generic behavioral -> mixed outcome-equality schema. -/
def KuhnBehavioralToMixedOutcome
    (Behavioral Pure Outcome : Type)
    (mixedOfBehavioral : Behavioral → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  ∀ σ : Behavioral, (mixedOfBehavioral σ).bind evalPure = evalBehavioral σ

/-- Generic mixed -> behavioral realization schema. -/
def KuhnMixedToBehavioralViaOutcome
    (Behavioral Mixed Pure Outcome : Type)
    (joint : Mixed → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  ∀ μ : Mixed, ∃ σ : Behavioral, evalBehavioral σ = (joint μ).bind evalPure

/-- Complete Kuhn statement (both directions) at outcome-distribution level. -/
def KuhnCompleteViaOutcome
    (Behavioral Mixed Pure Outcome : Type)
    (mixedOfBehavioral : Behavioral → PMF Pure)
    (joint : Mixed → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  (∀ σ : Behavioral, (mixedOfBehavioral σ).bind evalPure = evalBehavioral σ) ∧
  (∀ μ : Mixed, ∃ σ : Behavioral, evalBehavioral σ = (joint μ).bind evalPure)

section InfoModel

open Execution
open GameTheory.InfoModel

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)
variable (k : Nat)

section Restricted

variable [DecidableEq ι]
variable [∀ i, DecidableEq (I.LocalTrace i)]

/-- Restricted pure-profile evaluation is full pure evaluation after extension
outside the finite cover by the deterministic action `none`. -/
noncomputable def evalRestrictedPure
    (D : Execution.Dynamics I) (k : Nat)
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (Option (M.Act i))]
    (π : RestrictedPureProfile (I := I) H) : PMF I.Outcome :=
  D.evalPure k (extendRestrictedPureProfile (I := I) H π)

/-- Restricted behavioral evaluation is full behavioral evaluation after
extension outside the finite cover by `PMF.pure none`. -/
noncomputable def evalRestrictedBehavioral
    (D : Execution.Dynamics I) (k : Nat)
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (Option (M.Act i))]
    (σ : RestrictedBehavioralProfile (I := I) H) : PMF I.Outcome :=
  D.evalBehavioral k (extendRestrictedBehavioralProfile (I := I) H σ)

/-- Canonical mixed evaluation for restricted mixed profiles. -/
noncomputable def evalRestrictedMixedCanonical
    (D : Execution.Dynamics I) (k : Nat) (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : RestrictedMixedProfile (I := I) H) : PMF I.Outcome :=
  (restrictedMixedJointRaw (I := I) H μ).bind
    (fun π => evalRestrictedPure (I := I) D k H π)

/-- Canonical behavioral-to-mixed map on a finite local-history cover. -/
noncomputable def mixedOfBehavioralCanonicalRestricted
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : RestrictedBehavioralProfile (I := I) H) :
    PMF (RestrictedPureProfile (I := I) H) :=
  restrictedMixedJointRaw (I := I) H (restrictedBehavioralToMixed (I := I) H σ)

/-- Restricted analogue of `evalBehavioral_eq_mixed_of_stepIndependence`. -/
theorem evalRestrictedBehavioral_eq_mixed_of_stepIndependence
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : RestrictedMixedProfile (I := I) H)
    (σ : RestrictedBehavioralProfile (I := I) H)
    (hStep : ∀ n,
      (restrictedMixedJointRaw (I := I) H μ).bind (fun π =>
        (D.runDistPure n (extendRestrictedPureProfile (I := I) H π)).bind (fun ss =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (extendRestrictedBehavioralProfile (I := I) H σ) ss)
            (fun t => ss ++ [t]))) =
      (restrictedMixedJointRaw (I := I) H μ).bind (fun π =>
        (D.runDistPure n (extendRestrictedPureProfile (I := I) H π)).bind (fun ss =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I
              (extendRestrictedPureProfile (I := I) H π)) ss)
            (fun t => ss ++ [t])))) :
    evalRestrictedBehavioral (I := I) D k H σ =
      (restrictedMixedJointRaw (I := I) H μ).bind
        (fun π => evalRestrictedPure (I := I) D k H π) := by
  have hrun :
      ∀ n,
        D.runDist n (extendRestrictedBehavioralProfile (I := I) H σ) =
          (restrictedMixedJointRaw (I := I) H μ).bind
            (fun π => D.runDistPure n (extendRestrictedPureProfile (I := I) H π)) := by
    intro n
    induction n with
    | zero =>
        simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
    | succ n ih =>
        calc
          D.runDist (n + 1) (extendRestrictedBehavioralProfile (I := I) H σ)
              = (D.runDist n (extendRestrictedBehavioralProfile (I := I) H σ)).bind
                  (fun ss =>
                    Math.ProbabilityMassFunction.pushforward
                      (D.stepDist (extendRestrictedBehavioralProfile (I := I) H σ) ss)
                      (fun t => ss ++ [t])) := by
                    simp [Execution.Dynamics.runDist]
          _ = ((restrictedMixedJointRaw (I := I) H μ).bind
                (fun π => D.runDistPure n (extendRestrictedPureProfile (I := I) H π))).bind
                  (fun ss =>
                    Math.ProbabilityMassFunction.pushforward
                      (D.stepDist (extendRestrictedBehavioralProfile (I := I) H σ) ss)
                      (fun t => ss ++ [t])) := by
                    rw [ih]
          _ = (restrictedMixedJointRaw (I := I) H μ).bind (fun π =>
                (D.runDistPure n (extendRestrictedPureProfile (I := I) H π)).bind (fun ss =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (extendRestrictedBehavioralProfile (I := I) H σ) ss)
                    (fun t => ss ++ [t]))) := by
                    rw [PMF.bind_bind]
          _ = (restrictedMixedJointRaw (I := I) H μ).bind (fun π =>
                (D.runDistPure n (extendRestrictedPureProfile (I := I) H π)).bind (fun ss =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (pureToBehavioral I
                      (extendRestrictedPureProfile (I := I) H π)) ss)
                    (fun t => ss ++ [t]))) := by
                    simpa using hStep n
          _ = (restrictedMixedJointRaw (I := I) H μ).bind
                (fun π => D.runDistPure (n + 1) (extendRestrictedPureProfile (I := I) H π)) := by
                    simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
  have hrun' := hrun k
  have hpush := congrArg
      (fun p => Math.ProbabilityMassFunction.pushforward p I.outcomeOfStates)
      hrun'
  calc
    evalRestrictedBehavioral (I := I) D k H σ
        = Math.ProbabilityMassFunction.pushforward
            (D.runDist k (extendRestrictedBehavioralProfile (I := I) H σ))
            I.outcomeOfStates := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((restrictedMixedJointRaw (I := I) H μ).bind
            (fun π => D.runDistPure k (extendRestrictedPureProfile (I := I) H π)))
          I.outcomeOfStates := by
            simpa using hpush
    _ = (restrictedMixedJointRaw (I := I) H μ).bind
          (fun π => evalRestrictedPure (I := I) D k H π) := by
            simpa [evalRestrictedPure, Execution.Dynamics.evalPure] using
              (Math.ProbabilityMassFunction.pushforward_bind
                (μ := restrictedMixedJointRaw (I := I) H μ)
                (k := fun π => D.runDistPure k (extendRestrictedPureProfile (I := I) H π))
                (f := I.outcomeOfStates))

/-- Behavioral -> mixed direction from restricted step-independence. -/
theorem kuhn_behavioral_to_mixed_core_restricted
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hStepIndep : ∀ μ n, RestrictedStepIndependence (I := I) D H μ n) :
    KuhnBehavioralToMixedOutcome
      (RestrictedBehavioralProfile (I := I) H)
      (RestrictedPureProfile (I := I) H)
      I.Outcome
      (mixedOfBehavioralCanonicalRestricted (I := I) H)
      (evalRestrictedBehavioral (I := I) D k H)
      (evalRestrictedPure (I := I) D k H) := by
  classical
  intro σ
  let μσ : RestrictedMixedProfile (I := I) H :=
    restrictedBehavioralToMixed (I := I) H σ
  have hσeq :
      restrictedRealizeBehavioralCanonical (I := I) H μσ =
        extendRestrictedBehavioralProfile (I := I) H σ := by
    funext i v
    by_cases hv : v ∈ H i
    · have hres :=
        congrFun (congrFun
          (restricted_realize_behavioralToMixed (I := I) H σ) i) ⟨v, hv⟩
      simpa [restrictBehavioralProfile, extendRestrictedBehavioralProfile, hv] using hres
    · simp [restrictedRealizeBehavioralCanonical, extendRestrictedBehavioralProfile, hv]
  have hrun := restricted_run_factorization (I := I) (D := D) H hStepIndep μσ k
  have hrun' :
      D.runDist k (extendRestrictedBehavioralProfile (I := I) H σ) =
        (restrictedMixedJointRaw (I := I) H μσ).bind
          (fun π => D.runDistPure k (extendRestrictedPureProfile (I := I) H π)) := by
    simpa [hσeq] using hrun
  have hpush := congrArg
      (fun p => Math.ProbabilityMassFunction.pushforward p I.outcomeOfStates)
      hrun'
  have hright :
      Math.ProbabilityMassFunction.pushforward
          ((restrictedMixedJointRaw (I := I) H μσ).bind
            (fun π => D.runDistPure k (extendRestrictedPureProfile (I := I) H π)))
          I.outcomeOfStates =
        (restrictedMixedJointRaw (I := I) H μσ).bind
          (fun π => evalRestrictedPure (I := I) D k H π) := by
      simpa [evalRestrictedPure, Execution.Dynamics.evalPure] using
        (Math.ProbabilityMassFunction.pushforward_bind
          (μ := restrictedMixedJointRaw (I := I) H μσ)
          (k := fun π => D.runDistPure k (extendRestrictedPureProfile (I := I) H π))
          (f := I.outcomeOfStates))
  calc
    (mixedOfBehavioralCanonicalRestricted (I := I) H σ).bind
        (fun π => evalRestrictedPure (I := I) D k H π)
          = (restrictedMixedJointRaw (I := I) H μσ).bind
              (fun π => evalRestrictedPure (I := I) D k H π) := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((restrictedMixedJointRaw (I := I) H μσ).bind
            (fun π => D.runDistPure k (extendRestrictedPureProfile (I := I) H π)))
          I.outcomeOfStates := hright.symm
    _ = Math.ProbabilityMassFunction.pushforward
          (D.runDist k (extendRestrictedBehavioralProfile (I := I) H σ))
          I.outcomeOfStates := by
            simpa using hpush.symm
    _ = evalRestrictedBehavioral (I := I) D k H σ := rfl

/-- Mixed -> behavioral direction from restricted step-independence. -/
theorem kuhn_mixed_to_behavioral_core_restricted
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hStepIndep : ∀ μ n, RestrictedStepIndependence (I := I) D H μ n) :
    KuhnMixedToBehavioralViaOutcome
      (RestrictedBehavioralProfile (I := I) H)
      (RestrictedMixedProfile (I := I) H)
      (RestrictedPureProfile (I := I) H)
      I.Outcome
      (restrictedMixedJointRaw (I := I) H)
      (evalRestrictedBehavioral (I := I) D k H)
      (evalRestrictedPure (I := I) D k H) := by
  classical
  intro μ
  have hcanon :
      extendRestrictedBehavioralProfile (I := I) H
        (restrictBehavioralProfile (I := I) H
          (restrictedRealizeBehavioralCanonical (I := I) H μ)) =
        restrictedRealizeBehavioralCanonical (I := I) H μ := by
    funext i v
    by_cases hv : v ∈ H i
    · simp [extendRestrictedBehavioralProfile, restrictBehavioralProfile, hv]
    · simp [extendRestrictedBehavioralProfile, restrictedRealizeBehavioralCanonical, hv]
  refine ⟨restrictBehavioralProfile (I := I) H
    (restrictedRealizeBehavioralCanonical (I := I) H μ), ?_⟩
  have hmain :=
    evalRestrictedBehavioral_eq_mixed_of_stepIndependence
      (I := I) D k H μ
      (restrictBehavioralProfile (I := I) H
        (restrictedRealizeBehavioralCanonical (I := I) H μ))
      (fun n => by
        simpa [hcanon]
          using hStepIndep μ n)
  simpa [evalRestrictedBehavioral, restrict_extend_behavioralProfile] using hmain

/-- Full restricted Kuhn theorem from restricted step-independence. -/
theorem kuhn_complete_of_infoModel_restricted
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hStepIndep : ∀ μ n, RestrictedStepIndependence (I := I) D H μ n) :
    KuhnCompleteViaOutcome
      (RestrictedBehavioralProfile (I := I) H)
      (RestrictedMixedProfile (I := I) H)
      (RestrictedPureProfile (I := I) H)
      I.Outcome
      (mixedOfBehavioralCanonicalRestricted (I := I) H)
      (restrictedMixedJointRaw (I := I) H)
      (evalRestrictedBehavioral (I := I) D k H)
      (evalRestrictedPure (I := I) D k H) := by
  exact ⟨
    kuhn_behavioral_to_mixed_core_restricted (I := I) D k H hStepIndep,
    kuhn_mixed_to_behavioral_core_restricted (I := I) D k H hStepIndep
  ⟩

end Restricted

noncomputable def mixedOfBehavioralCanonical
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) : PMF (PureProfile I) :=
  InfoModel.mixedJoint (I := I) (InfoModel.behavioralToMixed (I := I) σ)

/-- If a behavioral profile `σ` satisfies one-step mixed/pure compatibility
at every depth under `μ`, then its bounded evaluation equals mixed evaluation. -/
theorem evalBehavioral_eq_mixed_of_stepIndependence
    [DecidableEq ι]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (σ : BehavioralProfile I)
    (hStep : ∀ n,
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun ss =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist σ ss)
            (fun t => ss ++ [t]))) =
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun ss =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) ss)
            (fun t => ss ++ [t])))) :
    D.evalBehavioral k σ = (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
  have hrun :
      ∀ n,
        D.runDist n σ =
          (InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure n π) := by
    intro n
    induction n with
    | zero =>
        simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
    | succ n ih =>
        calc
          D.runDist (n + 1) σ
              = (D.runDist n σ).bind (fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                    (fun t => ss ++ [t])) := by
                  simp [Execution.Dynamics.runDist]
          _ = ((InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure n π)).bind
                (fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                    (fun t => ss ++ [t])) := by
                rw [ih]
          _ = (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
                (D.runDistPure n π).bind (fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                    (fun t => ss ++ [t]))) := by
                rw [PMF.bind_bind]
          _ = (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
                (D.runDistPure n π).bind (fun ss =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (pureToBehavioral I π) ss)
                    (fun t => ss ++ [t]))) := by
                simpa using hStep n
          _ = (InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure (n + 1) π) := by
                simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
  have hrun' := hrun k
  have hpush := congrArg
      (fun p => Math.ProbabilityMassFunction.pushforward p I.outcomeOfStates)
      hrun'
  calc
    D.evalBehavioral k σ
        = Math.ProbabilityMassFunction.pushforward (D.runDist k σ) I.outcomeOfStates := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure k π))
          I.outcomeOfStates := by
          simpa using hpush
    _ = (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
          simpa [Execution.Dynamics.evalPure] using
            (Math.ProbabilityMassFunction.pushforward_bind
              (μ := InfoModel.mixedJoint (I := I) μ)
              (k := fun π => D.runDistPure k π)
              (f := I.outcomeOfStates))

/-- Behavioral -> mixed direction from model-level step-independence. -/
theorem kuhn_behavioral_to_mixed_core
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hStepIndep : ∀ μ n, InfoModel.StepIndependence (I := I) D μ n) :
    KuhnBehavioralToMixedOutcome
      (BehavioralProfile I) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  intro σ
  let μσ : InfoModel.MixedProfile (I := I) := InfoModel.behavioralToMixed (I := I) σ
  have hrun :=
    InfoModel.run_factorization (I := I) (D := D) hStepIndep μσ k
  have hrun' :
      D.runDist k σ =
        (InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π) := by
    simpa [μσ, InfoModel.realize_behavioralToMixed] using hrun
  have hpush :=
    congrArg
      (fun p => Math.ProbabilityMassFunction.pushforward p I.outcomeOfStates)
      hrun'
  have hright :
      Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π))
          I.outcomeOfStates =
        (InfoModel.mixedJoint (I := I) μσ).bind (D.evalPure k) := by
    simpa [Execution.Dynamics.evalPure] using
      (Math.ProbabilityMassFunction.pushforward_bind
        (μ := InfoModel.mixedJoint (I := I) μσ)
        (k := fun π => D.runDistPure k π)
        (f := I.outcomeOfStates))
  calc
    (mixedOfBehavioralCanonical (I := I) σ).bind (D.evalPure k)
        = (InfoModel.mixedJoint (I := I) μσ).bind (D.evalPure k) := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π))
          I.outcomeOfStates := hright.symm
    _ = Math.ProbabilityMassFunction.pushforward (D.runDist k σ) I.outcomeOfStates := by
          simpa using hpush.symm
    _ = D.evalBehavioral k σ := rfl

/-- Mixed -> behavioral direction from model-level step-independence. -/
theorem kuhn_mixed_to_behavioral_core
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hStepIndep : ∀ μ n, InfoModel.StepIndependence (I := I) D μ n) :
    KuhnMixedToBehavioralViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (InfoModel.mixedJoint (I := I)) (D.evalBehavioral k) (D.evalPure k) := by
  intro μ
  refine ⟨InfoModel.realizeBehavioralCanonical (I := I) μ, ?_⟩
  have hrun :=
    InfoModel.run_factorization (I := I) (D := D) hStepIndep μ k
  have hpush :=
    congrArg
      (fun p => Math.ProbabilityMassFunction.pushforward p I.outcomeOfStates)
      hrun
  calc
    D.evalBehavioral k (InfoModel.realizeBehavioralCanonical (I := I) μ)
        = Math.ProbabilityMassFunction.pushforward
            (D.runDist k (InfoModel.realizeBehavioralCanonical (I := I) μ))
            I.outcomeOfStates := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure k π))
          I.outcomeOfStates := by
          simpa using hpush
    _ = (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
          simpa [Execution.Dynamics.evalPure] using
            (Math.ProbabilityMassFunction.pushforward_bind
              (μ := InfoModel.mixedJoint (I := I) μ)
              (k := fun π => D.runDistPure k π)
              (f := I.outcomeOfStates))

/-- Full Kuhn on `InfoModel` from the step-independence bridge. -/
theorem kuhn_complete_of_infoModel
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hStepIndep : ∀ μ n, InfoModel.StepIndependence (I := I) D μ n) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  exact ⟨
    kuhn_behavioral_to_mixed_core (I := I) (D := D) (k := k) hStepIndep,
    kuhn_mixed_to_behavioral_core (I := I) (D := D) (k := k) hStepIndep
  ⟩

/-- Full Kuhn from structural atomic factorization plus finite horizon. -/
theorem kuhn_complete_of_infoModel_atomic
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hAtomic : ∀ μ : InfoModel.MixedProfile (I := I),
      InfoModel.AtomicCoordinateFactorization (I := I) μ) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  have hStepIndep : ∀ μ n, InfoModel.StepIndependence (I := I) D μ n := by
    intro μ n
    exact InfoModel.atomicFactorization_implies_stepIndependence
      (I := I) (D := D) (μ := μ) (n := n) (hAtomic μ)
  exact kuhn_complete_of_infoModel (I := I) (D := D) (k := k) hStepIndep

/-- Kuhn's behavioral-to-mixed direction for `InfoModel` outcome distributions. -/
theorem kuhn_behavioral_to_mixed
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))] :
    KuhnBehavioralToMixedOutcome
      (BehavioralProfile I) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  intro σ
  let μσ : InfoModel.MixedProfile (I := I) := InfoModel.behavioralToMixed (I := I) σ
  have hrun :
      ∀ n,
        D.runDist n σ =
          (InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure n π) := by
    intro n
    induction n with
    | zero =>
        simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure, μσ]
    | succ n ih =>
        calc
          D.runDist (n + 1) σ
              = (D.runDist n σ).bind (fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                    (fun t => ss ++ [t])) := by
                  simp [Execution.Dynamics.runDist]
          _ = ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure n π)).bind
                (fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                    (fun t => ss ++ [t])) := by
                rw [ih]
          _ = (InfoModel.mixedJoint (I := I) μσ).bind (fun π =>
                (D.runDistPure n π).bind (fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                    (fun t => ss ++ [t]))) := by
                rw [PMF.bind_bind]
          _ = (InfoModel.mixedJoint (I := I) μσ).bind (fun π =>
                (D.runDistPure n π).bind (fun ss =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (pureToBehavioral I π) ss)
                    (fun t => ss ++ [t]))) := by
                simpa [μσ] using
                  (InfoModel.behavioralToMixed_stepIndependence_bridge
                    (I := I) (D := D) σ n)
          _ = (InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure (n + 1) π) := by
                simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
  have hrun' := hrun k
  have hpush := congrArg
      (fun p => Math.ProbabilityMassFunction.pushforward p I.outcomeOfStates)
      hrun'
  have hright :
      Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π))
          I.outcomeOfStates =
        (InfoModel.mixedJoint (I := I) μσ).bind (D.evalPure k) := by
    simpa [Execution.Dynamics.evalPure] using
      (Math.ProbabilityMassFunction.pushforward_bind
        (μ := InfoModel.mixedJoint (I := I) μσ)
        (k := fun π => D.runDistPure k π)
        (f := I.outcomeOfStates))
  calc
    (mixedOfBehavioralCanonical (I := I) σ).bind (D.evalPure k)
        = (InfoModel.mixedJoint (I := I) μσ).bind (D.evalPure k) := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π))
          I.outcomeOfStates := hright.symm
    _ = Math.ProbabilityMassFunction.pushforward (D.runDist k σ) I.outcomeOfStates := by
          simpa using hpush.symm
    _ = D.evalBehavioral k σ := rfl

end InfoModel

end Theorems
end GameTheory
