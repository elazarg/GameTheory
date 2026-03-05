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

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)
variable (k : Nat)

noncomputable def mixedOfBehavioralCanonical
    [Fintype M.Label]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) : PMF (PureProfile I) :=
  InfoModel.mixedJoint (I := I) (InfoModel.behavioralToMixed (I := I) σ)

/-- If a behavioral profile `σ` satisfies one-step mixed/pure compatibility
at every depth under `μ`, then its bounded evaluation equals mixed evaluation. -/
theorem evalBehavioral_eq_mixed_of_stepIndependence
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (σ : BehavioralProfile I)
    (hStep :
      ∀ n,
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun hs =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist σ hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) =
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun hs =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))) :
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
              = (D.runDist n σ).bind (fun hs =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) := by
                  simp [Execution.Dynamics.runDist]
          _ = ((InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure n π)).bind
                (fun hs =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) := by
                rw [ih]
          _ = (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
                (D.runDistPure n π).bind (fun hs =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
                rw [PMF.bind_bind]
          _ = (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
                (D.runDistPure n π).bind (fun hs =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (pureToBehavioral I π) hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
                simpa using hStep n
          _ = (InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure (n + 1) π) := by
                simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
  have hrun' := hrun k
  have hpush := congrArg
      (fun p =>
        Math.ProbabilityMassFunction.pushforward p (fun hs => I.outcomeOfStates hs.2))
      hrun'
  calc
    D.evalBehavioral k σ
        = Math.ProbabilityMassFunction.pushforward (D.runDist k σ)
            (fun hs => I.outcomeOfStates hs.2) := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure k π))
          (fun hs => I.outcomeOfStates hs.2) := by
          simpa using hpush
    _ = (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
          simpa [Execution.Dynamics.evalPure] using
            (Math.ProbabilityMassFunction.pushforward_bind
              (μ := InfoModel.mixedJoint (I := I) μ)
              (k := fun π => D.runDistPure k π)
              (f := fun hs => I.outcomeOfStates hs.2))

/-- Behavioral -> mixed direction from model-level step-independence. -/
theorem kuhn_behavioral_to_mixed_core
    [Fintype M.Label]
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
      (fun p =>
        Math.ProbabilityMassFunction.pushforward p (fun hs => I.outcomeOfStates hs.2))
      hrun'
  have hright :
      Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π))
          (fun hs => I.outcomeOfStates hs.2) =
        (InfoModel.mixedJoint (I := I) μσ).bind (D.evalPure k) := by
    simpa [Execution.Dynamics.evalPure] using
      (Math.ProbabilityMassFunction.pushforward_bind
        (μ := InfoModel.mixedJoint (I := I) μσ)
        (k := fun π => D.runDistPure k π)
        (f := fun hs => I.outcomeOfStates hs.2))
  calc
    (mixedOfBehavioralCanonical (I := I) σ).bind (D.evalPure k)
        = (InfoModel.mixedJoint (I := I) μσ).bind (D.evalPure k) := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π))
          (fun hs => I.outcomeOfStates hs.2) := hright.symm
    _ = Math.ProbabilityMassFunction.pushforward (D.runDist k σ)
          (fun hs => I.outcomeOfStates hs.2) := by
          simpa using hpush.symm
    _ = D.evalBehavioral k σ := rfl

/-- Mixed -> behavioral direction from model-level step-independence. -/
theorem kuhn_mixed_to_behavioral_core
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
      (fun p =>
        Math.ProbabilityMassFunction.pushforward p (fun hs => I.outcomeOfStates hs.2))
      hrun
  calc
    D.evalBehavioral k (InfoModel.realizeBehavioralCanonical (I := I) μ)
        = Math.ProbabilityMassFunction.pushforward
            (D.runDist k (InfoModel.realizeBehavioralCanonical (I := I) μ))
            (fun hs => I.outcomeOfStates hs.2) := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μ).bind (fun π => D.runDistPure k π))
          (fun hs => I.outcomeOfStates hs.2) := by
          simpa using hpush
    _ = (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
          simpa [Execution.Dynamics.evalPure] using
            (Math.ProbabilityMassFunction.pushforward_bind
              (μ := InfoModel.mixedJoint (I := I) μ)
              (k := fun π => D.runDistPure k π)
              (f := fun hs => I.outcomeOfStates hs.2))

/-- Full Kuhn on `InfoModel` from the step-independence bridge. -/
theorem kuhn_complete_of_infoModel
    [Fintype M.Label]
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
    [Fintype M.Label]
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

/-- **Kuhn (behavioral → mixed)** at the `InfoModel` level.

Do not strengthen this statement by adding structural assumptions
(in particular, do not add factorization assumptions such as
`AtomicCoordinateFactorization`).
-/
theorem kuhn_behavioral_to_mixed
    [Fintype M.Label]
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
              = (D.runDist n σ).bind (fun hs =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) := by
                  simp [Execution.Dynamics.runDist]
          _ = ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure n π)).bind
                (fun hs =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) := by
                rw [ih]
          _ = (InfoModel.mixedJoint (I := I) μσ).bind (fun π =>
                (D.runDistPure n π).bind (fun hs =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
                rw [PMF.bind_bind]
          _ = (InfoModel.mixedJoint (I := I) μσ).bind (fun π =>
                (D.runDistPure n π).bind (fun hs =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (pureToBehavioral I π) hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
                simpa [μσ] using
                  (InfoModel.behavioralToMixed_stepIndependence_bridge
                    (I := I) (D := D) σ n)
          _ = (InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure (n + 1) π) := by
                simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
  have hrun' := hrun k
  have hpush := congrArg
      (fun p =>
        Math.ProbabilityMassFunction.pushforward p (fun hs => I.outcomeOfStates hs.2))
      hrun'
  have hright :
      Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π))
          (fun hs => I.outcomeOfStates hs.2) =
        (InfoModel.mixedJoint (I := I) μσ).bind (D.evalPure k) := by
    simpa [Execution.Dynamics.evalPure] using
      (Math.ProbabilityMassFunction.pushforward_bind
        (μ := InfoModel.mixedJoint (I := I) μσ)
        (k := fun π => D.runDistPure k π)
        (f := fun hs => I.outcomeOfStates hs.2))
  calc
    (mixedOfBehavioralCanonical (I := I) σ).bind (D.evalPure k)
        = (InfoModel.mixedJoint (I := I) μσ).bind (D.evalPure k) := rfl
    _ = Math.ProbabilityMassFunction.pushforward
          ((InfoModel.mixedJoint (I := I) μσ).bind (fun π => D.runDistPure k π))
          (fun hs => I.outcomeOfStates hs.2) := hright.symm
    _ = Math.ProbabilityMassFunction.pushforward (D.runDist k σ)
          (fun hs => I.outcomeOfStates hs.2) := by
          simpa using hpush.symm
    _ = D.evalBehavioral k σ := rfl

end InfoModel

end Theorems
end GameTheory

