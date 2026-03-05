import Math.PMFProduct
import Math.ProbabilityMassFunction
import GameTheory.Model.Lemmas.StepIndependence

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

section Generic

variable {ι : Type} [Fintype ι]
variable {A : ι → Type} [∀ i, Fintype (A i)]
variable {β γ : Type} [Finite β]

open Classical in
 theorem kuhn_behavioral_to_mixed_indep
    (σ : ∀ i, PMF (A i))
    (f : (∀ i, A i) → PMF β)
    (g : β → (∀ i, A i) → PMF γ)
    (J : Finset ι)
    (hf : ∀ j, j ∉ J → Ignores j f)
    (hg : ∀ j, j ∈ J → ∀ b, Ignores j (g b)) :
    (pmfPi σ).bind (fun s => (f s).bind (fun b => g b s)) =
    (pmfPi σ).bind (fun s => (f s).bind (fun b => (pmfPi σ).bind (fun t => g b t))) :=
  pmfPi_bind_indep (σ := σ) (f := f) (g := g) (J := J) hf hg

variable {α : Type} [Fintype α]

theorem kuhn_mixed_to_behavioral_disintegrate
    {β γ : Type} [Finite β]
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) :
    μ.bind g =
      (Math.ProbabilityMassFunction.pushforward μ proj).bind
        (fun b => (Math.ProbabilityMassFunction.condOn μ proj b).bind g) := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  simpa using
    (Math.ProbabilityMassFunction.bind_pushforward_condOn
      (μ := μ) (proj := proj) (g := g))

end Generic

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
    (hStepIndep : ∀ μ n, InfoModel.StepIndependence (I := I) D μ n)
    (hH : M.FiniteHorizon k) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  have _ := hH
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
      InfoModel.AtomicCoordinateFactorization (I := I) μ)
    (hH : M.FiniteHorizon k) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  have hStepIndep : ∀ μ n, InfoModel.StepIndependence (I := I) D μ n := by
    intro μ n
    exact InfoModel.atomicFactorization_implies_stepIndependence
      (I := I) (D := D) (μ := μ) (n := n) (hAtomic μ)
  exact kuhn_complete_of_infoModel (I := I) (D := D) (k := k) hStepIndep hH

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

/-- Condition a player-local mixed strategy on taking action `a` at local
observation trace `v`. Falls back to `μ` on zero-mass events. -/
noncomputable def condMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i))
    (v : I.LocalTrace i)
    (a : Option (M.Act i)) :
    PMF (InfoModel.LocalPure (I := I) i) :=
  if _ : Math.ProbabilityMassFunction.pushforward μi (fun f => f v) a ≠ 0 then
    Math.ProbabilityMassFunction.condOn μi (fun f => f v) a
  else
    μi

/-- Player-local history token used for iterated conditioning:
past local observation trace paired with the realized own action. -/
abbrev LocalHistTok (i : ι) : Type :=
  I.LocalTrace i × Option (M.Act i)

/-- Iterated local conditioning. -/
noncomputable def iterCondMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    List (LocalHistTok (I := I) i) → PMF (InfoModel.LocalPure (I := I) i)
  | [] => μi
  | (v, a) :: rest =>
      iterCondMixedLocal i (condMixedLocal (I := I) i μi v a) rest

omit [Fintype ι] in
@[simp] theorem iterCondMixedLocal_nil
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    iterCondMixedLocal (I := I) i μi [] = μi := rfl

omit [Fintype ι] in
theorem pushforward_bind_condMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i))
    (v : I.LocalTrace i) :
    (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
      (condMixedLocal (I := I) i μi v) = μi := by
  classical
  have hcond :
      ∀ a, (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)) a ≠ 0 →
        condMixedLocal (I := I) i μi v a =
          Math.ProbabilityMassFunction.condOn μi (fun f => f v) a := by
    intro a ha
    simp [condMixedLocal, ha]
  calc
    (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
        (condMixedLocal (I := I) i μi v)
        =
      (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
        (fun a =>
          Math.ProbabilityMassFunction.condOn μi (fun f => f v) a) := by
            exact Math.ProbabilityMassFunction.bind_congr_of_ne_zero
              (μ := Math.ProbabilityMassFunction.pushforward μi (fun f => f v))
              (f := condMixedLocal (I := I) i μi v)
              (g := fun a => Math.ProbabilityMassFunction.condOn μi (fun f => f v) a)
              hcond
    _ = μi := by
          simpa using
            (Math.ProbabilityMassFunction.bind_pushforward_condOn
              (μ := μi) (proj := fun f => f v) (g := fun f => PMF.pure f)).symm

/-- Build player-local conditioning tokens from an action/state trace.
Each token stores `(localTrace_before_t, ownAction_t)`. -/
private noncomputable def localHistTokensAux
    (i : ι)
    (pref : List M.State)
    (ha : List (M.Label × (∀ j, Option (M.Act j))))
    (ssTail : List M.State) :
    List (LocalHistTok (I := I) i) :=
  match ha, ssTail with
  | [], _ => []
  | (_, a) :: ha', s' :: ss' =>
      (I.projectStates i pref, a i) ::
        localHistTokensAux i (pref ++ [s']) ha' ss'
  | _ :: _, [] => []

/-- Player-local conditioning tokens from a full action/state trace. -/
private noncomputable def localHistTokens
    (i : ι)
    (ha : List (M.Label × (∀ j, Option (M.Act j))))
    (ss : List M.State) :
    List (LocalHistTok (I := I) i) :=
  match ss with
  | [] => []
  | s0 :: ssTail => localHistTokensAux (I := I) i [s0] ha ssTail

/-- Canonical conditional behavioral realization from a mixed profile,
defined by conditioning on one chosen reachable local history witness. -/
noncomputable def mixedToBehavioral
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I)) :
    BehavioralProfile I := by
  classical
  refine fun i v =>
    if h :
      ∃ ha : List (M.Label × (∀ j, Option (M.Act j))),
      ∃ ss : List M.State,
        InfoModel.ReachActionTrace M ha ss ∧
        I.projectStates i ss = v
    then ?_ else PMF.pure none
  let ha : List (M.Label × (∀ j, Option (M.Act j))) := Classical.choose h
  let ss : List M.State := Classical.choose (Classical.choose_spec h)
  have hv : I.projectStates i ss = v := (Classical.choose_spec (Classical.choose_spec h)).2
  let hist := localHistTokens (I := I) i ha ss
  exact Math.ProbabilityMassFunction.pushforward
    (iterCondMixedLocal (I := I) i (μ i) hist) (fun f => f v)

/-- Remaining kernel for mixed → behavioral:
one-step compatibility of the conditional realization under perfect recall. -/
theorem mixedToBehavioral_stepIndependence
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (hH : M.FiniteHorizon k)
    (μ : InfoModel.MixedProfile (I := I)) :
    ∀ n,
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun hs =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) =
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun hs =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
  have _ := hPR
  have _ := hH
  -- Core missing proof:
  -- 1) witness-independence of `mixedToBehavioral` via `ActionRecall`
  -- 2) per-coordinate decomposition using `pushforward_bind_condMixedLocal`
  -- 3) context-preserving induction on bounded runs.
  sorry

/-- **Kuhn (mixed → behavioral)** at the `InfoModel` level.

Do not strengthen this statement by introducing ad hoc assumptions
on mixed profiles. The intended assumptions are only model-level:
perfect recall and finite horizon.
-/
theorem mixedToBehavioral_correct
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (hH : M.FiniteHorizon k)
    (μ : InfoModel.MixedProfile (I := I)) :
    D.evalBehavioral k (mixedToBehavioral (I := I) μ) =
      (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
  exact evalBehavioral_eq_mixed_of_stepIndependence (I := I) (D := D) (k := k) μ
    (mixedToBehavioral (I := I) μ)
    (mixedToBehavioral_stepIndependence (I := I) (D := D) (k := k) hPR hH μ)

theorem kuhn_mixed_to_behavioral
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (hH : M.FiniteHorizon k) :
    KuhnMixedToBehavioralViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (InfoModel.mixedJoint (I := I)) (D.evalBehavioral k) (D.evalPure k) := by
  have _ := hPR
  have _ := hH
  intro μ
  refine ⟨mixedToBehavioral (I := I) μ, ?_⟩
  simpa using mixedToBehavioral_correct (I := I) (D := D) (k := k) hPR hH μ

/-- **Kuhn (complete, both directions)** at the `InfoModel` level.

Do not modify this by strengthening assumptions in either direction.
If proof infrastructure is missing, keep the exact statement and refine lemmas.
-/
theorem kuhn_complete
    [Fintype M.Label]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (hH : M.FiniteHorizon k) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  exact ⟨
    kuhn_behavioral_to_mixed (I := I) (D := D) (k := k),
    kuhn_mixed_to_behavioral (I := I) (D := D) (k := k) hPR hH
  ⟩

end InfoModel

end Theorems
end GameTheory
