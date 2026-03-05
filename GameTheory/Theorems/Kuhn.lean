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
  InfoModel.LocalHistTok (I := I) i

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
  let hist := InfoModel.localHistTokens (I := I) i ha ss
  exact Math.ProbabilityMassFunction.pushforward
    (iterCondMixedLocal (I := I) i (μ i) hist) (fun f => f v)

omit [Fintype ι] in
private theorem reachActionTrace_nonempty
    {ha : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss) :
    ss ≠ [] := by
  induction hr with
  | nil => simp
  | snoc _ _ _ => simp

omit [Fintype ι] in
private theorem projectStates_getLast?
    (i : ι) (ss : List M.State) :
    (I.projectStates i ss).getLast? = Option.map (I.observe i) ss.getLast? := by
  induction ss with
  | nil => rfl
  | cons s tl ih =>
      cases tl with
      | nil => simp [InfoModel.projectStates]
      | cons s' tl' =>
          simpa [InfoModel.projectStates] using ih

omit [Fintype ι] in
private theorem actionRecall_of_projectStates_eq
    (hPR : I.PerfectRecall)
    (i : ι)
    {ha₁ ha₂ : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss₁ ss₂ : List M.State}
    (hr₁ : InfoModel.ReachActionTrace M ha₁ ss₁)
    (hr₂ : InfoModel.ReachActionTrace M ha₂ ss₂)
    (hproj : I.projectStates i ss₁ = I.projectStates i ss₂) :
    InfoModel.projectActions i ha₁ = InfoModel.projectActions i ha₂ := by
  have hne1 : ss₁ ≠ [] := reachActionTrace_nonempty (M := M) hr₁
  have hne2 : ss₂ ≠ [] := reachActionTrace_nonempty (M := M) hr₂
  let s1 : M.State := ss₁.getLast hne1
  let s2 : M.State := ss₂.getLast hne2
  have hs1 : ss₁.getLast? = some s1 := by
    simpa [s1] using (List.getLast?_eq_getLast_of_ne_nil hne1)
  have hs2 : ss₂.getLast? = some s2 := by
    simpa [s2] using (List.getLast?_eq_getLast_of_ne_nil hne2)
  have hlastObs :
      Option.map (I.observe i) ss₁.getLast? = Option.map (I.observe i) ss₂.getLast? := by
    simpa [projectStates_getLast? (I := I) i ss₁, projectStates_getLast? (I := I) i ss₂] using
      congrArg List.getLast? hproj
  have hobserve : I.observe i s1 = I.observe i s2 := by
    simpa [hs1, hs2] using hlastObs
  have hobsEq : I.obsEq i s1 s2 :=
    I.observe_eq_implies_obsEq i hobserve
  exact (InfoModel.perfectRecall_action (I := I) hPR) i ha₁ ha₂ ss₁ ss₂ s1 s2
    hr₁ hr₂ hs1 hs2 hobsEq

theorem mixedToBehavioral_stepIndependence
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
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
  intro n
  classical
  ext y
  set μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
  let Lfun : (List M.Label × List M.State) → ENNReal :=
    fun hs =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
  let Gfun : (List M.Label × List M.State) → PureProfile I → ENNReal :=
    fun hs π =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
  let FL : PureProfile I → (List M.Label × List M.State) → ENNReal :=
    fun π hs => μJ π * ((D.runDistPure n π) hs * Lfun hs)
  let FR : PureProfile I → (List M.Label × List M.State) → ENNReal :=
    fun π hs => μJ π * ((D.runDistPure n π) hs * Gfun hs π)
  have hswapL :
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs)
        = ∑' hs, ∑' π, FL π hs := by
    calc
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs)
          = ∑' π, ∑' hs, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' hs, ∑' π, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
            simpa using
              (ENNReal.tsum_comm
                (f := fun π hs => μJ π * ((D.runDistPure n π) hs * Lfun hs)))
      _ = ∑' hs, ∑' π, FL π hs := by simp [FL]
  have hswapR :
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π)
        = ∑' hs, ∑' π, FR π hs := by
    calc
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π)
          = ∑' π, ∑' hs, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' hs, ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
            simpa using
              (ENNReal.tsum_comm
                (f := fun π hs => μJ π * ((D.runDistPure n π) hs * Gfun hs π)))
      _ = ∑' hs, ∑' π, FR π hs := by simp [FR]
  have hPerHs :
      ∀ hs : List M.Label × List M.State, (∑' π, FL π hs) = ∑' π, FR π hs := by
    intro hs
    by_cases hlen : hs.2.length = n + 1
    · let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
      have hL :
          (∑' π, FL π hs) = C * Lfun hs := by
        calc
          (∑' π, FL π hs)
              = ∑' π, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
                  simp [FL]
          _ = ∑' π, (μJ π * (D.runDistPure n π) hs) * Lfun hs := by
                apply tsum_congr
                intro π
                ring
          _ = (∑' π, μJ π * (D.runDistPure n π) hs) * Lfun hs := by
                rw [ENNReal.tsum_mul_right]
          _ = C * Lfun hs := rfl
      have hR :
          (∑' π, FR π hs) =
            ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
        simp [FR, mul_assoc, mul_comm]
      have hBridge :
          C * Lfun hs =
            ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
        by_cases hC : C = 0
        · have hweights0 : ∀ π : PureProfile I, μJ π * (D.runDistPure n π) hs = 0 := by
            have hsum0 : (∑' π, μJ π * (D.runDistPure n π) hs) = 0 := by
              simpa [C] using hC
            exact (ENNReal.tsum_eq_zero.mp hsum0)
          have hR0 :
              (∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π)) = 0 := by
            refine ENNReal.tsum_eq_zero.mpr ?_
            intro π
            have hw0 : μJ π * (D.runDistPure n π) hs = 0 := hweights0 π
            calc
              μJ π * ((D.runDistPure n π) hs * Gfun hs π)
                  = (μJ π * (D.runDistPure n π) hs) * Gfun hs π := by ring
              _ = 0 := by simp [hw0]
          calc
            C * Lfun hs = 0 := by simp [hC]
            _ = ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
                  rw [hR0]
        · -- Remaining mixed→behavioral bridge at fixed prefix, positive-mass case.
          -- To finish: normalize by `C`, disintegrate posterior, and identify the
          -- local conditional factors with `mixedToBehavioral`.
          have hC0 : C ≠ 0 := hC
          have hCtop : C ≠ ⊤ := by
            have hC_le_one : C ≤ 1 := by
              calc
                C = ∑ π, μJ π * (D.runDistPure n π) hs := by
                      simp [C, tsum_fintype]
                _ ≤ ∑ π, μJ π * 1 := by
                      refine Finset.sum_le_sum ?_
                      intro π _
                      gcongr
                      exact PMF.coe_le_one (D.runDistPure n π) hs
                _ = ∑ π, μJ π := by simp
                _ = 1 := by simpa [tsum_fintype] using μJ.tsum_coe
            exact ne_of_lt (lt_of_le_of_lt hC_le_one (by simp))
          have hPosterior :
              Lfun hs =
                ∑' π, ((μJ π * (D.runDistPure n π) hs) / C) * Gfun hs π := by
            -- Remaining core identity: one-step law under `mixedToBehavioral`
            -- equals posterior expectation of pure one-step continuation.
            -- ι : Type
            -- inst✝³ : Fintype ι
            -- M : LSM ι
            -- I : InfoModel M
            -- D : Dynamics I
            -- inst✝² : (i : ι) → Fintype (I.LocalTrace i)
            -- inst✝¹ : (i : ι) → Fintype (I.LocalPure i)
            -- inst✝ : (i : ι) → Fintype (Option (M.Act i))
            -- hPR : I.PerfectRecall
            -- μ : I.MixedProfile
            -- n : ℕ
            -- y : List M.Label × List M.State
            -- μJ : PMF (PureProfile I) := I.mixedJoint μ
            -- Lfun : List M.Label × List M.State → ENNReal := fun hs ↦
            --   (ProbabilityMassFunction.pushforward (D.stepDist (mixedToBehavioral I μ) hs.2) fun ls ↦
            --       (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))
            --     y
            -- Gfun : List M.Label × List M.State → PureProfile I → ENNReal := fun hs π ↦
            --   (ProbabilityMassFunction.pushforward (D.stepDist (pureToBehavioral I π) hs.2) fun ls ↦
            --       (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))
            --     y
            -- FL : PureProfile I → List M.Label × List M.State → ENNReal := fun π hs ↦ μJ π * ((D.runDistPure n π) hs * Lfun hs)
            -- FR : PureProfile I → List M.Label × List M.State → ENNReal := fun π hs ↦ μJ π * ((D.runDistPure n π) hs * Gfun hs π)
            -- hswapL : ∑' (π : PureProfile I), μJ π * ∑' (hs : List M.Label × List M.State), (D.runDistPure n π) hs * Lfun hs =
            --   ∑' (hs : List M.Label × List M.State) (π : PureProfile I), FL π hs
            -- hswapR : ∑' (π : PureProfile I), μJ π * ∑' (hs : List M.Label × List M.State), (D.runDistPure n π) hs * Gfun hs π =
            --   ∑' (hs : List M.Label × List M.State) (π : PureProfile I), FR π hs
            -- hs : List M.Label × List M.State
            -- hlen : hs.2.length = n + 1
            -- C : ENNReal := ∑' (π : PureProfile I), μJ π * (D.runDistPure n π) hs
            -- hL : ∑' (π : PureProfile I), FL π hs = C * Lfun hs
            -- hR : ∑' (π : PureProfile I), FR π hs = ∑' (π : PureProfile I), μJ π * ((D.runDistPure n π) hs * Gfun hs π)
            -- hC : ¬C = 0
            -- hC0 : C ≠ 0
            -- hCtop : C ≠ ⊤
            -- ⊢ Lfun hs = ∑' (π : PureProfile I), μJ π * (D.runDistPure n π) hs / C * Gfun hs π
            sorry
          calc
            C * Lfun hs
                = C * (∑' π, ((μJ π * (D.runDistPure n π) hs) / C) * Gfun hs π) := by
                    rw [hPosterior]
            _ = ∑' π, C * (((μJ π * (D.runDistPure n π) hs) / C) * Gfun hs π) := by
                  simpa using
                    (ENNReal.tsum_mul_left
                      (f := fun π : PureProfile I =>
                        ((μJ π * (D.runDistPure n π) hs) / C) * Gfun hs π)
                      (a := C)).symm
            _ = ∑' π, (μJ π * (D.runDistPure n π) hs) * Gfun hs π := by
                  apply tsum_congr
                  intro π
                  calc
                    C * (((μJ π * (D.runDistPure n π) hs) / C) * Gfun hs π)
                        = (C * ((μJ π * (D.runDistPure n π) hs) / C)) * Gfun hs π := by ring
                    _ = (μJ π * (D.runDistPure n π) hs) * Gfun hs π := by
                          simpa using congrArg
                            (fun t => t * Gfun hs π)
                            (ENNReal.mul_div_cancel
                              (a := C)
                              (b := μJ π * (D.runDistPure n π) hs)
                              hC0 hCtop)
            _ = ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
                  apply tsum_congr
                  intro π
                  ring
      exact hL.trans (hBridge.trans hR.symm)
    · have hfzero : ∀ π : PureProfile I, (D.runDistPure n π) hs = 0 := by
        intro π
        by_contra hne
        have hlen' :
            hs.2.length = n + 1 := by
          have hrun : (D.runDist n (pureToBehavioral I π)) hs ≠ 0 := by
            simpa [Execution.Dynamics.runDistPure] using hne
          exact InfoModel.runDist_support_stateLength (I := I) (D := D) n
            (pureToBehavioral I π) hs hrun
        exact hlen hlen'
      have hFL0 : (∑' π, FL π hs) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FL, hfzero π])
      have hFR0 : (∑' π, FR π hs) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FR, hfzero π])
      rw [hFL0, hFR0]
  calc
    (μJ.bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))) y
        = (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs) := by
            simp [μJ, Lfun, PMF.bind_apply]
    _ = ∑' hs, ∑' π, FL π hs := hswapL
    _ = ∑' hs, ∑' π, FR π hs := by
          apply tsum_congr
          intro hs
          exact hPerHs hs
    _ = (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π) := hswapR.symm
    _ = (μJ.bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))) y := by
            simp [μJ, Gfun, PMF.bind_apply]

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
    (μ : InfoModel.MixedProfile (I := I)) :
    D.evalBehavioral k (mixedToBehavioral (I := I) μ) =
      (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
  exact evalBehavioral_eq_mixed_of_stepIndependence (I := I) (D := D) (k := k) μ
    (mixedToBehavioral (I := I) μ)
    (mixedToBehavioral_stepIndependence (I := I) (D := D) hPR μ)

theorem kuhn_mixed_to_behavioral
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall) :
    KuhnMixedToBehavioralViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (InfoModel.mixedJoint (I := I)) (D.evalBehavioral k) (D.evalPure k) := by
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  intro μ
  refine ⟨mixedToBehavioral (I := I) μ, ?_⟩
  simpa using mixedToBehavioral_correct (I := I) (D := D) (k := k) hPR μ

/-- **Kuhn (complete, both directions)** at the `InfoModel` level.

Do not modify this by strengthening assumptions in either direction.
If proof infrastructure is missing, keep the exact statement and refine lemmas.
-/
theorem kuhn_complete
    [Fintype M.Label]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  exact ⟨
    kuhn_behavioral_to_mixed (I := I) (D := D) (k := k),
    kuhn_mixed_to_behavioral (I := I) (D := D) (k := k) hPR
  ⟩

end InfoModel

end Theorems
end GameTheory
