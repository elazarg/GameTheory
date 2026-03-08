import GameTheory.Model.Lemmas.ExecutionSupport
import GameTheory.Model.Lemmas.Coordinates
import GameTheory.Model.Lemmas.ProjectStates
import GameTheory.Model.Lemmas.Profiles

namespace GameTheory
namespace InfoModel

open Execution
open Execution.Dynamics

variable {ι : Type} [Fintype ι]
variable {σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)
variable (D : Execution.Dynamics I)

/-- One-step pure extension from a state trace depends only on the current
queried coordinates induced by that trace. -/
theorem stepDist_depends_on_current_context
    [DecidableEq ι]
    [∀ i, Fintype (Option (Act i))]
    (ω₁ ω₂ : I.FlatPolicy) (ss : List σ)
    (hag : ∀ i,
      ω₁ ⟨i, I.projectStates i ss⟩ =
        ω₂ ⟨i, I.projectStates i ss⟩) :
    D.stepDist (pureToBehavioral I (I.reassemblePolicy ω₁)) ss =
      D.stepDist (pureToBehavioral I (I.reassemblePolicy ω₂)) ss := by
  have hprof :
      ∀ i,
        (I.reassemblePolicy ω₁) i (I.projectStates i ss) =
          (I.reassemblePolicy ω₂) i (I.projectStates i ss) := by
    intro i
    simpa [InfoModel.reassemblePolicy] using hag i
  simp only [Execution.Dynamics.stepDist]
  congr 1
  ext a
  simp [Execution.Dynamics.jointActionDist, pureToBehavioral, hprof]

/-- Explicit one-step pure extension from a state trace depends only on the
current queried coordinates induced by that trace. -/
theorem stepActionStateDist_depends_on_current_context
    [DecidableEq ι]
    [∀ i, Fintype (Option (Act i))]
    (ω₁ ω₂ : I.FlatPolicy) (ss : List σ)
    (hag : ∀ i,
      ω₁ ⟨i, I.projectStates i ss⟩ =
        ω₂ ⟨i, I.projectStates i ss⟩) :
    D.stepActionStateDist (pureToBehavioral I (I.reassemblePolicy ω₁)) ss =
      D.stepActionStateDist (pureToBehavioral I (I.reassemblePolicy ω₂)) ss := by
  have hprof :
      ∀ i,
        (I.reassemblePolicy ω₁) i (I.projectStates i ss) =
          (I.reassemblePolicy ω₂) i (I.projectStates i ss) := by
    intro i
    simpa [InfoModel.reassemblePolicy] using hag i
  simp only [Execution.Dynamics.stepActionStateDist]
  congr 1
  ext a
  simp [Execution.Dynamics.jointActionDist, pureToBehavioral, hprof]

/-- One-step behavioral extension depends only on the current queried local
contexts. -/
theorem stepDist_behavioral_depends_on_current_context
    [DecidableEq ι]
    [∀ i, Fintype (Option (Act i))]
    (b τ : BehavioralProfile I) (ss : List σ)
    (hag : ∀ i, b i (I.projectStates i ss) = τ i (I.projectStates i ss)) :
    D.stepDist b ss = D.stepDist τ ss := by
  simp only [Execution.Dynamics.stepDist]
  congr 1
  ext a
  simp [Execution.Dynamics.jointActionDist, hag]

/-- Explicit one-step behavioral extension depends only on the current queried
local contexts. -/
theorem stepActionStateDist_behavioral_depends_on_current_context
    [DecidableEq ι]
    [∀ i, Fintype (Option (Act i))]
    (b τ : BehavioralProfile I) (ss : List σ)
    (hag : ∀ i, b i (I.projectStates i ss) = τ i (I.projectStates i ss)) :
    D.stepActionStateDist b ss = D.stepActionStateDist τ ss := by
  simp only [Execution.Dynamics.stepActionStateDist]
  congr 1
  ext a
  simp [Execution.Dynamics.jointActionDist, hag]

/-- For a fixed state-trace prefix, one-step pure extension depends only on the
queried local actions at `projectStates`. -/
theorem pure_step_pushforward_depends_on_query
    [DecidableEq ι]
    [∀ i, Fintype (Option (Act i))]
    (hs y : List σ)
    (π π' : PureProfile I)
    (hquery :
      ∀ i, π i (I.projectStates i hs) = π' i (I.projectStates i hs)) :
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π) hs)
      (fun t => hs ++ [t])) y
      =
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π') hs)
      (fun t => hs ++ [t])) y := by
  let ω : I.FlatPolicy := fun k => π k.1 k.2
  let ω' : I.FlatPolicy := fun k => π' k.1 k.2
  have hnow :
      ∀ i, ω ⟨i, I.projectStates i hs⟩ = ω' ⟨i, I.projectStates i hs⟩ := by
    intro i
    simpa [ω, ω'] using hquery i
  have hstep :
      D.stepDist (pureToBehavioral I (I.reassemblePolicy ω)) hs =
        D.stepDist (pureToBehavioral I (I.reassemblePolicy ω')) hs :=
    stepDist_depends_on_current_context (I := I) (D := D) ω ω' hs hnow
  have hpush := congrArg
    (fun ν =>
      (Math.ProbabilityMassFunction.pushforward ν
        (fun t => hs ++ [t])) y)
    hstep
  simpa [ω, ω'] using hpush

/-- Prefix execution up to round `n` depends only on coordinates whose private
visible-history length is at most `n`. -/
theorem runDistPure_depends_on_len_le
    [DecidableEq ι]
    [∀ i, Fintype (Option (Act i))]
    (n : Nat)
    (ω₁ ω₂ : I.FlatPolicy)
    (hag : ∀ i v, v.2.length ≤ n →
      ω₁ ⟨i, v⟩ = ω₂ ⟨i, v⟩) :
    D.runDistPure n (I.reassemblePolicy ω₁) =
      D.runDistPure n (I.reassemblePolicy ω₂) := by
  induction n with
  | zero =>
      simp [Execution.Dynamics.runDistPure, Execution.Dynamics.runDist]
  | succ n ih =>
      simp only [Execution.Dynamics.runDistPure, runDist_succ]
      have ih' :
          D.runDist n (pureToBehavioral I (I.reassemblePolicy ω₁)) =
            D.runDist n (pureToBehavioral I (I.reassemblePolicy ω₂)) :=
        ih (fun i v hv => hag i v (Nat.le_succ_of_le hv))
      rw [ih']
      ext y
      simp only [PMF.bind_apply]
      apply tsum_congr
      intro hs
      by_cases hsupp : (D.runDist n (pureToBehavioral I (I.reassemblePolicy ω₂))) hs = 0
      · simp [hsupp]
      · have hlenState :
            hs.length = n + 1 :=
          runDist_support_stateLength (I := I) (D := D) n
            (pureToBehavioral I (I.reassemblePolicy ω₂)) hs hsupp
        have hstep := stepDist_depends_on_current_context (I := I) (D := D) ω₁ ω₂ hs
          (fun i => by
            have hprojLen :
                (I.projectStates i hs).2.length = n + 1 := by
              exact (I.projectStates_lengths i hs).2.trans hlenState
            apply hag
            rw [hprojLen])
        simp [Math.ProbabilityMassFunction.pushforward, hstep]

section
omit [Fintype ι]

/-- Freshness by length: for a run-state at round `n`, no coordinate can be
both "past" (`≤ n`) and "now" (`= projection at round n+1`). -/
theorem past_now_disjoint_by_length
    (n : Nat) (ss : List σ)
    (hlen : ss.length = n + 1) :
    Disjoint
      {k : I.CoordIdx | I.IsPastCoord n k}
      {k : I.CoordIdx | I.IsNowCoord ss k} := by
  rw [Set.disjoint_left]
  intro k hkPast hkNow
  rcases hkNow with ⟨i, hkEq⟩
  have hkPast' : (I.projectStates i ss).2.length ≤ n := by
    have : k.2.2.length = (I.projectStates i ss).2.length := by
      cases hkEq
      rfl
    simpa [InfoModel.IsPastCoord, this] using hkPast
  have hkNowLen : (I.projectStates i ss).2.length = n + 1 := by
    exact (I.projectStates_lengths i ss).2.trans hlen
  have : n + 1 ≤ n := by
    rw [← hkNowLen]
    exact hkPast'
  exact (Nat.not_succ_le_self n) this

end

/-- The joint action distribution under a fresh draw from the product measure
equals the behavioral joint action distribution. -/
theorem jointAction_marginal
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (b : BehavioralProfile I) (ss : List σ) :
    Math.ProbabilityMassFunction.pushforward
      (mixedJoint (I := I) (behavioralToMixed (I := I) b))
      (fun π i => π i (I.projectStates i ss)) =
    Execution.Dynamics.jointActionDist (I := I) b ss := by
  classical
  simp only [mixedJoint, Execution.Dynamics.jointActionDist]
  let g : ∀ i, (LocalPure (I := I) i) → Option (Act i) :=
    fun i fi => fi (I.projectStates i ss)
  change Math.ProbabilityMassFunction.pushforward (Math.PMFProduct.pmfPi (behavioralToMixed I b))
    (fun f i => g i (f i)) = _
  rw [Math.PMFProduct.pmfPi_push_coordwise]
  congr 1
  funext i
  change Math.ProbabilityMassFunction.pushforward (behavioralToMixed I b i) (g i) =
    b i (I.projectStates i ss)
  have h := congr_fun (congr_fun
    (realize_behavioralToMixed (I := I) b) i) (I.projectStates i ss)
  simpa [realizeBehavioralCanonical] using h

/-- The expected one-step transition under a fresh draw from the product measure
equals the behavioral step distribution. -/
theorem marginal_stepDist
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (b : BehavioralProfile I) (ss : List σ) :
    (mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind
      (fun π => D.stepDist (pureToBehavioral I π) ss) =
    D.stepDist b ss := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  set s := (ss.getLast?).getD I.init
  calc
    (mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind
        (fun π => D.stepDist (pureToBehavioral I π) ss)
      =
    (mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind
        (fun π => D.nextState (fun i => π i (I.projectStates i ss)) s)
        := by
          congr 1
          funext π
          simpa [s] using (stepDist_pure (I := I) (D := D) π ss)
    _ =
    (mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind
        (fun π =>
          (PMF.pure (fun i => π i (I.projectStates i ss))).bind
            (fun a => D.nextState a s)) := by
          congr 1
          funext π
          rw [PMF.pure_bind]
    _ =
    ((mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind
        (fun π => PMF.pure (fun i => π i (I.projectStates i ss)))).bind
        (fun a => D.nextState a s) := by
          rw [PMF.bind_bind]
    _ =
      (Execution.Dynamics.jointActionDist (I := I) b ss).bind
        (fun a => D.nextState a s) := by
          have hJA :
              (mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind
                (fun π => PMF.pure (fun i => π i (I.projectStates i ss))) =
              Execution.Dynamics.jointActionDist (I := I) b ss := by
            simpa [Math.ProbabilityMassFunction.pushforward] using
              (jointAction_marginal (I := I) b ss)
          rw [hJA]
    _ = D.stepDist b ss := by
          simp [Execution.Dynamics.stepDist, s]

/-- The expected explicit step under a fresh draw from the product measure
equals the explicit step distribution of the canonical behavioral realization. -/
theorem mixedJoint_stepActionStateDist_eq_realizeBehavioralCanonical
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (μ : MixedProfile (I := I)) (ss : List σ) :
    (mixedJoint (I := I) μ).bind
      (fun π => D.stepActionStateDist (pureToBehavioral I π) ss) =
    D.stepActionStateDist (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  set s := (ss.getLast?).getD I.init
  calc
    (mixedJoint (I := I) μ).bind
        (fun π => D.stepActionStateDist (pureToBehavioral I π) ss)
      =
    (mixedJoint (I := I) μ).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.nextState (fun i => π i (I.projectStates i ss)) s)
            (fun t => ((fun i => π i (I.projectStates i ss)), t)))
        := by
          congr 1
          funext π
          simpa [s] using (stepActionStateDist_pure (I := I) (D := D) π ss)
    _ =
    (mixedJoint (I := I) μ).bind
        (fun π =>
          ((D.nextState (fun i => π i (I.projectStates i ss)) s).bind
            (fun t => PMF.pure ((fun i => π i (I.projectStates i ss)), t)))) := by
          rfl
    _ =
    ((mixedJoint (I := I) μ).bind
        (fun π => PMF.pure (fun i => π i (I.projectStates i ss)))).bind
        (fun a =>
          Math.ProbabilityMassFunction.pushforward (D.nextState a s)
            (fun t => (a, t))) := by
          rw [PMF.bind_bind]
          congr
          funext a
          simp [Math.ProbabilityMassFunction.pushforward]
    _ =
      (Execution.Dynamics.jointActionDist (I := I)
        (InfoModel.realizeBehavioralCanonical (I := I) μ) ss).bind
        (fun a =>
          Math.ProbabilityMassFunction.pushforward (D.nextState a s)
            (fun t => (a, t))) := by
          have hJA :
              (mixedJoint (I := I) μ).bind
                (fun π => PMF.pure (fun i => π i (I.projectStates i ss))) =
              Execution.Dynamics.jointActionDist (I := I)
                (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
            simpa [Math.ProbabilityMassFunction.pushforward, InfoModel.mixedJoint,
              Execution.Dynamics.jointActionDist, InfoModel.realizeBehavioralCanonical] using
              (Math.PMFProduct.pmfPi_push_coordwise
                (μ := μ) (g := fun i fi => fi (I.projectStates i ss)))
          rw [hJA]
    _ =
      D.stepActionStateDist (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
          simp [Execution.Dynamics.stepActionStateDist, s]

/-- Pointwise explicit one-step bridge between a mixed profile and its
canonical behavioral realization. -/
theorem mixedJoint_stepActionStatePoint_eq_realizeBehavioralCanonical
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (I := I))
    (hs y : List (I.JointAction) × List σ) :
    (∑' π, (mixedJoint (I := I) μ) π *
      (Math.ProbabilityMassFunction.pushforward
        (D.stepActionStateDist (pureToBehavioral I π) hs.2)
        (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) y) =
    (Math.ProbabilityMassFunction.pushforward
      (D.stepActionStateDist (InfoModel.realizeBehavioralCanonical (I := I) μ) hs.2)
      (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) y := by
  have hstep :=
    mixedJoint_stepActionStateDist_eq_realizeBehavioralCanonical
      (I := I) (D := D) μ hs.2
  have hpush := congrArg
    (fun ν =>
      (Math.ProbabilityMassFunction.pushforward ν
        (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) y)
    hstep
  have hpushBind :
      ((mixedJoint (I := I) μ).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepActionStateDist (pureToBehavioral I π) hs.2)
            (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2])))) y
        =
      (Math.ProbabilityMassFunction.pushforward
        ((mixedJoint (I := I) μ).bind
          (fun π => D.stepActionStateDist (pureToBehavioral I π) hs.2))
        (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) y := by
          simpa using congrArg (fun ν => ν y) (
            (Math.ProbabilityMassFunction.pushforward_bind
              (μ := mixedJoint (I := I) μ)
              (k := fun π => D.stepActionStateDist (pureToBehavioral I π) hs.2)
              (f := fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))).symm)
  calc
    (∑' π, (mixedJoint (I := I) μ) π *
      (Math.ProbabilityMassFunction.pushforward
        (D.stepActionStateDist (pureToBehavioral I π) hs.2)
        (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) y)
        =
      ((mixedJoint (I := I) μ).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepActionStateDist (pureToBehavioral I π) hs.2)
            (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2])))) y := by
              simp [PMF.bind_apply]
    _ =
      (Math.ProbabilityMassFunction.pushforward
        ((mixedJoint (I := I) μ).bind
          (fun π => D.stepActionStateDist (pureToBehavioral I π) hs.2))
        (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) y := hpushBind
    _ =
      (Math.ProbabilityMassFunction.pushforward
        (D.stepActionStateDist (InfoModel.realizeBehavioralCanonical (I := I) μ) hs.2)
        (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) y := by
          simpa using hpush

end InfoModel
end GameTheory
