import Semantics.Execution
import GameTheory.Model.Lemmas.Coordinates
import GameTheory.Model.Lemmas.ProjectStates
import GameTheory.Model.Lemmas.Profiles

namespace GameTheory
namespace InfoModel

open Execution
open Execution.Dynamics

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)

/-- One-step extension from a state-trace depends only on the current queried
coordinates induced by that trace. -/
theorem stepDist_depends_on_current_context
    [∀ i, Fintype (Option (M.Act i))]
    (ω₁ ω₂ : I.FlatPolicy) (ss : List M.State)
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
  simp only [Dynamics.stepDist]
  congr 1
  funext ℓ
  congr 1
  simp only [Execution.Dynamics.jointActionDist, pureToBehavioral]
  congr 1
  funext i
  exact congrArg PMF.pure (hprof i)

/-- Explicit one-step extension from a state-trace depends only on the current
queried coordinates induced by that trace. -/
theorem stepActionStateDist_depends_on_current_context
    [∀ i, Fintype (Option (M.Act i))]
    (ω₁ ω₂ : I.FlatPolicy) (ss : List M.State)
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
  simp only [Dynamics.stepActionStateDist]
  congr 1
  funext ℓ
  congr 1
  simp only [Execution.Dynamics.jointActionDist, pureToBehavioral]
  congr 1
  funext i
  exact congrArg PMF.pure (hprof i)

/-- One-step behavioral extension depends only on the current queried local
contexts. -/
theorem stepDist_behavioral_depends_on_current_context
    [∀ i, Fintype (Option (M.Act i))]
    (σ τ : BehavioralProfile I) (ss : List M.State)
    (hag : ∀ i, σ i (I.projectStates i ss) = τ i (I.projectStates i ss)) :
    D.stepDist σ ss = D.stepDist τ ss := by
  simp only [Execution.Dynamics.stepDist]
  congr 1
  funext lab
  congr 1
  simp [Execution.Dynamics.jointActionDist, hag]

/-- Explicit one-step behavioral extension depends only on the current queried
local contexts. -/
theorem stepActionStateDist_behavioral_depends_on_current_context
    [∀ i, Fintype (Option (M.Act i))]
    (σ τ : BehavioralProfile I) (ss : List M.State)
    (hag : ∀ i, σ i (I.projectStates i ss) = τ i (I.projectStates i ss)) :
    D.stepActionStateDist σ ss = D.stepActionStateDist τ ss := by
  simp only [Execution.Dynamics.stepActionStateDist]
  congr 1
  funext lab
  congr 1
  simp [Execution.Dynamics.jointActionDist, hag]

/-- For a fixed state-trace prefix, one-step pure extension depends only on the
queried local actions at `projectStates`. -/
theorem pure_step_pushforward_depends_on_query
    [∀ i, Fintype (Option (M.Act i))]
    (hs : List M.Label × List M.State)
    (y : List M.Label × List M.State)
    (π π' : PureProfile I)
    (hquery :
      ∀ i, π i (I.projectStates i hs.2) = π' i (I.projectStates i hs.2)) :
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π) hs.2)
      (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
      =
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π') hs.2)
      (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := by
  let ω : I.FlatPolicy := fun k => π k.1 k.2
  let ω' : I.FlatPolicy := fun k => π' k.1 k.2
  have hnow :
      ∀ i, ω ⟨i, I.projectStates i hs.2⟩ = ω' ⟨i, I.projectStates i hs.2⟩ := by
    intro i
    simpa [ω, ω'] using hquery i
  have hstep :
      D.stepDist (pureToBehavioral I (I.reassemblePolicy ω)) hs.2 =
        D.stepDist (pureToBehavioral I (I.reassemblePolicy ω')) hs.2 :=
    stepDist_depends_on_current_context (I := I) (D := D) ω ω' hs.2 hnow
  have hpush := congrArg
    (fun ν =>
      (Math.ProbabilityMassFunction.pushforward ν
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
    hstep
  simpa [ω, ω'] using hpush

/-- Support-local trace length at round `n`: any sampled run-state has state
trace length `n+1`, hence each local projection also has length `n+1`. -/
theorem support_current_localTrace_length
    (n : Nat)
    [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I) (hs : List M.Label × List M.State)
    (hhs : D.runDistPure n π hs ≠ 0) (i : ι) :
    (I.projectStates i hs.2).length = n + 1 := by
  have hrun : (D.runDist n (pureToBehavioral I π)) hs ≠ 0 := by
    simpa [Execution.Dynamics.runDistPure] using hhs
  have hlen := runDist_support_stateLength (I := I) (D := D) n (pureToBehavioral I π) hs hrun
  calc
    (I.projectStates i hs.2).length = hs.2.length := I.projectStates_length i hs.2
    _ = n + 1 := hlen

/-- Prefix execution up to `n` depends only on coordinates whose local-trace
length is at most `n`. -/
theorem runDistPure_depends_on_len_le
    (n : Nat)
    [∀ i, Fintype (Option (M.Act i))]
    (ω₁ ω₂ : I.FlatPolicy)
    (hag : ∀ i v, v.length ≤ n →
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
            hs.2.length = n + 1 :=
          runDist_support_stateLength (I := I) (D := D) n
            (pureToBehavioral I (I.reassemblePolicy ω₂)) hs hsupp
        have hstep := stepDist_depends_on_current_context (I := I) (D := D) ω₁ ω₂ hs.2
          (fun i => by
            apply hag
            simp [I.projectStates_length i hs.2, hlenState])
        simp [Math.ProbabilityMassFunction.pushforward, hstep]

section
omit [Fintype ι]

/-- Freshness by length: for a run-state at round `n`, no coordinate can be
both "past" (`≤ n`) and "now" (`= projection at round n+1`). -/
theorem past_now_disjoint_by_length
    (n : Nat) (hs : List M.Label × List M.State)
    (hlen : hs.2.length = n + 1) :
    Disjoint
      {k : I.CoordIdx | I.IsPastCoord n k}
      {k : I.CoordIdx | I.IsNowCoord hs k} := by
  rw [Set.disjoint_left]
  intro k hkPast hkNow
  rcases hkNow with ⟨i, hkEq⟩
  have hkPast' : (I.projectStates i hs.2).length ≤ n := by
    have : k.2.length = (I.projectStates i hs.2).length := by
      cases hkEq
      rfl
    simpa [InfoModel.IsPastCoord, this] using hkPast
  have hkNowLen : (I.projectStates i hs.2).length = n + 1 := by
    simpa [hlen] using (I.projectStates_length i hs.2)
  have : n + 1 ≤ n := by
    rw [hkNowLen] at hkPast'
    exact hkPast'
  exact (Nat.not_succ_le_self n) this

end

/-- The joint action distribution under a fresh draw from the product measure
    equals the behavioral joint action distribution. -/
theorem jointAction_marginal
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (σ : BehavioralProfile I) (ss : List M.State) :
    Math.PMFProduct.pushforward
      (mixedJoint (I := I) (behavioralToMixed (I := I) σ))
      (fun π i => π i (I.projectStates i ss)) =
    Execution.Dynamics.jointActionDist (I := I) σ ss := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  simp only [mixedJoint, Execution.Dynamics.jointActionDist]
  let g : ∀ i, (LocalPure (I := I) i) → Option (M.Act i) :=
    fun i fi => fi (I.projectStates i ss)
  change Math.PMFProduct.pushforward (Math.PMFProduct.pmfPi (behavioralToMixed I σ))
    (fun f i => g i (f i)) = _
  rw [Math.PMFProduct.pmfPi_push_coordwise]
  congr 1; funext i
  change Math.PMFProduct.pushforward (behavioralToMixed I σ i) (g i) = σ i (I.projectStates i ss)
  have h := congr_fun (congr_fun
    (realize_behavioralToMixed (I := I) σ) i) (I.projectStates i ss)
  simp only [realizeBehavioralCanonical, Math.ProbabilityMassFunction.pushforward] at h
  exact h

/-- The expected step under a fresh draw from the product measure
    equals the behavioral step distribution. -/
theorem marginal_stepDist
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (σ : BehavioralProfile I) (ss : List M.State) :
    (mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind
      (fun π => D.stepDist (pureToBehavioral I π) ss) =
    D.stepDist σ ss := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  simp_rw [stepDist_pure (I := I)]
  set s := (ss.getLast?).getD M.init
  conv_lhs => rw [PMF.bind_comm]
  simp only [Execution.Dynamics.stepDist]
  congr 1; funext ℓ
  simp only [Math.ProbabilityMassFunction.pushforward]
  conv_lhs =>
    arg 2; ext π
    rw [← PMF.pure_bind (fun i => π i (I.projectStates i ss))
      (fun a => (D.nextState ℓ a s).bind (fun t => PMF.pure (ℓ, t)))]
  rw [show ((mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind fun π =>
      (PMF.pure (fun i => π i (I.projectStates i ss))).bind fun a =>
        (D.nextState ℓ a s).bind fun t => PMF.pure (ℓ, t)) =
    ((mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind
      (fun π => PMF.pure (fun i => π i (I.projectStates i ss)))).bind (fun a =>
        (D.nextState ℓ a s).bind fun t => PMF.pure (ℓ, t)) from
    (PMF.bind_bind _ _ _).symm]
  have hJA' :
      (mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind
        (fun π => PMF.pure (fun i => π i (I.projectStates i ss))) =
      Execution.Dynamics.jointActionDist (I := I) σ ss := by
    simpa [Math.ProbabilityMassFunction.pushforward] using
      (jointAction_marginal (I := I) σ ss)
  rw [hJA']

/-- The expected explicit step under the product measure induced by a mixed
profile equals the explicit step distribution of its canonical behavioral
realization. -/
theorem mixedJoint_stepActionStateDist_eq_realizeBehavioralCanonical
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (μ : MixedProfile (I := I)) (ss : List M.State) :
    (mixedJoint (I := I) μ).bind
      (fun π => D.stepActionStateDist (pureToBehavioral I π) ss) =
    D.stepActionStateDist (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  simp_rw [stepActionStateDist_pure (I := I)]
  set s := (ss.getLast?).getD M.init
  conv_lhs => rw [PMF.bind_comm]
  simp only [Execution.Dynamics.stepActionStateDist]
  congr 1
  funext ℓ
  simp only [Math.ProbabilityMassFunction.pushforward]
  conv_lhs =>
    arg 2
    ext π
    rw [← PMF.pure_bind (fun i => π i (I.projectStates i ss))
      (fun a => (D.nextState ℓ a s).bind (fun t => PMF.pure ((ℓ, a), t)))]
  rw [show ((mixedJoint (I := I) μ).bind fun π =>
      (PMF.pure (fun i => π i (I.projectStates i ss))).bind fun a =>
        (D.nextState ℓ a s).bind fun t => PMF.pure ((ℓ, a), t)) =
    ((mixedJoint (I := I) μ).bind
      (fun π => PMF.pure (fun i => π i (I.projectStates i ss)))).bind (fun a =>
        (D.nextState ℓ a s).bind fun t => PMF.pure ((ℓ, a), t)) from
    (PMF.bind_bind _ _ _).symm]
  have hJA' :
      (mixedJoint (I := I) μ).bind
        (fun π => PMF.pure (fun i => π i (I.projectStates i ss))) =
      Execution.Dynamics.jointActionDist (I := I)
        (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
    simpa [Math.ProbabilityMassFunction.pushforward, InfoModel.mixedJoint,
      Execution.Dynamics.jointActionDist, InfoModel.realizeBehavioralCanonical] using
      (Math.PMFProduct.pmfPi_push_coordwise
        (μ := μ) (g := fun i fi => fi (I.projectStates i ss)))
  rw [hJA']

/-- Pointwise explicit one-step bridge between a mixed profile and its
canonical behavioral realization. -/
theorem mixedJoint_stepActionStatePoint_eq_realizeBehavioralCanonical
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (μ : MixedProfile (I := I))
    (hs y : List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :
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
