import GameTheory.Model.SemanticForm
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

/-- Unfold `runDist` at `0`. -/
@[simp] theorem runDist_zero
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) :
    D.runDist 0 σ = PMF.pure ([], [M.init]) := rfl

/-- One-step unfolding equation for `runDist`. -/
@[simp] theorem runDist_succ
    [∀ i, Fintype (Option (M.Act i))]
    (n : Nat) (σ : BehavioralProfile I) :
    D.runDist (n + 1) σ =
      (D.runDist n σ).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) := rfl

/-- In the support of `runDist n`, state traces have length `n + 1`. -/
theorem runDist_support_stateLength
    (n : Nat)
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (hs : List M.Label × List M.State) :
    (D.runDist n σ) hs ≠ 0 → hs.2.length = n + 1 := by
  induction n generalizing hs with
  | zero =>
      intro h
      have hmem : hs ∈ (PMF.pure ([], [M.init]) : PMF _).support := by
        rwa [runDist_zero (I := I) (D := D)] at h
      rw [PMF.support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      rfl
  | succ n ih =>
      intro h
      rw [runDist_succ (I := I) (D := D), PMF.bind_apply] at h
      by_contra hlen
      apply h
      rw [ENNReal.tsum_eq_zero]
      intro hs'
      by_cases hhs' : (D.runDist n σ) hs' = 0
      · simp [hhs']
      · have hlen' := ih hs' hhs'
        suffices hsuff :
            (Math.ProbabilityMassFunction.pushforward
              (D.stepDist σ hs'.2) (fun ls => (hs'.1 ++ [ls.1], hs'.2 ++ [ls.2]))) hs = 0 by
          simp [hsuff]
        simp only [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply]
        rw [ENNReal.tsum_eq_zero]
        intro ls
        suffices hne : hs ≠ (hs'.1 ++ [ls.1], hs'.2 ++ [ls.2]) by
          simp [PMF.pure_apply, hne]
        intro heq
        apply hlen
        have : hs.2.length = hs'.2.length + 1 := by
          simpa [List.length_append] using congrArg (fun z => z.2.length) heq
        omega

/-- One-step extension from a state-trace depends only on the current queried
coordinates induced by that trace. -/
theorem stepDist_depends_on_current_context
    [∀ i, Fintype (Option (M.Act i))]
    (ω₁ ω₂ : I.FlatPolicy) (ss : List M.State)
    (hag : ∀ i ℓ,
      ω₁ ⟨i, (ℓ, I.projectStates i ss)⟩ =
        ω₂ ⟨i, (ℓ, I.projectStates i ss)⟩) :
    D.stepDist (pureToBehavioral I (I.reassemblePolicy ω₁)) ss =
      D.stepDist (pureToBehavioral I (I.reassemblePolicy ω₂)) ss := by
  have hprof :
      ∀ i ℓ,
        (I.reassemblePolicy ω₁) i ℓ (I.projectStates i ss) =
          (I.reassemblePolicy ω₂) i ℓ (I.projectStates i ss) := by
    intro i ℓ
    simpa [InfoModel.reassemblePolicy] using hag i ℓ
  simp only [Dynamics.stepDist]
  congr 1
  funext ℓ
  congr 1
  simp only [Execution.Dynamics.jointActionDist, pureToBehavioral]
  congr 1
  funext i
  exact congrArg PMF.pure (hprof i ℓ)

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
    (hag : ∀ i ℓ v, v.length ≤ n →
      ω₁ ⟨i, (ℓ, v)⟩ = ω₂ ⟨i, (ℓ, v)⟩) :
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
        ih (fun i ℓ v hv => hag i ℓ v (Nat.le_succ_of_le hv))
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
          (fun i ℓ => by
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
  rcases hkNow with ⟨i, ℓ, hkEq⟩
  have hkPast' : (I.projectStates i hs.2).length ≤ n := by
    have : k.2.2.length = (I.projectStates i hs.2).length := by
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
    [Fintype M.Label]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (σ : BehavioralProfile I) (ss : List M.State) (ℓ : M.Label) :
    Math.PMFProduct.pushforward
      (mixedJoint (I := I) (behavioralToMixed (I := I) σ))
      (fun π i => π i ℓ (I.projectStates i ss)) =
    Execution.Dynamics.jointActionDist (I := I) σ ss ℓ := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  simp only [mixedJoint, Execution.Dynamics.jointActionDist]
  let g : ∀ i, (LocalPure (I := I) i) → Option (M.Act i) :=
    fun i fi => fi ℓ (I.projectStates i ss)
  change Math.PMFProduct.pushforward (Math.PMFProduct.pmfPi (behavioralToMixed I σ))
    (fun f i => g i (f i)) = _
  rw [Math.PMFProduct.pmfPi_push_coordwise]
  congr 1; funext i
  change Math.PMFProduct.pushforward (behavioralToMixed I σ i) (g i) = σ i ℓ (I.projectStates i ss)
  have h := congr_fun (congr_fun (congr_fun
    (realize_behavioralToMixed (I := I) σ) i) ℓ) (I.projectStates i ss)
  simp only [realizeBehavioralCanonical, Math.ProbabilityMassFunction.pushforward] at h
  exact h

/-- The expected step under a fresh draw from the product measure
    equals the behavioral step distribution. -/
theorem marginal_stepDist
    [Fintype M.Label]
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
    rw [← PMF.pure_bind (fun i => π i ℓ (I.projectStates i ss))
      (fun a => (D.nextState ℓ a s).bind (fun t => PMF.pure (ℓ, t)))]
  rw [show ((mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind fun π =>
      (PMF.pure (fun i => π i ℓ (I.projectStates i ss))).bind fun a =>
        (D.nextState ℓ a s).bind fun t => PMF.pure (ℓ, t)) =
    ((mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind
      (fun π => PMF.pure (fun i => π i ℓ (I.projectStates i ss)))).bind (fun a =>
        (D.nextState ℓ a s).bind fun t => PMF.pure (ℓ, t)) from
    (PMF.bind_bind _ _ _).symm]
  have hJA' :
      (mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind
        (fun π => PMF.pure (fun i => π i ℓ (I.projectStates i ss))) =
      Execution.Dynamics.jointActionDist (I := I) σ ss ℓ := by
    simpa [Math.ProbabilityMassFunction.pushforward] using
      (jointAction_marginal (I := I) σ ss ℓ)
  rw [hJA']

end InfoModel
end GameTheory
