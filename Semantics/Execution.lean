import GameTheory.Model.SemanticForm
import GameTheory.Model.Lemmas.ReachStateTrace

namespace GameTheory
namespace InfoModel

open Execution
open Execution.Dynamics

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)

/-- Unfold `runDist` at `0`. -/
@[simp] theorem runDist_zero
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) :
    D.runDist 0 σ = PMF.pure [M.init] := rfl

/-- One-step unfolding equation for `runDist`. -/
@[simp] theorem runDist_succ
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (n : Nat) (σ : BehavioralProfile I) :
    D.runDist (n + 1) σ =
      (D.runDist n σ).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
          (fun t => ss ++ [t])) := rfl

/-- In the support of `runDist n`, state traces have length `n + 1`. -/
theorem runDist_support_stateLength
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (n : Nat)
    (σ : BehavioralProfile I) (ss : List M.State) :
    (D.runDist n σ) ss ≠ 0 → ss.length = n + 1 := by
  induction n generalizing ss with
  | zero =>
      intro h
      have hmem : ss ∈ (PMF.pure [M.init] : PMF _).support := by
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
      intro ss'
      by_cases hss' : (D.runDist n σ) ss' = 0
      · simp [hss']
      · have hlen' := ih ss' hss'
        suffices hsuff :
            (Math.ProbabilityMassFunction.pushforward
              (D.stepDist σ ss') (fun t => ss' ++ [t])) ss = 0 by
          simp [hsuff]
        simp only [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply]
        rw [ENNReal.tsum_eq_zero]
        intro t
        suffices hne : ss ≠ ss' ++ [t] by
          simp [PMF.pure_apply, hne]
        intro heq
        apply hlen
        have : ss.length = ss'.length + 1 := by
          simpa [List.length_append] using congrArg List.length heq
        omega

end InfoModel

namespace Execution
namespace Dynamics

variable {ι : Type} [Fintype ι]
variable {M : LSM ι}
variable {I : InfoModel M}

/-- Action-explicit one-step kernel from a current state under behavioral
profile `σ`. The sampled result retains the realized joint action and successor
state. -/
noncomputable def stepActionStateDist
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I) (ss : List M.State) :
    PMF (JointAction M × M.State) :=
  let s := (ss.getLast?).getD M.init
  (jointActionDist (I := I) σ ss).bind fun a =>
    Math.ProbabilityMassFunction.pushforward (D.nextState a s) (fun t => (a, t))

/-- Forgetting the realized joint action from `stepActionStateDist` recovers the
ordinary one-step kernel `stepDist`. -/
theorem stepDist_eq_pushforward_stepActionStateDist
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I) (ss : List M.State) :
    Math.ProbabilityMassFunction.pushforward
      (stepActionStateDist (I := I) D σ ss)
      Prod.snd =
    D.stepDist σ ss := by
  classical
  ext t
  simp [stepActionStateDist, Execution.Dynamics.stepDist,
    Math.ProbabilityMassFunction.pushforward, PMF.bind_bind]

private theorem pushforward_fixedAction_apply_same
    {α β : Type*}
    (ν : PMF α) (b : β) (a : α) :
    Math.ProbabilityMassFunction.pushforward ν (fun x => (b, x)) (b, a) = ν a := by
  classical
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply]
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    have hzero : (PMF.pure (b, a')) (b, a) = 0 := by
      by_cases hp : (b, a') = (b, a)
      · exfalso
        exact ha' (by simpa using congrArg Prod.snd hp)
      · have hneq' : (b, a) ≠ (b, a') := by
          intro hpair
          exact hp hpair.symm
        simpa [PMF.pure_apply] using hneq'
    simp [hzero]

private theorem pushforward_fixedAction_apply_ne
    {α β : Type*}
    (ν : PMF α) (b b' : β) (a : α) (h : b' ≠ b) :
    Math.ProbabilityMassFunction.pushforward ν (fun x => (b', x)) (b, a) = 0 := by
  classical
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply]
  rw [ENNReal.tsum_eq_zero]
  intro a'
  have hEq : (b', a') ≠ (b, a) := by
    intro hpair
    exact h (by simpa using congrArg Prod.fst hpair)
  have hzero : (PMF.pure (b', a')) (b, a) = 0 := by
    by_cases hp : (b', a') = (b, a)
    · exact False.elim (hEq hp)
    · have hneq' : (b, a) ≠ (b', a') := by
        intro hpair
        exact hp hpair.symm
      simpa [PMF.pure_apply] using hneq'
  simp [hzero]

end Dynamics
end Execution
end GameTheory
