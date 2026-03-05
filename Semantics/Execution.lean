import GameTheory.Model.SemanticForm

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

end InfoModel

namespace Execution
namespace Dynamics

variable {ι : Type} [Fintype ι]
variable {M : LSM ι}
variable {I : InfoModel M}

/-- Prefix-parametrized bounded execution: start from an already accumulated
history `hs0` and extend it for `n` further steps under `σ`. -/
noncomputable def runDistFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I)
    (hs0 : List M.Label × List M.State) : PMF (List M.Label × List M.State) :=
  Nat.rec (PMF.pure hs0)
    (fun _ rec =>
      rec.bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))
    n

/-- Base case for `runDistFrom`: zero additional rounds leaves the starting
prefix unchanged. -/
@[simp] theorem runDistFrom_zero
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I)
    (hs0 : List M.Label × List M.State) :
    runDistFrom D 0 σ hs0 = PMF.pure hs0 := rfl

/-- One-step unfolding equation for prefix-parametrized execution. -/
@[simp] theorem runDistFrom_succ
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I)
    (hs0 : List M.Label × List M.State) :
    runDistFrom D (n + 1) σ hs0 =
      (runDistFrom D n σ hs0).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) := rfl

/-- Ordinary bounded execution is the special case of `runDistFrom` started
from the initial history. -/
theorem runDist_eq_runDistFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I) :
    D.runDist n σ = runDistFrom D n σ ([], [M.init]) := rfl

/-- Pure-profile continuation from an arbitrary already accumulated history. -/
noncomputable def runDistPureFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (π : PureProfile I)
    (hs0 : List M.Label × List M.State) : PMF (List M.Label × List M.State) :=
  runDistFrom D n (pureToBehavioral I π) hs0

/-- Ordinary pure bounded execution is the initial-history specialization of
`runDistPureFrom`. -/
theorem runDistPure_eq_runDistPureFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (π : PureProfile I) :
    D.runDistPure n π = runDistPureFrom D n π ([], [M.init]) := rfl

end Dynamics
end Execution

end GameTheory
