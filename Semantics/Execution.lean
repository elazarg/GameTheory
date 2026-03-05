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
end GameTheory
