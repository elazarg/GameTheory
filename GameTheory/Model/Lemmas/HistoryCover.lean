import GameTheory.Model.Lemmas.Profiles
import GameTheory.Model.Lemmas.ExecutionLocality
import Semantics.Execution

namespace GameTheory
namespace InfoModel

open Execution

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)

omit [Fintype ι] in
/-- Monotonicity of bounded history covers. -/
theorem CoversHistoriesUpTo.mono
    {H H' : ∀ i, Finset (I.LocalTrace i)} {k : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hsub : ∀ i, H i ⊆ H' i) :
    I.CoversHistoriesUpTo H' k := by
  intro i ss hr hlen
  exact hsub i (hCover i hr hlen)

/-- Any state trace in the support of a `k`-step run is covered by `H` when `H`
covers all reachable histories up to horizon `k`. -/
theorem CoversHistoriesUpTo.mem_of_runDist_support
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (σ : BehavioralProfile I)
    {ss : List M.State}
    (hss : (D.runDist n σ) ss ≠ 0)
    (i : ι) :
    I.projectStates i ss ∈ H i := by
  have hr : ReachStateTrace M ss :=
    GameTheory.InfoModel.runDist_support_reachStateTrace (I := I) (D := D) n σ ss hss
  have hlen : ss.length = n + 1 :=
    runDist_support_stateLength (I := I) (D := D) n σ ss hss
  exact hCover i hr (by simpa [hlen] using Nat.succ_le_succ hn)

/-- Pure-run support specialization of `CoversHistoriesUpTo.mem_of_runDist_support`. -/
theorem CoversHistoriesUpTo.mem_of_runDistPure_support
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (π : PureProfile I)
    {ss : List M.State}
    (hss : (D.runDistPure n π) ss ≠ 0)
    (i : ι) :
    I.projectStates i ss ∈ H i := by
  simpa [Execution.Dynamics.runDistPure] using
    CoversHistoriesUpTo.mem_of_runDist_support
      (I := I) (D := D) hCover hn (pureToBehavioral I π) hss i

/-- If two behavioral profiles agree on a cover `H`, then their `n`-step run
distributions agree whenever `H` covers all histories up to horizon `k ≥ n`. -/
theorem runDist_eq_of_agreeOnCover
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (σ τ : BehavioralProfile I)
    (hag : ∀ i (v : I.LocalTrace i), v ∈ H i → σ i v = τ i v) :
    D.runDist n σ = D.runDist n τ := by
  induction n generalizing σ τ with
  | zero =>
      simp [Execution.Dynamics.runDist]
  | succ n ih =>
      have hn' : n ≤ k := Nat.le_trans (Nat.le_succ n) hn
      calc
        D.runDist (n + 1) σ
            = (D.runDist n σ).bind (fun ss =>
                Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                  (fun t => ss ++ [t])) := by
                    simp [Execution.Dynamics.runDist]
        _ = (D.runDist n τ).bind (fun ss =>
              Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                (fun t => ss ++ [t])) := by
              rw [ih hn' σ τ hag]
        _ = (D.runDist n τ).bind (fun ss =>
              Math.ProbabilityMassFunction.pushforward (D.stepDist τ ss)
                (fun t => ss ++ [t])) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                (μ := D.runDist n τ)
                (f := fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist σ ss)
                    (fun t => ss ++ [t]))
                (g := fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist τ ss)
                    (fun t => ss ++ [t])) ?_
              intro ss hsupp
              have hss : (D.runDist n τ) ss ≠ 0 := by
                simpa [PMF.mem_support_iff] using hsupp
              have hstep :
                  D.stepDist σ ss = D.stepDist τ ss := by
                apply stepDist_behavioral_depends_on_current_context (I := I) (D := D)
                intro i
                exact hag i (I.projectStates i ss)
                  (CoversHistoriesUpTo.mem_of_runDist_support
                    (I := I) (D := D) hCover hn' τ hss i)
              simpa using congrArg
                (fun ν =>
                  Math.ProbabilityMassFunction.pushforward ν (fun t => ss ++ [t])) hstep
        _ = D.runDist (n + 1) τ := by
              simp [Execution.Dynamics.runDist]

/-- Pure-run corollary of `runDist_eq_of_agreeOnCover`. -/
theorem runDistPure_eq_of_agreeOnCover
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (π π' : PureProfile I)
    (hag : ∀ i (v : I.LocalTrace i), v ∈ H i → π i v = π' i v) :
    D.runDistPure n π = D.runDistPure n π' := by
  simpa [Execution.Dynamics.runDistPure, pureToBehavioral] using
    runDist_eq_of_agreeOnCover
      (I := I) (D := D) hCover hn (pureToBehavioral I π) (pureToBehavioral I π')
      (fun i v hv => by simp [pureToBehavioral, hag i v hv])

/-- Outcome-level behavioral corollary of `runDist_eq_of_agreeOnCover`. -/
theorem evalBehavioral_eq_of_agreeOnCover
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (σ τ : BehavioralProfile I)
    (hag : ∀ i (v : I.LocalTrace i), v ∈ H i → σ i v = τ i v) :
    D.evalBehavioral k σ = D.evalBehavioral k τ := by
  unfold Execution.Dynamics.evalBehavioral
  exact congrArg
    (fun ν => Math.ProbabilityMassFunction.pushforward ν I.outcomeOfStates)
    (runDist_eq_of_agreeOnCover (I := I) (D := D) hCover le_rfl σ τ hag)

/-- Outcome-level pure-run corollary of `runDistPure_eq_of_agreeOnCover`. -/
theorem evalPure_eq_of_agreeOnCover
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (π π' : PureProfile I)
    (hag : ∀ i (v : I.LocalTrace i), v ∈ H i → π i v = π' i v) :
    D.evalPure k π = D.evalPure k π' := by
  unfold Execution.Dynamics.evalPure
  exact congrArg
    (fun ν => Math.ProbabilityMassFunction.pushforward ν I.outcomeOfStates)
    (runDistPure_eq_of_agreeOnCover (I := I) (D := D) hCover le_rfl π π' hag)

end InfoModel
end GameTheory
