import GameTheory.Model.Lemmas.Profiles
import GameTheory.Model.Lemmas.ExecutionLocality
import GameTheory.Model.Lemmas.ExecutionSupport

namespace GameTheory
namespace InfoModel

open Execution

section BoundedLists

variable {α : Type} [DecidableEq α]

/-- Finite enumeration of lists of length exactly `n` over a finite alphabet
`s`. -/
def listsOfLength (s : Finset α) : Nat → Finset (List α)
  | 0 => {[]}
  | n + 1 => (s.product (listsOfLength s n)).image (fun p => p.1 :: p.2)

/-- Finite enumeration of lists of length at most `n` over a finite alphabet
`s`. -/
def listsUpToLength (s : Finset α) (n : Nat) : Finset (List α) :=
  (Finset.range (n + 1)).biUnion (fun k => listsOfLength s k)

theorem mem_listsOfLength_of_forall_mem
    {s : Finset α} :
    ∀ {xs : List α} {n : Nat},
      xs.length = n →
      (∀ x ∈ xs, x ∈ s) →
      xs ∈ listsOfLength s n
  | [], 0, hlen, _ => by simp [listsOfLength]
  | [], n + 1, hlen, _ => by cases hlen
  | x :: xs, 0, hlen, _ => by cases hlen
  | x :: xs, n + 1, hlen, hmem => by
      have hx : x ∈ s := hmem x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ s := by
        intro y hy
        exact hmem y (by simp [hy])
      have htail : xs.length = n := by simpa using Nat.succ.inj hlen
      have hrec : xs ∈ listsOfLength s n :=
        mem_listsOfLength_of_forall_mem htail hxs
      refine Finset.mem_image.mpr ?_
      refine ⟨(x, xs), ?_, by simp⟩
      simp [hx, hrec]

theorem mem_listsUpToLength_of_forall_mem
    {s : Finset α} {xs : List α} {n : Nat}
    (hlen : xs.length ≤ n)
    (hmem : ∀ x ∈ xs, x ∈ s) :
    xs ∈ listsUpToLength s n := by
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨xs.length, ?_, ?_⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlen)
  · exact mem_listsOfLength_of_forall_mem (s := s) rfl hmem

end BoundedLists

variable {ι : Type} [Fintype ι]
variable {σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)
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
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (b : BehavioralProfile I)
    {ss : List σ}
    (hss : (D.runDist n b) ss ≠ 0)
    (i : ι) :
    I.projectStates i ss ∈ H i := by
  have hr : Semantics.SM.ReachStateTrace I.toSM ss :=
    GameTheory.InfoModel.runDist_support_reachStateTrace (I := I) (D := D) n b ss hss
  have hlen : ss.length = n + 1 :=
    runDist_support_stateLength (I := I) (D := D) n b ss hss
  exact hCover i hr (by simpa [hlen] using Nat.succ_le_succ hn)

/-- Pure-run support specialization of `CoversHistoriesUpTo.mem_of_runDist_support`. -/
theorem CoversHistoriesUpTo.mem_of_runDistPure_support
    [DecidableEq ι]
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (π : PureProfile I)
    {ss : List σ}
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
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (b τ : BehavioralProfile I)
    (hag : ∀ i (v : I.LocalTrace i), v ∈ H i → b i v = τ i v) :
    D.runDist n b = D.runDist n τ := by
  induction n generalizing b τ with
  | zero =>
      simp [Execution.Dynamics.runDist]
  | succ n ih =>
      have hn' : n ≤ k := Nat.le_trans (Nat.le_succ n) hn
      calc
        D.runDist (n + 1) b
            = (D.runDist n b).bind (fun ss =>
                Math.ProbabilityMassFunction.pushforward (D.stepDist b ss)
                  (fun t => ss ++ [t])) := by
                    simp [Execution.Dynamics.runDist]
        _ = (D.runDist n τ).bind (fun ss =>
              Math.ProbabilityMassFunction.pushforward (D.stepDist b ss)
                (fun t => ss ++ [t])) := by
              rw [ih hn' b τ hag]
        _ = (D.runDist n τ).bind (fun ss =>
              Math.ProbabilityMassFunction.pushforward (D.stepDist τ ss)
                (fun t => ss ++ [t])) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                (μ := D.runDist n τ)
                (f := fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist b ss)
                    (fun t => ss ++ [t]))
                (g := fun ss =>
                  Math.ProbabilityMassFunction.pushforward (D.stepDist τ ss)
                    (fun t => ss ++ [t])) ?_
              intro ss hsupp
              have hss : (D.runDist n τ) ss ≠ 0 := by
                simpa [PMF.mem_support_iff] using hsupp
              have hstep :
                  D.stepDist b ss = D.stepDist τ ss := by
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
    [∀ i, Fintype (Option (Act i))]
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
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (b τ : BehavioralProfile I)
    (hag : ∀ i (v : I.LocalTrace i), v ∈ H i → b i v = τ i v) :
    D.evalBehavioral k b = D.evalBehavioral k τ := by
  unfold Execution.Dynamics.evalBehavioral
  exact congrArg
    (fun ν => Math.ProbabilityMassFunction.pushforward ν I.outcomeOfStates)
    (runDist_eq_of_agreeOnCover (I := I) (D := D) hCover le_rfl b τ hag)

/-- Outcome-level pure-run corollary of `runDistPure_eq_of_agreeOnCover`. -/
theorem evalPure_eq_of_agreeOnCover
    [DecidableEq ι]
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (π π' : PureProfile I)
    (hag : ∀ i (v : I.LocalTrace i), v ∈ H i → π i v = π' i v) :
    D.evalPure k π = D.evalPure k π' := by
  unfold Execution.Dynamics.evalPure
  exact congrArg
    (fun ν => Math.ProbabilityMassFunction.pushforward ν I.outcomeOfStates)
    (runDistPure_eq_of_agreeOnCover (I := I) (D := D) hCover le_rfl π π' hag)

/-- Under a valid cover, extending a restricted behavioral profile obtained by
restriction from `σ` does not change `n`-step run distributions. -/
theorem runDist_eq_extend_restrict_behavioral_of_cover
    [DecidableEq ι]
    [∀ i, DecidableEq (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (b : BehavioralProfile I) :
    D.runDist n
      (I.extendRestrictedBehavioralProfile H
        (I.restrictBehavioralProfile H b)) =
      D.runDist n b := by
  exact runDist_eq_of_agreeOnCover (I := I) (D := D) hCover hn
    (I.extendRestrictedBehavioralProfile H (I.restrictBehavioralProfile H b)) b
    (fun i v hv => I.extendRestrictedBehavioralProfile_apply_mem H
      (I.restrictBehavioralProfile H b) i v hv)

/-- Under a valid cover, extending a restricted pure profile obtained by
restriction from `π` does not change `n`-step pure-run distributions. -/
theorem runDistPure_eq_extend_restrict_pure_of_cover
    [DecidableEq ι]
    [∀ i, DecidableEq (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k n : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (hn : n ≤ k)
    (π : PureProfile I) :
    D.runDistPure n
      (I.extendRestrictedPureProfile H (I.restrictPureProfile H π)) =
      D.runDistPure n π := by
  exact runDistPure_eq_of_agreeOnCover (I := I) (D := D) hCover hn
    (I.extendRestrictedPureProfile H (I.restrictPureProfile H π)) π
    (fun i v hv => I.extendRestrictedPureProfile_apply_mem H
      (I.restrictPureProfile H π) i v hv)

/-- Outcome-level behavioral corollary of
`runDist_eq_extend_restrict_behavioral_of_cover`. -/
theorem evalBehavioral_eq_extend_restrict_behavioral_of_cover
    [DecidableEq ι]
    [∀ i, DecidableEq (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (b : BehavioralProfile I) :
    D.evalBehavioral k
      (I.extendRestrictedBehavioralProfile H
        (I.restrictBehavioralProfile H b)) =
      D.evalBehavioral k b := by
  unfold Execution.Dynamics.evalBehavioral
  exact congrArg
    (fun ν => Math.ProbabilityMassFunction.pushforward ν I.outcomeOfStates)
    (runDist_eq_extend_restrict_behavioral_of_cover
      (I := I) (D := D) hCover le_rfl b)

/-- Outcome-level pure-run corollary of
`runDistPure_eq_extend_restrict_pure_of_cover`. -/
theorem evalPure_eq_extend_restrict_pure_of_cover
    [DecidableEq ι]
    [∀ i, DecidableEq (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    {H : ∀ i, Finset (I.LocalTrace i)} {k : Nat}
    (hCover : I.CoversHistoriesUpTo H k)
    (π : PureProfile I) :
    D.evalPure k
      (I.extendRestrictedPureProfile H (I.restrictPureProfile H π)) =
      D.evalPure k π := by
  unfold Execution.Dynamics.evalPure
  exact congrArg
    (fun ν => Math.ProbabilityMassFunction.pushforward ν I.outcomeOfStates)
    (runDistPure_eq_extend_restrict_pure_of_cover
      (I := I) (D := D) hCover le_rfl π)

end InfoModel
end GameTheory
