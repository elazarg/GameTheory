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

/-- Action-explicit one-step kernel from a current state under behavioral
profile `σ`. The sampled result retains the public label, the realized joint
action, and the successor state. -/
noncomputable def stepActionStateDist
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I) (ss : List M.State) :
    PMF ((M.Label × (∀ i, Option (M.Act i))) × M.State) :=
  let s := (ss.getLast?).getD M.init
  (D.labelKernel s).bind fun ℓ =>
    (jointActionDist (I := I) σ ss).bind fun a =>
      Math.ProbabilityMassFunction.pushforward (D.nextState ℓ a s) (fun t => ((ℓ, a), t))

/-- Forgetting the realized joint action from `stepActionStateDist` recovers the
ordinary one-step kernel `stepDist`. -/
theorem stepDist_eq_pushforward_stepActionStateDist
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I) (ss : List M.State) :
    Math.ProbabilityMassFunction.pushforward
      (stepActionStateDist (I := I) D σ ss)
      (fun x => (x.1.1, x.2)) =
    D.stepDist σ ss := by
  classical
  ext y
  simp [stepActionStateDist, Execution.Dynamics.stepDist,
    Math.ProbabilityMassFunction.pushforward, PMF.bind_bind]

private theorem pushforward_fixedPair_apply_same
    {α β : Type*}
    (ν : PMF α) (b : β) (a : α) :
    Math.ProbabilityMassFunction.pushforward ν (fun x => (b, x)) (b, a) = ν a := by
  simp only [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply, PMF.pure_apply,
    Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, eq_comm]
  rw [tsum_eq_single a]
  · simp
  · intro a' ha'
    by_cases hEq : (b, a) = (b, a')
    · have : a = a' := by simpa using congrArg Prod.snd hEq
      exact False.elim (ha' this.symm)
    · simp [hEq]

private theorem pushforward_fixedPair_apply_ne
    {α β : Type*}
    (ν : PMF α) (b b' : β) (a : α) (h : b' ≠ b) :
    Math.ProbabilityMassFunction.pushforward ν (fun x => (b', x)) (b, a) = 0 := by
  simp only [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply, PMF.pure_apply,
    Prod.mk.injEq, mul_ite, mul_one, mul_zero, eq_comm]
  symm
  rw [ENNReal.tsum_eq_zero]
  intro a'
  have hEq : (b, a) ≠ (b', a') := by
    intro hpair
    exact h ((by simpa using (congrArg Prod.fst hpair).symm) : b' = b)
  simp [hEq]

private theorem stepActionStateDist_apply_point
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I) (ss : List M.State)
    (lab : M.Label) (a : ∀ i, Option (M.Act i)) (t : M.State) :
    let s := (ss.getLast?).getD M.init
    (D.stepActionStateDist σ ss) ((lab, a), t) =
      (D.labelKernel s) lab * (jointActionDist (I := I) σ ss) a * D.nextState lab a s t := by
  classical
  let s := (ss.getLast?).getD M.init
  rw [Execution.Dynamics.stepActionStateDist]
  simp only [PMF.bind_apply]
  have hinner :
      ∀ lab' : M.Label,
        ((jointActionDist (I := I) σ ss).bind fun a' =>
            Math.ProbabilityMassFunction.pushforward
              (D.nextState lab' a' s) (fun u => ((lab', a'), u))) ((lab, a), t) =
          if lab' = lab then
            (jointActionDist (I := I) σ ss) a * D.nextState lab a s t
          else 0 := by
    intro lab'
    by_cases hEq : lab' = lab
    · rw [hEq]
      simp only [PMF.bind_apply]
      rw [tsum_eq_single a]
      · simpa [mul_assoc] using
          congrArg
            (fun z => (jointActionDist (I := I) σ ss) a * z)
            (pushforward_fixedPair_apply_same
              (ν := D.nextState lab a s) (b := (lab, a)) (a := t))
      · intro a' ha'
        have hPair : (lab, a') ≠ (lab, a) := by
          intro hpair
          exact ha' (by simpa using congrArg Prod.snd hpair)
        have hzero :=
          pushforward_fixedPair_apply_ne
            (ν := D.nextState lab a' s) (b := (lab, a)) (b' := (lab, a')) (a := t) hPair
        simp [hzero]
    · rw [show
        (if lab' = lab then
            (jointActionDist (I := I) σ ss) a * D.nextState lab a s t
          else 0) = 0 by
        simp [hEq]]
      simp only [PMF.bind_apply]
      rw [ENNReal.tsum_eq_zero]
      intro a'
      have hPair : (lab', a') ≠ (lab, a) := by
        intro hpair
        exact hEq (by simpa using congrArg Prod.fst hpair)
      have hzero :=
        pushforward_fixedPair_apply_ne
          (ν := D.nextState lab' a' s) (b := (lab, a)) (b' := (lab', a')) (a := t) hPair
      simp [hzero]
  rw [tsum_eq_single lab]
  · have hinnerLab := hinner lab
    simp only [PMF.bind_apply] at hinnerLab
    rw [hinnerLab]
    simp [mul_assoc, s]
  · intro lab' hne
    have hinnerLab' := hinner lab'
    simp only [PMF.bind_apply] at hinnerLab'
    rw [hinnerLab']
    simp [hne]

/-- A positive explicit-step mass certifies a machine step with the sampled
label, action profile, and successor state. -/
theorem stepActionStateDist_point_nonzero_sound
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I) (ss : List M.State)
    (lab : M.Label) (a : ∀ i, Option (M.Act i)) (t : M.State)
    (hstep : (D.stepActionStateDist σ ss) ((lab, a), t) ≠ 0) :
    let s := (ss.getLast?).getD M.init
    M.step lab a s t := by
  let s := (ss.getLast?).getD M.init
  have hform := stepActionStateDist_apply_point (I := I) (D := D) σ ss lab a t
  have hprod :
      (D.labelKernel s) lab * (jointActionDist (I := I) σ ss) a * D.nextState lab a s t ≠ 0 := by
    simpa [hform] using hstep
  have hnext : D.nextState lab a s t ≠ 0 := by
    intro hzero
    apply hprod
    simp [hzero]
  exact D.nextState_sound lab a s t hnext

omit [Fintype ι] in
private theorem pushforward_append_action_nonzero_exists
    (μ : PMF ((M.Label × (∀ i, Option (M.Act i))) × M.State))
    (ha : List (M.Label × (∀ i, Option (M.Act i)))) (ss : List M.State)
    (hs : List (M.Label × (∀ i, Option (M.Act i))) × List M.State)
    (hpush : (Math.ProbabilityMassFunction.pushforward μ
      (fun x => (ha ++ [x.1], ss ++ [x.2]))) hs ≠ 0) :
    ∃ la t, hs = (ha ++ [la], ss ++ [t]) ∧ μ (la, t) ≠ 0 := by
  classical
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply] at hpush
  by_contra hnone
  push_neg at hnone
  apply hpush
  rw [ENNReal.tsum_eq_zero]
  intro x
  rcases x with ⟨la, t⟩
  by_cases heq : hs = (ha ++ [la], ss ++ [t])
  · have hμ : μ (la, t) = 0 := hnone la t heq
    simp [PMF.pure_apply, heq, hμ]
  · simp [PMF.pure_apply, heq]

/-- Prefix-parametrized bounded execution that records explicit joint actions
alongside public labels and state traces. -/
noncomputable def runActionStateDistFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I)
    (hs0 : List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :
    PMF (List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :=
  Nat.rec (PMF.pure hs0)
    (fun _ rec =>
      rec.bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (stepActionStateDist (I := I) D σ hs.2)
          (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))))
    n

/-- Bounded execution from the initial history, recording explicit joint
actions. -/
noncomputable def runActionStateDist
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I) :
    PMF (List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :=
  runActionStateDistFrom D n σ ([], [M.init])

/-- Pure-profile continuation from an explicit action/state prefix. -/
noncomputable def runActionStateDistPureFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (π : PureProfile I)
    (hs0 : List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :
    PMF (List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :=
  runActionStateDistFrom D n (pureToBehavioral I π) hs0

/-- Pure-profile action/state execution from the initial history. -/
noncomputable def runActionStateDistPure
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (π : PureProfile I) :
    PMF (List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :=
  runActionStateDistPureFrom D n π ([], [M.init])

/-- Base case for `runActionStateDistFrom`. -/
@[simp] theorem runActionStateDistFrom_zero
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I)
    (hs0 : List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :
    runActionStateDistFrom D 0 σ hs0 = PMF.pure hs0 := rfl

/-- One-step unfolding equation for action-explicit continuation execution. -/
@[simp] theorem runActionStateDistFrom_succ
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I)
    (hs0 : List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :
    runActionStateDistFrom D (n + 1) σ hs0 =
      (runActionStateDistFrom D n σ hs0).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (stepActionStateDist (I := I) D σ hs.2)
          (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) := rfl

/-- Ordinary action-explicit bounded execution is the initial-history
specialization of `runActionStateDistFrom`. -/
theorem runActionStateDist_eq_runActionStateDistFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I) :
    runActionStateDist D n σ = runActionStateDistFrom D n σ ([], [M.init]) := rfl

/-- Pure action-explicit bounded execution is the initial-history specialization
of `runActionStateDistPureFrom`. -/
theorem runActionStateDistPure_eq_runActionStateDistPureFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (π : PureProfile I) :
    runActionStateDistPure D n π = runActionStateDistPureFrom D n π ([], [M.init]) := rfl


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

/-- In the support of `runDistFrom D n σ hs₀`, the resulting state trace has
length `hs₀.2.length + n`. This is the continuation analogue of
`runDist_support_stateLength`. -/
theorem runDistFrom_support_stateLength
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I)
    (hs₀ hs : List M.Label × List M.State) :
    runDistFrom D n σ hs₀ hs ≠ 0 → hs.2.length = hs₀.2.length + n := by
  induction n generalizing hs with
  | zero =>
      intro h
      have hmem : hs ∈ (PMF.pure hs₀ : PMF _).support := by
        rwa [runDistFrom_zero (D := D)] at h
      rw [PMF.support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      simp
  | succ n ih =>
      intro h
      rw [runDistFrom_succ (D := D), PMF.bind_apply] at h
      by_contra hlen
      apply h
      rw [ENNReal.tsum_eq_zero]
      intro hs'
      by_cases hhs' : runDistFrom D n σ hs₀ hs' = 0
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

/-- Forgetting explicit joint actions from an action/state continuation run
recovers the ordinary continuation run. -/
theorem runDistFrom_eq_pushforward_runActionStateDistFrom
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (n : Nat) (σ : BehavioralProfile I)
    (hs0 : List (M.Label × (∀ i, Option (M.Act i))) × List M.State) :
    Math.ProbabilityMassFunction.pushforward
      (runActionStateDistFrom D n σ hs0)
      (fun hs => (hs.1.map Prod.fst, hs.2)) =
    runDistFrom D n σ (hs0.1.map Prod.fst, hs0.2) := by
  induction n generalizing hs0 with
  | zero =>
      simp [runActionStateDistFrom, runDistFrom, Math.ProbabilityMassFunction.pushforward_pure]
  | succ n ih =>
      rw [runActionStateDistFrom_succ (D := D), runDistFrom_succ (D := D)]
      calc
        Math.ProbabilityMassFunction.pushforward
          ((runActionStateDistFrom D n σ hs0).bind
            (fun hs =>
              Math.ProbabilityMassFunction.pushforward
                (stepActionStateDist (I := I) D σ hs.2)
                (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))))
          (fun hs => (hs.1.map Prod.fst, hs.2))
            =
          (runActionStateDistFrom D n σ hs0).bind
            (fun hs =>
              Math.ProbabilityMassFunction.pushforward
                (stepDist (I := I) D σ hs.2)
                (fun x => (hs.1.map Prod.fst ++ [x.1], hs.2 ++ [x.2]))) := by
                  rw [Math.ProbabilityMassFunction.pushforward_bind]
                  apply Math.ProbabilityMassFunction.bind_congr_on_support
                  intro hs _
                  calc
                    Math.ProbabilityMassFunction.pushforward
                      (Math.ProbabilityMassFunction.pushforward
                        (stepActionStateDist (I := I) D σ hs.2)
                        (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2])))
                      (fun hs' => (hs'.1.map Prod.fst, hs'.2))
                        =
                      Math.ProbabilityMassFunction.pushforward
                        (stepActionStateDist (I := I) D σ hs.2)
                        (fun x => ((hs.1 ++ [x.1]).map Prod.fst, hs.2 ++ [x.2])) := by
                          rw [Math.ProbabilityMassFunction.pushforward_comp]
                          rfl
                    _ =
                      Math.ProbabilityMassFunction.pushforward
                        (stepActionStateDist (I := I) D σ hs.2)
                        (fun x => (hs.1.map Prod.fst ++ [x.1.1], hs.2 ++ [x.2])) := by
                          simp [List.map_append]
                    _ =
                      Math.ProbabilityMassFunction.pushforward
                        (stepDist (I := I) D σ hs.2)
                        (fun x => (hs.1.map Prod.fst ++ [x.1], hs.2 ++ [x.2])) := by
                          calc
                            Math.ProbabilityMassFunction.pushforward
                              (stepActionStateDist (I := I) D σ hs.2)
                              (fun x => (hs.1.map Prod.fst ++ [x.1.1], hs.2 ++ [x.2]))
                                =
                              Math.ProbabilityMassFunction.pushforward
                                (Math.ProbabilityMassFunction.pushforward
                                  (stepActionStateDist (I := I) D σ hs.2)
                                  (fun x => (x.1.1, x.2)))
                                (fun x => (hs.1.map Prod.fst ++ [x.1], hs.2 ++ [x.2])) := by
                                  rw [Math.ProbabilityMassFunction.pushforward_comp]
                                  rfl
                            _ =
                              Math.ProbabilityMassFunction.pushforward
                                (stepDist (I := I) D σ hs.2)
                                (fun x => (hs.1.map Prod.fst ++ [x.1], hs.2 ++ [x.2])) := by
                                  rw [stepDist_eq_pushforward_stepActionStateDist
                                        (I := I) (D := D) σ hs.2]
        _ =
          (Math.ProbabilityMassFunction.pushforward
            (runActionStateDistFrom D n σ hs0)
            (fun hs => (hs.1.map Prod.fst, hs.2))).bind
              (fun hs =>
                Math.ProbabilityMassFunction.pushforward
                  (stepDist (I := I) D σ hs.2)
                  (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) := by
                    simp [Math.ProbabilityMassFunction.pushforward, PMF.bind_bind]
        _ = (runDistFrom D n σ (hs0.1.map Prod.fst, hs0.2)).bind
              (fun hs =>
                Math.ProbabilityMassFunction.pushforward
                  (stepDist (I := I) D σ hs.2)
                  (fun x => (hs.1 ++ [x.1], hs.2 ++ [x.2]))) := by
                    rw [ih]

private theorem exists_prev_of_runActionStateDistFrom_succ_ne_zero
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I)
    (n : Nat)
    (hs0 hs : List (M.Label × (∀ i, Option (M.Act i))) × List M.State)
    (hhs : runActionStateDistFrom D (n + 1) σ hs0 hs ≠ 0) :
    ∃ hsPrev,
      runActionStateDistFrom D n σ hs0 hsPrev ≠ 0 ∧
      (Math.ProbabilityMassFunction.pushforward
        (stepActionStateDist (I := I) D σ hsPrev.2)
        (fun x => (hsPrev.1 ++ [x.1], hsPrev.2 ++ [x.2]))) hs ≠ 0 := by
  classical
  rw [runActionStateDistFrom_succ (D := D), PMF.bind_apply] at hhs
  by_contra hnone
  push_neg at hnone
  apply hhs
  rw [ENNReal.tsum_eq_zero]
  intro hsPrev
  by_cases hprev : runActionStateDistFrom D n σ hs0 hsPrev = 0
  · simp [hprev]
  · simp [hnone hsPrev hprev]

/-- Any history in the support of an action-explicit continuation run extends
the starting prefix by a genuine reachable action trace. -/
theorem runActionStateDistFrom_support_reachActionTrace
    [∀ i, Fintype (Option (M.Act i))]
    (D : Dynamics I)
    (σ : BehavioralProfile I)
    {ha0 : List (M.Label × (∀ i, Option (M.Act i)))}
    {ss0 : List M.State}
    (hr0 : InfoModel.ReachActionTrace M ha0 ss0)
    (n : Nat)
    {hs : List (M.Label × (∀ i, Option (M.Act i))) × List M.State}
    (hhs : runActionStateDistFrom D n σ (ha0, ss0) hs ≠ 0) :
    InfoModel.ReachActionTrace M hs.1 hs.2 := by
  induction n generalizing hs with
  | zero =>
      have hmem : hs ∈ (PMF.pure (ha0, ss0) : PMF _).support := by
        rwa [runActionStateDistFrom_zero (D := D)] at hhs
      rw [PMF.support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact hr0
  | succ n ih =>
      obtain ⟨hsPrev, hprev, hpush⟩ :=
        exists_prev_of_runActionStateDistFrom_succ_ne_zero
          (I := I) (D := D) σ n (ha0, ss0) hs hhs
      have hrPrev : InfoModel.ReachActionTrace M hsPrev.1 hsPrev.2 := ih hprev
      obtain ⟨la, t, hEq, hstep⟩ :=
        pushforward_append_action_nonzero_exists
          (μ := stepActionStateDist (I := I) D σ hsPrev.2)
          hsPrev.1 hsPrev.2 hs hpush
      subst hEq
      have hnonempty : hsPrev.2 ≠ [] := by
        intro hnil
        have hlen := InfoModel.ReachActionTrace.length_states_eq_succ_actions hrPrev
        simp [hnil] at hlen
      let s : M.State := hsPrev.2.getLast hnonempty
      have hsLast : hsPrev.2.getLast? = some s := by
        simpa [s] using List.getLast?_eq_getLast_of_ne_nil hnonempty
      have hrel : M.step la.1 la.2 s t := by
        have hrel' :=
          stepActionStateDist_point_nonzero_sound
            (I := I) (D := D) σ hsPrev.2 la.1 la.2 t hstep
        simpa [s, hsLast] using hrel'
      exact InfoModel.ReachActionTrace.snoc hrPrev hsLast hrel

end Dynamics
end Execution

end GameTheory
