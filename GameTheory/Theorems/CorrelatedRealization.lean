import GameTheory.Model.SemanticForm
import Math.ParameterizedChain

/-! # Correlated realization theorem

For **any** joint distribution `ν : PMF (PureProfile I)` (not necessarily a product),
there exists a **mediator** — a history-dependent correlated action recommendation —
producing the same outcome distribution.  No perfect-recall assumption is needed.

The mediator sees the full state trace and recommends correlated joint actions,
which the dynamics then converts to state transitions.  This separates the
strategic choice (actions) from the physical transition (dynamics).

Decentralizing the mediator into independent per-player behavioral strategies
requires perfect recall (classical Kuhn = correlated realization + decentralization).
-/

set_option autoImplicit false

namespace GameTheory

open Math.ProbabilityMassFunction Math.ParameterizedChain Execution Execution.Dynamics

variable {ι : Type} {M : LSM ι} {I : InfoModel M}

section

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- The parameterized step function extracted from game dynamics:
maps a pure profile and a state trace to a next-state distribution. -/
noncomputable def pureStep (D : Dynamics I) (π : PureProfile I)
    (ss : List M.State) : PMF M.State :=
  D.stepDist (pureToBehavioral I π) ss

/-- `runDistPure` is definitionally equal to `pureRun` applied to `pureStep`. -/
theorem runDistPure_eq_pureRun (D : Dynamics I) (k : Nat) (π : PureProfile I) :
    D.runDistPure k π = pureRun (pureStep D) M.init k π := rfl

/-- Mediator construction: condition `ν` on the probability of reaching
the current state trace, then extract correlated joint actions. -/
noncomputable def mixedToMediator [Fintype (PureProfile I)]
    (ν : PMF (PureProfile I)) (D : Dynamics I)
    (n : Nat) (ss : List M.State) : PMF (JointAction M) :=
  (reweightPMF ν (fun π => pureRun (pureStep D) M.init n π ss)).bind
    (fun π => jointActionDist (pureToBehavioral I π) ss)

/-- The mediator's action recommendations composed with dynamics equal
the `condStep` from `ParameterizedChain` (monad associativity). -/
theorem mediator_step_eq_condStep [Fintype (PureProfile I)]
    (ν : PMF (PureProfile I)) (D : Dynamics I) (n : Nat) (ss : List M.State) :
    (mixedToMediator ν D n ss).bind
      (fun a => D.nextState a ((ss.getLast?).getD M.init)) =
      condStep ν (pureStep D) M.init n ss := by
  unfold mixedToMediator condStep pureStep stepDist
  rw [PMF.bind_bind]

variable [∀ i, Fintype (I.LocalTrace i)]

set_option linter.unusedFintypeInType false in
/-- **Correlated realization theorem**: for any joint distribution `ν` over
pure profiles, there exists a mediator `m` — producing correlated action
recommendations from the state trace at each step — such that the run under `m`
(with actions converted to state transitions by the dynamics) yields the same
outcome distribution as the `ν`-averaged pure runs.

No perfect recall is needed. -/
theorem correlated_realization (D : Dynamics I) (ν : PMF (PureProfile I)) (k : Nat) :
    ∃ m : Nat → List M.State → PMF (JointAction M),
      pushforward
        (seqRun (fun n ss =>
          (m n ss).bind (fun a => D.nextState a ((ss.getLast?).getD M.init)))
          M.init k)
        I.outcomeOfStates =
        ν.bind (fun π => D.evalPure k π) := by
  classical
  refine ⟨mixedToMediator ν D, ?_⟩
  have hstep : (fun n ss =>
      (mixedToMediator ν D n ss).bind
        (fun a => D.nextState a ((ss.getLast?).getD M.init))) =
      condStep ν (pureStep D) M.init := by
    funext n ss
    exact mediator_step_eq_condStep ν D n ss
  rw [hstep, condRun_eq_mixedRun, pushforward_bind]
  rfl

end

end GameTheory
