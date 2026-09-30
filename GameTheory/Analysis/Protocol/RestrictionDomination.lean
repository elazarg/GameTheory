/-
# Execution retains almost all mass of the smaller protocol under rare trembles

When retained decisions mix the embedded law with a small reference weight,
their independent product keeps a common fraction of every embedded joint
choice. The one-step square and kernel iteration carry this bound to behavioral
play of any length. Play after a new action is unrestricted.
-/

import GameTheory.Math.Probability.Domination
import GameTheory.Protocol.RestrictionExecution
import GameTheory.Protocol.RestrictionProfile

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {ι : Type*} [Fintype ι] {E T : ExecutionProtocol ι}
  {M : InformationModel E} {N : InformationModel T}

/-- One behavioral step draws the local choices and takes one local step. -/
theorem runBehavioralFrom_one_localStep (profile : (i : ι) → M.BehavioralPolicy i)
    (history : E.History) :
    M.runBehavioralFrom profile 1 history =
      (independentProduct fun who => profile who (M.infoOf who history.trace)).bind
        (M.localStep history) := by
  rw [M.runBehavioralFrom_succ_localStep profile 0]
  exact PMF.bind_pure _

/-- Behavioral play of a given length iterates single steps. -/
theorem runBehavioralFrom_eq_iterate (profile : (i : ι) → M.BehavioralPolicy i)
    (fuel : ℕ) (history : E.History) :
    M.runBehavioralFrom profile fuel history =
      (fun law => law.bind (M.runBehavioralFrom profile 1))^[fuel] (PMF.pure history) := by
  induction fuel with
  | zero => rfl
  | succ fuel induction =>
      rw [M.runBehavioralFrom_add profile fuel 1 history, induction,
        Function.iterate_succ_apply']

namespace ActionRestriction

variable (restriction : M.ActionRestriction N)

/-- One step of a perturbing profile keeps at least the untrembled fraction of
every embedded step of the smaller protocol. -/
theorem perturbed_step_domination
    (source : (i : ι) → M.BehavioralPolicy i)
    (reference target : (i : ι) → N.BehavioralPolicy i)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (perturbs : restriction.PerturbsProfile source reference target epsilon nonnegative small)
    (original : E.History) (next : T.History) :
    (1 - epsilon) ^ Fintype.card ι *
        (((M.runBehavioralFrom source 1 original).map restriction.history) next).toReal ≤
      ((N.runBehavioralFrom target 1 (restriction.history original)) next).toReal := by
  classical
  by_cases stopped : E.terminal original.state
  · rw [M.runBehavioralFrom_of_terminal source _ stopped,
      N.runBehavioralFrom_of_terminal target _ ((restriction.terminal original).mpr stopped),
      PMF.pure_map]
    have factor : (1 - epsilon) ^ Fintype.card ι ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr small) (by linarith)
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg factor
  · let legal := restriction.extendProfile source reference
    have agrees := restriction.extendProfile_extends source reference
    rw [restriction.runFrom_law source legal agrees 1 original,
      runBehavioralFrom_one_localStep, runBehavioralFrom_one_localStep]
    have good := funext
      (restriction.extends_at_history source legal agrees original stopped)
    have bad := funext
      (restriction.perturbs_at_history source reference target epsilon nonnegative small
        perturbs original stopped)
    rw [good, bad]
    exact prob_pi_mix_bind_lower _ _ epsilon nonnegative small
      (N.localStep (restriction.history original)) next

/-- Behavioral play of every length under a perturbing profile dominates the
embedded play of the smaller protocol by the product of the untrembled
fractions. -/
theorem perturbed_run_domination
    (source : (i : ι) → M.BehavioralPolicy i)
    (reference target : (i : ι) → N.BehavioralPolicy i)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (perturbs : restriction.PerturbsProfile source reference target epsilon nonnegative small)
    (fuel : ℕ) (next : T.History) :
    (1 - epsilon) ^ (Fintype.card ι * fuel) *
        (((M.runBehavioral source fuel).map restriction.history) next).toReal ≤
      ((N.runBehavioral target fuel) next).toReal := by
  have bound := iterate_prob_domination (PMF.pure E.initHistory)
    restriction.history (M.runBehavioralFrom source 1) (N.runBehavioralFrom target 1)
    ((1 - epsilon) ^ Fintype.card ι) (pow_nonneg (sub_nonneg.mpr small) _)
    (restriction.perturbed_step_domination source reference target epsilon nonnegative small
      perturbs) fuel next
  simpa only [PMF.pure_map, restriction.initial, ← runBehavioralFrom_eq_iterate,
    ← pow_mul, runBehavioral] using bound

end ActionRestriction

end GameTheory.Protocol.InformationModel
