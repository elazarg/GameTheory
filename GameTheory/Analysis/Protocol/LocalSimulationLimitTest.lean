module

public import GameTheory.Analysis.Protocol.LocalSimulationLimit
public import GameTheory.Analysis.Protocol.SequentialExistenceTest
public import GameTheory.Analysis.Protocol.WellFoundedTerminalEquilibriumTest

@[expose] public section

noncomputable section

namespace GameTheory.Tests.LocalSimulationLimit

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability Filter
open GameTheory.Tests.WellFoundedTerminalGate

local notation "N" => GameTheory.Tests.SequentialExistence.information
local notation "T" => GameTheory.Tests.SequentialExistence.execution
local notation "targetCertificate" => GameTheory.Tests.SequentialExistence.game.wellFoundedHistories
local notation "targetPayoff" => GameTheory.Tests.SequentialExistence.payoff
local notation "targetAntichain" => GameTheory.Tests.SequentialExistence.antichain

/-- An unbounded-duration source certifies an unequal-depth target through
caller-supplied approximate gain mixtures. No finite source-history instance,
source clock, or common target decision depth is available. -/
theorem unbounded_source_unequal_depth_target :
    (¬ ∃ horizon, execution.BoundedHorizon horizon) ∧
      (¬ ∃ depth, InformationSite.CommonDepth N GameTheory.Tests.SequentialExistence.actingSite
        depth) ∧
        ∃ source : information.BehavioralAssessment,
          ∀ (sequence : ℕ → GameTheory.Tests.SequentialExistence.information.BehavioralAssessment)
            (target : GameTheory.Tests.SequentialExistence.information.BehavioralAssessment),
            BehavioralAssessmentConvergesPointwise sequence target →
            target.IsSequentiallyConsistent targetAntichain →
            (∀ n who (site : GameTheory.Tests.SequentialExistence.information.InformationSite who)
              (law : PMF (GameTheory.Tests.SequentialExistence.information.Choice who site.1)),
              ∃ mixture : PMF (information.AssessmentDeviation who),
                ((sequence n).continuationContext targetCertificate site (targetPayoff who)).value
                    (((sequence n).strategy who).withLaw site.1 law) -
                  ((sequence n).continuationContext targetCertificate site (targetPayoff who)).value
                    ((sequence n).strategy who) ≤
                  expect mixture (fun deviation =>
                    (source.continuationContext wellFounded.wellFoundedHistories deviation.1
                        (terminalPayoff who)).value deviation.2 -
                      (source.continuationContext wellFounded.wellFoundedHistories deviation.1
                        (terminalPayoff who)).value (source.strategy who)) + trembleWeight n) →
            target.IsSequentialEquilibrium targetAntichain targetCertificate targetPayoff := by
  classical
  let _ : Fintype GameTheory.Tests.SequentialExistence.execution.History :=
    GameTheory.Tests.SequentialExistence.execution.historyFintype
    GameTheory.Tests.SequentialExistence.treeShaped
  have : ∀ who : Unit, Finite (information.InformationSite who) := by
    intro who
    cases who
    infer_instance
  have : ∀ who (site : information.InformationSite who),
      Finite (information.Choice who site.1) := by
    intro who site
    infer_instance
  obtain ⟨source, rational, _⟩ := exists_sequential_equilibrium
  refine ⟨no_boundedHorizon, GameTheory.Tests.SequentialExistence.no_commonDepth, source, ?_⟩
  intro sequence target converges consistent comparisons
  apply sequentialEquilibrium_of_copied_comparisons_limit
    wellFounded.wellFoundedHistories targetCertificate
    (GameTheory.Tests.SequentialExistence.information.decisionRecall_of_perfectRecall
      GameTheory.Tests.SequentialExistence.perfectRecall)
    terminalPayoff targetPayoff (fun _ => 1) (fun _ => by norm_num) terminalPayoff_bound
    (behavioralAssessmentConvergesPointwise_const source) rational converges
    (fun _ _ => True) consistent (fun n _ _ => trembleWeight n)
    (fun _ _ _ => trembleWeight_tendsto_zero)
    (fun n who site _ law => Or.inr (comparisons n who site law))
    (fun _ _ impossible => False.elim (impossible trivial))

/-- A shrinking perturbation of a point mass cannot converge to a different
law, even with a natural-number outcome carrier and arbitrary noise. -/
theorem infinite_outcome_limit_matching (noise : PMF ℕ) (target : PMF ℕ)
    (converges : PMFConvergesPointwise
      (fun n => mix (trembleWeight n) (trembleWeight_pos n).le (trembleWeight_le_one n)
        noise (PMF.pure 0)) target) : target = PMF.pure 0 := by
  have pureLimit := pmfConvergesPointwise_mix_zero trembleWeight
    (fun n => (trembleWeight_pos n).le) trembleWeight_le_one trembleWeight_tendsto_zero
    noise (PMF.pure 0)
  exact converges.eq_of_statisticalDistance_le (pmfConvergesPointwise_const (PMF.pure 0))
    (fun n => statisticalDistance
      (mix (trembleWeight n) (trembleWeight_pos n).le (trembleWeight_le_one n) noise (PMF.pure 0))
      (PMF.pure 0)) pureLimit.statisticalDistance_tendsto (fun _ => le_rfl)

/-- Globally unbounded values outside the support cannot affect an expectation bound. -/
theorem support_local_unbounded_payoff :
    |expect (PMF.pure (0 : ℕ)) (fun n => (n : ℝ))| ≤ 0 := by
  apply expect_abs_le_of_bounded_on_support
  intro n supported
  have same : n = 0 := by simpa only [PMF.mem_support_pure_iff] using supported
  subst n
  simp

end GameTheory.Tests.LocalSimulationLimit
