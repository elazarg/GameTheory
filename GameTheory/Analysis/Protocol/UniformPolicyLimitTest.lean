module

public import GameTheory.Analysis.Protocol.UniformPolicyLimit
public import GameTheory.Analysis.Protocol.WellFoundedTerminalEquilibriumTest

@[expose] public section

noncomputable section

namespace GameTheory.Tests.UniformPolicyLimit

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability Filter
open GameTheory.Tests.WellFoundedTerminalGate

/-- Every sequence converging to an optimal countdown assessment has uniformly
vanishing whole-policy regret, although play has no uniform horizon and raw
information states are real numbers. No rationality of the sequence is needed. -/
theorem unbounded_countdown_uniform_regret :
    (¬ ∃ horizon, execution.BoundedHorizon horizon) ∧
      ∃ target : information.BehavioralAssessment,
        ∀ sequence : ℕ → information.BehavioralAssessment,
          BehavioralAssessmentConvergesPointwise sequence target →
            ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
              ∀ n (site : information.InformationSite ())
                (alternative : information.BehavioralPolicy ()),
                ((sequence n).continuationContext wellFounded.wellFoundedHistories site
                    (terminalPayoff ())).value alternative -
                  ((sequence n).continuationContext wellFounded.wellFoundedHistories site
                    (terminalPayoff ())).value ((sequence n).strategy ()) ≤ error n := by
  obtain ⟨target, rational, _⟩ := exists_sequential_equilibrium
  refine ⟨no_boundedHorizon, target, ?_⟩
  intro sequence converges
  exact converges.exists_uniform_terminal_policy_gain_bound ()
    wellFounded.wellFoundedHistories (terminalPayoff ()) 1 (by norm_num)
    (terminalPayoff_bound ()) (rational ())

end GameTheory.Tests.UniformPolicyLimit
