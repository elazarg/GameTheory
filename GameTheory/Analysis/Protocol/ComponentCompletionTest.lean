import GameTheory.Analysis.Protocol.ComponentCompletion
import GameTheory.Analysis.Protocol.SequentialExistenceTest
noncomputable section
namespace GameTheory.Tests.ProtocolComponentCompletion
open GameTheory GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability Filter
open GameTheory.Tests.SequentialExistence

/-- Full-menu trembling components produce a sequential equilibrium even at unequal-depth sites. -/
theorem unequal_depth_equilibrium_from_components :
    (¬ ∃ depth, InformationSite.CommonDepth information actingSite depth) ∧
      ∃ limit : information.BehavioralAssessment,
        limit.IsSequentialEquilibrium antichain game.wellFoundedHistories GameTheory.Tests.SequentialExistence.payoff := by
  classical
  let _ : Fintype execution.History := execution.historyFintype treeShaped
  let F := information.agentForm fallback game.wellFoundedHistories
  let _ (agent : information.InformationAgent information.playedInformation) : Fintype (F.sig.Strategy agent) :=
    @Fintype.ofFinite _ (information.finite_choice_of_played agent.2.2)
  have inhabited (agent : information.InformationAgent information.playedInformation) : Nonempty (F.sig.Strategy agent) :=
    information.nonempty_choice_of_played agent.2.2
  let weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < weight n := by
    dsimp only [weight]
    positivity
  have small (n : ℕ) : weight n ≤ 1 := by
    dsimp only [weight]
    apply (div_le_one (by positivity : (0 : ℝ) < n + 2)).mpr
    have nonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) := by
    have bound := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    convert bound using 1
    funext n
    simp [weight, Nat.cast_add]
    ring
  let reference (agent : information.InformationAgent information.playedInformation) : PMF (F.sig.Strategy agent) :=
    PMF.uniformOfFintype _
  let component (n : ℕ) (agent : information.InformationAgent information.playedInformation)
      (part : F.sig.Strategy agent) := mix (weight n) (positive n).le (small n) (reference agent) (PMF.pure part)
  have full : ∀ n agent part, FullSupport (component n agent part) := by
    intro n agent part choice
    exact mem_support_mix_left _ _ _ (positive n)
      (PMF.mem_support_uniformOfFintype choice)
  let decisionRecallCertificate := information.decisionRecall_of_perfectRecall perfectRecall
  obtain ⟨weights, sequence, limit, index, played, mixed, bayes, increasing, converges,
      consistent, stepOptimal, limitFacts⟩ :=
    information.exists_consistent_component_completion decisionRecallCertificate fallback
      game.wellFoundedHistories GameTheory.Tests.SequentialExistence.payoff component full
  refine ⟨no_commonDepth, limit, ?_⟩
  apply (BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal information
    decisionRecallCertificate limit game.wellFoundedHistories GameTheory.Tests.SequentialExistence.payoff).mpr
  refine ⟨consistent, ?_⟩
  intro who site law
  have componentConverges (part : F.sig.Strategy (information.agentAt site)) :
      PMFConvergesPointwise (fun n => component n (information.agentAt site) part) (PMF.pure part) :=
    pmfConvergesPointwise_mix_zero weight (fun n => (positive n).le) small vanishes _ _
  obtain ⟨_, optimal⟩ := limitFacts who site (fun part => PMF.pure part) componentConverges
  have bound := optimal law
  exact ((congrArg (fun candidate : PMF (information.Choice who site.1) =>
    (limit.continuationContext game.wellFoundedHistories site
      (GameTheory.Tests.SequentialExistence.payoff who)).value
        ((limit.strategy who).withLaw site.1 candidate)) (PMF.bind_pure law)).symm).le.trans bound

end GameTheory.Tests.ProtocolComponentCompletion
