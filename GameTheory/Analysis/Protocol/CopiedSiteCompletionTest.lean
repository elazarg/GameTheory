import GameTheory.Analysis.Protocol.CopiedSiteCompletion
import GameTheory.Analysis.Protocol.SequentialExistenceTest
import GameTheory.Math.Probability.FiniteUniform

noncomputable section

namespace GameTheory.Tests.CopiedSiteCompletion

open GameTheory GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability Filter
open GameTheory.Tests.SequentialExistence

/-- All agents share one group of full profiles. Its projected component menus
span every site's lotteries. This consumer checks both free and copied-site
branches on actual unequal-depth histories, for a constant terminal payoff. -/
theorem shared_weights_unequal_depth (copied : ∀ who, information.InformationSite who → Prop) :
    (¬ ∃ depth, InformationSite.CommonDepth information actingSite depth) ∧
      ∃ limit : information.BehavioralAssessment,
        limit.IsSequentialEquilibrium antichain game.wellFoundedHistories
          (fun _ _ => 0) := by
  classical
  let _ : Fintype execution.History := execution.historyFintype treeShaped
  let F := information.agentForm fallback game.wellFoundedHistories
  let _ (agent : information.InformationAgent information.playedInformation) :
      Fintype (F.sig.Strategy agent) :=
    @Fintype.ofFinite _ (information.finite_choice_of_played agent.2.2)
  let _ (agent : information.InformationAgent information.playedInformation) :
      Nonempty (F.sig.Strategy agent) :=
    information.nonempty_choice_of_played agent.2.2
  let Part := Profile F.sig
  let groupOf (_ : information.InformationAgent information.playedInformation) : Unit := ()
  let weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < weight n := by dsimp [weight]; positivity
  have small (n : ℕ) : weight n ≤ 1 := by
    dsimp [weight]
    apply (div_le_one (by positivity : (0 : ℝ) < n + 2)).mpr
    have nonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) := by
    have bound := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert bound using 1
    funext n
    simp [weight, Nat.cast_add]
    ring
  let component (n : ℕ) (agent : information.InformationAgent information.playedInformation)
      (part : Part) := mix (weight n) (positive n).le (small n)
        (uniformLaw (F.sig.Strategy agent)) (PMF.pure (part agent))
  have full : ∀ n agent part, FullSupport (component n agent part) := by
    intro n agent part choice
    exact mem_support_mix_left _ _ _ (positive n)
      (mem_support_uniformLaw choice)
  let menu (who : Unit) (site : information.InformationSite who) (part : Part) :=
    PMF.pure (part (information.agentAt site))
  have menuConverges who (site : information.InformationSite who) (part : Part) :
      PMFConvergesPointwise (fun n => component n (information.agentAt site) part)
        (menu who site part) :=
    pmfConvergesPointwise_mix_zero weight (fun n => (positive n).le) small vanishes _ _
  have spans who (site : information.InformationSite who)
      (law : PMF (information.Choice who site.1)) :
      ∃ alternative : PMF Part, alternative.bind (menu who site) = law := by
    let base : Part := Classical.choice inferInstance
    refine ⟨law.map (fun choice => Profile.update (sig := F.sig) base
      (information.agentAt site) choice), ?_⟩
    apply (PMF.bind_map law _ _).trans
    calc
      law.bind _ = law.bind PMF.pure := by
        apply congrArg (fun kernel => law.bind kernel)
        funext choice
        exact congrArg PMF.pure (Profile.update_same base (information.agentAt site) choice)
      _ = law := PMF.bind_pure law
  let decisionRecall := information.decisionRecall_of_perfectRecall perfectRecall
  obtain ⟨weights, sequence, limit, index, played, mixed, bayes, increasing,
      converges, equilibrium, representation⟩ :=
    information.exists_sequentialEquilibrium_of_shared_mixture_weight_certificates
      decisionRecall fallback game.wellFoundedHistories (fun _ _ => 0) groupOf
      (Part := fun _ => Part) component full copied menu
      (fun who site _ => menuConverges who site)
      (fun who site _ => spans who site) (fun _ sequence _ _ _ _ => by
        refine ⟨fun _ _ _ => 0, fun _ _ => tendsto_const_nhds, ?_, ?_⟩ <;>
          intros <;> simp [Context.value, BehavioralAssessment.continuationContext,
            BehavioralAssessment.continuationContextWith, Context.ofBelief,
            expect_constant])
  exact ⟨no_commonDepth, limit, equilibrium⟩

end GameTheory.Tests.CopiedSiteCompletion
