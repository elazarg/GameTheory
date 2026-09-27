/-
# EXP-142: fully mixed assessments on the unbounded countdown

The root Boolean decision has a vanishing false-action tremble. Bayes beliefs
are built from the actual fully supported behavioral profiles. The repair
mixes every whole-policy alternative with that same positive tremble.
-/

import GameTheory.Experimental.PostArchitecture.WellFoundedTerminalGate
import GameTheory.Analysis.Protocol.SequentialTerminalExistence
import GameTheory.Analysis.Protocol.BehavioralBayes

noncomputable section

namespace GameTheory.Tests.WellFoundedTerminalGate

open Filter GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- The only decision site is the root, so site-indexed laws have one
coordinate even though the raw information-state carrier is `ℝ`. -/
instance : Subsingleton (information.InformationSite ()) :=
  ⟨fun first second => (informationSite_eq_rootSite first).trans
    (informationSite_eq_rootSite second).symm⟩

/-- A positive tremble weight that tends to zero. -/
def trembleWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem trembleWeight_pos (n : ℕ) : 0 < trembleWeight n := by
  exact one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))

theorem trembleWeight_le_one (n : ℕ) : trembleWeight n ≤ 1 := by
  apply (div_le_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem trembleWeight_lt_one (n : ℕ) : trembleWeight n < 1 := by
  apply (div_lt_iff₀ (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem trembleWeight_tendsto_zero : Tendsto trembleWeight atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  simp [trembleWeight, Nat.cast_add]
  ring

/-- At the root the fallback chooses `false`; elsewhere it chooses the
unique legal no-op. -/
def fallbackChoice (info : ℝ) : information.Choice () info :=
  if h : info = 1 then ⟨some false, by simp [h]⟩
  else ⟨none, by simp [h]⟩

/-- At the root the candidate chooses `true`; elsewhere it chooses the
unique legal no-op. -/
def trueChoice (info : ℝ) : information.Choice () info :=
  if h : info = 1 then ⟨some true, by simp [h]⟩
  else ⟨none, by simp [h]⟩

/-- Reference and candidate policies are total on the uncountable raw
information-state carrier. -/
def fallbackPolicy : information.BehavioralPolicy () :=
  fun info => PMF.pure (fallbackChoice info)

def pureTruePolicy : information.BehavioralPolicy () :=
  fun info => PMF.pure (trueChoice info)

/-- Every whole-policy alternative is repaired by the same positive
tremble, without restricting its behavior at any information state. -/
def repair (n : ℕ) (_who : Unit)
    (alternative : information.BehavioralPolicy ()) :
    information.BehavioralPolicy () := fun info =>
  mix (trembleWeight n) (trembleWeight_pos n).le
    (trembleWeight_le_one n) (fallbackPolicy info) (alternative info)

/-- The incumbent trembles toward `false` and otherwise chooses `true`. -/
def strategy (n : ℕ) (_who : Unit) : information.BehavioralPolicy () :=
  repair n () pureTruePolicy

private theorem rootChoice_cases
    (choice : information.Choice () rootSite.1) :
    choice = fallbackChoice rootSite.1 ∨ choice = trueChoice rootSite.1 := by
  rcases choice with ⟨choice, hchoice⟩
  cases choice with
  | none => simp [information, rootSite] at hchoice
  | some action =>
      cases action <;> simp [fallbackChoice, trueChoice, rootSite]

/-- Every actual root choice has positive probability under each approximant. -/
theorem strategy_fullSupport (n : ℕ) :
    ∀ i (site : information.InformationSite i) choice,
      choice ∈ (strategy n i site.1).support := by
  intro i site choice
  cases i
  have hsite := informationSite_eq_rootSite site
  subst site
  rcases rootChoice_cases choice with hfalse | htrue
  · rw [hfalse]
    simpa only [strategy, repair, fallbackPolicy] using
      (mem_support_mix_left _ _ _ (trembleWeight_pos n)
        ((PMF.mem_support_pure_iff _ _).mpr rfl))
  · rw [htrue]
    simpa only [strategy, repair, pureTruePolicy] using
      (mem_support_mix_right _ _ _ (trembleWeight_lt_one n)
        ((PMF.mem_support_pure_iff _ _).mpr rfl))

/-- Actual fully mixed Bayes assessments at every tremble level. -/
def assessment (n : ℕ) : information.BehavioralAssessment :=
  information.bayesAssessment (strategy n) (strategy_fullSupport n)
    decisionInformationAntichain

theorem assessment_fullyMixed (n : ℕ) : (assessment n).IsFullyMixed := by
  intro i site choice
  exact strategy_fullSupport n i site choice

theorem assessment_bayesConsistent (n : ℕ) :
    BehavioralAssessment.IsBayesConsistent information (assessment n)
      decisionInformationAntichain :=
  information.bayesAssessment_isBayesConsistent
    (strategy n) (strategy_fullSupport n) decisionInformationAntichain

/-- Every root-choice carrier is finite even though raw information states
range over all real numbers. -/
theorem assessment_strategy_uniformlyTight
    (i : Unit) (site : information.InformationSite i) :
    UniformlyTight (fun n => (assessment n).strategy i site.1) := by
  exact uniformlyTight_of_finite _

theorem assessment_belief_uniformlyTight
    (i : Unit) (site : information.InformationSite i) :
    UniformlyTight (fun n => (assessment n).belief i site) := by
  cases i
  have : Subsingleton (information.InformationHistory () site.1) :=
    ⟨fun first second => Subtype.ext
      ((informationHistory_eq_initHistory site first).trans
        (informationHistory_eq_initHistory site second).symm)⟩
  exact uniformlyTight_of_finite _

/-- Repaired whole policies converge at every decision site to the
unrestricted alternative. -/
theorem repair_convergesPointwise_on_sites
    (i : Unit) (alternative : information.BehavioralPolicy i)
    (site : information.InformationSite i) :
    PMFConvergesPointwise
      (fun n => repair n i alternative site.1) (alternative site.1) := by
  cases i
  exact pmfConvergesPointwise_mix_zero trembleWeight
    (fun n => (trembleWeight_pos n).le) trembleWeight_le_one
    trembleWeight_tendsto_zero (fallbackPolicy site.1) (alternative site.1)

/-- The initial joint behavioral draw has exactly the root policy's reward law. -/
theorem root_behavioral_reward_law
    (policies : (i : Unit) → information.BehavioralPolicy i) :
    PMF.map
      (fun draw => if (draw.1 ()).getD false then (1 : ℝ) else 0)
      (information.randomizedChooser policies execution.initHistory
        (by simp [execution])) =
      PMF.map
        (fun choice : information.Choice () 1 =>
          if choice.1 = some true then (1 : ℝ) else 0)
        (policies () 1) := by
  unfold InformationModel.randomizedChooser
  rw [information.behavioralJoint_eq_map_of_at_most_one_active
    policies execution.initHistory.trace (by simp [execution]) ()
    (by intro i _; cases i; rfl)]
  simp only [ExecutionProtocol.initHistory, signals_infoOf_start, PMF.map_comp]
  congr 1
  funext choice
  cases hchoice : choice.1 with
  | none => simp [hchoice]
  | some action => cases action <;> simp [hchoice]

end GameTheory.Tests.WellFoundedTerminalGate
