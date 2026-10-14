module

/-
# Observation abstraction for response laws

A hidden state is drawn from a prior and a response depends on its observed
summary. The retained outcome consists of a fact about the state and the
public action. A summary determines the fact when that fact factors through
the summary on the prior support.

Conditional averaging preserves every fully informed fact/action law when
the summary determines the fact. Neither the carriers nor the prior support
need be finite. The total posterior's default at a zero-mass observation is
irrelevant to the initialized law. Perfect reporting and preservation of every
fully informed reporting law hold exactly when the summary determines the fact.
-/

public import GameTheory.Math.Probability.ConditionalObservation
public import GameTheory.Math.Probability.ExpectationAtoms

@[expose] public section

noncomputable section

namespace GameTheory.Math.Probability.ObservationAbstraction
open GameTheory.Math.Probability
variable {State Signal Action Fact : Type*}

/-- The fact factors through observation after restricting to the prior support. -/
abbrev Determines (prior : PMF State) (observe : State → Signal) (fact : State → Fact) : Prop :=
  Function.FactorsThrough (fun state : prior.support => fact state.1)
    (fun state : prior.support => observe state.1)

/-- Fact recovery only needs to hold at positive-prior states. -/
theorem determines_iff_decoder (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) : Determines prior observe fact ↔
      ∃ decode : Signal → Fact, ∀ state ∈ prior.support, decode (observe state) = fact state := by
  let _ : Nonempty Fact := ⟨fact prior.support_nonempty.choose⟩
  rw [Determines, Function.factorsThrough_iff]
  constructor
  · rintro ⟨decode, decodes⟩
    exact ⟨decode, fun state used => (congr_fun decodes ⟨state, used⟩).symm⟩
  · rintro ⟨decode, decodes⟩
    exact ⟨decode, funext fun state => (decodes state.1 state.2).symm⟩

/-- Sample a hidden state, respond to its observation, and retain fact and action. -/
abbrev responseLaw (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (policy : Signal → PMF Action) : PMF (Fact × Action) :=
  (bindPairLaw prior (fun state => policy (observe state))).map fun pair => (fact pair.1, pair.2)

theorem responseLaw_eq_bind (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (policy : Signal → PMF Action) : responseLaw prior observe fact policy =
      prior.bind fun state => (policy (observe state)).map fun action => (fact state, action) := by
  simp only [responseLaw, bindPairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem responseLaw_fst (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (policy : Signal → PMF Action) : (responseLaw prior observe fact policy).map Prod.fst =
      prior.map fact := by
  rw [responseLaw_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have constant (law : PMF Action) (a : Fact) : law.map (fun _ => a) = PMF.pure a := PMF.map_const
    _ _
  simp only [constant]
  exact PMF.bind_pure_comp _ _

theorem responseLaw_of_decoder {Summary : Type*} (prior : PMF State) (observe : State → Signal)
    (summary : State → Summary) (fact : State → Fact) (decode : Summary → Fact)
    (decodes : ∀ state ∈ prior.support, decode (summary state) = fact state)
    (policy : Signal → PMF Action) : responseLaw prior observe fact policy =
      (responseLaw prior observe summary policy).map fun pair => (decode pair.1, pair.2) := by
  simp only [responseLaw_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support
  intro state used
  rw [decodes state used]

/-- Average a fully informed response over states compatible with each observation. -/
def averagePolicy (prior : PMF State) (observe : State → Signal) (policy : State → PMF Action) :
    Signal → PMF Action := fun signal =>
  (fiberPosterior (responseLaw prior id observe policy) Prod.fst signal).map Prod.snd

theorem averagePolicy_observation_law (prior : PMF State) (observe : State → Signal)
    (policy : State → PMF Action) : responseLaw prior observe observe (averagePolicy prior observe
      policy) =
      responseLaw prior id observe policy := by
  have disintegration := eq_bind_fst_fiberPosterior_snd (responseLaw prior id observe policy)
  rw [responseLaw_fst, PMF.bind_map] at disintegration
  rw [responseLaw_eq_bind]
  exact disintegration.symm

/-- Averaging preserves the entire fact/action law, with no independence hypothesis. -/
theorem averagePolicy_response_law (prior : PMF State) (observe : State → Signal) (fact : State →
  Fact)
    (determines : Determines prior observe fact) (policy : State → PMF Action) :
    responseLaw prior observe fact (averagePolicy prior observe policy) =
      responseLaw prior id fact policy := by
  obtain ⟨decode, decodes⟩ := (determines_iff_decoder prior observe fact).mp determines
  rw [responseLaw_of_decoder prior observe observe fact decode decodes,
    responseLaw_of_decoder prior id observe fact decode decodes, averagePolicy_observation_law]

/-- A supported hidden state and supported response give a supported retained outcome. -/
theorem mem_support_responseLaw (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (policy : Signal → PMF Action) (state : State) (used : state ∈ prior.support)
    (action : Action) (selected : action ∈ (policy (observe state)).support) :
    (fact state, action) ∈ (responseLaw prior observe fact policy).support := by
  rw [responseLaw_eq_bind, PMF.support_bind]
  simp only [Set.mem_iUnion]
  refine ⟨state, used, ?_⟩
  rw [PMF.support_map]
  exact ⟨action, selected, rfl⟩

theorem responseLaw_report_eq_map (prior : PMF State) (fact : State → Fact) :
    responseLaw prior id fact (fun state => PMF.pure (fact state)) =
      prior.map (fun state => (fact state, fact state)) := by
  rw [responseLaw_eq_bind]
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- Randomization can reproduce perfect fact reporting exactly when observation determines the
  fact. -/
theorem exists_report_law_iff_determines (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) :
    (∃ policy : Signal → PMF Fact, responseLaw prior observe fact policy =
      prior.map (fun state => (fact state, fact state))) ↔ Determines prior observe fact := by
  constructor
  · rintro ⟨policy, sameLaw⟩
    have certain (state : State) (used : state ∈ prior.support) (action : Fact)
        (selected : action ∈ (policy (observe state)).support) : fact state = action := by
      have present := mem_support_responseLaw prior observe fact policy state used action selected
      rw [sameLaw] at present
      obtain ⟨original, -, same⟩ := (PMF.mem_support_map_iff _ _ _).mp present
      exact (Prod.mk.inj same).1.symm.trans (Prod.mk.inj same).2
    intro first second same
    obtain ⟨action, selected⟩ := (policy (observe first.1)).support_nonempty
    exact (certain first.1 first.2 action selected).trans
      (certain second.1 second.2 action (by simpa only [same] using selected)).symm
  · intro determines
    obtain ⟨decode, decodes⟩ := (determines_iff_decoder prior observe fact).mp determines
    refine ⟨fun signal => PMF.pure (decode signal), ?_⟩
    rw [responseLaw_eq_bind, ← PMF.bind_pure_comp]
    apply bind_congr_on_support
    intro state used
    rw [PMF.pure_map, decodes state used]
    rfl

/-- Reporting actions alone characterize preservation of every fully informed response law. -/
theorem all_response_laws_iff_determines (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) :
    (∀ informed : State → PMF Fact, ∃ policy : Signal → PMF Fact,
      responseLaw prior observe fact policy = responseLaw prior id fact informed) ↔
        Determines prior observe fact := by
  constructor
  · intro preserves
    apply (exists_report_law_iff_determines prior observe fact).mp
    obtain ⟨policy, same⟩ := preserves (fun state => PMF.pure (fact state))
    exact ⟨policy, same.trans (responseLaw_report_eq_map prior fact)⟩
  · intro determines informed
    exact ⟨averagePolicy prior observe informed,
      averagePolicy_response_law prior observe fact determines informed⟩

/-- Draw the observation first, then its posterior state and the response. -/
theorem responseLaw_eq_observation_bind (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → PMF Action) :
    responseLaw prior observe fact policy = (prior.map observe).bind fun signal =>
      (fiberPosterior prior observe signal).bind fun state =>
        (policy signal).map fun action => (fact state, action) := by
  rw [responseLaw_eq_bind]
  conv_lhs => rw [← fiberPosterior_reconstruct prior observe]
  rw [PMF.bind_bind]
  apply bind_congr_on_support
  intro signal used
  apply bind_congr_on_support
  intro state selected
  rw [(mem_support_fiberPosterior used selected).1]

open Classical in
/-- Expected reporting accuracy is the prior mean of correct-report probabilities. -/
theorem expect_responseLaw_report_eq (prior : PMF State) (observe : State → Signal)
    (fact : State → Fact) (policy : Signal → PMF Fact) :
    expect (responseLaw prior observe fact policy)
      (fun pair => if pair.1 = pair.2 then 1 else 0) =
        expect prior (fun state => (policy (observe state) (fact state)).toReal) := by
  classical
  have integrable : PayoffIntegrable (responseLaw prior observe fact policy)
      (fun pair => if pair.1 = pair.2 then (1 : ℝ) else 0) := by
    apply payoffIntegrable_of_bounded (C := 1)
    intro pair
    split <;> norm_num
  rw [responseLaw_eq_bind] at integrable ⊢
  rw [expect_bind_tower _ _ _ integrable]
  apply expect_congr_on_support
  intro state _
  rw [expect_map]
  change expect (policy (observe state)) (fun report => if fact state = report then 1 else 0) = _
  rw [expect_ite_eq, mul_one]

end GameTheory.Math.Probability.ObservationAbstraction
