/-
# Common-knowledge agreement regression

A fair Boolean state is observed perfectly by one agent and not at all by the
other. The full event gives a positive common-knowledge agreement witness;
the true singleton has different posteriors and cannot be common knowledge.
-/

import GameTheory.Epistemic.Agreement
import GameTheory.Epistemic.ApproximateAgreement

noncomputable section

namespace GameTheory.Tests.Agreement

open GameTheory.Epistemic GameTheory.Math.Probability

def fairPrior : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

theorem fairPrior_fullSupport : FullSupport fairPrior := by
  intro state
  cases state <;> rw [PMF.mem_support_iff]
  all_goals norm_num [fairPrior, mix_apply, PMF.pure_apply]

def revealing : Setoid Bool where
  r := Eq
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

def coarse : Setoid Bool where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

def partition : Bool → Setoid Bool
  | false => revealing
  | true => coarse

theorem univ_commonKnowledgeAt (state : Bool) :
    CommonKnowledgeAt partition Set.univ state := by
  refine ⟨Set.univ, fun _ _ => Set.mem_univ _, Set.mem_univ state, ?_⟩
  intro agent world _ other _
  exact Set.mem_univ other

theorem reports_on_full_event_agree {firstReport secondReport : ℝ}
    (hfirst : ∀ world,
      posterior fairPrior (partition false) Set.univ world = firstReport)
    (hsecond : ∀ world,
      posterior fairPrior (partition true) Set.univ world = secondReport) :
    firstReport = secondReport := by
  exact aumann_full_agreement_of_commonKnowledgeAt fairPrior
    partition false true Set.univ Set.univ
    (univ_commonKnowledgeAt false)
    (fun world _ => hfirst world) (fun world _ => hsecond world)

@[simp]
theorem revealing_posterior_true :
    posterior fairPrior revealing {true} true = 1 := by
  exact posterior_eq_one_of_selfEvident_of_cell_mass_pos fairPrior
    revealing {true} true (Set.mem_singleton_iff.mpr rfl) (by
      intro state hstate other hcell
      have hs : state = true := by
        exact Set.mem_singleton_iff.mp hstate
      rw [hs] at hcell
      exact hcell.symm)
    (outerMeasure_pos_of_mem_support (μ := fairPrior)
      (event := cell revealing true) true (by simp [cell])
      (fairPrior_fullSupport true))

@[simp]
theorem coarse_posterior_true :
    posterior fairPrior coarse {true} true = 1 / 2 := by
  have hnum : fairPrior.toOuterMeasure {true} = ENNReal.ofReal (1 / 2) := by
    rw [PMF.toOuterMeasure_apply, tsum_fintype]
    norm_num [fairPrior, Fintype.sum_bool, Set.indicator, mix_apply,
      PMF.pure_apply]
  have hden : fairPrior.toOuterMeasure Set.univ = 1 := by
    exact (PMF.toOuterMeasure_apply_eq_one_iff fairPrior Set.univ).2
      (Set.subset_univ _)
  have hcell : cell coarse true = Set.univ := by
    ext world
    show coarse.r true world ↔ True
    rfl
  rw [posterior, hcell, Set.inter_univ, hnum, hden]
  norm_num

theorem revealingTrueCellPositive :
    ∃ world ∈ cell revealing true, world ∈ fairPrior.support :=
  ⟨true, by simp [cell], fairPrior_fullSupport true⟩

theorem coarseTrueCellPositive :
    ∃ world ∈ cell coarse true, world ∈ fairPrior.support :=
  ⟨true, by simp [cell], fairPrior_fullSupport true⟩

theorem revealing_condOn_prob_true :
    posterior fairPrior revealing {true} true = 1 := revealing_posterior_true

theorem coarse_condOn_prob_true :
    posterior fairPrior coarse {true} true = 1 / 2 := coarse_posterior_true

theorem pureFalse_revealingTrueCell_not_positive :
    ¬ ∃ world ∈ cell revealing true,
      world ∈ (PMF.pure false).support := by
  rintro ⟨world, hcell, hsupport⟩
  have hworld : world = true := by
    exact hcell.symm
  subst world
  simp at hsupport

theorem true_not_commonKnowledgeAt :
    ¬ CommonKnowledgeAt partition {true} true := by
  intro hcommon
  have hagree : (1 : ℝ) = 1 / 2 :=
    aumann_full_agreement_of_commonKnowledgeAt fairPrior
      partition false true {true} {true} hcommon
      (fun world hworld => by
        simp at hworld
        subst world
        exact revealing_posterior_true)
      (fun world hworld => by
        simp at hworld
        subst world
        exact coarse_posterior_true)
  norm_num at hagree

end GameTheory.Tests.Agreement

namespace GameTheory.Tests.ApproximateAgreement

open GameTheory.Epistemic GameTheory.Math.Probability

abbrev World := Option Bool

namespace World

def center : World := none
def left : World := some false
def right : World := some true

end World

abbrev Agent := Bool

namespace Agent

def first : Agent := false
def second : Agent := true

end Agent

/-- The center has enough mass that either two-world cell assigns it
probability `6/7`. -/
def skewedPrior : PMF World :=
  mix (3 / 4) (by norm_num) (by norm_num)
    (PMF.pure .center)
    (mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure .left) (PMF.pure .right))

theorem skewedPrior_fullSupport : FullSupport skewedPrior := by
  intro world
  rw [PMF.mem_support_iff]
  cases world with
  | none => norm_num [skewedPrior, mix_apply, PMF.pure_apply,
      World.center, World.left, World.right]
  | some bit => cases bit <;>
      norm_num [skewedPrior, mix_apply, PMF.pure_apply,
        World.center, World.left, World.right]

def leftTag : World → Bool
  | none => false
  | some false => false
  | some true => true

def rightTag : World → Bool
  | none => false
  | some false => true
  | some true => false

def leftCell : Setoid World where
  r first second := leftTag first = leftTag second
  iseqv := ⟨fun _ => rfl, fun {_ _} h => h.symm,
    fun {_ _ _} h₁ h₂ => h₁.trans h₂⟩

def rightCell : Setoid World where
  r first second := rightTag first = rightTag second
  iseqv := ⟨fun _ => rfl, fun {_ _} h => h.symm,
    fun {_ _ _} h₁ h₂ => h₁.trans h₂⟩

@[simp]
theorem leftCell_center_cell :
    cell leftCell none = {none, some false} := by
  ext world
  show leftTag none = leftTag world ↔
    world = none ∨ world = some false
  cases world with
  | none => simp [leftTag]
  | some bit => cases bit <;>
      simp [leftTag]

@[simp]
theorem leftCell_left_cell :
    cell leftCell (some false) = {none, some false} := by
  ext world
  show leftTag (some false) = leftTag world ↔
    world = none ∨ world = some false
  cases world with
  | none => simp [leftTag]
  | some bit => cases bit <;>
      simp [leftTag]

@[simp]
theorem leftCell_right_cell :
    cell leftCell (some true) = {some true} := by
  ext world
  show leftTag (some true) = leftTag world ↔ world = some true
  cases world with
  | none => simp [leftTag]
  | some bit => cases bit <;>
      simp [leftTag]

@[simp]
theorem rightCell_center_cell :
    cell rightCell none = {none, some true} := by
  ext world
  show rightTag none = rightTag world ↔
    world = none ∨ world = some true
  cases world with
  | none => simp [rightTag]
  | some bit => cases bit <;>
      simp [rightTag]

@[simp]
theorem rightCell_right_cell :
    cell rightCell (some true) = {none, some true} := by
  ext world
  show rightTag (some true) = rightTag world ↔
    world = none ∨ world = some true
  cases world with
  | none => simp [rightTag]
  | some bit => cases bit <;>
      simp [rightTag]

@[simp]
theorem rightCell_left_cell :
    cell rightCell (some false) = {some false} := by
  ext world
  show rightTag (some false) = rightTag world ↔ world = some false
  cases world with
  | none => simp [rightTag]
  | some bit => cases bit <;>
      simp [rightTag]

def approximatePartition : Agent → Setoid World
  | false => leftCell
  | true => rightCell

def report : Agent → ℝ
  | false => 1 / 7
  | true => 0

private theorem skewedDenom_toReal :
    (ENNReal.ofReal (3 / 4 : ℝ) +
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (1 / 2 : ℝ)).toReal =
        7 / 8 := by
  rw [ENNReal.toReal_add (by simp) (ENNReal.mul_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_mul]
  norm_num

@[simp]
theorem center_posterior_left (agent : Agent) :
    posterior skewedPrior (approximatePartition agent) {.left} .center =
      report agent := by
  cases agent <;>
    simp only [approximatePartition]
  all_goals
    norm_num [posterior, approximatePartition,
      report, skewedPrior, mix_apply, PMF.pure_apply,
      PMF.toOuterMeasure_apply_fintype, Fintype.sum_option,
      Fintype.sum_bool, skewedDenom_toReal,
      World.center, World.left, World.right,
      Agent.first, Agent.second]

theorem reports_distinct : report .first ≠ report .second := by
  norm_num [report, Agent.first, Agent.second]

@[simp]
theorem center_posterior_center (agent : Agent) :
    posterior skewedPrior (approximatePartition agent) {.center} .center =
      6 / 7 := by
  cases agent <;>
    simp only [approximatePartition]
  all_goals
    norm_num [posterior, approximatePartition,
      skewedPrior, mix_apply, PMF.pure_apply,
      PMF.toOuterMeasure_apply_fintype, Fintype.sum_option,
      Fintype.sum_bool, skewedDenom_toReal,
      World.center, World.left, World.right,
      Agent.first, Agent.second]

private theorem left_reports_posterior_first :
    posterior skewedPrior (approximatePartition .first) {.left} .left =
      1 / 7 := by
  norm_num [posterior, approximatePartition, report, skewedPrior,
    mix_apply, PMF.pure_apply, PMF.toOuterMeasure_apply_fintype,
    Fintype.sum_option, World.center, World.left, World.right,
    Agent.first, Agent.second, skewedDenom_toReal]

private theorem left_reports_posterior_second :
    posterior skewedPrior (approximatePartition .second) {.left} .left =
      1 := by
  norm_num [posterior, approximatePartition, report, skewedPrior,
    mix_apply, PMF.pure_apply, PMF.toOuterMeasure_apply_fintype,
    Fintype.sum_option, World.center, World.left, World.right,
    Agent.first, Agent.second]

private theorem right_reports_posterior_first :
    posterior skewedPrior (approximatePartition .first) {.left} .right =
      0 := by
  norm_num [posterior, approximatePartition, report, skewedPrior,
    mix_apply, PMF.pure_apply, PMF.toOuterMeasure_apply_fintype,
    Fintype.sum_option, World.center, World.left, World.right,
    Agent.first, Agent.second]

private theorem right_reports_posterior_second :
    posterior skewedPrior (approximatePartition .second) {.left} .right =
      0 := by
  norm_num [posterior, approximatePartition, report, skewedPrior,
    mix_apply, PMF.pure_apply, PMF.toOuterMeasure_apply_fintype,
    Fintype.sum_option, World.center, World.left, World.right,
    Agent.first, Agent.second, skewedDenom_toReal]

def reportStates : Set World :=
  {world | ∀ agent : Agent,
    posterior skewedPrior (approximatePartition agent) {.left} world =
      report agent}

theorem report_states_eq : reportStates = {.center} := by
  ext world
  simp only [reportStates, Set.mem_ofPred_eq]
  cases world with
  | none =>
      constructor
      · intro _
        trivial
      · intro _ agent
        exact center_posterior_left agent
  | some bit => cases bit with
    | false =>
        constructor
        · intro h
          have hh := h true
          have hp : posterior skewedPrior (approximatePartition true)
              {World.left} (some false) = 1 := by
            simpa [World.left, Agent.second] using
              left_reports_posterior_second
          rw [hp] at hh
          norm_num [report] at hh
        · intro h
          simp [World.center] at h
    | true =>
        constructor
        · intro h
          have hh := h false
          have hp : posterior skewedPrior (approximatePartition false)
              {World.left} (some true) = 0 := by
            simpa [World.right, Agent.first] using
              right_reports_posterior_first
          rw [hp] at hh
          norm_num [report] at hh
        · intro h
          simp [World.center] at h

theorem commonThreeQuarterBelief_reports :
    CommonPBeliefAt skewedPrior approximatePartition (3 / 4 : ℝ)
      reportStates .center := by
  refine ⟨{.center}, by simp, ?_, ?_⟩
  · intro agent world hworld
    simp only [Set.mem_singleton_iff] at hworld
    subst world
    rw [mem_PBelief_iff, center_posterior_center]
    norm_num
  · intro world hworld
    simp only [Set.mem_singleton_iff] at hworld
    subst world
    rw [mem_mutualPBelief_iff]
    intro agent
    rw [report_states_eq, center_posterior_center]
    norm_num

theorem distinct_reports_satisfy_monderer_samet_bound :
    |report .first - report .second| ≤ 2 * (1 - (3 / 4 : ℝ)) := by
  exact commonPBelief_posterior_reports_close (by norm_num)
    commonThreeQuarterBelief_reports .first .second

end GameTheory.Tests.ApproximateAgreement
