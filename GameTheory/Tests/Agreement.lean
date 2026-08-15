/-
# Common-knowledge agreement regression

A fair Boolean state is observed perfectly by one agent and not at all by the
other. The full event gives a positive common-knowledge agreement witness;
the true singleton gives different posteriors and therefore cannot be common
knowledge.
-/

import GameTheory.Epistemic.Agreement
import GameTheory.Epistemic.ApproximateAgreement

noncomputable section

namespace GameTheory.Tests.Agreement

open GameTheory.Epistemic GameTheory.Math.Probability

def fairPrior : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

theorem fairPrior_fullSupport : fairPrior.FullSupport := by
  intro state
  rw [← FinDist.prob_pos_iff]
  cases state <;> norm_num [fairPrior, FinDist.prob_pure_eq_ite]

def revealing : InfoPartition Bool where
  cell state := {state}
  reflexive state := by simp
  coherent state other hother := by
    simp at hother
    subst other
    rfl

def coarse : InfoPartition Bool where
  cell _ := Finset.univ
  reflexive state := Finset.mem_univ state
  coherent _ _ _ := rfl

def partition : Bool → InfoPartition Bool
  | false => revealing
  | true => coarse

theorem univ_commonKnowledgeAt (state : Bool) :
    CommonKnowledgeAt partition Finset.univ state := by
  refine ⟨Finset.univ, fun _ _ => Finset.mem_univ _, Finset.mem_univ state, ?_⟩
  intro agent world _
  cases agent <;> simp [partition, revealing, coarse]

/-- The concrete family reaches the common-knowledge formulation of Aumann's
theorem, not only its lower-level self-evident-event helper. -/
theorem reports_on_full_event_agree {firstReport secondReport : ℝ}
    (hfirst : ∀ world,
      posterior fairPrior (partition false) Finset.univ world = firstReport)
    (hsecond : ∀ world,
      posterior fairPrior (partition true) Finset.univ world = secondReport) :
    firstReport = secondReport := by
  exact aumann_full_agreement_of_commonKnowledgeAt fairPrior
    fairPrior_fullSupport partition false true Finset.univ Finset.univ
    (univ_commonKnowledgeAt false)
    (fun world _ => hfirst world) (fun world _ => hsecond world)

@[simp]
theorem revealing_posterior_true :
    posterior fairPrior revealing {true} true = 1 := by
  norm_num [posterior, revealing, fairPrior, FinDist.prob_pure_eq_ite]

@[simp]
theorem coarse_posterior_true :
    posterior fairPrior coarse {true} true = 1 / 2 := by
  norm_num [posterior, coarse, fairPrior, FinDist.prob_pure_eq_ite]

theorem revealingTrueCellPositive :
    ∃ world ∈ (revealing.cell true : Set Bool), world ∈ fairPrior.support :=
  ⟨true, by simp [revealing], fairPrior_fullSupport true⟩

theorem coarseTrueCellPositive :
    ∃ world ∈ (coarse.cell true : Set Bool), world ∈ fairPrior.support :=
  ⟨true, by simp [coarse], fairPrior_fullSupport true⟩

/-- The finite-cell posterior and canonical conditioning interfaces compute the
same revealing posterior. -/
theorem revealing_condOn_prob_true :
    (fairPrior.condOn (revealing.cell true : Set Bool)
      revealingTrueCellPositive).probOf ({true} : Set Bool) = 1 := by
  have hevent : ({true} : Set Bool) = (({true} : Finset Bool) : Set Bool) := by
    ext world
    simp
  rw [hevent]
  rw [← posterior_eq_probOf_condOn fairPrior revealing {true} true
    revealingTrueCellPositive]
  exact revealing_posterior_true

/-- The bridge is not confined to singleton cells: the coarse conditional law
assigns the true event probability one half. -/
theorem coarse_condOn_prob_true :
    (fairPrior.condOn (coarse.cell true : Set Bool)
      coarseTrueCellPositive).probOf ({true} : Set Bool) = 1 / 2 := by
  have hevent : ({true} : Set Bool) = (({true} : Finset Bool) : Set Bool) := by
    ext world
    simp
  rw [hevent]
  rw [← posterior_eq_probOf_condOn fairPrior coarse {true} true
    coarseTrueCellPositive]
  exact coarse_posterior_true

/-- A zero-mass information cell has no conditioning witness.  The bridge does
not hide an arbitrary posterior at an impossible observation. -/
theorem pureFalse_revealingTrueCell_not_positive :
    ¬ ∃ world ∈ (revealing.cell true : Set Bool),
      world ∈ (FinDist.pure false).support := by
  simp [revealing]

/-- If the singleton were common knowledge, the two constant reports on it
would have to agree; their computed values `1` and `1/2` refute that claim. -/
theorem true_not_commonKnowledgeAt :
    ¬ CommonKnowledgeAt partition {true} true := by
  intro hcommon
  have hagree : (1 : ℝ) = 1 / 2 :=
    aumann_full_agreement_of_commonKnowledgeAt fairPrior
      fairPrior_fullSupport partition false true {true} {true} hcommon
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

/-- Three worlds supporting common `p`-belief without exact common knowledge. -/
inductive World
  | center
  | left
  | right
  deriving DecidableEq, Fintype

inductive Agent
  | first
  | second
  deriving DecidableEq, Fintype

/-- The center has enough mass that either two-world cell assigns it
probability `6/7`. -/
def skewedPrior : FinDist World :=
  FinDist.mix (3 / 4) (by norm_num) (by norm_num)
    (FinDist.pure .center)
    (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure .left) (FinDist.pure .right))

theorem skewedPrior_fullSupport : skewedPrior.FullSupport := by
  intro world
  rw [← FinDist.prob_pos_iff]
  cases world with
  | center =>
      simp [skewedPrior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
  | left =>
      simp [skewedPrior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
      norm_num
  | right =>
      simp [skewedPrior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
      norm_num

/-- Agent `false` pools the center with the left world. -/
def leftCell : InfoPartition World where
  cell
    | .center | .left => {.center, .left}
    | .right => {.right}
  reflexive world := by cases world <;> simp
  coherent world other hother := by
    cases world <;> cases other <;> simp_all

/-- Agent `true` instead pools the center with the right world. -/
def rightCell : InfoPartition World where
  cell
    | .center | .right => {.center, .right}
    | .left => {.left}
  reflexive world := by cases world <;> simp
  coherent world other hother := by
    cases world <;> cases other <;> simp_all

def approximatePartition : Agent → InfoPartition World
  | .first => leftCell
  | .second => rightCell

/-- The reports at the center are genuinely different: the left-pooling agent
assigns probability `1/7` to the left world, while the right-pooling agent
assigns probability zero. -/
def report : Agent → ℝ
  | .first => 1 / 7
  | .second => 0

@[simp]
theorem center_posterior_left (agent : Agent) :
    posterior skewedPrior (approximatePartition agent) {.left} .center =
      report agent := by
  cases agent with
  | first =>
    simp [posterior, approximatePartition, leftCell,
      skewedPrior, report, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
    norm_num
  | second =>
    simp [posterior, approximatePartition, rightCell,
      skewedPrior, report, FinDist.prob_mix, FinDist.prob_pure_eq_ite]

theorem reports_distinct : report .first ≠ report .second := by
  norm_num [report]

@[simp]
theorem center_posterior_center (agent : Agent) :
    posterior skewedPrior (approximatePartition agent) {.center} .center =
      6 / 7 := by
  cases agent with
  | first =>
    simp [posterior, approximatePartition, leftCell,
      skewedPrior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
    norm_num
  | second =>
    simp [posterior, approximatePartition, rightCell,
      skewedPrior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
    norm_num

theorem report_states_eq :
    (Finset.univ.filter fun world =>
      ∀ agent : Agent,
        posterior skewedPrior (approximatePartition agent) {.left} world =
          report agent) =
      {.center} := by
  ext world
  cases world with
  | center =>
    simp [center_posterior_left]
  | left =>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hall
      have hsecond := hall Agent.second
      simp [posterior, approximatePartition, rightCell, skewedPrior,
        report, FinDist.prob_mix, FinDist.prob_pure_eq_ite] at hsecond
      norm_num at hsecond
    · intro hfalse
      exact (World.noConfusion hfalse)
  | right =>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hall
      have hfirst := hall Agent.first
      simp [posterior, approximatePartition, leftCell, skewedPrior,
        report, FinDist.prob_mix, FinDist.prob_pure_eq_ite] at hfirst
    · intro hfalse
      exact (World.noConfusion hfalse)

/-- At threshold `3/4`, the center singleton is `p`-evident for both agents,
and it lies in the event where both named posterior reports are realized. -/
theorem commonThreeQuarterBelief_reports :
    CommonPBeliefAt skewedPrior approximatePartition (3 / 4)
      (Finset.univ.filter fun world =>
        ∀ agent : Agent,
          posterior skewedPrior (approximatePartition agent) {.left} world =
            report agent)
      .center := by
  refine ⟨{.center}, by simp, ?_, ?_⟩
  · intro agent world hworld
    simp only [Finset.mem_singleton] at hworld
    subst world
    rw [mem_PBelief_iff]
    rw [center_posterior_center]
    norm_num
  · intro world hworld
    simp only [Finset.mem_singleton] at hworld
    subst world
    rw [mem_mutualPBelief_iff]
    intro agent
    rw [show (Finset.univ.filter fun candidate =>
          ∀ who : Agent,
            posterior skewedPrior (approximatePartition who) {.left}
                candidate = report who) = {.center} from report_states_eq]
    rw [center_posterior_center]
    norm_num

/-- A stable `p < 1` consumer of the full approximate-agreement entry point.
The conclusion is non-vacuous because the two reports are distinct. -/
theorem distinct_reports_satisfy_monderer_samet_bound :
    |report .first - report .second| ≤ 2 * (1 - (3 / 4 : ℝ)) := by
  exact @commonPBelief_posterior_reports_close
    World instFintypeWorld instDecidableEqWorld
    Agent instFintypeAgent skewedPrior skewedPrior_fullSupport
    approximatePartition {.left} .center (3 / 4)
    (by norm_num) report commonThreeQuarterBelief_reports .first .second

end GameTheory.Tests.ApproximateAgreement
