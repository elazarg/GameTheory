/-
# Common-knowledge agreement regression

A fair Boolean state is observed perfectly by one agent and not at all by the
other. The full event gives a positive common-knowledge agreement witness;
the true singleton gives different posteriors and therefore cannot be common
knowledge.
-/

import GameTheory.Epistemic.Agreement

noncomputable section

namespace GameTheory.Tests.Agreement

open GameTheory.Epistemic GameTheory.Probability

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
