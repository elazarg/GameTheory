/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.SequentialAssessment
import GameTheory.Languages.EFG.Syntax

/-!
# Sequential and Perfect-Bayesian Assessments for EFGs

Concrete assessment predicates for extensive-form refinements.

The existing `EFGGame.Assessment`, `IsSequentialEqFor`, and
`IsPerfectBayesianEqFor` definitions are intentionally schema-level. This file
supplies reusable concrete predicates for the usual ingredients:

* histories reaching information sets,
* beliefs supported on the information set,
* on-path Bayes consistency,
* sequential rationality against behavioral continuation deviations.

The definitions are preference-parametric where possible. Expected-utility
specializations are provided as corollaries of those generic predicates.
-/

namespace EFG

open GameTheory
open Math.Probability

namespace GameTree

variable {S : InfoStructure} {Outcome : Type}

/-- Probability of a concrete history under a behavioral profile, starting from
the given tree.

Invalid histories have probability `0`. The empty history has probability `1`
from any tree. -/
noncomputable def historyProb (σ : BehavioralProfile S) :
    GameTree S Outcome → List (HistoryStep S) → ENNReal
  | _, [] => 1
  | .terminal _, _ :: _ => 0
  | .chance k μ _hk next, HistoryStep.chance k' b :: rest =>
      if hk : k' = k then
        μ (hk ▸ b) * historyProb σ (next (hk ▸ b)) rest
      else 0
  | .chance _ _ _ _, HistoryStep.action _ _ _ :: _ => 0
  | .decision (p := p) I next, HistoryStep.action q J a :: rest =>
      if hq : q = p then by
        subst hq
        exact
          if hI : J = I then
            σ _ J a * historyProb σ (next (hI ▸ a)) rest
          else 0
      else 0
  | .decision _ _, HistoryStep.chance _ _ :: _ => 0

@[simp] theorem historyProb_nil (σ : BehavioralProfile S) (t : GameTree S Outcome) :
    t.historyProb σ [] = 1 := by
  cases t <;> rfl

@[simp] theorem historyProb_terminal_cons (σ : BehavioralProfile S) (z : Outcome)
    (step : HistoryStep S) (rest : List (HistoryStep S)) :
    (GameTree.terminal z).historyProb σ (step :: rest) = 0 := by
  cases step <;> rfl

@[simp] theorem historyProb_chance_valid (σ : BehavioralProfile S)
    (k : Nat) (μ : PMF (Fin k)) {hk : 0 < k}
    (next : Fin k → GameTree S Outcome) (b : Fin k)
    (rest : List (HistoryStep S)) :
    (GameTree.chance k μ hk next).historyProb σ
      (HistoryStep.chance k b :: rest) =
        μ b * (next b).historyProb σ rest := by
  simp [historyProb]

@[simp] theorem historyProb_decision_valid (σ : BehavioralProfile S)
    {p : S.Player} (I : S.Infoset p) (next : S.Act I → GameTree S Outcome)
    (a : S.Act I) (rest : List (HistoryStep S)) :
    (GameTree.decision I next).historyProb σ
      (HistoryStep.action p I a :: rest) =
        σ p I a * (next a).historyProb σ rest := by
  simp [historyProb]

end GameTree

namespace EFGGame

variable (G : EFGGame)

/-- A history reaches a particular subtree of the game. -/
def ReachesTree (h : List (HistoryStep G.inf))
    (t : GameTree G.inf G.Outcome) : Prop :=
  ReachBy h G.tree t

/-- A history reaches information set `I`. -/
def ReachesInfoSet {p : G.inf.Player} (I : G.inf.Infoset p)
    (h : List (HistoryStep G.inf)) : Prop :=
  ∃ next : G.inf.Act I → GameTree G.inf G.Outcome,
    ReachBy h G.tree (.decision I next)

/-- Probability of a history under a behavioral profile. -/
noncomputable def historyProb (σ : BehavioralProfile G.inf)
    (h : List (HistoryStep G.inf)) : ENNReal :=
  G.tree.historyProb σ h

/-- Choose the subtree reached by a history when it exists, falling back to the
root for invalid histories. Predicates such as belief support ensure the
fallback is irrelevant on the support of well-formed beliefs. -/
noncomputable def continuationTree (h : List (HistoryStep G.inf)) :
    GameTree G.inf G.Outcome :=
  by
    classical
    exact
      if hreach : ∃ t : GameTree G.inf G.Outcome, ReachBy h G.tree t then
        Classical.choose hreach
      else
        G.tree

theorem continuationTree_spec {h : List (HistoryStep G.inf)}
    (hreach : ∃ t : GameTree G.inf G.Outcome, ReachBy h G.tree t) :
    ReachBy h G.tree (G.continuationTree h) := by
  unfold continuationTree
  rw [dif_pos hreach]
  exact Classical.choose_spec hreach

/-- Outcome distribution obtained by first sampling a history from a belief and
then continuing from the reached subtree under `σ`. -/
noncomputable def continuationOutcome
    (β : PMF (List (HistoryStep G.inf))) (σ : BehavioralProfile G.inf) :
    PMF G.Outcome :=
  β.bind fun h => (G.continuationTree h).evalDist σ

/-- The generic assessment form induced by an EFG game. -/
noncomputable abbrev toAssessmentForm : AssessmentForm G.inf.Player where
  Strategy := BehavioralStrategy G.inf
  Outcome := G.Outcome
  History := List (HistoryStep G.inf)
  Info := G.inf.Infoset
  historyProb := G.historyProb
  reachesInfo := fun {_} I h => G.ReachesInfoSet I h
  continuationOutcome := G.continuationOutcome

/-- Generic assessment object associated with the EFG assessment form. -/
abbrev GenericAssessment := G.toAssessmentForm.Assessment

/-- Generic assessment-deviation family associated with the EFG assessment
form. -/
abbrev AssessmentDeviationFamily := G.toAssessmentForm.AssessmentDeviationFamily

/-- Convert the existing EFG assessment structure to the generic assessment
structure. -/
def Assessment.toGeneric (A : G.Assessment) : G.GenericAssessment where
  strategy := A.strategy
  beliefs := A.beliefs

/-- Convert a generic assessment for the induced assessment form back to the
existing EFG assessment structure. -/
def Assessment.ofGeneric (A : G.GenericAssessment) : G.Assessment where
  strategy := A.strategy
  beliefs := A.beliefs

@[simp] theorem Assessment.ofGeneric_toGeneric (A : G.Assessment) :
    Assessment.ofGeneric G (A.toGeneric G) = A := by
  cases A
  rfl

@[simp] theorem Assessment.toGeneric_ofGeneric (A : G.GenericAssessment) :
    (Assessment.ofGeneric G A).toGeneric G = A := by
  cases A
  rfl

/-- Total probability mass of histories reaching an EFG information set. -/
noncomputable def infoSetMass (σ : BehavioralProfile G.inf)
    {p : G.inf.Player} (I : G.inf.Infoset p) : ENNReal :=
  G.toAssessmentForm.infoMass σ I

/-- An information set is on path under `σ`. -/
def IsOnPath (σ : BehavioralProfile G.inf)
    {p : G.inf.Player} (I : G.inf.Infoset p) : Prop :=
  G.toAssessmentForm.IsOnPath σ I

/-- Belief support at an EFG information set. -/
def BeliefSupportedAt (A : G.Assessment)
    {p : G.inf.Player} (I : G.inf.Infoset p) : Prop :=
  G.toAssessmentForm.BeliefSupportedAt (A.toGeneric G) I

/-- Belief support at all EFG information sets. -/
def BeliefsSupported (A : G.Assessment) : Prop :=
  G.toAssessmentForm.BeliefsSupported (A.toGeneric G)

/-- Pointwise Bayes rule at an EFG information set. -/
noncomputable def BayesRuleAt (A : G.Assessment)
    {p : G.inf.Player} (I : G.inf.Infoset p) : Prop :=
  G.toAssessmentForm.BayesRuleAt (A.toGeneric G) I

/-- On-path Bayes consistency for EFG assessments. -/
noncomputable def BayesConsistentOnPath (A : G.Assessment) : Prop :=
  G.toAssessmentForm.BayesConsistentOnPath (A.toGeneric G)

/-- Weak consistency for EFG PBE-style assessments. -/
noncomputable def WeaklyConsistentAssessment (A : G.Assessment) : Prop :=
  G.toAssessmentForm.WeaklyConsistentAssessment (A.toGeneric G)

/-- Expected continuation utility from a belief over histories. -/
noncomputable def continuationEU
    (β : PMF (List (HistoryStep G.inf))) (σ : BehavioralProfile G.inf)
    (who : G.inf.Player) : ℝ :=
  expect (G.continuationOutcome β σ) (fun ω => G.utility ω who)

section StrategicDeviation

variable [DecidableEq G.inf.Player]

/-- Preference-parametric sequential rationality at one EFG information set,
relative to an explicit deviation family. -/
noncomputable def SequentiallyRationalAtForFamily
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Δ : G.AssessmentDeviationFamily)
    (A : G.Assessment) {p : G.inf.Player} (I : G.inf.Infoset p) : Prop :=
  G.toAssessmentForm.SequentiallyRationalAtForFamily pref Δ (A.toGeneric G) I

/-- Preference-parametric sequential rationality at every EFG information set,
relative to an explicit deviation family. -/
noncomputable def SequentiallyRationalForFamily
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Δ : G.AssessmentDeviationFamily)
    (A : G.Assessment) : Prop :=
  G.toAssessmentForm.SequentiallyRationalForFamily pref Δ (A.toGeneric G)

/-- Preference-parametric sequential rationality at one EFG information set. -/
noncomputable def SequentiallyRationalAtFor
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (A : G.Assessment) {p : G.inf.Player} (I : G.inf.Infoset p) : Prop :=
  G.toAssessmentForm.SequentiallyRationalAtFor pref (A.toGeneric G) I

/-- Preference-parametric sequential rationality at every EFG information set. -/
noncomputable def SequentiallyRationalFor
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (A : G.Assessment) : Prop :=
  G.toAssessmentForm.SequentiallyRationalFor pref (A.toGeneric G)

/-- Expected-utility preference on EFG outcome distributions. -/
noncomputable def euOutcomePref :
    G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop :=
  G.toAssessmentForm.euOutcomePref G.utility

/-- EU-specialized sequential rationality at one information set. -/
noncomputable def SequentiallyRationalAt
    (A : G.Assessment) {p : G.inf.Player} (I : G.inf.Infoset p) : Prop :=
  G.SequentiallyRationalAtFor G.euOutcomePref A I

/-- EU-specialized sequential rationality at every information set. -/
noncomputable def SequentiallyRational (A : G.Assessment) : Prop :=
  G.SequentiallyRationalFor G.euOutcomePref A

/-- Concrete perfect-Bayesian equilibrium with a supplied preference relation on
outcome distributions. -/
noncomputable def IsPerfectBayesianEqForFamily
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Δ : G.AssessmentDeviationFamily)
    (A : G.Assessment) : Prop :=
  G.SequentiallyRationalForFamily pref Δ A ∧ G.WeaklyConsistentAssessment A

/-- Concrete perfect-Bayesian equilibrium with a supplied preference relation on
outcome distributions and the default full-strategy deviation family. -/
noncomputable def IsPerfectBayesianEqForPref
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (A : G.Assessment) : Prop :=
  G.IsPerfectBayesianEqFor
    (G.SequentiallyRationalFor pref)
    G.WeaklyConsistentAssessment
    A

/-- EU-specialized concrete perfect-Bayesian equilibrium. -/
noncomputable def IsPerfectBayesianEq (A : G.Assessment) : Prop :=
  G.IsPerfectBayesianEqForPref G.euOutcomePref A

/-- Concrete sequential-equilibrium shape with an explicit consistency
predicate. This is the reusable hook for stronger notions such as
Kreps-Wilson consistency as a limit of fully mixed assessments. -/
noncomputable def IsSequentialEqWithConsistencyForFamily
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Δ : G.AssessmentDeviationFamily)
    (Consistent : G.Assessment → Prop)
    (A : G.Assessment) : Prop :=
  G.SequentiallyRationalForFamily pref Δ A ∧ Consistent A

/-- Concrete sequential-equilibrium shape with an explicit consistency predicate
and the default full-strategy deviation family. -/
noncomputable def IsSequentialEqWithConsistencyFor
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Consistent : G.Assessment → Prop)
    (A : G.Assessment) : Prop :=
  G.IsSequentialEqFor (G.SequentiallyRationalFor pref) Consistent A

/-- The on-path/Bayes concrete specialization of sequential equilibrium. Full
Kreps-Wilson sequential equilibrium can be obtained by replacing
`WeaklyConsistentAssessment` with a stronger limit-consistency predicate. -/
noncomputable def IsSequentialEqForPref
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (A : G.Assessment) : Prop :=
  G.IsSequentialEqWithConsistencyFor pref G.WeaklyConsistentAssessment A

/-- EU-specialized concrete sequential-equilibrium predicate using the same
weak consistency condition as `IsPerfectBayesianEq`. -/
noncomputable def IsSequentialEq (A : G.Assessment) : Prop :=
  G.IsSequentialEqForPref G.euOutcomePref A

theorem isPerfectBayesianEqForPref_iff
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (A : G.Assessment) :
    G.IsPerfectBayesianEqForPref pref A ↔
      G.SequentiallyRationalFor pref A ∧ G.WeaklyConsistentAssessment A := by
  rfl

omit [DecidableEq G.inf.Player] in
theorem isPerfectBayesianEqForFamily_iff
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Δ : G.AssessmentDeviationFamily)
    (A : G.Assessment) :
    G.IsPerfectBayesianEqForFamily pref Δ A ↔
      G.SequentiallyRationalForFamily pref Δ A ∧ G.WeaklyConsistentAssessment A := by
  rfl

omit [DecidableEq G.inf.Player] in
theorem isSequentialEqWithConsistencyForFamily_iff
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Δ : G.AssessmentDeviationFamily)
    (Consistent : G.Assessment → Prop)
    (A : G.Assessment) :
    G.IsSequentialEqWithConsistencyForFamily pref Δ Consistent A ↔
      G.SequentiallyRationalForFamily pref Δ A ∧ Consistent A := by
  rfl

theorem isSequentialEqForPref_iff
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (A : G.Assessment) :
    G.IsSequentialEqForPref pref A ↔
      G.SequentiallyRationalFor pref A ∧ G.WeaklyConsistentAssessment A := by
  rfl

theorem isPerfectBayesianEq_iff (A : G.Assessment) :
    G.IsPerfectBayesianEq A ↔
      G.SequentiallyRational A ∧ G.WeaklyConsistentAssessment A := by
  rfl

theorem isSequentialEq_iff (A : G.Assessment) :
    G.IsSequentialEq A ↔
      G.SequentiallyRational A ∧ G.WeaklyConsistentAssessment A := by
  rfl

theorem IsPerfectBayesianEq.sequentiallyRational {A : G.Assessment}
    (h : G.IsPerfectBayesianEq A) : G.SequentiallyRational A :=
  h.1

theorem IsPerfectBayesianEq.weaklyConsistent {A : G.Assessment}
    (h : G.IsPerfectBayesianEq A) : G.WeaklyConsistentAssessment A :=
  h.2

theorem IsPerfectBayesianEq.beliefsSupported {A : G.Assessment}
    (h : G.IsPerfectBayesianEq A) : G.BeliefsSupported A :=
  h.2.1

theorem IsPerfectBayesianEq.bayesConsistentOnPath {A : G.Assessment}
    (h : G.IsPerfectBayesianEq A) : G.BayesConsistentOnPath A :=
  h.2.2

theorem IsSequentialEq.sequentiallyRational {A : G.Assessment}
    (h : G.IsSequentialEq A) : G.SequentiallyRational A :=
  h.1

theorem IsSequentialEq.weaklyConsistent {A : G.Assessment}
    (h : G.IsSequentialEq A) : G.WeaklyConsistentAssessment A :=
  h.2

end StrategicDeviation

end EFGGame

end EFG
