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

open Filter
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

/-- A history with nonzero probability must be a syntactically valid path in
the tree. Zero-probability branches may still be reachable; this lemma only
rules out malformed histories. -/
theorem historyProb_ne_zero_reachable (σ : BehavioralProfile S)
    (t : GameTree S Outcome) (h : List (HistoryStep S))
    (hp : t.historyProb σ h ≠ 0) :
    ∃ u : GameTree S Outcome, ReachBy h t u := by
  induction t generalizing h with
  | terminal z =>
      cases h with
      | nil => exact ⟨.terminal z, ReachBy.here _⟩
      | cons step rest =>
          simp at hp
  | chance k μ hk next ih =>
      cases h with
      | nil =>
          exact ⟨.chance k μ hk next, ReachBy.here _⟩
      | cons step rest =>
          cases step with
          | chance k' b =>
              by_cases hk' : k' = k
              · subst hk'
                have hmul : μ b * (next b).historyProb σ rest ≠ 0 := by
                  simpa [historyProb] using hp
                have hrest : (next b).historyProb σ rest ≠ 0 := right_ne_zero_of_mul hmul
                obtain ⟨u, hu⟩ := ih b rest hrest
                exact ⟨u, ReachBy.chance b hu⟩
              · simp [historyProb, hk'] at hp
          | action p I a =>
              simp [historyProb] at hp
  | @decision p I next ih =>
      cases h with
      | nil =>
          exact ⟨.decision I next, ReachBy.here _⟩
      | cons step rest =>
          cases step with
          | chance k b =>
              simp [historyProb] at hp
          | action q J a =>
              by_cases hq : q = p
              · subst hq
                by_cases hI : J = I
                · subst hI
                  have hmul : σ q J a * (next a).historyProb σ rest ≠ 0 := by
                    simpa [historyProb] using hp
                  have hrest : (next a).historyProb σ rest ≠ 0 := right_ne_zero_of_mul hmul
                  obtain ⟨u, hu⟩ := ih a rest hrest
                  exact ⟨u, ReachBy.action a hu⟩
                · simp [historyProb, hI] at hp
              · simp [historyProb, hq] at hp

/-- Contrapositive of `historyProb_ne_zero_reachable`: malformed histories have
zero probability. -/
theorem historyProb_eq_zero_of_not_reachable (σ : BehavioralProfile S)
    (t : GameTree S Outcome) (h : List (HistoryStep S))
    (hnot : ¬ ∃ u : GameTree S Outcome, ReachBy h t u) :
    t.historyProb σ h = 0 := by
  by_contra hp
  exact hnot (historyProb_ne_zero_reachable σ t h hp)

end GameTree

namespace BehavioralStrategy

variable {S : InfoStructure} {p : S.Player}

/-- Pointwise convergence of behavioral strategies: for every information set,
the local mixed action converges pointwise as a PMF. -/
def ConvergesPointwise
    (σs : ℕ → BehavioralStrategy S p) (σ : BehavioralStrategy S p) : Prop :=
  ∀ I : S.Infoset p, PMFConvergesPointwise (fun n => σs n I) (σ I)

theorem ConvergesPointwise.apply {σs : ℕ → BehavioralStrategy S p}
    {σ : BehavioralStrategy S p} (h : ConvergesPointwise σs σ)
    (I : S.Infoset p) (a : S.Act I) :
    Tendsto (fun n : ℕ => σs n I a) atTop (nhds (σ I a)) :=
  (h I).apply a

end BehavioralStrategy

namespace BehavioralProfile

variable {S : InfoStructure}

/-- A behavioral profile is fully mixed when every local action at every
information set receives nonzero probability. -/
def FullyMixed (σ : BehavioralProfile S) : Prop :=
  ∀ (p : S.Player) (I : S.Infoset p) (a : S.Act I), σ p I a ≠ 0

theorem FullyMixed.apply {σ : BehavioralProfile S} (h : σ.FullyMixed)
    (p : S.Player) (I : S.Infoset p) (a : S.Act I) :
    σ p I a ≠ 0 :=
  h p I a

/-- Pointwise convergence of behavioral profiles, player by player and then
information-set/action by information-set/action. -/
def ConvergesPointwise
    (σs : ℕ → BehavioralProfile S) (σ : BehavioralProfile S) : Prop :=
  ProfileConvergesWith
    (fun p : S.Player => BehavioralStrategy.ConvergesPointwise (S := S) (p := p))
    σs σ

theorem ConvergesPointwise.apply {σs : ℕ → BehavioralProfile S}
    {σ : BehavioralProfile S} (h : ConvergesPointwise σs σ)
    (p : S.Player) (I : S.Infoset p) (a : S.Act I) :
    Tendsto (fun n : ℕ => σs n p I a) atTop (nhds (σ p I a)) :=
  (h p).apply I a

end BehavioralProfile

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

theorem historyProb_ne_zero_reachesTree {σ : BehavioralProfile G.inf}
    {h : List (HistoryStep G.inf)} (hp : G.historyProb σ h ≠ 0) :
    ∃ t : GameTree G.inf G.Outcome, G.ReachesTree h t := by
  exact G.tree.historyProb_ne_zero_reachable σ h hp

theorem historyProb_eq_zero_of_not_reachesTree {σ : BehavioralProfile G.inf}
    {h : List (HistoryStep G.inf)}
    (hnot : ¬ ∃ t : GameTree G.inf G.Outcome, G.ReachesTree h t) :
    G.historyProb σ h = 0 := by
  exact G.tree.historyProb_eq_zero_of_not_reachable σ h hnot

theorem continuationTree_spec_of_reachesTree {h : List (HistoryStep G.inf)}
    {t : GameTree G.inf G.Outcome} (hr : G.ReachesTree h t) :
    ReachBy h G.tree (G.continuationTree h) :=
  G.continuationTree_spec ⟨t, hr⟩

theorem continuationTree_spec_of_reachesInfoSet {p : G.inf.Player}
    {I : G.inf.Infoset p} {h : List (HistoryStep G.inf)}
    (hr : G.ReachesInfoSet I h) :
    ReachBy h G.tree (G.continuationTree h) := by
  obtain ⟨next, hnext⟩ := hr
  exact G.continuationTree_spec ⟨.decision I next, hnext⟩

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

/-- An EFG assessment has a fully mixed behavioral strategy profile. -/
def Assessment.FullyMixed (A : G.Assessment) : Prop :=
  A.strategy.FullyMixed

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

theorem BeliefsSupported.at {A : G.Assessment}
    (h : G.BeliefsSupported A) {p : G.inf.Player} (I : G.inf.Infoset p) :
    G.BeliefSupportedAt A I :=
  h p I

theorem BeliefSupportedAt.reachesInfoSet {A : G.Assessment}
    {p : G.inf.Player} {I : G.inf.Infoset p}
    (h : G.BeliefSupportedAt A I)
    {hist : List (HistoryStep G.inf)} (hhist : A.beliefs I hist ≠ 0) :
    G.ReachesInfoSet I hist :=
  h hist hhist

theorem BeliefSupportedAt.continuationTree_spec {A : G.Assessment}
    {p : G.inf.Player} {I : G.inf.Infoset p}
    (h : G.BeliefSupportedAt A I)
    {hist : List (HistoryStep G.inf)} (hhist : A.beliefs I hist ≠ 0) :
    ReachBy hist G.tree (G.continuationTree hist) :=
  G.continuationTree_spec_of_reachesInfoSet (h.reachesInfoSet G hhist)

/-- Pointwise Bayes rule at an EFG information set. -/
noncomputable def BayesRuleAt (A : G.Assessment)
    {p : G.inf.Player} (I : G.inf.Infoset p) : Prop :=
  G.toAssessmentForm.BayesRuleAt (A.toGeneric G) I

/-- On-path Bayes consistency for EFG assessments. -/
noncomputable def BayesConsistentOnPath (A : G.Assessment) : Prop :=
  G.toAssessmentForm.BayesConsistentOnPath (A.toGeneric G)

/-- Bayes consistency at all EFG information sets. This is the usual
per-approximant consistency condition for fully mixed assessments. -/
noncomputable def BayesConsistentEverywhere (A : G.Assessment) : Prop :=
  G.toAssessmentForm.BayesConsistentEverywhere (A.toGeneric G)

/-- Weak consistency for EFG PBE-style assessments. -/
noncomputable def WeaklyConsistentAssessment (A : G.Assessment) : Prop :=
  G.toAssessmentForm.WeaklyConsistentAssessment (A.toGeneric G)

/-- Strong pointwise consistency for EFG assessments: support everywhere and
Bayes' rule everywhere. -/
noncomputable def FullyConsistentAssessment (A : G.Assessment) : Prop :=
  G.toAssessmentForm.FullyConsistentAssessment (A.toGeneric G)

/-- Generic limit consistency specialized to EFG assessments.

The convergence relation is intentionally supplied by the caller, so this
definition can be used with product-topology convergence, coordinatewise
convergence, or a finite-game metric without changing the equilibrium layer. -/
noncomputable def IsLimitConsistentAssessment
    (Admissible : G.Assessment → Prop)
    (StepConsistent : G.Assessment → Prop)
    (ConvergesTo : (ℕ → G.Assessment) → G.Assessment → Prop)
    (A : G.Assessment) : Prop :=
  G.toAssessmentForm.IsLimitConsistentAssessment
    (fun A' => Admissible (Assessment.ofGeneric G A'))
    (fun A' => StepConsistent (Assessment.ofGeneric G A'))
    (fun As A' =>
      ConvergesTo
        (fun n => Assessment.ofGeneric G (As n))
        (Assessment.ofGeneric G A'))
    (A.toGeneric G)

theorem isLimitConsistentAssessment_iff
    (Admissible : G.Assessment → Prop)
    (StepConsistent : G.Assessment → Prop)
    (ConvergesTo : (ℕ → G.Assessment) → G.Assessment → Prop)
    (A : G.Assessment) :
    G.IsLimitConsistentAssessment Admissible StepConsistent ConvergesTo A ↔
      ∃ As : ℕ → G.Assessment,
        (∀ n, Admissible (As n) ∧ StepConsistent (As n)) ∧ ConvergesTo As A := by
  constructor
  · intro h
    rcases h with ⟨As, hstep, hconv⟩
    refine ⟨fun n => Assessment.ofGeneric G (As n), ?_, ?_⟩
    · intro n
      exact hstep n
    · change ConvergesTo
        (fun n => Assessment.ofGeneric G (As n))
        (Assessment.ofGeneric G (A.toGeneric G)) at hconv
      simpa using hconv
  · rintro ⟨As, hstep, hconv⟩
    refine ⟨fun n => (As n).toGeneric G, ?_, ?_⟩
    · intro n
      simpa using hstep n
    · change ConvergesTo
        (fun n => Assessment.ofGeneric G ((As n).toGeneric G))
        (Assessment.ofGeneric G (A.toGeneric G))
      simpa using hconv

theorem FullyConsistentAssessment.weaklyConsistent {A : G.Assessment}
    (h : G.FullyConsistentAssessment A) :
    G.WeaklyConsistentAssessment A :=
  GameTheory.AssessmentForm.FullyConsistentAssessment.weaklyConsistent G.toAssessmentForm h

/-- Pointwise convergence of EFG assessments: behavioral strategies converge
pointwise and every belief PMF converges pointwise over histories. -/
def AssessmentConvergesPointwise
    (As : ℕ → G.Assessment) (A : G.Assessment) : Prop :=
  BehavioralProfile.ConvergesPointwise (fun n => (As n).strategy) A.strategy ∧
    ∀ (p : G.inf.Player) (I : G.inf.Infoset p),
      PMFConvergesPointwise (fun n => (As n).beliefs I) (A.beliefs I)

/-- Generic assessment pointwise convergence agrees with the concrete EFG
componentwise spelling. -/
theorem assessmentConvergesPointwise_iff_generic
    (As : ℕ → G.Assessment) (A : G.Assessment) :
    G.AssessmentConvergesPointwise As A ↔
      G.toAssessmentForm.AssessmentConvergesPointwiseWith
        (fun p : G.inf.Player =>
          BehavioralStrategy.ConvergesPointwise (S := G.inf) (p := p))
        (fun n => (As n).toGeneric G)
        (A.toGeneric G) := by
  rfl

/-- Kreps-Wilson-style consistency shape for EFG assessments: the assessment is
a pointwise limit of fully mixed, weakly consistent assessments.

The per-approximant consistency condition is weak/on-path consistency rather
than Bayes everywhere because chance moves may have zero-probability branches;
fully mixed player behavior alone does not make those histories reachable. -/
noncomputable def SequentiallyConsistentAssessment (A : G.Assessment) : Prop :=
  G.IsLimitConsistentAssessment
    (fun A' => A'.FullyMixed G)
    G.WeaklyConsistentAssessment
    G.AssessmentConvergesPointwise
    A

theorem sequentiallyConsistentAssessment_iff (A : G.Assessment) :
    G.SequentiallyConsistentAssessment A ↔
      ∃ As : ℕ → G.Assessment,
        (∀ n, (As n).FullyMixed G ∧ G.WeaklyConsistentAssessment (As n)) ∧
          G.AssessmentConvergesPointwise As A := by
  exact G.isLimitConsistentAssessment_iff
    (fun A' => A'.FullyMixed G)
    G.WeaklyConsistentAssessment
    G.AssessmentConvergesPointwise
    A

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

/-- EFG sequential-equilibrium shape with generic limit consistency and an
explicit deviation family. -/
noncomputable def IsSequentialEqWithLimitConsistencyForFamily
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Δ : G.AssessmentDeviationFamily)
    (Admissible : G.Assessment → Prop)
    (StepConsistent : G.Assessment → Prop)
    (ConvergesTo : (ℕ → G.Assessment) → G.Assessment → Prop)
    (A : G.Assessment) : Prop :=
  G.IsSequentialEqWithConsistencyForFamily pref Δ
    (G.IsLimitConsistentAssessment Admissible StepConsistent ConvergesTo) A

/-- Concrete sequential-equilibrium shape with an explicit consistency predicate
and the default full-strategy deviation family. -/
noncomputable def IsSequentialEqWithConsistencyFor
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Consistent : G.Assessment → Prop)
    (A : G.Assessment) : Prop :=
  G.IsSequentialEqFor (G.SequentiallyRationalFor pref) Consistent A

/-- EFG sequential-equilibrium shape with generic limit consistency and the
default full-strategy deviation family. -/
noncomputable def IsSequentialEqWithLimitConsistencyFor
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (Admissible : G.Assessment → Prop)
    (StepConsistent : G.Assessment → Prop)
    (ConvergesTo : (ℕ → G.Assessment) → G.Assessment → Prop)
    (A : G.Assessment) : Prop :=
  G.IsSequentialEqWithConsistencyFor pref
    (G.IsLimitConsistentAssessment Admissible StepConsistent ConvergesTo) A

/-- Concrete sequential equilibrium: sequential rationality plus
Kreps-Wilson-style pointwise limit consistency. The weaker on-path/Bayes notion
is `IsPerfectBayesianEqForPref`. -/
noncomputable def IsSequentialEqForPref
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (A : G.Assessment) : Prop :=
  G.IsSequentialEqWithConsistencyFor pref G.SequentiallyConsistentAssessment A

/-- EU-specialized concrete sequential-equilibrium predicate using pointwise
limit consistency. -/
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
      G.SequentiallyRationalFor pref A ∧ G.SequentiallyConsistentAssessment A := by
  rfl

theorem isPerfectBayesianEq_iff (A : G.Assessment) :
    G.IsPerfectBayesianEq A ↔
      G.SequentiallyRational A ∧ G.WeaklyConsistentAssessment A := by
  rfl

theorem isSequentialEq_iff (A : G.Assessment) :
    G.IsSequentialEq A ↔
      G.SequentiallyRational A ∧ G.SequentiallyConsistentAssessment A := by
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

theorem IsSequentialEq.sequentiallyConsistent {A : G.Assessment}
    (h : G.IsSequentialEq A) : G.SequentiallyConsistentAssessment A :=
  h.2

end StrategicDeviation

end EFGGame

end EFG
